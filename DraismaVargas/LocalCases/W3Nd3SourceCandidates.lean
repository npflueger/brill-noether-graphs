module

public import DraismaVargas.LocalCases.W3Nd2SourceCandidates

@[expose] public section

/-!
# Source-derived W3 nd3-t3 candidates: Equation (4), Figure 30

Source: Draisma–Vargas Part I, arXiv:1909.12924, Case `{w3-r1-nd3-t3}`, Figure 30 and
Equation (4).  This is the
`W3IncomingClassification.Classification.nd3CoarseFine` branch: the
distinguished wall block `A₀` carries three surviving occurrences `e₂, e₃, e₄`
with `e₂`, `e₃` in **one** target direction `t₃` and `e₄` in another, `t₄`.
The paper's arithmetic then forces `k₄ = |A₀|` and `k₂ + k₃ = |A₀|`, which are
exactly `W3R1SourceProfile.Nd3Profile.doubled_direction`.

## What this module builds

From an actual `W3SourceInput`, an actual `Nd3Profile` and the doubled
direction `hSame`, it constructs

* `geometry`, the numerical `GlobalCoarseFine.Nd3Geometry` of Equation (4),
  with `k₂`, `k₃` the two literal occurrence indices in the doubled direction;
* `coarseCandidate`, Figure 30's member `M⁽¹⁾` (`α = 3`), together with
  `coarseCandidate_valid` and `coarseCandidate_sourceGenus`;
* `fineCandidate`, Figure 30's member `M⁽²⁾` (`α = 4`), together with
  `fineCandidate_valid` and `fineCandidate_sourceGenus`;
* the three denominators of Equation (4) as literal block cardinalities of the
  two assembled resolutions: `coarse_pasted_newEdge_blockCard_selected`
  (`|e'| = k₄ = k₂ + k₃`), `fine_pasted_newEdge_blockCard_first` (`|e'| = k₂`)
  and `fine_pasted_newEdge_blockCard_second` (`|e''| = k₃`).

In `M⁽¹⁾` the doubled direction `t₃` sits at the divalent endpoint `u`, the new
edge `t₁` carries the whole block `A₀`, and `t₂`, `t₄` sit at the trivalent
endpoint `v`.  In `M⁽²⁾` the largest direction `t₄` sits at `u`, the whole
block `A₀` is retained there, and the two-block partition of `A₀` cut out by
`t₃` sits on the new edge **and at the trivalent endpoint** `v`, beside `t₃`
and `t₂`.

Every unramified wall block is resolved with the divalent-side direction's
edge partition on the new edge, so the original `r = 0` local ramification
equation supplies the arbitrary-degree background Riemann--Hurwitz count in
both members.

## The fine member is *not* `Nd3Geometry.fineLocal`

`GlobalCoarseFine.Nd3Geometry.fineLocal` is `fineResolution`, which places the
fine partition at the **divalent** endpoint.  That is the conditional
interface's same-side resolution and is a different geometry from Figure 30's
`M⁽²⁾`; validity and genus preservation alone would not justify substituting
it, exactly as for Equation (5)'s fine member (`W3Nd2SourceCandidates`).  `fineCandidate`
below therefore uses `selectedResolution`, the `LocalResolution.reverse` of
`fineResolution`, and is installed through `Background.install` directly rather
than through `GlobalCoarseFine.nd3Candidates`.  Pairing the two members into
`GlobalCoarseFine.nd3BalancedFamily` would first need that family to accept the
reversed fine pattern; that is a change to `GlobalCoarseFine`, not to this
file, and is **not** claimed here.

## Which side of the presentation bridge

`ThirdEquation.W3SourceInput` is the **codimension-one wall datum** interface,
field for field the `W4StableSource.AuxR0SourceInput` shape: it carries
`equation_c : data.targetExcess wall = 1` and
`stablePath_card : #(StablePath data) = |E(target)| + 1`.  By
`FullDimensionalSource`, both fields are incompatible with a
`FullDimensionalSourcePresentation` of the *same* datum.  Everything here
therefore lives on the `AuxR0SourceInput` / wall-datum side of that bridge, and
nothing here may be applied to a full-dimensional presentation without the
`WallDegeneration` bridge between the two data.

## Why the hypotheses can hold at once

The only added hypothesis beyond an actual `W3SourceInput` and an actual
`Nd3Profile` is `hSame : profile.first.1.1.1 = profile.second.1.1.1`, the
doubled target direction.  `W3R1SourceProfile.Nd3Profile.cases` splits every
nd3 profile into exactly three mutually exclusive alternatives, and this is the
first of them; `W3IncomingClassification.exists_classification` routes it to
`.nd3CoarseFine`.  The numerical fields `k₂ + k₃ = |A₀|` and `k₄ = |A₀|` are
*derived* from `hSame` through `Nd3Profile.doubled_direction`, not assumed, so
no numerical diagram is imposed on the source.

## Two source notes on Figure 30 / Equation (4)

* Figure 30 and Equation (4) **are** consistent: the apparent transposition
  of the `σ₀` terms is a regrouping.  Figure 30
  gives `c⁽¹⁾ = c(e₄)/(k₂+k₃) + σ₀(J₀,3)` and
  `c⁽²⁾ = c(e₂)/k₂ + c(e₃)/k₃ + σ₀(J₀,4)`, which is what the geometry of
  `α = 3, 4` forces; Equation (4) displays the same total regrouped as
  `(c(e₄)/(k₂+k₃) + σ₀(J₀,4)) + (c(e₂)/k₂ + c(e₃)/k₃ + σ₀(J₀,3))`, whose two
  brackets are exactly the two vanishing `M₀` relations, hence `0 + 0 = 0`.
  The brackets are therefore not `c⁽¹⁾` and `c⁽²⁾` individually.
  `ResolutionCoarseFine.w3_nd3_t3_block_resolution` formalizes it that way
  round: Figure 30's determinants as the conclusion, the two `M₀` relations as
  `h₃` and `h₄`.
* The prose of the case attaches the two members to `α = 3` and `α = 4` the
  other way round from Figure 30: with `α = 3` the divalent end `u` carries
  `t₃`, so it is `e₄⁽¹⁾` that has an end above `v` and `G⁽¹⁾_{A₀}` that has the
  single edge `e'` with `|e'| = k₄`, while `α = 4` gives the two edges `e'`,
  `e''` of sizes `k₂`, `k₃`.  This module follows the figure.
-/
namespace DraismaVargas.LocalCases.W3Nd3SourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine GlobalCoarseFine
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary M11SourceGenus
open W3Nd2SourceCandidates (OrientedStar exists_orientedStar rightOf
  wallEdgesAssigned_false wallEdgesAssigned_true external_count_eq)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-! ## Literal occurrences of the distinguished block -/

/-- Every occurrence incident to the distinguished wall block lies above an
occurrence incident to the wall. -/
theorem incident_target_mem (input : W3SourceInput data star)
    (edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) :
    edge.1.1.1 ∈ GluingDatum.incidentEdges wall :=
  ((incident_wallBlock_sourceVertex_iff data input.distinguishedBlock
    edge.1).mp edge.2).1

/-- Every occurrence incident to the distinguished wall block has its sheet in
that block. -/
theorem incident_wall_rel (input : W3SourceInput data star)
    (edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock)) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.1.2 := by
  have hBlock := ((incident_wallBlock_sourceVertex_iff data
    input.distinguishedBlock edge.1).mp edge.2).2
  have hValue := congrArg Subtype.val hBlock
  change (data.vertexPartition wall).repr edge.1.1.2 =
    input.distinguishedBlock.1 at hValue
  change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
    (data.vertexPartition wall).repr edge.1.1.2
  rw [input.distinguishedBlock.2, hValue]

/-! ## The Figure 30 partition data -/

/-- Figure 30's fine partition is the actual edge partition of the doubled
target direction `t₃`. -/
abbrev finePartition (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    SheetPartition degree := data.edgePartition profile.first.1.1.1

theorem fine_refines_wall (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (finePartition input profile).Refines (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data (incident_target_mem input profile.first)

/-- The second survivor's sheet is a representative of the **same** edge
partition, because the two survivors share a target direction. -/
theorem second_repr (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (finePartition input profile).repr profile.second.1.1.2 =
      profile.second.1.1.2 := by
  show (data.edgePartition profile.first.1.1.1).repr profile.second.1.1.2 =
    profile.second.1.1.2
  rw [congrArg data.edgePartition hSame]
  exact profile.second.1.2

/-- The two smaller survivors are distinct blocks of the doubled direction. -/
theorem fine_separate (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    ¬ (finePartition input profile).Rel profile.first.1.1.2
      profile.second.1.1.2 := by
  intro hRel
  apply profile.first_ne_second
  have hFirst : (finePartition input profile).repr profile.first.1.1.2 =
      profile.first.1.1.2 := profile.first.1.2
  have hSecond := second_repr input profile hSame
  have hSheet : profile.first.1.1.2 = profile.second.1.1.2 := by
    have hEq : (finePartition input profile).repr profile.first.1.1.2 =
      (finePartition input profile).repr profile.second.1.1.2 := hRel
    rw [hFirst, hSecond] at hEq
    exact hEq
  exact Subtype.ext (Subtype.ext (Prod.ext hSame hSheet))

/-- The literal Figure 30 profile supplies every numerical field of the
conditional coarse/fine geometry interface for Equation (4).  `k₂` and `k₃`
are the two indices in the doubled direction; the paper's `k₄ = |A₀|` is
recorded by `Nd3Profile.doubled_direction` and is not a separate field. -/
noncomputable def geometry (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    Nd3Geometry data wall where
  fine := finePartition input profile
  first := profile.first.1.1.2
  second := profile.second.1.1.2
  fine_refines := fine_refines_wall input profile
  wall_together :=
    (incident_wall_rel input profile.first).symm.trans
      (incident_wall_rel input profile.second)
  fine_separate := fine_separate input profile hSame
  k₂ := data.sourceEdgeIndex profile.first.1
  k₃ := data.sourceEdgeIndex profile.second.1
  k₂_pos := sourceEdgeIndex_pos data profile.first.1
  k₃_pos := sourceEdgeIndex_pos data profile.second.1
  fineFirstCard := rfl
  fineSecondCard := by
    show (data.edgePartition profile.first.1.1.1).blockCard
      profile.second.1.1.2 = data.sourceEdgeIndex profile.second.1
    rw [congrArg data.edgePartition hSame]
    rfl
  wallCard := by
    have hRel := incident_wall_rel input profile.first
    unfold SheetPartition.blockCard
    rw [← (data.vertexPartition wall).block_eq_of_rel hRel]
    exact (profile.doubled_direction hSame).1.symm

/-! ## The doubled direction induces exactly two blocks -/

/-- The two smaller survivors have indices `k₂`, `k₃` summing to the whole
block size, so the doubled direction cuts the distinguished wall block into
**exactly** two pieces.  This is the source's `k₂ + k₃ = |A₀|`, read as a
statement about literal induced blocks. -/
theorem fine_blockCountWithin_eq_two (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePartition input profile).blockCountWithin
      (data.vertexPartition wall) sheet = 2 := by
  classical
  let fine := finePartition input profile
  let coarse := data.vertexPartition wall
  let coarseBlock : coarse.Blocks := input.distinguishedBlock
  let bigFirst : fine.Blocks := ⟨profile.first.1.1.2, profile.first.1.2⟩
  let bigSecond : fine.Blocks :=
    ⟨profile.second.1.1.2, second_repr input profile hSame⟩
  let blocks := SheetPartition.blocksWithin fine coarse coarseBlock
  have hFirstMem : bigFirst ∈ blocks := by
    apply (SheetPartition.mem_blocksWithin fine coarse coarseBlock bigFirst).mpr
    apply (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse
      bigFirst coarseBlock).mpr
    exact incident_wall_rel input profile.first
  have hSecondMem : bigSecond ∈ blocks := by
    apply (SheetPartition.mem_blocksWithin fine coarse coarseBlock bigSecond).mpr
    apply (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse
      bigSecond coarseBlock).mpr
    exact incident_wall_rel input profile.second
  have hNe : bigFirst ≠ bigSecond := by
    intro hEq
    apply fine_separate input profile hSame
    have hVal : profile.first.1.1.2 = profile.second.1.1.2 :=
      congrArg Subtype.val hEq
    show (finePartition input profile).Rel profile.first.1.1.2
      profile.second.1.1.2
    unfold SheetPartition.Rel
    rw [hVal]
  have hSecondErase : bigSecond ∈ blocks.erase bigFirst :=
    Finset.mem_erase.mpr ⟨fun hEq ↦ hNe hEq.symm, hSecondMem⟩
  have hFirstCard : fine.blockCard bigFirst.1 =
      data.sourceEdgeIndex profile.first.1 := rfl
  have hSecondCard : fine.blockCard bigSecond.1 =
      data.sourceEdgeIndex profile.second.1 := by
    show (data.edgePartition profile.first.1.1.1).blockCard
      profile.second.1.1.2 = data.sourceEdgeIndex profile.second.1
    rw [congrArg data.edgePartition hSame]
    rfl
  have hSum := sum_blockCard_blocksWithin fine coarse
    (fine_refines_wall input profile) coarseBlock
  have hEraseFirst :
      (∑ block ∈ blocks.erase bigFirst, (fine.blockCard block.1 : ℤ)) +
          (fine.blockCard bigFirst.1 : ℤ) =
        ∑ block ∈ blocks, (fine.blockCard block.1 : ℤ) :=
    Finset.sum_erase_add blocks (fun block ↦ (fine.blockCard block.1 : ℤ))
      hFirstMem
  have hEraseSecond :
      (∑ block ∈ (blocks.erase bigFirst).erase bigSecond,
            (fine.blockCard block.1 : ℤ)) +
          (fine.blockCard bigSecond.1 : ℤ) =
        ∑ block ∈ blocks.erase bigFirst, (fine.blockCard block.1 : ℤ) :=
    Finset.sum_erase_add (blocks.erase bigFirst)
      (fun block ↦ (fine.blockCard block.1 : ℤ)) hSecondErase
  have hRest : (((blocks.erase bigFirst).erase bigSecond).card : ℤ) ≤
      ∑ block ∈ (blocks.erase bigFirst).erase bigSecond,
        (fine.blockCard block.1 : ℤ) := by
    calc
      (((blocks.erase bigFirst).erase bigSecond).card : ℤ) =
          ∑ _block ∈ (blocks.erase bigFirst).erase bigSecond, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun block _ ↦ by
        exact_mod_cast fine.blockCard_pos block.1
  have hPair : data.sourceEdgeIndex profile.first.1 +
      data.sourceEdgeIndex profile.second.1 = coarse.blockCard coarseBlock.1 :=
    (profile.doubled_direction hSame).1
  have hRestZero : ((blocks.erase bigFirst).erase bigSecond).card = 0 := by
    have hCast : (data.sourceEdgeIndex profile.first.1 : ℤ) +
        (data.sourceEdgeIndex profile.second.1 : ℤ) =
          (coarse.blockCard coarseBlock.1 : ℤ) := by exact_mod_cast hPair
    rw [hFirstCard] at hEraseFirst
    rw [hSecondCard] at hEraseSecond
    have hZero : (((blocks.erase bigFirst).erase bigSecond).card : ℤ) ≤ 0 := by
      linarith [hSum, hEraseFirst, hEraseSecond, hRest, hCast]
    exact_mod_cast Nat.le_zero.mp (by exact_mod_cast hZero)
  have hCardFirst : (blocks.erase bigFirst).card + 1 = blocks.card :=
    Finset.card_erase_add_one hFirstMem
  have hCardSecond : ((blocks.erase bigFirst).erase bigSecond).card + 1 =
      (blocks.erase bigFirst).card :=
    Finset.card_erase_add_one hSecondErase
  have hBlocksCard : blocks.card = 2 := by omega
  have hCount := SheetPartition.card_blocksWithin_eq_blockCountWithin fine coarse
    (fine_refines_wall input profile) coarseBlock
  have hCongr := SheetPartition.blockCountWithin_congr fine coarse hSheet
  change fine.blockCountWithin coarse sheet = 2
  calc
    fine.blockCountWithin coarse sheet =
        fine.blockCountWithin coarse coarseBlock.1 := hCongr.symm
    _ = blocks.card := hCount.symm
    _ = 2 := hBlocksCard

/-! ## The Figure 30 coarse member `M⁽¹⁾` -/

/-- The source-prescribed orientation of `M⁽¹⁾` (`α = 3`): the doubled
direction `t₃` is the divalent-side occurrence, and the remaining two actual
target occurrences `t₂`, `t₄` sit at the trivalent endpoint. -/
noncomputable def orientedStar (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    OrientedStar target wall profile.first.1.1.1 :=
  Classical.choice (exists_orientedStar star profile.first.1.1.1
    (incident_target_mem input profile.first))

/-- The arbitrary-degree background uses the same doubled-direction/whole-wall
star on every unramified wall block.  The original `r = 0` equation is exactly
the trivalent endpoint count. -/
noncomputable def background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    Background data wall profile.first.1.1.2 := by
  let orientation := orientedStar input profile
  let fine := finePartition input profile
  have hFine := fine_refines_wall input profile
  let localResolution : LocalResolution degree :=
    fineResolution (data.vertexPartition wall) fine hFine
  refine {
    right := rightOf profile.first.1.1.1
    resolution := fun _ ↦ localResolution
    contracts := ?_
    exterior := ?_
    leftEdges := [profile.first.1.1.1]
    rightEdges := [orientation.rightFirst, orientation.rightSecond]
    leftEdges_eq := ?_
    rightEdges_eq := ?_
    left_riemannHurwitz := ?_
    right_riemannHurwitz := ?_ }
  · intro _ _
    exact fineResolution_contracts _ fine hFine
  · intro edge hIncident _ _
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hEq : edge = profile.first.1.1.1
    · subst edge
      change fine.Refines
        (if rightOf profile.first.1.1.1 profile.first.1.1.1 then
          localResolution.right else localResolution.left)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false,
        localResolution, fineResolution]
      exact SheetPartition.Refines.refl fine
    · have hRight : rightOf profile.first.1.1.1 edge = true := by
        simp [rightOf, hEq]
      rw [hRight, ite_eq_left rfl]
      change (data.edgePartition edge).Refines (data.vertexPartition wall)
      exact refines_of_mem_incidentEdges data hAt
  · rw [wallEdgesAssigned_false orientation]
    rfl
  · rw [wallEdgesAssigned_true orientation]
    rw [Finset.insert_val_of_notMem (by simpa using orientation.right_ne)]
    rfl
  · intro anchor _ _
    exact fineResolution_left_riemannHurwitzAtBlock
      (data.vertexPartition wall) fine (data.edgePartition profile.first.1.1.1)
      hFine anchor
  · intro anchor _ hOther
    apply riemannHurwitzAtBlock_trivalent_of_counts
      (data.vertexPartition wall) (data.vertexPartition wall) fine
      (data.edgePartition orientation.rightFirst)
      (data.edgePartition orientation.rightSecond) anchor
    intro sheet hSheet
    have hSheetOther : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet := fun h ↦ hOther
      ((incident_wall_rel input profile.first).symm.trans h |>.trans hSheet.symm)
    have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
        input.distinguishedBlock := by
      intro hEq
      apply hSheetOther
      have hValue := congrArg Subtype.val hEq
      change (data.vertexPartition wall).repr sheet =
        input.distinguishedBlock.1 at hValue
      change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
        (data.vertexPartition wall).repr sheet
      rw [input.distinguishedBlock.2, hValue]
    have hZero := input.localRamification_eq_zero_of_ne hBlockNe
    have hTotal := external_count_eq (data := data) star orientation sheet
    rw [hZero] at hTotal
    have hTotalNat' :
        (data.edgePartition profile.first.1.1.1).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          0 + 2 + (data.vertexPartition wall).blockCard sheet := by
      exact_mod_cast hTotal
    have hTotalNat :
        fine.blockCountWithin (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          (data.vertexPartition wall).blockCard sheet + 2 := by
      simpa [fine, finePartition, Nat.add_comm] using hTotalNat'
    change fine.blockCountWithin (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightFirst).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightSecond).blockCountWithin
          (data.vertexPartition wall) sheet ≥
      (data.vertexPartition wall).blockCard sheet + 2
    exact hTotalNat.ge

/-- On the distinguished block, the three exterior induced-block counts sum
to the block size plus three, because its local ramification is one. -/
theorem distinguished_external_count (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition profile.first.1.1.1).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition (orientedStar input profile).rightFirst).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition (orientedStar input profile).rightSecond).blockCountWithin
          (data.vertexPartition wall) sheet =
      (data.vertexPartition wall).blockCard sheet + 3 := by
  have hBlock : (data.vertexPartition wall).toBlock sheet =
      input.distinguishedBlock := by
    apply Subtype.ext
    exact (input.distinguishedBlock.2.symm.trans hSheet).symm
  have hRam : data.localRamification wall
      ((data.vertexPartition wall).toBlock sheet) = 1 := by
    rw [hBlock]
    exact input.localRamification_distinguishedBlock
  have hTotal := external_count_eq (data := data) star
    (orientedStar input profile) sheet
  rw [hRam] at hTotal
  have hNat :
      (data.edgePartition profile.first.1.1.1).blockCountWithin
            (data.vertexPartition wall) sheet +
          (data.edgePartition (orientedStar input profile).rightFirst).blockCountWithin
            (data.vertexPartition wall) sheet +
          (data.edgePartition (orientedStar input profile).rightSecond).blockCountWithin
            (data.vertexPartition wall) sheet =
        1 + 2 + (data.vertexPartition wall).blockCard sheet := by
    exact_mod_cast hTotal
  omega

/-- Figure 30's coarse member `M⁽¹⁾`: the whole distinguished wall block is
retained on the new edge and at both of its endpoints. -/
noncomputable def coarsePattern (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    TrivalentPattern (data := data) (wall := wall)
      (geometry input profile hSame).first
      (geometry input profile hSame).coarseLocal := by
  let orientation := orientedStar input profile
  refine {
    background := background input profile
    leftExternal := profile.first.1.1.1
    rightExternalFirst := orientation.rightFirst
    rightExternalSecond := orientation.rightSecond
    leftEdges := rfl
    rightEdges := rfl
    exterior := ?_
    rightCounts := ?_ }
  · intro edge hIncident
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    have hRefines := refines_of_mem_incidentEdges data hAt
    simpa only [Nd3Geometry.coarseLocal, thirdResolution, joinedResolutionAt,
      ite_self] using hRefines
  · intro anchor hAnchor sheet hSheet
    have hDistSheet : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet :=
      (incident_wall_rel input profile.first).trans hAnchor |>.trans hSheet
    have hTotal :
        (data.edgePartition profile.first.1.1.1).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          (data.vertexPartition wall).blockCard sheet + 3 := by
      simpa [orientation] using
        distinguished_external_count input profile sheet hDistSheet
    change (finePartition input profile).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightFirst).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightSecond).blockCountWithin
          (data.vertexPartition wall) sheet =
      (data.vertexPartition wall).blockCard sheet + 3 at hTotal
    have hFineTwo := fine_blockCountWithin_eq_two input profile hSame sheet
      hDistSheet
    change (data.vertexPartition wall).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightFirst).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightSecond).blockCountWithin
          (data.vertexPartition wall) sheet ≥
      (data.vertexPartition wall).blockCard sheet + 2
    rw [SheetPartition.blockCountWithin_self]
    omega

/-- The actual globally assembled coarse Figure 30 datum. -/
noncomputable def coarseCandidate (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    BalancedGlobal.Candidate target degree data wall :=
  (coarsePattern input profile hSame).candidate
    (nd3_coarse_contracts (geometry input profile hSame))

/-- The source-derived coarse member is valid whenever the incoming datum is. -/
theorem coarseCandidate_valid (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (coarseCandidate input profile hSame).datum.Valid :=
  (coarseCandidate input profile hSame).datum_valid input.valid

/-- The coarse member preserves the complete quotient-source genus.  Selected
and background blocks are both pasted stars, so the Euler identity is
pointwise and does not assume a separate genus receipt. -/
theorem coarseCandidate_sourceGenus (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    genus (coarseCandidate input profile hSame).datum.sourceGraph =
      genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro sheet
  have hResolution : (coarseCandidate input profile hSame).resolution sheet =
      LocalResolution.onBlock (data.vertexPartition wall)
        (geometry input profile hSame).first
        (geometry input profile hSame).coarseLocal
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (finePartition input profile) (fine_refines_wall input profile))
        sheet := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel
      (geometry input profile hSame).first sheet
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩

/-! ## The third target direction

Above the distinguished block only `t₃` (twice) and `t₄` survive, so every
occurrence in the remaining direction `t₂` is dangling and therefore has a
singleton edge block.  This is the localized refinement input for Figure 30's
fine member, exactly as `W3Nd2FineRefinement` supplies it for Figure 31. -/

/-- The largest survivor's target direction `t₄`. -/
abbrev largestTarget (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) : target.edges :=
  profile.largest.1.1.1

theorem largestTarget_mem (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    largestTarget input profile ∈ GluingDatum.incidentEdges wall :=
  incident_target_mem input profile.largest

private theorem largest_eq_rightFirst_or_rightSecond
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    largestTarget input profile = (orientedStar input profile).rightFirst ∨
      largestTarget input profile = (orientedStar input profile).rightSecond := by
  have hAt := largestTarget_mem input profile
  rw [(orientedStar input profile).incidentEdges_eq] at hAt
  simp only [Finset.mem_insert, Finset.mem_singleton] at hAt
  rcases hAt with hShared | hFirst | hSecond
  · exact (profile.first_target_ne hShared.symm).elim
  · exact Or.inl hFirst
  · exact Or.inr hSecond

/-- The target occurrence `t₂`, distinct from both surviving directions. -/
noncomputable def thirdTarget (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) : target.edges :=
  if largestTarget input profile = (orientedStar input profile).rightFirst then
    (orientedStar input profile).rightSecond
  else
    (orientedStar input profile).rightFirst

theorem thirdTarget_mem (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    thirdTarget input profile ∈ GluingDatum.incidentEdges wall := by
  by_cases hLargest : largestTarget input profile =
      (orientedStar input profile).rightFirst
  · simp only [thirdTarget, ite_eq_left hLargest]
    rw [(orientedStar input profile).incidentEdges_eq]
    simp
  · simp only [thirdTarget, ite_eq_right hLargest]
    rw [(orientedStar input profile).incidentEdges_eq]
    simp

theorem thirdTarget_ne_shared (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    thirdTarget input profile ≠ profile.first.1.1.1 := by
  by_cases hLargest : largestTarget input profile =
      (orientedStar input profile).rightFirst
  · simpa only [thirdTarget, ite_eq_left hLargest] using
      (orientedStar input profile).rightSecond_ne_left
  · simpa only [thirdTarget, ite_eq_right hLargest] using
      (orientedStar input profile).rightFirst_ne_left

theorem thirdTarget_ne_largest (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    thirdTarget input profile ≠ largestTarget input profile := by
  by_cases hLargest : largestTarget input profile =
      (orientedStar input profile).rightFirst
  · simp only [thirdTarget, ite_eq_left hLargest]
    intro hEq
    apply (orientedStar input profile).right_ne
    exact hLargest.symm.trans hEq.symm
  · simp only [thirdTarget, ite_eq_right hLargest]
    intro hEq
    exact hLargest hEq.symm

theorem incidentEdges_eq (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    GluingDatum.incidentEdges wall =
      {profile.first.1.1.1, largestTarget input profile,
        thirdTarget input profile} := by
  by_cases hLargest : largestTarget input profile =
      (orientedStar input profile).rightFirst
  · rw [(orientedStar input profile).incidentEdges_eq]
    simp only [thirdTarget, ite_eq_left hLargest]
    rw [hLargest]
  · rcases largest_eq_rightFirst_or_rightSecond input profile with
      hFirst | hSecond
    · exact (hLargest hFirst).elim
    · rw [(orientedStar input profile).incidentEdges_eq]
      simp only [thirdTarget, ite_eq_right hLargest]
      rw [hSecond, Finset.pair_comm]

/-- The canonical source occurrence in the third direction through a selected
sheet. -/
noncomputable abbrev thirdSourceEdge (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) (sheet : Fin degree) :
    data.SourceEdge :=
  data.sourceEdge (thirdTarget input profile) sheet

theorem thirdSourceEdge_incident (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    Incident data (thirdSourceEdge input profile sheet)
      (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
  have hRefines := refines_of_mem_incidentEdges data (thirdTarget_mem input profile)
  have hEdgeRel := hRefines.rel
    ((data.edgePartition (thirdTarget input profile)).rel_repr_right sheet)
  apply (incident_wallBlock_sourceVertex_iff data input.distinguishedBlock _).mpr
  refine ⟨thirdTarget_mem input profile, Subtype.ext ?_⟩
  exact hEdgeRel.symm.trans (hSheet.symm.trans input.distinguishedBlock.2)

theorem thirdSourceEdge_isDangling (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    IsDangling data (thirdSourceEdge input profile sheet) := by
  by_contra hSurvives
  let incident : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) :=
    ⟨thirdSourceEdge input profile sheet,
      thirdSourceEdge_incident input profile sheet hSheet⟩
  have hMem : incident ∈ survivors data input.distinguishedBlock :=
    (mem_survivors data input.distinguishedBlock incident).mpr hSurvives
  rw [profile.surviving] at hMem
  have hTargetOf : ∀ edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock),
      incident = edge → thirdTarget input profile = edge.1.1.1 :=
    fun edge hEq ↦ congrArg (fun e : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦ e.1.1.1) hEq
  rcases Finset.mem_insert.mp hMem with hFirst | hRest
  · exact thirdTarget_ne_shared input profile (hTargetOf _ hFirst)
  · rcases Finset.mem_insert.mp hRest with hSecond | hLargest
    · exact thirdTarget_ne_shared input profile
        ((hTargetOf _ hSecond).trans hSame.symm)
    · exact thirdTarget_ne_largest input profile
        (hTargetOf _ (Finset.mem_singleton.mp hLargest))

theorem third_blockCard_eq_one (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition (thirdTarget input profile)).blockCard sheet = 1 := by
  rw [← GluingDatum.sourceEdgeIndex_sourceEdge data
    (thirdTarget input profile) sheet]
  exact input.dangling_no_glue _
    (thirdSourceEdge_isDangling input profile hSame sheet hSheet)

/-- The third-direction partition is singleton-refined on the distinguished
wall block. -/
theorem third_refinesOnBlock_splitBlock (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (data.edgePartition (thirdTarget input profile)).RefinesOnBlock
      ((data.vertexPartition wall).splitBlock input.distinguishedBlock.1)
      (data.vertexPartition wall) input.distinguishedBlock.1 := by
  intro first second hFirst hThird
  have hSingleton :=
    (data.edgePartition (thirdTarget input profile)).block_eq_singleton_of_blockCard_eq_one
      first (third_blockCard_eq_one input profile hSame first hFirst)
  have hMember :=
    ((data.edgePartition (thirdTarget input profile)).mem_block_iff first second).mpr
      hThird
  rw [hSingleton, Finset.mem_singleton] at hMember
  subst second
  rfl

/-- Exact third-direction contribution at the selected fine endpoint: one
induced edge block for each sheet of the doubled-direction block. -/
theorem third_blockCountWithin_fine (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition (thirdTarget input profile)).blockCountWithin
        (finePartition input profile) sheet =
      (finePartition input profile).blockCard sheet :=
  SheetPartition.blockCountWithin_eq_blockCard_of_refinesOnBlock_splitBlock
    (data.edgePartition (thirdTarget input profile))
    (finePartition input profile) (data.vertexPartition wall)
    input.distinguishedBlock.1 sheet
    (third_refinesOnBlock_splitBlock input profile hSame)
    (fine_refines_wall input profile) hSheet

/-! ## The Figure 30 fine member `M⁽²⁾`

Figure 30 keeps its ramification-one source vertex `A⁽q⁾ = A₀` over the
divalent endpoint in **both** members.  In `M⁽²⁾` (`α = 4`) the largest
direction `t₄` is the divalent-side occurrence, while the doubled direction
`t₃` and the third direction `t₂` meet the two-block partition at the
trivalent side.  So the selected star is the **reverse** of
`Nd3Geometry.fineLocal`, which places the fine partition at the divalent
endpoint instead.

The selected fine partition is made wall-coarse away from the distinguished
block, which turns the genuinely local third-direction singleton refinement
into the global refinement expected by `Background.install` without imposing
any condition on unrelated background blocks. -/

abbrev largestPartition (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) : SheetPartition degree :=
  data.edgePartition (largestTarget input profile)

theorem largest_refines_wall (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (largestPartition input profile).Refines (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data (largestTarget_mem input profile)

/-- Orient the actual target star with the largest direction on the divalent
side and the doubled and third directions, in that order, on the trivalent
side. -/
noncomputable def fineOrientation (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    OrientedStar target wall (largestTarget input profile) where
  rightFirst := profile.first.1.1.1
  rightSecond := thirdTarget input profile
  left_mem := largestTarget_mem input profile
  rightFirst_ne_left := profile.first_target_ne
  rightSecond_ne_left := thirdTarget_ne_largest input profile
  right_ne := (thirdTarget_ne_shared input profile).symm
  incidentEdges_eq := by
    rw [incidentEdges_eq input profile]
    ext edge
    simp [or_left_comm]

/-- The selected doubled-direction partition, made equal to the wall partition
on every nondistinguished block. -/
noncomputable def selectedFine (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) : SheetPartition degree :=
  (data.vertexPartition wall).paste
    (fun blockAnchor ↦
      if (data.vertexPartition wall).Rel input.distinguishedBlock.1 blockAnchor then
        finePartition input profile
      else data.vertexPartition wall)
    (by
      intro blockAnchor
      split
      · exact fine_refines_wall input profile
      · exact SheetPartition.Refines.refl _)

theorem selectedFine_refines_wall (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (selectedFine input profile).Refines (data.vertexPartition wall) :=
  (data.vertexPartition wall).paste_refines _ _

theorem selectedFine_rel_iff_of_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel input.distinguishedBlock.1 first) :
    (selectedFine input profile).Rel first second ↔
      (finePartition input profile).Rel first second := by
  unfold selectedFine
  rw [(data.vertexPartition wall).paste_rel_iff]
  have hRepresentative : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 ((data.vertexPartition wall).repr first) :=
    hFirst.trans ((data.vertexPartition wall).rel_repr_right first)
  rw [ite_eq_left hRepresentative]

theorem selectedFine_rel_iff_of_background (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    {first second : Fin degree}
    (hFirst : ¬(data.vertexPartition wall).Rel input.distinguishedBlock.1 first) :
    (selectedFine input profile).Rel first second ↔
      (data.vertexPartition wall).Rel first second := by
  unfold selectedFine
  rw [(data.vertexPartition wall).paste_rel_iff]
  have hRepresentative : ¬(data.vertexPartition wall).Rel
      input.distinguishedBlock.1 ((data.vertexPartition wall).repr first) := by
    intro hRel
    exact hFirst (hRel.trans ((data.vertexPartition wall).rel_repr_left first))
  rw [ite_eq_right hRepresentative]

theorem selectedFine_block_eq_fine (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (selectedFine input profile).block sheet =
      (finePartition input profile).block sheet := by
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff,
    selectedFine_rel_iff_of_selected input profile hSheet]

theorem selectedFine_blockCard_eq_fine (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (selectedFine input profile).blockCard sheet =
      (finePartition input profile).blockCard sheet := by
  unfold SheetPartition.blockCard
  rw [selectedFine_block_eq_fine input profile sheet hSheet]

private theorem refines_selectedFine_of_local
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (edgePartition : SheetPartition degree)
    (hWall : edgePartition.Refines (data.vertexPartition wall))
    (hLocal : edgePartition.RefinesOnBlock (finePartition input profile)
      (data.vertexPartition wall) input.distinguishedBlock.1) :
    edgePartition.Refines (selectedFine input profile) := by
  intro first second hEdge
  by_cases hSelected : (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 first
  · apply (selectedFine_rel_iff_of_selected input profile hSelected).mpr
    exact hLocal.rel hSelected hEdge
  · apply (selectedFine_rel_iff_of_background input profile hSelected).mpr
    exact hWall.rel hEdge

theorem shared_refines_selectedFine (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (data.edgePartition profile.first.1.1.1).Refines
      (selectedFine input profile) :=
  refines_selectedFine_of_local input profile _
    (fine_refines_wall input profile)
    ((SheetPartition.Refines.refl (finePartition input profile)).refinesOnBlock _)

theorem third_refines_selectedFine (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (data.edgePartition (thirdTarget input profile)).Refines
      (selectedFine input profile) :=
  refines_selectedFine_of_local input profile _
    (refines_of_mem_incidentEdges data (thirdTarget_mem input profile))
    ((third_refinesOnBlock_splitBlock input profile hSame).refinesAny_of_splitBlock _)

/-- The literal selected fine star of `M⁽²⁾`: the whole wall block at the
divalent endpoint, the doubled-direction partition at the trivalent endpoint
and on the new edge. -/
noncomputable def selectedResolution (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) : LocalResolution degree :=
  (fineResolution (data.vertexPartition wall) (selectedFine input profile)
    (selectedFine_refines_wall input profile)).reverse

@[simp] theorem selectedResolution_left (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (selectedResolution input profile).left = data.vertexPartition wall := rfl

@[simp] theorem selectedResolution_right (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (selectedResolution input profile).right = selectedFine input profile := rfl

@[simp] theorem selectedResolution_newEdge (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (selectedResolution input profile).newEdge = selectedFine input profile := rfl

theorem selectedResolution_contracts (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (selectedResolution input profile).ContractsTo (data.vertexPartition wall) :=
  LocalResolution.reverse_contracts
    (fineResolution_contracts (data.vertexPartition wall) (selectedFine input profile)
      (selectedFine_refines_wall input profile))

/-- Background blocks of `M⁽²⁾` use the largest-direction partition at the
divalent endpoint and on the new edge, and the wall partition at the trivalent
endpoint. -/
noncomputable def fineBackground (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    Background data wall profile.first.1.1.2 := by
  let orientation := fineOrientation input profile
  let fine := largestPartition input profile
  have hFine := largest_refines_wall input profile
  let localResolution : LocalResolution degree :=
    fineResolution (data.vertexPartition wall) fine hFine
  refine {
    right := rightOf (largestTarget input profile)
    resolution := fun _ ↦ localResolution
    contracts := ?_
    exterior := ?_
    leftEdges := [largestTarget input profile]
    rightEdges := [orientation.rightFirst, orientation.rightSecond]
    leftEdges_eq := ?_
    rightEdges_eq := ?_
    left_riemannHurwitz := ?_
    right_riemannHurwitz := ?_ }
  · intro _ _
    exact fineResolution_contracts _ fine hFine
  · intro edge hIncident _ _
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hEq : edge = largestTarget input profile
    · subst edge
      change fine.Refines
        (if rightOf (largestTarget input profile) (largestTarget input profile) then
          localResolution.right else localResolution.left)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false,
        localResolution, fineResolution]
      exact SheetPartition.Refines.refl fine
    · have hRight : rightOf (largestTarget input profile) edge = true := by
        simp [rightOf, hEq]
      rw [hRight, ite_eq_left rfl]
      change (data.edgePartition edge).Refines (data.vertexPartition wall)
      exact refines_of_mem_incidentEdges data hAt
  · rw [wallEdgesAssigned_false orientation]
    rfl
  · rw [wallEdgesAssigned_true orientation]
    rw [Finset.insert_val_of_notMem (by simpa using orientation.right_ne)]
    rfl
  · intro blockAnchor _ _
    exact fineResolution_left_riemannHurwitzAtBlock
      (data.vertexPartition wall) fine
      (data.edgePartition (largestTarget input profile)) hFine blockAnchor
  · intro blockAnchor _ hOther
    apply riemannHurwitzAtBlock_trivalent_of_counts
      (data.vertexPartition wall) (data.vertexPartition wall) fine
      (data.edgePartition orientation.rightFirst)
      (data.edgePartition orientation.rightSecond) blockAnchor
    intro sheet hSheet
    have hSheetOther : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet := by
      intro hDist
      apply hOther
      exact (incident_wall_rel input profile.first).symm.trans
        (hDist.trans hSheet.symm)
    have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
        input.distinguishedBlock := by
      intro hEq
      apply hSheetOther
      have hValue := congrArg Subtype.val hEq
      change (data.vertexPartition wall).repr sheet =
        input.distinguishedBlock.1 at hValue
      change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
        (data.vertexPartition wall).repr sheet
      rw [input.distinguishedBlock.2, hValue]
    have hZero := input.localRamification_eq_zero_of_ne hBlockNe
    have hTotal := external_count_eq (data := data) star orientation sheet
    rw [hZero] at hTotal
    have hTotalNat' :
        (data.edgePartition (largestTarget input profile)).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          0 + 2 + (data.vertexPartition wall).blockCard sheet := by
      exact_mod_cast hTotal
    have hTotalNat :
        fine.blockCountWithin (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          (data.vertexPartition wall).blockCard sheet + 2 := by
      simpa [fine, largestPartition, Nat.add_comm] using hTotalNat'
    exact hTotalNat.ge

theorem shared_blockCountWithin_selectedFine
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition profile.first.1.1.1).blockCountWithin
      (selectedFine input profile) sheet = 1 := by
  unfold SheetPartition.blockCountWithin
  rw [selectedFine_block_eq_fine input profile sheet hSheet]
  exact SheetPartition.blockCountWithin_self (finePartition input profile) sheet

theorem third_blockCountWithin_selectedFine
    (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition (thirdTarget input profile)).blockCountWithin
        (selectedFine input profile) sheet =
      (finePartition input profile).blockCard sheet := by
  unfold SheetPartition.blockCountWithin
  rw [selectedFine_block_eq_fine input profile sheet hSheet]
  exact third_blockCountWithin_fine input profile hSame sheet hSheet

/-- Assemble the actual oppositely oriented fine Figure 30 member `M⁽²⁾`. -/
noncomputable def fineCandidate (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    BalancedGlobal.Candidate target degree data wall := by
  let background := fineBackground input profile
  let selected := selectedResolution input profile
  apply background.install selected (selectedResolution_contracts input profile)
  · intro edge hIncident
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hLargest : edge = largestTarget input profile
    · subst edge
      simp only [background, fineBackground, rightOf, ne_eq, not_true_eq_false,
        decide_false, selected, selectedResolution,
        LocalResolution.reverse_left, fineResolution]
      exact refines_of_mem_incidentEdges data hAt
    · have hRight : rightOf (largestTarget input profile) edge = true := by
        simp [rightOf, hLargest]
      simp only [background, fineBackground, hRight, ite_true, selected,
        selectedResolution, LocalResolution.reverse_right, fineResolution]
      have hCases : edge = profile.first.1.1.1 ∨
          edge = thirdTarget input profile := by
        rw [incidentEdges_eq input profile] at hAt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hAt
        rcases hAt with hShared | hLargestEq | hThird
        · exact Or.inl hShared
        · exact (hLargest hLargestEq).elim
        · exact Or.inr hThird
      rcases hCases with rfl | rfl
      · exact shared_refines_selectedFine input profile
      · exact third_refines_selectedFine input profile hSame
  · intro blockAnchor _ _
    change LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (data.vertexPartition wall)
      [selectedFine input profile,
        data.edgePartition (largestTarget input profile)] blockAnchor
    exact riemannHurwitzAtBlock_divalent _ _ _ _ _
  · intro blockAnchor hAnchor _
    change LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedFine input profile)
      [selectedFine input profile,
        data.edgePartition profile.first.1.1.1,
        data.edgePartition (thirdTarget input profile)] blockAnchor
    apply riemannHurwitzAtBlock_trivalent_of_counts
    intro sheet hSheet
    have hDistSheet : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet :=
      (incident_wall_rel input profile.first).trans (hAnchor.trans hSheet)
    rw [SheetPartition.blockCountWithin_self,
      shared_blockCountWithin_selectedFine input profile sheet hDistSheet,
      third_blockCountWithin_selectedFine input profile hSame sheet hDistSheet,
      selectedFine_blockCard_eq_fine input profile sheet hDistSheet]
    omega

/-- The true fine member is valid from the original source datum alone. -/
theorem fineCandidate_valid (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (fineCandidate input profile hSame).datum.Valid :=
  (fineCandidate input profile hSame).datum_valid input.valid

/-- The true fine member preserves source genus: the selected block and the
background blocks are pasted stars in opposite orientations. -/
theorem fineCandidate_sourceGenus (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    genus (fineCandidate input profile hSame).datum.sourceGraph =
      genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro sheet
  have hResolution : (fineCandidate input profile hSame).resolution sheet =
      LocalResolution.onBlock (data.vertexPartition wall) profile.first.1.1.2
        (selectedResolution input profile)
        (fineBackground input profile).resolution sheet := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel profile.first.1.1.2 sheet
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩

/-! ## Equation (4)'s displayed indices

Figure 30 displays `|e'| = k₄ = k₂ + k₃` for `M⁽¹⁾` and `|e'| = k₂`,
`|e''| = k₃` for `M⁽²⁾`.  These are the three denominators of Equation (4);
the lemmas below read them off the two assembled candidates. -/

theorem fine_blockCard_first (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock) :
    (finePartition input profile).blockCard profile.first.1.1.2 =
      data.sourceEdgeIndex profile.first.1 := rfl

theorem fine_blockCard_second (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (finePartition input profile).blockCard profile.second.1.1.2 =
      data.sourceEdgeIndex profile.second.1 := by
  show (data.edgePartition profile.first.1.1.1).blockCard profile.second.1.1.2 =
    data.sourceEdgeIndex profile.second.1
  rw [congrArg data.edgePartition hSame]
  rfl

/-- On the selected block the coarse candidate is literally the retained
whole-wall star. -/
theorem coarseCandidate_resolution_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarseCandidate input profile hSame).resolution sheet =
      thirdResolution (data.vertexPartition wall) := by
  change LocalResolution.onBlock (data.vertexPartition wall)
      profile.first.1.1.2 (thirdResolution (data.vertexPartition wall))
      (background input profile).resolution sheet = _
  rw [LocalResolution.onBlock_of_rel]
  exact (incident_wall_rel input profile.first).symm.trans hSheet

/-- On the selected block the fine candidate is literally the reversed
selected star. -/
theorem fineCandidate_resolution_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineCandidate input profile hSame).resolution sheet =
      selectedResolution input profile := by
  change LocalResolution.onBlock (data.vertexPartition wall)
      profile.first.1.1.2 (selectedResolution input profile)
      (fineBackground input profile).resolution sheet = _
  rw [LocalResolution.onBlock_of_rel]
  exact (incident_wall_rel input profile.first).symm.trans hSheet

/-- The globally pasted local resolution of the coarse member. -/
noncomputable abbrev coarsePastedResolution (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall)
    (coarseCandidate input profile hSame).resolution
    (coarseCandidate input profile hSame).contracts

/-- The globally pasted local resolution of the fine member. -/
noncomputable abbrev finePastedResolution (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall)
    (fineCandidate input profile hSame).resolution
    (fineCandidate input profile hSame).contracts

theorem coarse_pasted_newEdge_block_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile hSame).newEdge.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (coarseCandidate input profile hSame).resolution
    (coarseCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [coarseCandidate_resolution_selected input profile hSame
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

/-- Figure 30's `M⁽¹⁾` datum `|e'| = k₄ = k₂ + k₃`. -/
theorem coarse_pasted_newEdge_blockCard_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (coarsePastedResolution input profile hSame).newEdge.blockCard sheet =
      data.sourceEdgeIndex profile.first.1 +
        data.sourceEdgeIndex profile.second.1 := by
  have hCard : (data.vertexPartition wall).blockCard sheet =
      data.sourceEdgeIndex profile.first.1 +
        data.sourceEdgeIndex profile.second.1 := by
    unfold SheetPartition.blockCard
    rw [← (data.vertexPartition wall).block_eq_of_rel hSheet]
    exact (profile.doubled_direction hSame).1.symm
  rw [← hCard]
  unfold SheetPartition.blockCard
  rw [coarse_pasted_newEdge_block_selected input profile hSame sheet hSheet]

theorem fine_pasted_newEdge_block_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile hSame).newEdge.block sheet =
      (finePartition input profile).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (fineCandidate input profile hSame).resolution
    (fineCandidate input profile hSame).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_selected input profile hSame
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  exact selectedFine_block_eq_fine input profile sheet hSheet

theorem fine_pasted_newEdge_blockCard_selected (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile hSame).newEdge.blockCard sheet =
      (finePartition input profile).blockCard sheet := by
  unfold SheetPartition.blockCard
  rw [fine_pasted_newEdge_block_selected input profile hSame sheet hSheet]

/-- Figure 30's `M⁽²⁾` datum `|e'| = k₂`. -/
theorem fine_pasted_newEdge_blockCard_first (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (finePastedResolution input profile hSame).newEdge.blockCard
        profile.first.1.1.2 = data.sourceEdgeIndex profile.first.1 := by
  rw [fine_pasted_newEdge_blockCard_selected input profile hSame _
    (incident_wall_rel input profile.first)]
  exact fine_blockCard_first input profile

/-- Figure 30's `M⁽²⁾` datum `|e''| = k₃`. -/
theorem fine_pasted_newEdge_blockCard_second (input : W3SourceInput data star)
    (profile : Nd3Profile data input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1) :
    (finePastedResolution input profile hSame).newEdge.blockCard
        profile.second.1.1.2 = data.sourceEdgeIndex profile.second.1 := by
  rw [fine_pasted_newEdge_blockCard_selected input profile hSame _
    (incident_wall_rel input profile.second)]
  exact fine_blockCard_second input profile hSame

end DraismaVargas.LocalCases.W3Nd3SourceCandidates
