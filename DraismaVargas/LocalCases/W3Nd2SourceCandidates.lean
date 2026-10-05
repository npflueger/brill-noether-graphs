module

public import DraismaVargas.LocalCases.W3IncomingClassification
public import DraismaVargas.LocalCases.GlobalCoarseFine
public import DraismaVargas.LocalCases.M11SourceGenus

@[expose] public section

/-!
# Source-derived W3 nd2 coarse candidate

This module constructs the coarse member of Figure 31 / Equation (5) from an
actual `W3SourceInput` and `Nd2Profile`. The smaller surviving direction is
placed on the divalent side; the other two actual target occurrences are
placed on the trivalent side. Every unramified wall block is resolved with its
smaller-direction edge partition on the new edge, so the original local
ramification equation supplies the arbitrary-degree background RH count.

This is deliberately only the **coarse** source member. In the true fine
member of Figure 31, the r1 vertex remains over the divalent endpoint, the
large surviving direction is isolated there, and the selected fine resolution
is reversed. In particular, `geometry.fineLocal` below is only the conditional
interface's same-side local resolution and is not claimed to be the source's
fine member. Constructing the latter also needs the localized refinement of
the third direction at the distinguished block.
-/

namespace DraismaVargas.LocalCases.W3Nd2SourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine GlobalCoarseFine
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary M11SourceGenus

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- An orientation of the three actual target occurrences with one occurrence
on the divalent side and the other two on the trivalent side. -/
structure OrientedStar (target : CFGraph) (wall : target.V) (left : target.edges) where
  rightFirst : target.edges
  rightSecond : target.edges
  left_mem : left ∈ GluingDatum.incidentEdges wall
  rightFirst_ne_left : rightFirst ≠ left
  rightSecond_ne_left : rightSecond ≠ left
  right_ne : rightFirst ≠ rightSecond
  incidentEdges_eq : GluingDatum.incidentEdges wall = {left, rightFirst, rightSecond}

theorem exists_orientedStar (star : ThreeStar target wall) (left : target.edges)
    (hLeft : left ∈ GluingDatum.incidentEdges wall) :
    Nonempty (OrientedStar target wall left) := by
  classical
  have hEraseCard : ((GluingDatum.incidentEdges wall).erase left).card = 2 := by
    rw [Finset.card_erase_of_mem hLeft, star.card_incidentEdges]
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hEraseCard
  have hFirst := Finset.mem_of_mem_erase (show first ∈
      (GluingDatum.incidentEdges wall).erase left by simp [hPair])
  have hSecond := Finset.mem_of_mem_erase (show second ∈
      (GluingDatum.incidentEdges wall).erase left by simp [hPair])
  have hFirstNe := (Finset.mem_erase.mp (show first ∈
      (GluingDatum.incidentEdges wall).erase left by simp [hPair])).1
  have hSecondNe := (Finset.mem_erase.mp (show second ∈
      (GluingDatum.incidentEdges wall).erase left by simp [hPair])).1
  refine ⟨⟨first, second, hLeft, hFirstNe, hSecondNe, hNe, ?_⟩⟩
  rw [← Finset.insert_erase hLeft, hPair]

/-- Choose the source-prescribed orientation whose divalent-side occurrence
is the smaller survivor in Figure 31. -/
noncomputable def orientedStar
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    OrientedStar target wall profile.small.1.1.1 :=
  Classical.choice (exists_orientedStar star profile.small.1.1.1
    ((incident_iff_target_mem_and_rel data profile.small.1 _).mp profile.small.2).1)

/-- The residual fine partition is the actual partition of the smaller
surviving source occurrence. -/
abbrev finePartition (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    SheetPartition degree := data.edgePartition profile.small.1.1.1

/-- The canonical sheet representing that smaller source occurrence. -/
abbrev anchor (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : Fin degree :=
  profile.small.1.1.2

theorem anchor_wall_rel (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1
      (anchor input profile) := by
  have hBlock := (incident_wallBlock_sourceVertex_iff data input.distinguishedBlock
    profile.small.1).mp profile.small.2 |>.2
  have hValue := congrArg Subtype.val hBlock
  change (data.vertexPartition wall).repr (anchor input profile) =
    input.distinguishedBlock.1 at hValue
  change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
    (data.vertexPartition wall).repr (anchor input profile)
  rw [input.distinguishedBlock.2, hValue]

theorem fine_refines_wall (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (finePartition input profile).Refines (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data
    ((incident_iff_target_mem_and_rel data profile.small.1 _).mp profile.small.2).1

/-- The literal Figure 31 profile supplies every numerical field of the
conditional coarse/fine geometry interface. -/
noncomputable def geometry (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : Nd2Geometry data wall where
  fine := finePartition input profile
  anchor := anchor input profile
  fine_refines := fine_refines_wall input profile
  k := data.sourceEdgeIndex profile.small.1
  k_pos := data.sourceEdgeIndex_pos profile.small.1
  fineCard := rfl
  wallCard := by
    have hRel := anchor_wall_rel input profile
    unfold SheetPartition.blockCard
    rw [← (data.vertexPartition wall).block_eq_of_rel hRel]
    exact profile.small_index.symm

/-- The wall ramification formula, enumerated in the source-prescribed
one-plus-two target orientation. -/
theorem external_count_eq (star : ThreeStar target wall)
    (orientation : OrientedStar target wall left)
    (sheet : Fin degree) :
    (data.edgePartition left).blockCountWithin (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightFirst).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightSecond).blockCountWithin
          (data.vertexPartition wall) sheet =
      data.localRamification wall ((data.vertexPartition wall).toBlock sheet) + 2 +
        (data.vertexPartition wall).blockCard sheet := by
  have hRel := (data.vertexPartition wall).rel_repr_left sheet
  have hEnum :
      (∑ edge ∈ GluingDatum.incidentEdges wall,
        ((data.edgePartition edge).blockCountWithin
          (data.vertexPartition wall) ((data.vertexPartition wall).repr sheet) : ℤ)) =
        (data.edgePartition left).blockCountWithin (data.vertexPartition wall)
            ((data.vertexPartition wall).repr sheet) +
          (data.edgePartition orientation.rightFirst).blockCountWithin
            (data.vertexPartition wall) ((data.vertexPartition wall).repr sheet) +
          (data.edgePartition orientation.rightSecond).blockCountWithin
            (data.vertexPartition wall) ((data.vertexPartition wall).repr sheet) := by
    rw [orientation.incidentEdges_eq]
    rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨orientation.rightFirst_ne_left.symm,
        orientation.rightSecond_ne_left.symm⟩)]
    rw [Finset.sum_pair orientation.right_ne]
    ring
  unfold GluingDatum.localRamification
  simp only [SheetPartition.toBlock_val]
  have hLeft := SheetPartition.blockCountWithin_congr
    (data.edgePartition left) (data.vertexPartition wall) hRel
  have hFirst := SheetPartition.blockCountWithin_congr
    (data.edgePartition orientation.rightFirst) (data.vertexPartition wall) hRel
  have hSecond := SheetPartition.blockCountWithin_congr
    (data.edgePartition orientation.rightSecond) (data.vertexPartition wall) hRel
  have hCard := SheetPartition.blockCard_congr (data.vertexPartition wall) hRel
  rw [ThreeStar.card_incidentEdges star, hEnum, hLeft, hFirst, hSecond, hCard]
  push_cast
  ring

/-- The smaller survivor has index `k` inside a wall block of size `k+1`, so
its actual edge partition induces at most two blocks on that wall block. -/
theorem fine_blockCountWithin_le_two (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePartition input profile).blockCountWithin
      (data.vertexPartition wall) sheet ≤ 2 := by
  classical
  let fine := finePartition input profile
  let coarse := data.vertexPartition wall
  let coarseBlock : coarse.Blocks := input.distinguishedBlock
  let big : fine.Blocks := ⟨anchor input profile, profile.small.1.2⟩
  let blocks := SheetPartition.blocksWithin fine coarse coarseBlock
  have hBigMem : big ∈ blocks := by
    apply (SheetPartition.mem_blocksWithin fine coarse coarseBlock big).mpr
    apply (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse
      big coarseBlock).mpr
    exact anchor_wall_rel input profile
  have hBigCard : fine.blockCard big.1 = data.sourceEdgeIndex profile.small.1 := rfl
  have hSum := sum_blockCard_blocksWithin fine coarse
    (fine_refines_wall input profile) coarseBlock
  have hTotal :
      (∑ block ∈ blocks.erase big, (fine.blockCard block.1 : ℤ)) +
          (data.sourceEdgeIndex profile.small.1 : ℤ) =
        (data.sourceEdgeIndex profile.small.1 : ℤ) + 1 := by
    calc
      _ = ∑ block ∈ blocks, (fine.blockCard block.1 : ℤ) := by
        rw [← hBigCard]
        exact Finset.sum_erase_add blocks
          (fun block ↦ (fine.blockCard block.1 : ℤ)) hBigMem
      _ = (coarse.blockCard coarseBlock.1 : ℤ) := hSum
      _ = _ := by exact_mod_cast profile.small_index.symm
  have hRest : ((blocks.erase big).card : ℤ) ≤
      ∑ block ∈ blocks.erase big, (fine.blockCard block.1 : ℤ) := by
    calc
      ((blocks.erase big).card : ℤ) =
          ∑ _block ∈ blocks.erase big, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun block _ ↦ by
        exact_mod_cast fine.blockCard_pos block.1
  have hEraseCard := Finset.card_erase_of_mem hBigMem
  have hBlocksPos : 0 < blocks.card := Finset.card_pos.mpr ⟨big, hBigMem⟩
  have hBlocksLe : blocks.card ≤ 2 := by omega
  have hCount := SheetPartition.card_blocksWithin_eq_blockCountWithin fine coarse
    (fine_refines_wall input profile) coarseBlock
  have hCongr := SheetPartition.blockCountWithin_congr fine coarse hSheet
  change fine.blockCountWithin coarse sheet ≤ 2
  calc
    fine.blockCountWithin coarse sheet = fine.blockCountWithin coarse coarseBlock.1 := hCongr.symm
    _ = blocks.card := hCount.symm
    _ ≤ 2 := hBlocksLe

/-- Put exactly the chosen smaller-survivor direction on the left. -/
noncomputable def rightOf (left edge : target.edges) : Bool := decide (edge ≠ left)

theorem wallEdgesAssigned_false (orientation : OrientedStar target wall left) :
    wallEdgesAssigned target wall (rightOf left) false = {left} := by
  classical
  ext edge
  have hIncidentIff : edge ∈ GluingDatum.incidentEdges wall ↔
      edge = left ∨ edge = orientation.rightFirst ∨ edge = orientation.rightSecond := by
    rw [orientation.incidentEdges_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hEnds : ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) ↔
      edge = left ∨ edge = orientation.rightFirst ∨ edge = orientation.rightSecond := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hIncidentIff
  rw [mem_wallEdgesAssigned, Finset.mem_singleton, hEnds]
  simp only [rightOf, decide_eq_false_iff_not, Classical.not_not]
  constructor
  · exact fun h ↦ h.2
  · intro hEq
    subst edge
    exact ⟨Or.inl rfl, rfl⟩

theorem wallEdgesAssigned_true (orientation : OrientedStar target wall left) :
    wallEdgesAssigned target wall (rightOf left) true =
      {orientation.rightFirst, orientation.rightSecond} := by
  classical
  ext edge
  have hIncidentIff : edge ∈ GluingDatum.incidentEdges wall ↔
      edge = left ∨ edge = orientation.rightFirst ∨ edge = orientation.rightSecond := by
    rw [orientation.incidentEdges_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hEnds : ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) ↔
      edge = left ∨ edge = orientation.rightFirst ∨ edge = orientation.rightSecond := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hIncidentIff
  rw [mem_wallEdgesAssigned, hEnds]
  simp only [rightOf, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hIncident, hNe⟩
    rcases hIncident with hLeft | hFirst | hSecond
    · exact (hNe hLeft) |>.elim
    · exact Or.inl hFirst
    · exact Or.inr hSecond
  · intro hRight
    rcases hRight with hFirst | hSecond
    · exact ⟨Or.inr (Or.inl hFirst), fun hEq ↦
        orientation.rightFirst_ne_left (hFirst.symm.trans hEq)⟩
    · exact ⟨Or.inr (Or.inr hSecond), fun hEq ↦
        orientation.rightSecond_ne_left (hSecond.symm.trans hEq)⟩

/-- The arbitrary-degree background uses the same fine/whole-wall star on
every unramified wall block. The original `r=0` equation is exactly
the trivalent endpoint count. -/
noncomputable def background (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Background data wall (anchor input profile) := by
  let orientation := orientedStar input profile
  let fine := finePartition input profile
  have hFine := fine_refines_wall input profile
  let localResolution : LocalResolution degree :=
    fineResolution (data.vertexPartition wall) fine hFine
  refine {
    right := rightOf profile.small.1.1.1
    resolution := fun _ ↦ localResolution
    contracts := ?_
    exterior := ?_
    leftEdges := [profile.small.1.1.1]
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
    by_cases hEq : edge = profile.small.1.1.1
    · subst edge
      change fine.Refines
        (if rightOf profile.small.1.1.1 profile.small.1.1.1 then
          localResolution.right else localResolution.left)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false,
        localResolution, fineResolution]
      exact SheetPartition.Refines.refl fine
    · have hRight : rightOf profile.small.1.1.1 edge = true := by
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
      (data.vertexPartition wall) fine (data.edgePartition profile.small.1.1.1)
      hFine anchor
  · intro anchor _ hOther
    apply riemannHurwitzAtBlock_trivalent_of_counts
      (data.vertexPartition wall) (data.vertexPartition wall) fine
      (data.edgePartition orientation.rightFirst)
      (data.edgePartition orientation.rightSecond) anchor
    intro sheet hSheet
    have hSheetOther : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet := fun h ↦ hOther
      ((anchor_wall_rel input profile).symm.trans h |>.trans hSheet.symm)
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
        (data.edgePartition profile.small.1.1.1).blockCountWithin
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
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition profile.small.1.1.1).blockCountWithin
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
      (data.edgePartition profile.small.1.1.1).blockCountWithin
            (data.vertexPartition wall) sheet +
          (data.edgePartition (orientedStar input profile).rightFirst).blockCountWithin
            (data.vertexPartition wall) sheet +
          (data.edgePartition (orientedStar input profile).rightSecond).blockCountWithin
            (data.vertexPartition wall) sheet =
        1 + 2 + (data.vertexPartition wall).blockCard sheet := by
    exact_mod_cast hTotal
  omega

/-- Figure 31's coarse member: the whole distinguished wall block is retained
on the new edge. -/
noncomputable def coarsePattern (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    TrivalentPattern (data := data) (wall := wall)
      (geometry input profile).anchor (geometry input profile).coarseLocal := by
  let orientation := orientedStar input profile
  refine {
    background := background input profile
    leftExternal := profile.small.1.1.1
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
    simpa only [Nd2Geometry.coarseLocal, thirdResolution, joinedResolutionAt,
      ite_self] using hRefines
  · intro anchor hAnchor sheet hSheet
    have hDistSheet : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet :=
      (anchor_wall_rel input profile).trans hAnchor |>.trans hSheet
    have hTotal :
        (data.edgePartition profile.small.1.1.1).blockCountWithin
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
    have hFineLe := fine_blockCountWithin_le_two input profile sheet hDistSheet
    change (data.vertexPartition wall).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightFirst).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightSecond).blockCountWithin
          (data.vertexPartition wall) sheet ≥
      (data.vertexPartition wall).blockCard sheet + 2
    rw [SheetPartition.blockCountWithin_self]
    omega

/-- The actual globally assembled coarse Figure 31 datum. -/
noncomputable def coarseCandidate (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    BalancedGlobal.Candidate target degree data wall :=
  (coarsePattern input profile).candidate (nd2_coarse_contracts (geometry input profile))

/-- The source-derived coarse member is valid whenever the incoming datum is. -/
theorem coarseCandidate_valid (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (coarseCandidate input profile).datum.Valid :=
  (coarseCandidate input profile).datum_valid input.valid

/-- The coarse member preserves the complete quotient-source genus. Selected
and background blocks are both pasted stars, so the Euler identity is
pointwise and does not assume a separate genus receipt. -/
theorem coarseCandidate_sourceGenus (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    genus (coarseCandidate input profile).datum.sourceGraph = genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro sheet
  have hResolution : (coarseCandidate input profile).resolution sheet =
      LocalResolution.onBlock (data.vertexPartition wall)
        (geometry input profile).anchor (geometry input profile).coarseLocal
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (finePartition input profile) (fine_refines_wall input profile)) sheet := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel
      (geometry input profile).anchor sheet
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩

end DraismaVargas.LocalCases.W3Nd2SourceCandidates
