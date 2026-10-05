module

public import DraismaVargas.LocalCases.W3Nd2FineRefinement
public import DraismaVargas.LocalCases.M11SourceGenus

@[expose] public section

/-!
# The true W3 nd2 fine candidate

Figure 31 keeps its ramification-one source vertex over the divalent endpoint
in both members.  In the fine member the large surviving direction is placed
on that divalent side, while the small and third directions meet the fine
partition at the trivalent side.  Background wall blocks use the opposite
local star: the large-direction partition is the divalent endpoint and new
edge, while the wall partition is the trivalent endpoint.

The selected fine partition is made wall-coarse away from the distinguished
block.  This turns the genuinely local third-direction singleton refinement
into the global refinement expected by `Background.install`, without imposing
any condition on unrelated background blocks.
-/

namespace DraismaVargas.LocalCases.W3Nd2FineCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine GlobalCoarseFine
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary M11SourceGenus
open W3Nd2SourceCandidates W3Nd2FineRefinement

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- Orient the actual target star with the large direction on the divalent
side and the small and third directions, in that order, on the trivalent
side. -/
noncomputable def fineOrientation (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    OrientedStar target wall (largeTarget input profile) where
  rightFirst := smallTarget input profile
  rightSecond := thirdTarget input profile
  left_mem := largeTarget_mem input profile
  rightFirst_ne_left := profile.target_ne
  rightSecond_ne_left := thirdTarget_ne_large input profile
  right_ne := (thirdTarget_ne_small input profile).symm
  incidentEdges_eq := by
    rw [W3Nd2FineRefinement.incidentEdges_eq input profile]
    ext edge
    simp [or_left_comm]

abbrev largePartition (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : SheetPartition degree :=
  data.edgePartition (largeTarget input profile)

theorem large_refines_wall (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (largePartition input profile).Refines (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data (largeTarget_mem input profile)

/-- The selected small-direction partition, made equal to the wall partition
on every nondistinguished block. -/
noncomputable def selectedFine (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : SheetPartition degree :=
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
    (profile : Nd2Profile data input.distinguishedBlock) :
    (selectedFine input profile).Refines (data.vertexPartition wall) :=
  (data.vertexPartition wall).paste_refines _ _

theorem selectedFine_rel_iff_of_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
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
    (profile : Nd2Profile data input.distinguishedBlock)
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
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (selectedFine input profile).block sheet =
      (finePartition input profile).block sheet := by
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff,
    selectedFine_rel_iff_of_selected input profile hSheet]

theorem selectedFine_blockCard_eq_fine (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (selectedFine input profile).blockCard sheet =
      (finePartition input profile).blockCard sheet := by
  unfold SheetPartition.blockCard
  rw [selectedFine_block_eq_fine input profile sheet hSheet]

private theorem refines_selectedFine_of_local
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock)
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

theorem small_refines_selectedFine (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.edgePartition (smallTarget input profile)).Refines
      (selectedFine input profile) :=
  refines_selectedFine_of_local input profile _
    (fine_refines_wall input profile) (small_refinesOnBlock_fine input profile)

theorem third_refines_selectedFine (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (data.edgePartition (thirdTarget input profile)).Refines
      (selectedFine input profile) :=
  refines_selectedFine_of_local input profile _
    (refines_of_mem_incidentEdges data (thirdTarget_mem input profile))
    (third_refinesOnBlock_fine input profile)

/-- The literal selected fine star: whole wall at the divalent endpoint,
small-direction fine partition at the trivalent endpoint and on the new edge. -/
noncomputable def selectedResolution (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : LocalResolution degree :=
  (fineResolution (data.vertexPartition wall) (selectedFine input profile)
    (selectedFine_refines_wall input profile)).reverse

@[simp] theorem selectedResolution_left (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (selectedResolution input profile).left = data.vertexPartition wall := rfl

@[simp] theorem selectedResolution_right (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (selectedResolution input profile).right = selectedFine input profile := rfl

@[simp] theorem selectedResolution_newEdge (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (selectedResolution input profile).newEdge = selectedFine input profile := rfl

theorem selectedResolution_contracts (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (selectedResolution input profile).ContractsTo (data.vertexPartition wall) :=
  LocalResolution.reverse_contracts
    (fineResolution_contracts (data.vertexPartition wall) (selectedFine input profile)
      (selectedFine_refines_wall input profile))

/-- Background blocks use the large-direction partition at the divalent
endpoint and on the new edge, and the wall partition at the trivalent endpoint. -/
noncomputable def fineBackground (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    Background data wall (anchor input profile) := by
  let orientation := fineOrientation input profile
  let fine := largePartition input profile
  have hFine := large_refines_wall input profile
  let localResolution : LocalResolution degree :=
    fineResolution (data.vertexPartition wall) fine hFine
  refine {
    right := rightOf (largeTarget input profile)
    resolution := fun _ ↦ localResolution
    contracts := ?_
    exterior := ?_
    leftEdges := [largeTarget input profile]
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
    by_cases hEq : edge = largeTarget input profile
    · subst edge
      change fine.Refines
        (if rightOf (largeTarget input profile) (largeTarget input profile) then
          localResolution.right else localResolution.left)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false,
        localResolution, fineResolution]
      exact SheetPartition.Refines.refl fine
    · have hRight : rightOf (largeTarget input profile) edge = true := by
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
      (data.vertexPartition wall) fine (data.edgePartition (largeTarget input profile))
      hFine blockAnchor
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
      exact (anchor_wall_rel input profile).symm.trans (hDist.trans hSheet.symm)
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
        (data.edgePartition (largeTarget input profile)).blockCountWithin
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
      simpa [fine, largePartition, Nat.add_comm] using hTotalNat'
    exact hTotalNat.ge

theorem small_blockCountWithin_selectedFine
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition (smallTarget input profile)).blockCountWithin
      (selectedFine input profile) sheet = 1 := by
  unfold SheetPartition.blockCountWithin
  rw [selectedFine_block_eq_fine input profile sheet hSheet]
  exact SheetPartition.blockCountWithin_self (finePartition input profile) sheet

theorem third_blockCountWithin_selectedFine
    (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition (thirdTarget input profile)).blockCountWithin
        (selectedFine input profile) sheet =
      (finePartition input profile).blockCard sheet := by
  unfold SheetPartition.blockCountWithin
  rw [selectedFine_block_eq_fine input profile sheet hSheet]
  exact third_blockCountWithin_fine input profile sheet hSheet

/-- Assemble the actual oppositely oriented fine Figure 31 candidate. -/
noncomputable def fineCandidate (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    BalancedGlobal.Candidate target degree data wall := by
  let orientation := fineOrientation input profile
  let background := fineBackground input profile
  let selected := selectedResolution input profile
  apply background.install selected (selectedResolution_contracts input profile)
  · intro edge hIncident
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hLarge : edge = largeTarget input profile
    · subst edge
      simp only [background, fineBackground, rightOf, ne_eq, not_true_eq_false,
        decide_false, selected, selectedResolution,
        LocalResolution.reverse_left, fineResolution]
      exact refines_of_mem_incidentEdges data hAt
    · have hRight : rightOf (largeTarget input profile) edge = true := by
        simp [rightOf, hLarge]
      simp only [background, fineBackground, hRight, ite_true, selected,
        selectedResolution, LocalResolution.reverse_right, fineResolution]
      have hCases : edge = smallTarget input profile ∨
          edge = thirdTarget input profile := by
        rw [W3Nd2FineRefinement.incidentEdges_eq input profile] at hAt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hAt
        rcases hAt with hSmall | hLargeEq | hThird
        · exact Or.inl hSmall
        · exact (hLarge hLargeEq).elim
        · exact Or.inr hThird
      rcases hCases with rfl | rfl
      · exact small_refines_selectedFine input profile
      · exact third_refines_selectedFine input profile
  · intro blockAnchor hAnchor _
    change LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (data.vertexPartition wall)
      [selectedFine input profile, data.edgePartition (largeTarget input profile)]
      blockAnchor
    exact riemannHurwitzAtBlock_divalent _ _ _ _ _
  · intro blockAnchor hAnchor _
    change LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (selectedFine input profile)
      [selectedFine input profile,
        data.edgePartition (smallTarget input profile),
        data.edgePartition (thirdTarget input profile)] blockAnchor
    apply riemannHurwitzAtBlock_trivalent_of_counts
    intro sheet hSheet
    have hDistSheet : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet :=
      (anchor_wall_rel input profile).trans (hAnchor.trans hSheet)
    rw [SheetPartition.blockCountWithin_self,
      small_blockCountWithin_selectedFine input profile sheet hDistSheet,
      third_blockCountWithin_selectedFine input profile sheet hDistSheet,
      selectedFine_blockCard_eq_fine input profile sheet hDistSheet]
    omega

/-- The true fine member is valid from the original source datum alone. -/
theorem fineCandidate_valid (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    (fineCandidate input profile).datum.Valid :=
  (fineCandidate input profile).datum_valid input.valid

/-- The true fine member preserves source genus: the selected block and the
background blocks are pasted stars in opposite orientations. -/
theorem fineCandidate_sourceGenus (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) :
    genus (fineCandidate input profile).datum.sourceGraph = genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro sheet
  have hResolution : (fineCandidate input profile).resolution sheet =
      LocalResolution.onBlock (data.vertexPartition wall) (anchor input profile)
        (selectedResolution input profile)
        (fineBackground input profile).resolution sheet := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel (anchor input profile) sheet
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩

/-- The candidate's blockwise resolution is literally the reversed selected
star on every sheet of the distinguished wall block. -/
theorem fineCandidate_resolution_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (fineCandidate input profile).resolution sheet = selectedResolution input profile := by
  change LocalResolution.onBlock (data.vertexPartition wall) (anchor input profile)
      (selectedResolution input profile) (fineBackground input profile).resolution sheet = _
  rw [LocalResolution.onBlock_of_rel]
  exact (anchor_wall_rel input profile).symm.trans hSheet

/-- The globally pasted local resolution used by the actual fine candidate. -/
noncomputable abbrev finePastedResolution (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) : LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall)
    (fineCandidate input profile).resolution (fineCandidate input profile).contracts

/-- On the selected block, the actual pasted divalent endpoint is the whole
wall block. -/
theorem pasted_left_block_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).left.block sheet =
      (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    (fineCandidate input profile).resolution
    (fineCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_selected input profile
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

/-- On the selected block, the actual pasted trivalent endpoint is the
small-direction fine block. -/
theorem pasted_right_block_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).right.block sheet =
      (finePartition input profile).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    (fineCandidate input profile).resolution
    (fineCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_selected input profile
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  exact selectedFine_block_eq_fine input profile sheet hSheet

/-- On the selected block, the actual pasted new edge is the small-direction
fine block. -/
theorem pasted_newEdge_block_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).newEdge.block sheet =
      (finePartition input profile).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    (fineCandidate input profile).resolution
    (fineCandidate input profile).contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [fineCandidate_resolution_selected input profile
    ((data.vertexPartition wall).repr sheet)
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  exact selectedFine_block_eq_fine input profile sheet hSheet

theorem pasted_left_blockCard_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).left.blockCard sheet =
      (data.vertexPartition wall).blockCard sheet := by
  unfold SheetPartition.blockCard
  rw [pasted_left_block_selected input profile sheet hSheet]

theorem pasted_right_blockCard_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).right.blockCard sheet =
      (finePartition input profile).blockCard sheet := by
  unfold SheetPartition.blockCard
  rw [pasted_right_block_selected input profile sheet hSheet]

theorem pasted_newEdge_blockCard_selected (input : W3SourceInput data star)
    (profile : Nd2Profile data input.distinguishedBlock) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (finePastedResolution input profile).newEdge.blockCard sheet =
      (finePartition input profile).blockCard sheet := by
  unfold SheetPartition.blockCard
  rw [pasted_newEdge_block_selected input profile sheet hSheet]

end DraismaVargas.LocalCases.W3Nd2FineCandidates

