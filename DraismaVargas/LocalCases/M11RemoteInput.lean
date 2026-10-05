module

public import DraismaVargas.LocalCases.SheetRelabelStable
public import DraismaVargas.LocalCases.M11RemotePruning
public import DraismaVargas.LocalCases.M11SplitLimitMatrix

@[expose] public section

/-!
# The remote M11 member is the first split of its relabelled source

Source: Draisma--Vargas Part I, §5.2 (inherited properties): the non-dangling
union lemma (`lemma-class-union`), the labellings compatible at a contracted
edge defined after it, and the limit-matrix lemma (`lemma-limit-matrix-change`).
The actual remote branch swap preserves the complete W2 source input.
Reconstruct its source profile with the exhaustive classifier, then identify its
first split with the literal second split. The profile enumeration is irrelevant
to that construction: the selected wall block determines the split, and the
other profile fields are proofs.
-/

namespace DraismaVargas.LocalCases.M11RemoteInput

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11RemoteCandidates M11RemotePruning M11SourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- The same literal representative is a wall block after the remote swap. -/
noncomputable def swappedBlock : WallBlock (swappedDatum profile hCard) wall :=
  ⟨block.1, by rw [swappedDatum_vertexPartition]; exact block.2⟩

include input in
theorem wallValency (sheet : Fin degree) :
    nonDanglingValency (swappedDatum profile hCard)
        ((swappedDatum profile hCard).sourceEndpoint wall sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  rw [← wall_endpoint_map profile hCard]
  exact SheetRelabelStable.nonDanglingValency_map _ input.valid.1 _

theorem targetChange_eq :
    (swappedDatum profile hCard).targetChange wall = data.targetChange wall := by
  rw [GluingDatum.targetChange_eq_card_formula, GluingDatum.targetChange_eq_card_formula,
    swappedDatum_vertexPartition]
  congr 2
  exact Finset.sum_congr rfl fun edge hAt ↦ by rw [swappedDatum_edgePartition profile hCard edge hAt]

include input in
/-- All W2 source-input fields are derived under the actual branch
isomorphism. This is not an additional assumption on the remote candidate. -/
theorem sourceInput : W2SourceInput (swappedDatum profile hCard) star where
  valid := (branchRelabeling profile hCard).valid input.valid
  stablePath_card := (Fintype.card_congr
    (SheetRelabelStable.stablePathEquiv (branchRelabeling profile hCard) input.valid.1)).symm.trans
      input.stablePath_card
  dangling_no_glue := SheetRelabelStable.danglingEdgeNoGlue_map _ input.valid.1 input.dangling_no_glue
  nonDangling_valency := by
    intro sourceBlock
    let old : WallBlock data wall := ⟨sourceBlock.1, by
      exact (congrArg (fun p : SheetPartition degree => p.repr sourceBlock.1)
        (swappedDatum_vertexPartition profile hCard)).symm.trans sourceBlock.2⟩
    change nonDanglingValency _ ((swappedDatum profile hCard).sourceEndpoint wall sourceBlock.1) = 0 ∨
      nonDanglingValency _ ((swappedDatum profile hCard).sourceEndpoint wall sourceBlock.1) = 2 ∨
      nonDanglingValency _ ((swappedDatum profile hCard).sourceEndpoint wall sourceBlock.1) = 3
    rw [wallValency input profile hCard]
    exact input.nonDangling_valency old
  equation_c := by
    unfold GluingDatum.targetExcess
    rw [targetChange_eq profile hCard]
    exact input.equation_c

theorem swappedBlock_ramification :
    (swappedDatum profile hCard).localRamification wall (swappedBlock profile hCard) = 2 := by
  have hEq : (swappedDatum profile hCard).localRamification wall (swappedBlock profile hCard) =
      data.localRamification wall block := by
    unfold GluingDatum.localRamification
    simp only [swappedBlock, swappedDatum_vertexPartition]
    congr 2
    exact Finset.sum_congr rfl fun edge hAt ↦ by rw [swappedDatum_edgePartition profile hCard edge hAt]
  exact hEq.trans profile.ramification

include input in
theorem swappedBlock_valency :
    nonDanglingValency (swappedDatum profile hCard)
      (WallBlock.sourceVertex (swappedDatum profile hCard) wall (swappedBlock profile hCard)) = 3 :=
  (wallValency input profile hCard block.1).trans profile.valency

/-- Apply the exhaustive profile constructor to the transported
input. Its enumeration may differ, but the literal split datum depends only
on the selected wall block, not that enumeration. -/
noncomputable def sourceProfile :
    W2R2SourceProfile.SourceProfile (swappedDatum profile hCard) star (swappedBlock profile hCard) :=
  Classical.choice (W2R2SourceProfile.exists_sourceProfile (sourceInput input profile hCard)
    (swappedBlock profile hCard) (swappedBlock_ramification profile hCard)
    (swappedBlock_valency input profile hCard))

theorem swappedBlock_card :
    ((swappedDatum profile hCard).vertexPartition wall).blockCard
      (swappedBlock profile hCard).1 = 2 := by
  change ((swappedDatum profile hCard).vertexPartition wall).blockCard block.1 = 2
  rw [swappedDatum_vertexPartition]
  exact hCard

theorem firstSplitPattern_eq_second :
    firstSplitPattern (sourceInput input profile hCard) (sourceProfile input profile hCard)
        (swappedBlock_card profile hCard) =
      secondSplitPattern input profile hCard := rfl

end DraismaVargas.LocalCases.M11RemoteInput
