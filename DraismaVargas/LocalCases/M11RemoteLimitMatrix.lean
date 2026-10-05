module

public import DraismaVargas.LocalCases.M11RemoteInput
public import DraismaVargas.LocalCases.M11RemoteColumn

@[expose] public section

/-!
# Literal common-wall rows and columns for the remote M11 split

The remote branch swap is an actual source-graph isomorphism. Its induced
stable-row equivalence composes with the existing first-split equivalence;
the relabelled first split is definitionally the actual second candidate.
Every retained source occurrence follows that composite map, so all retained
columns equal the original wall matrix. On a tree target the new column is
twice the indicator of the original opposite double row (Figure 32).
-/

namespace DraismaVargas.LocalCases.M11RemoteLimitMatrix

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open M11SourceCandidates M11RemoteCandidates M11RemotePruning M11RemoteInput

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- The complete row equivalence follows the actual branch swap and the
retained-edge first-split quotient map; it is not chosen from cardinalities. -/
noncomputable def stablePathEquiv :
    StablePath data ≃ StablePath (secondSplitPattern input profile hCard).candidate.datum :=
  (SheetRelabelStable.stablePathEquiv (branchRelabeling profile hCard) input.valid.1).trans
    (M11SplitRowDescent.stablePathEquiv (sourceInput input profile hCard)
      (sourceProfile input profile hCard) (swappedBlock_card profile hCard))

/-- Literal transport of an old surviving source occurrence. -/
noncomputable def retainedEdge (edge : NonDanglingEdge data) :
    NonDanglingEdge (secondSplitPattern input profile hCard).candidate.datum :=
  ResolutionAwayFromWall.retainedEdge (secondSplitPattern input profile hCard).candidate
    (sourceInput input profile hCard).valid.1
    (SheetRelabelStable.nonDanglingEdgeEquiv (branchRelabeling profile hCard) input.valid.1 edge)

theorem stablePathEquiv_mk (edge : NonDanglingEdge data) :
    stablePathEquiv input profile hCard edge.stablePath =
      (retainedEdge input profile hCard edge).stablePath := rfl

/-- Exact occurrence dictionary for every retained column and original row. -/
theorem occurrences_retained (path : StablePath data) (place : target.edges) :
    occurrences (secondSplitPattern input profile hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (secondSplitPattern input profile hCard).candidate.right (some place)) =
      (occurrences data path place).image
        (fun edge ↦ (secondSplitPattern input profile hCard).candidate.oldSourceEdge
          ((branchRelabeling profile hCard).sourceEdgeEquiv edge)) := by
  classical
  have hFirst := M11SplitLimitMatrix.occurrences_retained (sourceInput input profile hCard)
    (sourceProfile input profile hCard) (swappedBlock_card profile hCard)
    (SheetRelabelStable.stablePathEquiv (branchRelabeling profile hCard) input.valid.1 path) place
  have hRelabel := congrArg (fun edges : Finset (swappedDatum profile hCard).SourceEdge ↦
    edges.image (secondSplitPattern input profile hCard).candidate.oldSourceEdge)
    (SheetRelabelStable.occurrences_map (branchRelabeling profile hCard) input.valid.1 path place)
  exact hFirst.trans (hRelabel.trans Finset.image_image)

/-- The remote split has the same literal retained matrix as the original
wall, in the proved induced row coordinates. -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix (secondSplitPattern input profile hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (secondSplitPattern input profile hCard).candidate.right (some place)) =
      matrix data path place :=
  (M11SplitLimitMatrix.matrix_retained (sourceInput input profile hCard)
    (sourceProfile input profile hCard) (swappedBlock_card profile hCard) _ place).trans
    (SheetRelabelStable.matrix_map (branchRelabeling profile hCard) input.valid.1 path place)

/-- The opposite original double row transports to the natural retained row
used by the remote new-column calculation of `M11RemoteColumn`. -/
theorem stablePathEquiv_oppositeDouble
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    stablePathEquiv input profile hCard (M11BranchSeparation.oppositeDouble profile hCard).stablePath =
      (M11RemoteColumn.secondSplit_oppositeDouble hConnected hGenus input profile hCard).stablePath := rfl

/-- This and `matrix_retained` identify the complete actual second-split
matrix using original wall rows and literal target occurrence labels. -/
theorem matrix_new (hConnected : graph_connected target) (hGenus : genus target = 0)
    (path : StablePath data) :
    matrix (secondSplitPattern input profile hCard).candidate.datum
        (stablePathEquiv input profile hCard path)
        (occurrenceEquiv target wall (secondSplitPattern input profile hCard).candidate.right none) =
      if path = (M11BranchSeparation.oppositeDouble profile hCard).stablePath then 2 else 0 := by
  classical
  rw [M11RemoteColumn.secondSplit_matrix_new_column_original hConnected hGenus input profile hCard,
    ← stablePathEquiv_oppositeDouble input profile hCard hConnected hGenus]
  simp only [Equiv.apply_eq_iff_eq]

end DraismaVargas.LocalCases.M11RemoteLimitMatrix
