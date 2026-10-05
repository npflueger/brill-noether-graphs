module

public import DraismaVargas.LocalCases.M11SplitStableGraph
public import DraismaVargas.LocalCases.M11JoinedStableGraph
public import DraismaVargas.LocalCases.M11CommonBalance

@[expose] public section

/-!
# The actual M11 family has one stable graph

The remote member composes the literal branch sheet swap with the first-split
incidence equivalence. Together with the joined member this identifies all
three actual branch/row incidence structures, in exactly the row coordinates
used by the common-column and determinant-balance proof.
-/

namespace DraismaVargas.LocalCases.M11StableGraphs

open DraismaVargas.Infrastructure W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11RemoteCandidates M11RemotePruning M11RemoteInput
open StableGraphIncidence

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- The remote member follows the actual sheet swap, not an identification
of its raw datum with the original wall datum. -/
noncomputable def remote :
    Equivalence data (secondSplitPattern input profile hCard).candidate.datum :=
  (StableGraphIncidence.sheetRelabel (branchRelabeling profile hCard) input.valid.1).trans
    (M11SplitStableGraph.equivalence (sourceInput input profile hCard)
      (sourceProfile input profile hCard) (swappedBlock_card profile hCard))

theorem remote_row : (remote input profile hCard).row =
    M11RemoteLimitMatrix.stablePathEquiv input profile hCard := rfl

/-- Every actual source-derived family member preserves the original stable
graph's branch vertices, rows and all endpoint incidence multiplicities. -/
noncomputable def equivalence (position : Fin 3) :
    Equivalence data (candidates input profile hCard position).datum :=
  Fin.cases (M11SplitStableGraph.equivalence input profile hCard)
    (Fin.cases (remote input profile hCard)
      (Fin.cases (M11JoinedStableGraph.equivalence input profile hCard)
        (fun i ↦ Fin.elim0 i))) position

/-- The endpoint dictionary uses exactly the load-bearing matrix row maps. -/
theorem equivalence_row (position : Fin 3) :
    (equivalence input profile hCard position).row =
      M11CommonBalance.rowEquiv input profile hCard position := by
  fin_cases position <;> rfl

theorem hasPathEnds (hEnds : HasPathEnds data) (position : Fin 3) :
    HasPathEnds (candidates input profile hCard position).datum :=
  (equivalence input profile hCard position).hasPathEnds input.valid.1 hEnds

/-- Compare any two family members through their actual common stable graph. -/
noncomputable def between (first second : Fin 3) :
    Equivalence (candidates input profile hCard first).datum
      (candidates input profile hCard second).datum :=
  (equivalence input profile hCard first).symm.trans (equivalence input profile hCard second)

/-- A compatible square labelling names the same actual row across members. -/
theorem labelling_between {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (candidates input profile hCard 0).datum coordinate)
    (first second : Fin 3) (path : StablePath (candidates input profile hCard first).datum) :
    (M11CommonBalance.labelling input profile hCard initial second).row
        ((between input profile hCard first second).row path) =
      (M11CommonBalance.labelling input profile hCard initial first).row path := by
  change M11CommonBalance.sourceCoordinates input profile hCard initial
      ((M11CommonBalance.rowEquiv input profile hCard second).symm
        ((equivalence input profile hCard second).row
          ((equivalence input profile hCard first).row.symm path))) = _
  rw [equivalence_row, equivalence_row, Equiv.symm_apply_apply]
  rfl

end DraismaVargas.LocalCases.M11StableGraphs
