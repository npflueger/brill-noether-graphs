module

public import DraismaVargas.LocalCases.M11SplitVertices
public import DraismaVargas.LocalCases.M11SplitBranchFlags

@[expose] public section

/-!
# The first M11 split preserves the actual stable graph

M11 is Case {w2-r2-nd3-M-11} of Draisma--Vargas Part I (Figure 32).
The vertex map replaces the selected wall branch by the unique fresh branch
and retains every other branch. The row map is the proved descent/lift map.
Exact surviving stars at the selected branch and away from the wall establish
every incidence multiplicity, including both ends of stable loops.
-/

namespace DraismaVargas.LocalCases.M11SplitStableGraph

open DraismaVargas.Infrastructure W4Assembly W4StableSource W2R1Target SecondEquation
open M11SourceCandidates M11SplitVertices StableGraphIncidence

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- A complete actual branch/row incidence equivalence, with no added graph
or pruning receipt and no distinct-row or distinct-endpoint assumption. -/
noncomputable def equivalence :
    Equivalence data (firstSplitPattern input profile hCard).candidate.datum where
  vertex := branchVertexEquiv input profile hCard
  row := M11SplitRowDescent.stablePathEquiv input profile hCard
  incidence vertex path := by
    by_cases hAt : vertex.1.1.1 = wall
    · have hVertex : vertex = selectedOldBranch profile :=
        Subtype.ext (oldBranch_eq_selected input profile vertex hAt)
      subst vertex
      rw [show selectedOldBranch profile = ⟨WallBlock.sourceVertex data wall block,
          profile.valency.ge⟩ from rfl, branchVertexEquiv_selected]
      exact M11SplitBranchFlags.incidenceCount_branchVertex input profile hCard path
    · rw [branchVertexEquiv_away input profile hCard vertex hAt]
      exact ResolutionStableIncidence.incidenceCount_retainedVertex _ input.valid
        (M11SourceGenus.firstSplit_sourceGenus input profile hCard) _
        (M11SplitRowDescent.stablePathEquiv_mk input profile hCard) vertex.1 hAt path

theorem equivalence_row : (equivalence input profile hCard).row =
    M11SplitRowDescent.stablePathEquiv input profile hCard := rfl

/-- A path with an old branch end still has an actual branch end after splitting. -/
theorem hasPathEnds (hEnds : HasPathEnds data) :
    HasPathEnds (firstSplitPattern input profile hCard).candidate.datum :=
  (equivalence input profile hCard).hasPathEnds input.valid.1 hEnds

end DraismaVargas.LocalCases.M11SplitStableGraph
