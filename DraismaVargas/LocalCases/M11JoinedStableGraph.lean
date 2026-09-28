import DraismaVargas.LocalCases.M11JoinedBranchClassification
import DraismaVargas.LocalCases.M11JoinedIncidence
import DraismaVargas.LocalCases.ResolutionStableIncidence

/-!
# The actual stable incidence equivalence for joined M11

M11 is Case {w2-r2-nd3-M-11} of Draisma--Vargas Part I (Figure 32).
An old branch at the wall is necessarily the selected profile block: every
background wall block has only two incident occurrences. It maps to the
selected joined double-direction branch. An old branch away from the wall maps
to its literal retained source vertex.

The joined endpoint classification proves exhaustion at the wall, and the
unchanged source partitions prove exhaustion and injectivity away from it.
Thus `branchVertexEquiv` is the inverse completion of this proved geometric
map, not a bijection chosen from cardinality. Its rows are the actual retained
occurrence lift `M11JoinedRowDescent.stablePathEquiv`.

`equivalence` proves incidence multiplicity preservation at every branch and
every row by the selected three-flag calculation and the exact off-wall star
dictionary. Coincident stable rows and both flags of a loop remain counted.
This supplies a global `StableGraphIncidence.Equivalence` and transports the
path-end property. It constructs no requested `Spec`, metric dictionary, or
zero-contraction/terminal receipt.
-/

namespace DraismaVargas.LocalCases.M11JoinedStableGraph

open DraismaVargas.Infrastructure TargetExpansion W4StableSource W4Assembly
open W2R1Target SecondEquation M11SourceCandidates M11JoinedBranch
open M11JoinedGeometry M11JoinedBranchClassification ResolutionAwayFromWall
open StableGraphIncidence

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- The selected profile vertex is the unique old branch over the wall. -/
theorem eq_wallBlock_of_at_of_branch (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (vertex : data.SourceVertex) (hAt : vertex.1.1 = wall)
    (hBranch : 3 ≤ nonDanglingValency data vertex) :
    vertex = WallBlock.sourceVertex data wall block := by
  by_cases hSelected : (data.vertexPartition wall).Rel block.1 vertex.1.2
  · exact ((data.sourceEndpoint_eq_iff wall block.1 vertex).mpr ⟨hAt.symm, hSelected⟩).symm
  · have hCard := M11JoinedDescentGeometry.background_old_card_incident input profile
      vertex.1.2 hSelected
    have hVertex := data.sourceEndpoint_self vertex
    rw [hAt] at hVertex
    rw [hVertex] at hCard
    have hLe := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data vertex
    omega

/-- The geometric branch map: the selected joined branch at the wall, and
the literal retained copy everywhere else. -/
noncomputable def branchVertexMap (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (vertex : BranchVertex data) :
    BranchVertex (joinedPattern data star block hCard).candidate.datum := by
  classical
  exact if hAt : vertex.1.1.1 = wall then
    ⟨branchVertex profile hCard, by rw [branchVertex_valency input profile hCard]⟩
  else
    ⟨retainedVertex (joinedPattern data star block hCard).candidate vertex.1, by
      rw [nonDanglingValency_retainedVertex _ input.valid
        (M11SourceGenus.joined_sourceGenus data star block hCard) vertex.1 hAt]
      exact vertex.2⟩

/-- Contracting the expanded target recovers each original branch location. -/
theorem branchVertexMap_contractTarget (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (vertex : BranchVertex data) :
    contractVertex target wall (branchVertexMap input profile hCard vertex).1.1.1 =
      vertex.1.1.1 := by
  classical
  by_cases hAt : vertex.1.1.1 = wall
  · simp only [branchVertexMap, hAt, ↓reduceDIte]
    change contractVertex target wall (endpoint target wall profile.doubleLabel) = wall
    unfold endpoint
    split_ifs <;> rfl
  · simp only [branchVertexMap, hAt, ↓reduceDIte]
    rfl

/-- Branches cannot merge: uniqueness at the wall and literal injectivity
away from it handle the two cases. -/
theorem branchVertexMap_injective (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Function.Injective (branchVertexMap input profile hCard) := by
  classical
  intro first second hEqual
  have hTarget := congrArg
    (fun vertex : BranchVertex (joinedPattern data star block hCard).candidate.datum ↦
      contractVertex target wall vertex.1.1.1) hEqual
  rw [branchVertexMap_contractTarget, branchVertexMap_contractTarget] at hTarget
  apply Subtype.ext
  by_cases hFirst : first.1.1.1 = wall
  · have hSecond : second.1.1.1 = wall := hTarget.symm.trans hFirst
    exact (eq_wallBlock_of_at_of_branch input profile first.1 hFirst first.2).trans
      (eq_wallBlock_of_at_of_branch input profile second.1 hSecond second.2).symm
  · have hSecond : second.1.1.1 ≠ wall := fun h ↦ hFirst (hTarget.trans h)
    have hVertices := congrArg Subtype.val hEqual
    simp only [branchVertexMap, hFirst, hSecond, ↓reduceDIte] at hVertices
    exact ResolutionStableIncidence.retainedVertex_injective_away _ first.1 second.1
      hFirst hSecond hVertices

/-- Every joined branch is either its unique endpoint branch or the retained
copy of an old away branch. No count-based exhaustion is assumed. -/
theorem branchVertexMap_surjective (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Function.Surjective (branchVertexMap input profile hCard) := by
  classical
  intro vertex
  let candidate := (joinedPattern data star block hCard).candidate
  have hCases : (∃ label : Fin 2, vertex.1.1.1 = endpoint target wall label) ∨
      ∃ old : data.SourceVertex, old.1.1 ≠ wall ∧ retainedVertex candidate old = vertex.1 := by
    rcases hTarget : vertex.1.1.1 with place | fresh
    · by_cases hAt : place = wall
      · left
        refine ⟨0, ?_⟩
        simp [endpoint, oldVertex, hAt]
        rfl
      · right
        obtain ⟨old, hOld, hRetained⟩ :=
          exists_retainedVertex_of_target candidate vertex.1 place hAt hTarget
        exact ⟨old, fun h ↦ hAt (hOld.symm.trans h), hRetained⟩
    · left
      refine ⟨1, ?_⟩
      cases fresh
      rfl
  rcases hCases with ⟨label, hTarget⟩ | ⟨old, hAway, hRetained⟩
  · have hBranch := eq_branchVertex_of_endpoint_of_branch input profile hCard vertex.1
      label hTarget vertex.2
    let original : BranchVertex data :=
      ⟨WallBlock.sourceVertex data wall block, by rw [profile.valency]⟩
    refine ⟨original, ?_⟩
    apply Subtype.ext
    have hAt : original.1.1.1 = wall := rfl
    simp only [branchVertexMap, hAt, ↓reduceDIte]
    exact hBranch.symm
  · have hOldBranch : 3 ≤ nonDanglingValency data old := by
      rw [← nonDanglingValency_retainedVertex candidate input.valid
        (M11SourceGenus.joined_sourceGenus data star block hCard) old hAway, hRetained]
      exact vertex.2
    refine ⟨⟨old, hOldBranch⟩, ?_⟩
    apply Subtype.ext
    simpa only [branchVertexMap, hAway, ↓reduceDIte] using hRetained

/-- Complete the actual branch map to an equivalence using its proved
injectivity and surjectivity. -/
noncomputable def branchVertexEquiv (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    BranchVertex data ≃ BranchVertex (joinedPattern data star block hCard).candidate.datum :=
  Equiv.ofBijective (branchVertexMap input profile hCard)
    ⟨branchVertexMap_injective input profile hCard, branchVertexMap_surjective input profile hCard⟩

/-- A global, inhabited stable incidence dictionary for the joined candidate. -/
noncomputable def equivalence (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    StableGraphIncidence.Equivalence data (joinedPattern data star block hCard).candidate.datum where
  vertex := branchVertexEquiv input profile hCard
  row := M11JoinedRowDescent.stablePathEquiv input profile hCard
  incidence vertex path := by
    classical
    change StablePathCount.incidenceCount data vertex.1 path =
      StablePathCount.incidenceCount _ (branchVertexMap input profile hCard vertex).1 _
    by_cases hAt : vertex.1.1.1 = wall
    · simp only [branchVertexMap, hAt, ↓reduceDIte]
      rw [eq_wallBlock_of_at_of_branch input profile vertex.1 hAt vertex.2]
      exact M11JoinedIncidence.incidenceCount_branchVertex input profile hCard path
    · simp only [branchVertexMap, hAt, ↓reduceDIte]
      exact ResolutionStableIncidence.incidenceCount_retainedVertex _ input.valid
        (M11SourceGenus.joined_sourceGenus data star block hCard)
        (M11JoinedRowDescent.stablePathEquiv input profile hCard)
        (M11JoinedRowDescent.stablePathEquiv_mk input profile hCard) vertex.1 hAt path

/-- The certificate's vertex map is literally the geometric piecewise map. -/
theorem equivalence_vertex_apply (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (vertex : BranchVertex data) :
    (equivalence input profile hCard).vertex vertex = branchVertexMap input profile hCard vertex := rfl

/-- The certificate's row map follows each actual retained occurrence. -/
theorem equivalence_row_mk (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (edge : NonDanglingEdge data) :
    (equivalence input profile hCard).row edge.stablePath =
      (retainedEdge (joinedPattern data star block hCard).candidate input.valid.1 edge).stablePath := rfl

/-- The row equivalence is exactly the geometric joined row map. -/
theorem equivalence_row (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (equivalence input profile hCard).row =
      M11JoinedRowDescent.stablePathEquiv input profile hCard := rfl

/-- A genuine consumer of the complete incidence certificate. The path-end
property is required only on the original cover. -/
theorem hasPathEnds (input : W2SourceInput data star)
    {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (hEnds : HasPathEnds data) :
    HasPathEnds (joinedPattern data star block hCard).candidate.datum :=
  (equivalence input profile hCard).hasPathEnds input.valid.1 hEnds

end DraismaVargas.LocalCases.M11JoinedStableGraph
