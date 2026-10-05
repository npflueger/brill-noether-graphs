module

public import DraismaVargas.LocalCases.M11IncomingJoinedMatching
public import DraismaVargas.LocalCases.M11IncomingSplitMatching
public import DraismaVargas.LocalCases.IncomingNormalizationRows

@[expose] public section

/-!
# Actual M11 incoming matching with induced rows

The graph and compatible sheet normalization are constructed from the source
partition census. The row equivalence follows actual surviving occurrences
and preserves every natural matrix entry. The actual target-valency split
exhausts the joined case and the two leaf orientations.
-/

namespace DraismaVargas.LocalCases.M11IncomingMatching

open DraismaVargas.Infrastructure GraphContraction GluingContraction
open ContractionRamification
open W4StableSource W4Assembly W2R1Target SecondEquation FullDimensionalSource
open M11IncomingTargetNormalization M11IncomingCoordinates M11SourceCandidates

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (incoming : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  (hCompat : WallDegeneration.DanglingCompatible incoming hc hab hOne)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
  {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum incoming hc hab hOne) star block)
  (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard block.1 = 2)

include fullDim hForest

/-- Complete joined-case incoming matching: real cover isomorphism, exact
columns, occurrence-induced wall rows and every natural matrix entry. -/
theorem joined
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    IncomingMatchingConclusion incoming hc hab hOne hCompat input profile hCard := by
  let iso := joinedIso hc hab hOne star hLeft hRight
  let hv := M11IncomingJoinedMatching.vertex_sameBlocks incoming hc hab hOne
    fullDim hForest input profile hCard hLeft hRight
  let he := M11IncomingJoinedMatching.edge_sameBlocks incoming hc hab hOne
    fullDim hForest input profile hCard hLeft hRight
  let member := M11RemoteCandidates.candidates input profile hCard 2
  let rows := TargetPartitionNormalization.stablePathEquiv iso incoming member.datum
    hv he fullDim.valid.1
  refine ⟨2, iso,
    M11IncomingJoinedMatching.sheetRelabeling incoming hc hab hOne fullDim hForest
      input profile hCard hLeft hRight,
    M11IncomingJoinedMatching.sheetRelabeling_apply incoming hc hab hOne fullDim hForest
      input profile hCard hLeft hRight, ?_, rows, ?_, ?_⟩
  · intro column
    exact joinedIso_occurrence hc hab hOne star hLeft hRight
      fullDim.targetConnected fullDim.targetGenus column
  · intro edge
    have h := IncomingNormalizationRows.stablePathEquiv_retained incoming hc hab hOne
      (joinedPattern (contractDatum incoming hc hab hOne) star block hCard).candidate
      iso hv he
      (fun place => joinedIso_occurrence hc hab hOne star hLeft hRight
        fullDim.targetConnected fullDim.targetGenus (some place))
      fullDim.valid.1 input.valid.1 hCompat.1 edge
    exact h.trans (M11JoinedRowDescent.stablePathEquiv_mk input profile hCard edge).symm
  · intro path edge
    exact (TargetPartitionNormalization.matrix_map iso incoming member.datum
      hv he fullDim.valid.1 path edge).symm

/-- Complete split-case incoming matching for either orientation of the leaf. -/
theorem split
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    IncomingMatchingConclusion incoming hc hab hOne hCompat input profile hCard := by
  let iso := splitIso hc hab hOne star hLeaf
  let member := M11RemoteCandidates.candidates input profile hCard 0
  have hv : ∀ vertex, ((GluingTransport.transport iso incoming).vertexPartition vertex).SameBlocks
      (member.datum.vertexPartition vertex) := by
    rcases hLeaf with hLeft | hRight
    · exact M11IncomingSplitMatching.vertexPartitions_sameBlocks_of_left_leaf
        incoming hc hab hOne fullDim hForest input profile hCard hLeft
    · exact M11IncomingSplitMatching.vertexPartitions_sameBlocks_of_right_leaf
        incoming hc hab hOne fullDim hForest input profile hCard hRight
  have he : ∀ edge, ((GluingTransport.transport iso incoming).edgePartition edge).SameBlocks
      (member.datum.edgePartition edge) := by
    rcases hLeaf with hLeft | hRight
    · exact M11IncomingSplitMatching.edgePartitions_sameBlocks_of_left_leaf
        incoming hc hab hOne fullDim hForest input profile hCard hLeft
    · exact M11IncomingSplitMatching.edgePartitions_sameBlocks_of_right_leaf
        incoming hc hab hOne fullDim hForest input profile hCard hRight
  let rows := TargetPartitionNormalization.stablePathEquiv iso incoming member.datum
    hv he fullDim.valid.1
  refine ⟨0, iso,
    PartitionNormalization.sheetRelabeling (GluingTransport.transport iso incoming) member.datum hv he,
    PartitionNormalization.sheetRelabeling_apply (GluingTransport.transport iso incoming) member.datum hv he,
    ?_, rows, ?_, ?_⟩
  · intro column
    exact splitIso_occurrence hc hab hOne star hLeaf
      fullDim.targetConnected fullDim.targetGenus column
  · intro edge
    have h := IncomingNormalizationRows.stablePathEquiv_retained incoming hc hab hOne
      (firstSplitPattern input profile hCard).candidate iso hv he
      (fun place => splitIso_occurrence hc hab hOne star hLeaf
        fullDim.targetConnected fullDim.targetGenus (some place))
      fullDim.valid.1 input.valid.1 hCompat.1 edge
    exact h.trans (M11SplitRowDescent.stablePathEquiv_mk input profile hCard edge).symm
  · intro path edge
    exact (TargetPartitionNormalization.matrix_map iso incoming member.datum
      hv he fullDim.valid.1 path edge).symm

/-- Every actual incoming M11 cover matches one of the real family members,
with the prescribed induced rows and every natural matrix entry. The two
leaf orientations normalize to position zero; position one remains an
essential outgoing alternative, not a fourth incoming target-valency case. -/
theorem exists_matching :
    IncomingMatchingConclusion incoming hc hab hOne hCompat input profile hCard := by
  rcases valencySplit_of_twoStar incoming hc hab hOne fullDim.valid
      fullDim.changeMinimal star with hDivalent | hLeftLeaf | hRightLeaf
  · exact joined incoming hc hab hOne fullDim hForest hCompat input profile hCard
      hDivalent.1 hDivalent.2.1
  · exact split incoming hc hab hOne fullDim hForest hCompat input profile hCard
      (Or.inl hLeftLeaf.1)
  · exact split incoming hc hab hOne fullDim hForest hCompat input profile hCard
      (Or.inr hRightLeaf.2.1)

end DraismaVargas.LocalCases.M11IncomingMatching
