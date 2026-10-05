module

public import DraismaVargas.LocalCases.M11IncomingSelectedCases
public import DraismaVargas.LocalCases.M11IncomingBackground
public import DraismaVargas.LocalCases.M11IncomingOuterPartitions
public import DraismaVargas.Infrastructure.PartitionNormalization

@[expose] public section

/-!
# Actual incoming joined M11 cover matching

At two divalent incoming target endpoints, the selected two-sheet census and
the census of every other merged block both say that the two endpoint
partitions and contracted-edge partition are joined on that block.  Refinement
then identifies their complete block relations with the merged partition.

Transport by the actual `joinedIso` is compared pointwise with M11 member 2.
Outer vertex and retained-edge partitions agree literally.  Both expanded
endpoint partitions and the new-edge partition have the same blocks as the
literal joined candidate.  This is independent of the target endpoint swap
and of which profile label is double.

The checked within-block normalization produces an actual compatible
`SheetRelabeling` whose `apply` is exactly member 2's datum.  The final consumer
also preserves the actual common Option columns.  It does not prove the
retained-wall stable-row compatibility required by the full incoming-matching
conclusion, nor does it treat the leaf/split incoming cases.

Inputs are the original full-dimensional presentation, actual contraction
forest, derived W2 input and selected M11 profile/cardinality, and the two
incoming target valencies.  No pointwise SameBlocks, cover equality, NoReturn,
or row-matching premise is added.
-/

namespace DraismaVargas.LocalCases.M11IncomingJoinedMatching

open DraismaVargas.Infrastructure TargetExpansion GraphContraction GluingContraction
open ContractionRamification
open W4Assembly W2R1Target SecondEquation FullDimensionalSource
open M11IncomingPartitions M11IncomingTargetNormalization M11IncomingOuterPartitions
open M11SourceCandidates

private theorem sameBlocks_of_eq {d : ℕ} {first second : SheetPartition d}
    (h : first = second) : first.SameBlocks second := by
  rw [h]
  exact SheetPartition.SameBlocks.refl _

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
variable (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (hForest : ContractionForest incoming a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
    {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
    (profile : W2R2SourceProfile.SourceProfile (contractDatum incoming hc hab hOne) star block)
    (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard block.1 = 2)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)

include hc hab hOne fullDim hForest input profile hCard hLeft hRight

/-- Selected and background block censuses together recover the whole incoming
endpoint and contracted-edge relations, not just their selected restrictions. -/
theorem original_sameBlocks :
    (incoming.vertexPartition a).SameBlocks (mergedPartition incoming a b) ∧
      (incoming.edgePartition contracted).SameBlocks (mergedPartition incoming a b) ∧
      (incoming.vertexPartition b).SameBlocks (mergedPartition incoming a b) := by
  classical
  have hAll (anchor : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩) :
      JoinedOnBlock (incoming.vertexPartition a) (mergedPartition incoming a b) anchor.1 ∧
        JoinedOnBlock (incoming.edgePartition contracted) (mergedPartition incoming a b) anchor.1 ∧
        JoinedOnBlock (incoming.vertexPartition b) (mergedPartition incoming a b) anchor.1 := by
    by_cases hSelected : anchor = block
    · subst anchor
      have h := M11IncomingSelectedCases.selected_census_of_both_divalent incoming hc hab hOne
        fullDim hForest profile hCard hLeft hRight
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    · have h := M11IncomingBackground.background_census_of_both_divalent incoming hc hab hOne
        fullDim hForest input profile anchor hSelected hLeft hRight
      exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hReverse (first second : Fin degree) (hRel : (mergedPartition incoming a b).Rel first second) :
      (incoming.vertexPartition a).Rel first second ∧
        (incoming.edgePartition contracted).Rel first second ∧
        (incoming.vertexPartition b).Rel first second := by
    let anchor := WallBlock.ofSheet (contractDatum incoming hc hab hOne) ⟨a, hab⟩ first
    have hRoot : (mergedPartition incoming a b).Rel anchor.1 first := by
      rw [← contractDatum_vertexPartition_merge incoming hc hab hOne]
      exact ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_left first
    exact ⟨(hAll anchor).1 first second hRoot (hRoot.trans hRel),
      (hAll anchor).2.1 first second hRoot (hRoot.trans hRel),
      (hAll anchor).2.2 first second hRoot (hRoot.trans hRel)⟩
  exact ⟨fun first second => ⟨(vertexPartition_refines_mergedPartition incoming a b).rel,
      fun h => (hReverse first second h).1⟩,
    fun first second => ⟨(edgePartition_refines_mergedPartition incoming hc).rel,
      fun h => (hReverse first second h).2.1⟩,
    fun first second => ⟨(vertexPartition_refines_mergedPartition_right incoming a b).rel,
      fun h => (hReverse first second h).2.2⟩⟩

/-- The datum transported by the actual joined target normalization. -/
noncomputable abbrev transported :=
  GluingTransport.transport (joinedIso hc hab hOne star hLeft hRight) incoming

private theorem transported_endpoints_sameBlocks :
    ((transported incoming hc hab hOne (star := star) hLeft hRight).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩)).SameBlocks
        ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) ∧
      ((transported incoming hc hab hOne (star := star) hLeft hRight).vertexPartition
        (freshVertex (contract target hab hOne))).SameBlocks
        ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
  have hSame := original_sameBlocks incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight
  have hA : (incoming.vertexPartition a).SameBlocks
      ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
    rw [contractDatum_vertexPartition_merge]
    exact hSame.1
  have hB : (incoming.vertexPartition b).SameBlocks
      ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) := by
    rw [contractDatum_vertexPartition_merge]
    exact hSame.2.2
  have hPair := joined_endpointPartitions incoming hc hab hOne star hLeft hRight
  split_ifs at hPair with hSide
  · have hFirst := congrArg Prod.fst hPair
    have hSecond := congrArg Prod.snd hPair
    exact ⟨(sameBlocks_of_eq hFirst).trans hA, (sameBlocks_of_eq hSecond).trans hB⟩
  · have hFirst := congrArg Prod.fst hPair
    have hSecond := congrArg Prod.snd hPair
    exact ⟨(sameBlocks_of_eq hFirst).trans hB, (sameBlocks_of_eq hSecond).trans hA⟩

/-- Pointwise vertex partition matching against the actual joined member. -/
theorem vertex_sameBlocks
    (vertex : (M11RemoteCandidates.candidates input profile hCard 2).outgoingTarget.V) :
    ((transported incoming hc hab hOne (star := star) hLeft hRight).vertexPartition vertex).SameBlocks
      ((M11RemoteCandidates.candidates input profile hCard 2).datum.vertexPartition vertex) := by
  have hEnds := transported_endpoints_sameBlocks incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight
  cases vertex with
  | inl vertex =>
    by_cases hWall : vertex = ⟨a, hab⟩
    · subst vertex
      have hCandidate := M11JoinedGeometry.vertexPartition_endpoint
        (contractDatum incoming hc hab hOne) star block hCard 0
      exact hEnds.1.trans (sameBlocks_of_eq hCandidate.symm)
    · have hOuter := transported_vertexPartition_of_ne incoming hc hab hOne star.right
        (joinedPlacement hc hab hOne star hLeft hRight) vertex hWall
      have hCandidate : (M11RemoteCandidates.candidates input profile hCard 2).datum.vertexPartition
          (oldVertex (contract target hab hOne) vertex) =
          (contractDatum incoming hc hab hOne).vertexPartition vertex :=
        GlobalResolution.expandedVertexPartition_old_of_ne _ _ _ _ hWall
      exact sameBlocks_of_eq (hOuter.trans hCandidate.symm)
  | inr fresh =>
    cases fresh
    have hCandidate := M11JoinedGeometry.vertexPartition_endpoint
      (contractDatum incoming hc hab hOne) star block hCard 1
    exact hEnds.2.trans (sameBlocks_of_eq hCandidate.symm)

/-- Every literal retained occurrence matches exactly; on the new occurrence
the selected and background censuses give the whole merged block relation. -/
theorem edge_sameBlocks
    (edge : (M11RemoteCandidates.candidates input profile hCard 2).outgoingTarget.edges) :
    ((transported incoming hc hab hOne (star := star) hLeft hRight).edgePartition edge).SameBlocks
      ((M11RemoteCandidates.candidates input profile hCard 2).datum.edgePartition edge) := by
  obtain ⟨column, rfl⟩ := (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ star.right).surjective edge
  cases column with
  | none =>
    have hOuter := transported_edgePartition_new incoming hc hab hOne star.right
      (joinedPlacement hc hab hOne star hLeft hRight) fullDim.targetConnected fullDim.targetGenus
    have hCandidate := M11JoinedGeometry.new_edgePartition
      (contractDatum incoming hc hab hOne) star block hCard
    have hOriginal := (original_sameBlocks incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight).2.1
    exact (sameBlocks_of_eq hOuter).trans (hOriginal.trans
      (sameBlocks_of_eq (hCandidate.trans (contractDatum_vertexPartition_merge incoming hc hab hOne)).symm))
  | some edge =>
    have hOuter := transported_edgePartition_retained incoming hc hab hOne star.right
      (joinedPlacement hc hab hOne star hLeft hRight) fullDim.targetConnected fullDim.targetGenus edge
    have hCandidate : (M11RemoteCandidates.candidates input profile hCard 2).datum.edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ star.right (some edge)) =
        (contractDatum incoming hc hab hOne).edgePartition edge :=
      GlobalResolution.expandedEdgePartition_old _ _ _ _ edge
    exact sameBlocks_of_eq (hOuter.trans hCandidate.symm)

/-- The actual compatible within-block sheet normalization, built from the
proved whole-cover relation equalities. -/
noncomputable def sheetRelabeling :
    (transported incoming hc hab hOne (star := star) hLeft hRight).SheetRelabeling :=
  PartitionNormalization.sheetRelabeling
    (transported incoming hc hab hOne (star := star) hLeft hRight)
    (M11RemoteCandidates.candidates input profile hCard 2).datum
    (vertex_sameBlocks incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight)
    (edge_sameBlocks incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight)

/-- Exact equality of the normalized incoming datum with the actual joined
member, including stored representative tables. -/
theorem sheetRelabeling_apply :
    (sheetRelabeling incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight).apply =
      (M11RemoteCandidates.candidates input profile hCard 2).datum :=
  PartitionNormalization.sheetRelabeling_apply
    (transported incoming hc hab hOne (star := star) hLeft hRight)
    (M11RemoteCandidates.candidates input profile hCard 2).datum
    (vertex_sameBlocks incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight)
    (edge_sameBlocks incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight)

/-- The joined incoming cover is identified by a real target isomorphism and
compatible sheet relabelling, preserving the family's exact common columns.
Stable-row matching is deliberately not part of this endpoint. -/
theorem exists_target_sheet_matching :
    ∃ iso : Utilities.CFGraphIso target
        (M11RemoteCandidates.candidates input profile hCard 2).outgoingTarget,
      ∃ sheets : (GluingTransport.transport iso incoming).SheetRelabeling,
        sheets.apply = (M11RemoteCandidates.candidates input profile hCard 2).datum ∧
        ∀ column : Option (contract target hab hOne).edges,
          GluingTransport.edgeEquiv iso (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
            M11CommonBalance.columnEquiv input profile hCard 2 column := by
  refine ⟨joinedIso hc hab hOne star hLeft hRight,
    sheetRelabeling incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight,
    sheetRelabeling_apply incoming hc hab hOne fullDim hForest input profile hCard hLeft hRight, ?_⟩
  intro column
  exact joinedIso_occurrence hc hab hOne star hLeft hRight
    fullDim.targetConnected fullDim.targetGenus column

end DraismaVargas.LocalCases.M11IncomingJoinedMatching
