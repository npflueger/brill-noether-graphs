module

public import DraismaVargas.LocalCases.M11RemoteCandidates

@[expose] public section

/-!
# The genuine background leaves of the M11 split candidates

The split's target leaf has a degree-two source vertex on the distinguished
block and singleton source leaves on every background block. The proofs count
actual incident occurrences before invoking the dangling-edge theorem: index
one by itself does not imply that a source edge is dangling.
-/

namespace DraismaVargas.LocalCases.M11SplitLeaves

open DraismaVargas.Infrastructure TargetExpansion
open ResolutionM11 GlobalM11Arbitrary M11SourceCandidates M11RemoteCandidates
open W4Assembly W4StableSource W2R1Target SecondEquation

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- If the expanded left target endpoint is a leaf, its only incident target
occurrence is the newly inserted one. -/
theorem left_target_incident (candidate : BalancedGlobal.Candidate target degree data wall)
    (hLeaf : (GluingDatum.incidentEdges (target := graph target wall candidate.right)
      (oldVertex target wall)).card = 1) :
    GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (oldVertex target wall) = {occurrenceEquiv target wall candidate.right none} := by
  classical
  obtain ⟨edge, hEdge⟩ := Finset.card_eq_one.mp hLeaf
  have hMem : occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (oldVertex target wall) := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [occurrenceEquiv_none]
    exact Or.inl rfl
  have hNew : occurrenceEquiv target wall candidate.right none = edge := by
    simpa only [hEdge, Finset.mem_singleton] using hMem
  rwa [← hNew] at hEdge

/-- The source incidence count over the split's target leaf is precisely the
local new-edge block count, including at noncanonical sheet representatives. -/
theorem card_incident_left (candidate : BalancedGlobal.Candidate target degree data wall)
    (hLeaf : (GluingDatum.incidentEdges (target := graph target wall candidate.right)
      (oldVertex target wall)).card = 1) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge candidate.datum
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) =
      (candidate.resolution ((data.vertexPartition wall).repr sheet)).newEdge.blockCountWithin
        (candidate.resolution ((data.vertexPartition wall).repr sheet)).left sheet := by
  classical
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target wall),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (oldVertex target wall))
      ((candidate.datum.vertexPartition (oldVertex target wall)).repr sheet)) = _
  rw [left_target_incident candidate hLeaf, Finset.sum_singleton]
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GlobalResolution.datum_edgePartition_new, GlobalResolution.datum_vertexPartition_old_wall]
  let pasted := LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts
  have hRepr : pasted.newEdge.blockCountWithin pasted.left (pasted.left.repr sheet) =
      pasted.newEdge.blockCountWithin pasted.left sheet := by
    unfold SheetPartition.blockCountWithin
    rw [pasted.left.block_eq_of_rel (pasted.left.rel_repr_left sheet)]
  rw [hRepr]
  exact LocalResolution.paste_newEdge_blockCountWithin_left _ _ _ sheet

/-- The distinguished block is joined at the leaf endpoint; each other
block is split into singleton leaves. This is a literal local block count. -/
theorem split_background_count (partition : SheetPartition degree)
    (distinguished sheet : Fin degree) :
    (LocalResolution.onBlock partition distinguished (splitResolutionAt partition distinguished)
      (backgroundResolution partition) (partition.repr sheet)).newEdge.blockCountWithin
      (LocalResolution.onBlock partition distinguished (splitResolutionAt partition distinguished)
        (backgroundResolution partition) (partition.repr sheet)).left sheet =
      if partition.Rel distinguished sheet then partition.blockCard sheet else 1 := by
  by_cases hSelected : partition.Rel distinguished sheet
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _
      (hSelected.trans (partition.rel_repr_right sheet)), ite_eq_left hSelected]
    exact partition.splitBlock_blockCountWithin_of_rel distinguished sheet hSelected
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _
      (fun h ↦ hSelected (h.trans (partition.rel_repr_left sheet))), ite_eq_right hSelected]
    exact SheetPartition.blockCountWithin_self _ _

theorem firstSplit_left_card (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint
        (oldVertex target wall) sheet)) =
      if (data.vertexPartition wall).Rel block.1 sheet
      then (data.vertexPartition wall).blockCard sheet else 1 := by
  rw [card_incident_left _ (firstSplit_target_valencies input profile hCard).1]
  exact split_background_count _ _ _

/-- The remote split has the same local incidence census, stated on the
original wall partition, although its source graph is remotely relabelled. -/
theorem secondSplit_left_card (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.datum.sourceEndpoint
        (oldVertex target wall) sheet)) =
      if (data.vertexPartition wall).Rel block.1 sheet
      then (data.vertexPartition wall).blockCard sheet else 1 := by
  rw [card_incident_left _ (secondSplit_target_valencies input profile hCard).1]
  have hResolution :
      (secondSplitPattern input profile hCard).candidate.resolution
        (((swappedDatum profile hCard).vertexPartition wall).repr sheet) =
      LocalResolution.onBlock ((swappedDatum profile hCard).vertexPartition wall) block.1
        (splitResolutionAt ((swappedDatum profile hCard).vertexPartition wall) block.1)
        (backgroundResolution ((swappedDatum profile hCard).vertexPartition wall))
        (((swappedDatum profile hCard).vertexPartition wall).repr sheet) := rfl
  rw [hResolution, split_background_count, swappedDatum_vertexPartition profile hCard]

/-- A new occurrence with a genuine degree-one left source endpoint is
dangling. The actual endpoint identity is supplied by global assembly. -/
theorem newSourceEdge_isDangling_of_left_card_one
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (hValid : data.Valid) (sheet : Fin degree)
    (hCard : Fintype.card (IncidentSourceEdge candidate.datum
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) = 1) :
    IsDangling candidate.datum (candidate.newSourceEdge sheet) := by
  have hDegree : vertex_degree candidate.datum.sourceGraph
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 1 := by
    rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hCard]
    norm_num
  have hEndpoint := congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge
    data wall candidate.right
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right candidate.resolution
      candidate.contracts candidate.exterior) sheet)
  exact isDangling_of_sourceEnds_fst_degree_eq_one candidate.datum
    (candidate.datum_valid hValid).1 (candidate.newSourceEdge sheet) (hEndpoint ▸ hDegree)

/-- Every new first-split occurrence on a background wall block is an actual
dangling source leaf, for arbitrary background block size. -/
theorem firstSplit_background_isDangling (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    IsDangling (firstSplitPattern input profile hCard).candidate.datum
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge sheet) := by
  apply newSourceEdge_isDangling_of_left_card_one _ input.valid
  exact (firstSplit_left_card input profile hCard sheet).trans (ite_eq_right hBackground)

/-- The same leaf pruning holds on the remotely swapped second split. -/
theorem secondSplit_background_isDangling (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    IsDangling (secondSplitPattern input profile hCard).candidate.datum
      ((secondSplitPattern input profile hCard).candidate.newSourceEdge sheet) := by
  apply newSourceEdge_isDangling_of_left_card_one _
    (wallBranchSwap_preserves_valid data input.valid wall _ _ _ _ _)
  exact (secondSplit_left_card input profile hCard sheet).trans (ite_eq_right hBackground)

end DraismaVargas.LocalCases.M11SplitLeaves
