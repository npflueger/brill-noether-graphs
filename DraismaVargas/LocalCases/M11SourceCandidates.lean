import DraismaVargas.LocalCases.W2IncomingClassification
import DraismaVargas.LocalCases.GlobalM11Arbitrary

/-!
# M11 candidates derived from an actual Case {w2} source profile

Source: Draisma--Vargas Part I, Case {w2-r2-nd3-M-11} (abbreviated M11) and
Figure 32. On the distinguished two-sheet
block the split candidate has a joined leaf and singleton trivalent ends.
Every other wall block is r0. A background block of size m keeps its joined
trivalent vertex and grows m singleton leaf arms, each of index one. This is
the reverse split resolution, not the joined resolution. Its trivalent
Riemann--Hurwitz equality is
`m + 1 + 1 - 2 = m`.

The background receipts and distinguished exterior refinements below are
derived from actual ramification and occurrence data. They are not extra
fields for the caller to supply. The stable-source census and the matrix
balance are proved separately (`M11SplitStableGraph`, `M11CommonBalance`).
-/

namespace DraismaVargas.LocalCases.M11SourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-- The r0 background grows separate unit-index arms at the leaf, preserving
the old wall block at the trivalent endpoint. This allows arbitrary block size. -/
def backgroundResolution (partition : SheetPartition degree) (anchor : Fin degree) :
    LocalResolution degree := (splitResolutionAt partition anchor).reverse

theorem backgroundResolution_contracts (partition : SheetPartition degree) (anchor : Fin degree) :
    (backgroundResolution partition anchor).ContractsTo partition :=
  LocalResolution.reverse_contracts (splitResolutionAt_contracts partition anchor)

/-- The actual r0 block counts give equality at the new trivalent endpoint. -/
theorem backgroundResolution_right_riemannHurwitz
    (data : GluingDatum target degree) (star : TwoStar target wall) (anchor : Fin degree)
    (hZero : data.localRamification wall ((data.vertexPartition wall).toBlock anchor) = 0) :
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (backgroundResolution (data.vertexPartition wall) anchor).right
      [(backgroundResolution (data.vertexPartition wall) anchor).newEdge,
        data.edgePartition (star.edge 0), data.edgePartition (star.edge 1)] anchor := by
  intro sheet hSheet
  have hBlock : (data.vertexPartition wall).toBlock sheet =
      (data.vertexPartition wall).toBlock anchor := Subtype.ext hSheet.symm
  have hSheetZero : data.localRamification wall
      ((data.vertexPartition wall).toBlock sheet) = 0 := by rw [hBlock]; exact hZero
  have hFirst := blockCountWithin_eq_one_of_divalent_localRamification_zero data wall
    star.card_incidentEdges sheet hSheetZero (star.edge 0) (star.edge_mem_incidentEdges 0)
  have hSecond := blockCountWithin_eq_one_of_divalent_localRamification_zero data wall
    star.card_incidentEdges sheet hSheetZero (star.edge 1) (star.edge_mem_incidentEdges 1)
  have hNew := (data.vertexPartition wall).splitBlock_blockCountWithin_of_rel anchor sheet hSheet
  simp only [backgroundResolution, LocalResolution.reverse, splitResolutionAt,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil, hNew, hFirst, hSecond]
  omega

private theorem incidentEdges_eq_pair (star : TwoStar target wall) :
    GluingDatum.incidentEdges wall = {star.edge 0, star.edge 1} := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hEdge⟩
    have hTarget : star.edge label = edge := congrArg Subtype.val hLabel
    rw [← hTarget, Finset.mem_insert, Finset.mem_singleton]
    fin_cases label
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hEdge
    rcases Finset.mem_insert.mp hEdge with rfl | hEdge
    · exact star.edge_mem_incidentEdges 0
    · rw [Finset.mem_singleton.mp hEdge]; exact star.edge_mem_incidentEdges 1

private theorem all_right_occurrences (star : TwoStar target wall) :
    (↑([star.edge 0, star.edge 1] : List target.edges) : Multiset target.edges) =
      (wallEdgesAssigned target wall (fun _ ↦ true) true).val := by
  classical
  have hSet : wallEdgesAssigned target wall (fun _ ↦ true) true = GluingDatum.incidentEdges wall := by
    ext edge
    simp [mem_wallEdgesAssigned, GluingDatum.incidentEdges]
  have hNe : star.edge 0 ≠ star.edge 1 := fun h ↦
    (by decide : (0 : Fin 2) ≠ 1) (star.edge_injective h)
  rw [hSet, incidentEdges_eq_pair star, Finset.insert_val_of_notMem (by simpa using hNe)]
  rfl

/-- Assemble the split background from its local r0 facts. This local form
can be reused after branch relabelling, without transporting stable-path
counts or danglingness just to construct a candidate. -/
noncomputable def splitBackgroundOfUnramified (data : GluingDatum target degree)
    (star : TwoStar target wall) (distinguished : Fin degree)
    (hOthers : ∀ anchor, ¬ (data.vertexPartition wall).Rel distinguished anchor →
      data.localRamification wall ((data.vertexPartition wall).toBlock anchor) = 0) :
    Background data wall distinguished where
  right := fun _ ↦ true
  resolution := backgroundResolution (data.vertexPartition wall)
  contracts := fun anchor _ ↦ backgroundResolution_contracts _ anchor
  exterior := by
    intro edge hIncident _ _
    exact refines_of_mem_incidentEdges data (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hIncident)
  leftEdges := []
  rightEdges := [star.edge 0, star.edge 1]
  leftEdges_eq := by simp [wallEdgesAssigned]
  rightEdges_eq := all_right_occurrences star
  left_riemannHurwitz := fun anchor _ _ ↦ LocalResolution.riemannHurwitzAtBlock_leaf _ _ _ anchor
  right_riemannHurwitz := by
    intro anchor _ hOther
    exact backgroundResolution_right_riemannHurwitz data star anchor (hOthers anchor hOther)

/-- All background fields of the first split are consequences of the Case {w2}
input and concentration, including arbitrary-degree r0 blocks. -/
noncomputable def splitBackground (input : W2SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 2) :
    Background data wall block.1 :=
  splitBackgroundOfUnramified data star block.1 (by
    intro anchor hOther
    apply W2RankObstructions.other_localRamification_eq_zero input block hR
      (WallBlock.ofSheet data wall anchor)
    intro hEq
    apply hOther
    change (data.vertexPartition wall).repr block.1 = (data.vertexPartition wall).repr anchor
    exact block.2.trans (congrArg Subtype.val hEq).symm)

/-- On a two-sheet r2-nd3 block, positivity forces all four actual incident
indices to be one. This is exactly the M11 subcase of the M/P profile. -/
theorem index_eq_one_of_blockCard_eq_two
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    data.sourceEdgeIndex edge.1 = 1 := by
  have hFirstPos := sourceEdgeIndex_pos data profile.first.1
  have hSecondPos := sourceEdgeIndex_pos data profile.second.1
  have hIndices : data.sourceEdgeIndex profile.first.1 = 1 ∧
      data.sourceEdgeIndex profile.second.1 = 1 ∧ data.sourceEdgeIndex profile.third.1 = 1 := by
    rcases profile.cases with ⟨_, hPair, hSingle⟩ | ⟨_, hPair, _⟩ <;> omega
  rcases profile.exhaustive edge with rfl | rfl | rfl | rfl
  · exact hIndices.1
  · exact hIndices.2.1
  · exact hIndices.2.2
  · exact profile.deleted.index_one

/-- Every exterior partition is discrete on the distinguished M11 block.
Outside it refinement follows from the original gluing datum. -/
theorem exterior_refines_splitBlock
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (edge : target.edges) (hAt : edge ∈ GluingDatum.incidentEdges wall) :
    (data.edgePartition edge).Refines ((data.vertexPartition wall).splitBlock block.1) := by
  have hRefines := refines_of_mem_incidentEdges data hAt
  have hUnit (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
      (data.edgePartition edge).blockCard sheet = 1 := by
    have hRel := hRefines.rel ((data.edgePartition edge).rel_repr_right sheet)
    have hIncident : Incident data (data.sourceEdge edge sheet) (WallBlock.sourceVertex data wall block) := by
      apply (incident_wallBlock_sourceVertex_iff data block _).mpr
      refine ⟨hAt, Subtype.ext ?_⟩
      exact hRel.symm.trans (hSheet.symm.trans block.2)
    exact (GluingDatum.sourceEdgeIndex_sourceEdge data edge sheet).symm.trans
      (index_eq_one_of_blockCard_eq_two profile hCard ⟨data.sourceEdge edge sheet, hIncident⟩)
  intro first second hRel
  by_cases hFirst : (data.vertexPartition wall).Rel block.1 first
  · have hSingleton := (data.edgePartition edge).block_eq_singleton_of_blockCard_eq_one
      first (hUnit first hFirst)
    have hMember := ((data.edgePartition edge).mem_block_iff first second).mpr hRel
    rw [hSingleton, Finset.mem_singleton] at hMember
    rw [hMember]
    rfl
  · have hWall := hRefines.rel hRel
    have hSecond : ¬ (data.vertexPartition wall).Rel block.1 second :=
      fun h ↦ hFirst (h.trans hWall.symm)
    change ((data.vertexPartition wall).splitBlock block.1).repr first =
      ((data.vertexPartition wall).splitBlock block.1).repr second
    rw [SheetPartition.splitBlock_repr_of_not_rel _ _ _ hFirst,
      SheetPartition.splitBlock_repr_of_not_rel _ _ _ hSecond]
    exact hWall

/-- The first Figure 32 split, constructed from an actual M11 profile.
Every background and exterior-refinement field is derived, not assumed. -/
noncomputable def firstSplitPattern (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    SplitPattern data wall block.1 where
  background := splitBackground input block profile.ramification
  blockCard := hCard
  first := star.edge 0
  second := star.edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    exact exterior_refines_splitBlock profile hCard edge (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hAt)

/-- The source-derived candidate is an actual valid arbitrary-degree gluing
datum, not merely a local partition tuple. -/
theorem firstSplit_valid (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (firstSplitPattern input profile hCard).candidate.datum.Valid :=
  (firstSplitPattern input profile hCard).candidate.datum_valid input.valid

/-- Every actual new occurrence in the split candidate has index one,
including arms grown from background blocks of arbitrary size. -/
theorem firstSplit_newSourceEdge_index (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    (firstSplitPattern input profile hCard).candidate.datum.sourceEdgeIndex
      ((firstSplitPattern input profile hCard).candidate.newSourceEdge sheet) = 1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge, LocalResolution.paste_newEdge_blockCard]
  change (LocalResolution.onBlock (data.vertexPartition wall) block.1
    (splitResolutionAt (data.vertexPartition wall) block.1)
    (backgroundResolution (data.vertexPartition wall))
    ((data.vertexPartition wall).repr sheet)).newEdge.blockCard sheet = 1
  by_cases hSelected : (data.vertexPartition wall).Rel block.1 ((data.vertexPartition wall).repr sheet)
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact (data.vertexPartition wall).splitBlock_blockCard_of_rel block.1 sheet
      (hSelected.trans ((data.vertexPartition wall).rel_repr_left sheet))
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact (data.vertexPartition wall).splitBlock_blockCard_of_rel
      ((data.vertexPartition wall).repr sheet) sheet ((data.vertexPartition wall).rel_repr_left sheet)

/-- The joined candidate keeps the whole wall partition at both endpoints.
Its divalent endpoint inequalities follow from positivity of block counts. -/
noncomputable def joinedBackground (data : GluingDatum target degree)
    (star : TwoStar target wall) (distinguished : Fin degree) :
    Background data wall distinguished where
  right := star.right
  resolution := fun _ ↦ joinedResolutionAt (data.vertexPartition wall)
  contracts := fun _ _ ↦ joinedResolutionAt_contracts _
  exterior := by
    intro edge hAt _ _
    have hRefines := refines_of_mem_incidentEdges data (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hAt)
    simpa only [joinedResolutionAt, ite_self] using hRefines
  leftEdges := [star.edge 0]
  rightEdges := [star.edge 1]
  leftEdges_eq := by
    rw [star.wallEdgesAssigned_false, incidentEdges_eq_pair star, TwoStar.rightSet]
    have hNe : star.edge 0 ≠ star.edge 1 := fun h ↦
      (by decide : (0 : Fin 2) ≠ 1) (star.edge_injective h)
    simp [hNe]
  rightEdges_eq := by rw [star.wallEdgesAssigned_true, TwoStar.rightSet]; rfl
  left_riemannHurwitz := fun anchor _ _ ↦ joinedResolutionAt_endpoint_riemannHurwitzAtBlock_any
    (data.vertexPartition wall) (data.edgePartition (star.edge 0)) anchor
  right_riemannHurwitz := fun anchor _ _ ↦ joinedResolutionAt_endpoint_riemannHurwitzAtBlock_any
    (data.vertexPartition wall) (data.edgePartition (star.edge 1)) anchor

/-- Figure 32's joined candidate with no assumed background receipts. The
two-sheet hypothesis singles out M11, though validity itself is more general. -/
noncomputable def joinedPattern (data : GluingDatum target degree) (star : TwoStar target wall)
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    JoinedPattern data wall block.1 where
  background := joinedBackground data star block.1
  blockCard := hCard
  left := star.edge 0
  rightEdge := star.edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    have hRefines := refines_of_mem_incidentEdges data (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hAt)
    simpa only [joinedResolutionAt, ite_self] using hRefines

theorem joined_valid (input : W2SourceInput data star)
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (joinedPattern data star block hCard).candidate.datum.Valid :=
  (joinedPattern data star block hCard).candidate.datum_valid input.valid

/-- The joined new occurrences retain exactly their actual wall-block indices. -/
theorem joined_newSourceEdge_index (data : GluingDatum target degree) (star : TwoStar target wall)
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (sheet : Fin degree) :
    (joinedPattern data star block hCard).candidate.datum.sourceEdgeIndex
      ((joinedPattern data star block hCard).candidate.newSourceEdge sheet) =
        (data.vertexPartition wall).blockCard sheet := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge, LocalResolution.paste_newEdge_blockCard]
  change (LocalResolution.onBlock (data.vertexPartition wall) block.1
    (joinedResolutionAt (data.vertexPartition wall))
    (fun _ ↦ joinedResolutionAt (data.vertexPartition wall))
    ((data.vertexPartition wall).repr sheet)).newEdge.blockCard sheet = _
  simp only [LocalResolution.onBlock, ite_self, joinedResolutionAt]

/-- The actual target valencies of an assembled candidate, read from its
certified lists of incident old occurrences. -/
theorem candidate_target_valencies (candidate : BalancedGlobal.Candidate target degree data wall) :
    (GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (oldVertex target wall)).card = candidate.leftEdges.length + 1 ∧
      (GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (freshVertex target)).card = candidate.rightEdges.length + 1 := by
  have hLeft := congrArg Multiset.card (leftIncidentList_multiset target wall candidate.right)
  have hRight := congrArg Multiset.card (rightIncidentList_multiset target wall candidate.right)
  have hLeftList := congrArg Multiset.card candidate.leftEdges_eq
  have hRightList := congrArg Multiset.card candidate.rightEdges_eq
  simp [leftIncidentList, rightIncidentList, incidentList] at hLeft hRight
  simp only [Multiset.coe_card, Finset.card_val] at hLeftList hRightList
  omega

theorem firstSplit_target_valencies (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (GluingDatum.incidentEdges
      (target := graph target wall (firstSplitPattern input profile hCard).candidate.right)
      (oldVertex target wall)).card = 1 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (firstSplitPattern input profile hCard).candidate.right)
      (freshVertex target)).card = 3 :=
  candidate_target_valencies (firstSplitPattern input profile hCard).candidate

theorem joined_target_valencies (data : GluingDatum target degree) (star : TwoStar target wall)
    (block : WallBlock data wall) (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (GluingDatum.incidentEdges
      (target := graph target wall (joinedPattern data star block hCard).candidate.right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (joinedPattern data star block hCard).candidate.right)
      (freshVertex target)).card = 2 :=
  candidate_target_valencies (joinedPattern data star block hCard).candidate

end DraismaVargas.LocalCases.M11SourceCandidates
