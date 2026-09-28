import DraismaVargas.LocalCases.M11SourceCandidates

/-!
# The second M11 split, with the source's remote branch swap

Figure 32's second split swaps the two distinguished sheets on the branch
carrying the two surviving exterior occurrences. The wall itself is fixed.
Its incident edge partitions are also fixed as representative tables: both
selected sheets are singleton edge blocks. Thus the actual local ramification
and refinement data needed for the split construction survive the swap.
There is no need to assume a second W2 input or a second background census.
-/

namespace DraismaVargas.LocalCases.M11RemoteCandidates

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary M11SourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- Swapping two singleton blocks preserves the partition's representative
table, not merely its equivalence relation. -/
theorem relabel_swap_eq_of_singletons (partition : SheetPartition degree)
    (first second : Fin degree) (hFirst : partition.block first = {first})
    (hSecond : partition.block second = {second}) :
    partition.relabel (Equiv.swap first second) = partition := by
  have hFix (sheet : Fin degree) (hSingleton : partition.block sheet = {sheet}) :
      partition.repr sheet = sheet := by
    have hMem := (partition.mem_block_iff sheet (partition.repr sheet)).mpr (partition.rel_repr_right sheet)
    simpa only [hSingleton, Finset.mem_singleton] using hMem
  have hOnly (sheet : Fin degree) (hSingleton : partition.block sheet = {sheet})
      (other : Fin degree) (hRepr : partition.repr other = sheet) : other = sheet := by
    have hRel : partition.Rel sheet other := (hFix sheet hSingleton).trans hRepr.symm
    have hMem := (partition.mem_block_iff sheet other).mpr hRel
    simpa only [hSingleton, Finset.mem_singleton] using hMem
  apply SheetPartition.ext_repr
  funext sheet
  change (Equiv.swap first second) (partition.repr ((Equiv.swap first second).symm sheet)) =
    partition.repr sheet
  rw [Equiv.symm_swap]
  by_cases hIsFirst : sheet = first
  · rw [hIsFirst, Equiv.swap_apply_left, hFix second hSecond,
      Equiv.swap_apply_right, hFix first hFirst]
  · by_cases hIsSecond : sheet = second
    · rw [hIsSecond, Equiv.swap_apply_right, hFix first hFirst,
        Equiv.swap_apply_left, hFix second hSecond]
    · rw [Equiv.swap_apply_of_ne_of_ne hIsFirst hIsSecond,
        Equiv.swap_apply_of_ne_of_ne
          (fun h ↦ hIsFirst (hOnly first hFirst sheet h))
          (fun h ↦ hIsSecond (hOnly second hSecond sheet h))]

/-- The wall vertex lies outside the moved branch, so its representative
table is unchanged literally. -/
theorem swapped_vertexPartition (root : target.V) (hRoot : root ≠ wall)
    (first second : Fin degree) (hTogether : (data.vertexPartition wall).Rel first second) :
    (SwappedDatum data wall root hRoot first second hTogether).vertexPartition wall =
      data.vertexPartition wall := by
  change (data.vertexPartition wall).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.vertexMoved wall root hRoot wall) (Equiv.swap first second)) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  apply SheetPartition.ext_repr
  rfl

/-- Every actual edge partition incident to an M11 wall is fixed by the
branch swap. No discreteness of unrelated background blocks is assumed. -/
theorem swapped_edgePartition
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (root : target.V) (hRoot : root ≠ wall) (other : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel block.1 other)
    (edge : target.edges) (hAt : edge ∈ GluingDatum.incidentEdges wall) :
    (SwappedDatum data wall root hRoot block.1 other hTogether).edgePartition edge =
      data.edgePartition edge := by
  have hRefines := exterior_refines_splitBlock profile hCard edge hAt
  have hFirst := SheetPartition.block_eq_singleton_of_refines hRefines block.1
    ((data.vertexPartition wall).splitBlock_block_of_rel block.1 block.1 rfl)
  have hSecond := SheetPartition.block_eq_singleton_of_refines hRefines other
    ((data.vertexPartition wall).splitBlock_block_of_rel block.1 other hTogether)
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) (Equiv.swap block.1 other)) = _
  cases hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge
  · apply SheetPartition.ext_repr
    rfl
  · exact relabel_swap_eq_of_singletons (data.edgePartition edge) block.1 other hFirst hSecond

/-- Local ramification depends only on the wall partition and its incident
edge partitions, not on the remote representative tables. -/
theorem localRamification_toBlock_eq (otherData : GluingDatum target degree)
    (hVertex : otherData.vertexPartition wall = data.vertexPartition wall)
    (hEdges : ∀ edge ∈ GluingDatum.incidentEdges wall, otherData.edgePartition edge = data.edgePartition edge)
    (sheet : Fin degree) :
    otherData.localRamification wall ((otherData.vertexPartition wall).toBlock sheet) =
      data.localRamification wall ((data.vertexPartition wall).toBlock sheet) := by
  unfold GluingDatum.localRamification
  simp only [SheetPartition.toBlock_val, hVertex]
  congr 2
  exact Finset.sum_congr rfl (fun edge hAt ↦ by rw [hEdges edge hAt])

/-- The other endpoint of a named incident target occurrence. -/
def branchRoot (star : TwoStar target wall) (label : Fin 2) : target.V :=
  if (star.edge label : target.V × target.V).1 = wall
  then (star.edge label : target.V × target.V).2 else (star.edge label : target.V × target.V).1

theorem branchRoot_ne (star : TwoStar target wall) (label : Fin 2) : branchRoot star label ≠ wall := by
  unfold branchRoot
  split_ifs with hFirst
  · intro hSecond
    have hMem : (star.edge label : target.V × target.V) ∈ target.edges := Multiset.coe_mem
    have hPair : (star.edge label : target.V × target.V) = (wall, wall) := Prod.ext hFirst hSecond
    rw [hPair] at hMem
    exact target.loopless wall hMem
  · exact hFirst

/-- The root really selects the branch across the named target occurrence,
independently of its stored orientation. -/
theorem branchRoot_ends (star : TwoStar target wall) (label : Fin 2) :
    (star.edge label : target.V × target.V) = (wall, branchRoot star label) ∨
      (star.edge label : target.V × target.V) = (branchRoot star label, wall) := by
  have hAt := star.edge_mem_incidentEdges label
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hAt
  unfold branchRoot
  split_ifs with hFirst
  · exact Or.inl (Prod.ext hFirst rfl)
  · exact Or.inr (Prod.ext rfl (hAt.resolve_left hFirst))

noncomputable def otherSheet (block : WallBlock data wall)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) : Fin degree :=
  Classical.choose ((data.vertexPartition wall).exists_other_of_one_lt_blockCard block.1 (by omega))

theorem otherSheet_spec (block : WallBlock data wall)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (data.vertexPartition wall).Rel block.1 (otherSheet block hCard) ∧ block.1 ≠ otherSheet block hCard :=
  Classical.choose_spec ((data.vertexPartition wall).exists_other_of_one_lt_blockCard block.1 (by omega))

/-- Swap precisely the double-labelled branch of the actual M11 profile. -/
noncomputable def swappedDatum {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) : GluingDatum target degree :=
  SwappedDatum data wall (branchRoot star profile.doubleLabel)
    (branchRoot_ne star profile.doubleLabel) block.1 (otherSheet block hCard) (otherSheet_spec block hCard).1

theorem swappedDatum_vertexPartition {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (swappedDatum profile hCard).vertexPartition wall = data.vertexPartition wall :=
  swapped_vertexPartition _ _ _ _ _

theorem swappedDatum_edgePartition {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
    (edge : target.edges) (hAt : edge ∈ GluingDatum.incidentEdges wall) :
    (swappedDatum profile hCard).edgePartition edge = data.edgePartition edge :=
  swapped_edgePartition profile hCard _ _ _ _ edge hAt

/-- The second split's background conditions follow from the original
concentrated wall and exact preservation of its local partition data. -/
noncomputable def secondSplitPattern (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    SplitPattern (swappedDatum profile hCard) wall block.1 where
  background := splitBackgroundOfUnramified (swappedDatum profile hCard) star block.1 (by
    intro anchor hOther
    rw [localRamification_toBlock_eq _ (swappedDatum_vertexPartition profile hCard)
      (swappedDatum_edgePartition profile hCard)]
    apply W2RankObstructions.other_localRamification_eq_zero input block profile.ramification
      (WallBlock.ofSheet data wall anchor)
    intro hEq
    apply hOther
    rw [swappedDatum_vertexPartition profile hCard]
    change (data.vertexPartition wall).repr block.1 = (data.vertexPartition wall).repr anchor
    exact block.2.trans (congrArg Subtype.val hEq).symm)
  blockCard := by rw [swappedDatum_vertexPartition profile hCard]; exact hCard
  first := star.edge 0
  second := star.edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    have hIncident : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hAt
    change ((swappedDatum profile hCard).edgePartition edge).Refines
      (((swappedDatum profile hCard).vertexPartition wall).splitBlock block.1)
    rw [swappedDatum_vertexPartition profile hCard, swappedDatum_edgePartition profile hCard edge hIncident]
    exact exterior_refines_splitBlock profile hCard edge hIncident

theorem secondSplit_valid (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (secondSplitPattern input profile hCard).candidate.datum.Valid := by
  apply (secondSplitPattern input profile hCard).candidate.datum_valid
  exact wallBranchSwap_preserves_valid data input.valid wall _ _ _ _ _

/-- Remote pairing does not change the split's unit new-edge indices. -/
theorem secondSplit_newSourceEdge_index (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (sheet : Fin degree) :
    (secondSplitPattern input profile hCard).candidate.datum.sourceEdgeIndex
      ((secondSplitPattern input profile hCard).candidate.newSourceEdge sheet) = 1 := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge, LocalResolution.paste_newEdge_blockCard]
  let partition := (swappedDatum profile hCard).vertexPartition wall
  change (LocalResolution.onBlock partition block.1 (splitResolutionAt partition block.1)
    (backgroundResolution partition) (partition.repr sheet)).newEdge.blockCard sheet = 1
  by_cases hSelected : partition.Rel block.1 (partition.repr sheet)
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact partition.splitBlock_blockCard_of_rel block.1 sheet (hSelected.trans (partition.rel_repr_left sheet))
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact partition.splitBlock_blockCard_of_rel (partition.repr sheet) sheet (partition.rel_repr_left sheet)

theorem secondSplit_target_valencies (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    (GluingDatum.incidentEdges
      (target := TargetExpansion.graph target wall (secondSplitPattern input profile hCard).candidate.right)
      (TargetExpansion.oldVertex target wall)).card = 1 ∧
    (GluingDatum.incidentEdges
      (target := TargetExpansion.graph target wall (secondSplitPattern input profile hCard).candidate.right)
      (TargetExpansion.freshVertex target)).card = 3 :=
  candidate_target_valencies (secondSplitPattern input profile hCard).candidate

/-- All three actual M11 candidates, with the source-correct remote second
split. No local background, second wall input, or displayed matrix is assumed. -/
noncomputable def candidates (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    Fin 3 → BalancedGlobal.CertifiedCandidate data :=
  GlobalM11Arbitrary.candidates (branchRoot star profile.doubleLabel)
    (branchRoot_ne star profile.doubleLabel) (otherSheet_spec block hCard).2 (otherSheet_spec block hCard).1
    (firstSplitPattern input profile hCard) (secondSplitPattern input profile hCard)
    (joinedPattern data star block hCard)

theorem candidates_valid (input : W2SourceInput data star)
    {block : WallBlock data wall} (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (position : Fin 3) :
    (candidates input profile hCard position).datum.Valid :=
  (candidates input profile hCard position).valid_of_old input.valid

end DraismaVargas.LocalCases.M11RemoteCandidates
