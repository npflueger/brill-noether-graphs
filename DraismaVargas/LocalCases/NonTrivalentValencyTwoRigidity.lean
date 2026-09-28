import DraismaVargas.LocalCases.NonTrivalentWallSetup
import DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
import DraismaVargas.LocalCases.W4IncomingPrunedFibre

/-!
# Ramification of the actual four-valent anchor at a valency-two wall

Source: Vargas, Part II, arXiv:2609.09109, `lemma-above-w0` as used in Section 5.4 (valency-2
limits, case `{v2-nd4}`).  At a divalent wall `w₀` the total change is
`ch w₀ = 4 - val w₀ = 2` (`NonTrivalentWallSetup`,
`SecondEquation.targetChange_contractDatum_merge_eq_two`), and the paper
asserts `r₀(A) = 2` at the distinguished block of surviving valency four.  We
prove that assertion for the actual incoming contraction, with no vanishing
stable row named and no ramification hypothesis assumed.

## The two endpoint splits

`SecondEquation.valencySplit_of_twoStar` says the contracted occurrence joins
target endpoints of valencies `(2,2)`, `(1,3)` or `(3,1)`.

*Split `(2,2)`.*  Every active incoming constituent `v` of the fibre sits above
a **divalent** target vertex, where `N(v) = r(v) + 2 + |A_v| (val - 2)` reads
`N(v) = r(v) + 2`; with `nd(v) ≤ N(v)` this is
`nd(v) - 2 ≤ r(v)` (`nonDanglingValency_sub_two_le_localRamification_of_divalent`).
Summing over the actual pruned fibre and feeding in the tree excess identity
`nd(A) = Σ (nd(v) - 2) + 2`
(`PrunedFibreTree.nonDanglingValency_mergedVertex_eq_sum`, which is where the
pruned-fibre tree count enters) gives `r₀(A) ≥ nd(A) - 2 = 2`.  The sum of the
constituent ramifications is bounded by `r₀(A)` because the fibre vertices are
exactly the fine blocks merged by `A` (`sum_localRamification_fibreVertices`),
and every local ramification is nonnegative.

*Splits `(1,3)` and `(3,1)`.*  Here one endpoint is a target leaf.  Above a
leaf, `r(v) = N(v) + |A_v| - 2` with `N(v) ≤ |A_v|`, and an active vertex has
`nd(v) ≠ 1` by the connected-source dichotomy, hence `nd(v) ≥ 2`; therefore
`r(v) ≥ 2 nd(v) - 2 ≥ 2` (`two_le_localRamification_of_target_leaf`).  This is
the same dichotomy `StableLocalProperties.leaf_block_dichotomy` records above a
leaf -- an ordinary single-sheet block of local ramification zero whose one
incident occurrence dangles, or a two-sheet block of local ramification two --
derived here directly from the index balance, so that `NoDanglingTargetFibres`
and the leaf's change-minimality are not needed.  If `r₀(A) ≤ 1` then no active
constituent can lie above the leaf; every internal surviving occurrence has one
end above each endpoint, so there is none; pruned connectedness and the tree
count make the active fibre a singleton, and then
`nd(A) = nd(v) ≤ 3`, against `nd(A) = 4`.

Combining, `r₀(A) ≥ 2`; and `r₀(A) ≤ ch w₀ = 2` because the other blocks'
ramifications are nonnegative.  So `r₀(A) = 2` and every other block above the
wall is rigid.

## What remains explicit

Every theorem below takes, as explicit hypotheses:

* `fd : FullDimensionalSourcePresentation data coordinate` (the incoming
  full-dimensional cover; used for `Valid`, `ChangeMinimal`, `trivalent` and
  `DanglingEdgeNoGlue`);
* `hForest : ContractionForest data a b contracted` (the actual contraction
  forest);
* `hCompat : DanglingCompatible data hc hab hOne` (occurrencewise danglingness
  across the contraction);
* `star : W2R1Target.TwoStar (contract target hab hOne) ⟨a, hab⟩`, the divalent
  target star already used by every divalent-wall module -- no new star type;
* `hNd`, the anchor's surviving valency four.

Nothing here constructs a `FullDimensionalSourcePresentation`, and nothing here
produces `hNd`: identifying the anchor is the task of the boundary dispatcher
(through `NonTrivalentAnchorValency`), exactly as in the valency-three pair.  No
ramification hypothesis and no named stable endpoint remains in the producers
below.

## Consumers

`NonTrivalentValencyTwoAnchor.TwoBranchAnchor` (re-exported here as
`twoBranchAnchor`), and downstream the prescribed-type valency-two exit at
non-trivalent walls.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoRigidity

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties WallDegeneration ClassInjectivity
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree FullContractionFibre
open FullDimensionalSource NonDanglingValency

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  Two constituent bounds, at a divalent target vertex and at a leaf -/

section Constituents

variable (data : GluingDatum target degree)

/-- **`nd(v) - 2 ≤ r(v)` above a divalent target vertex.**  The occurrence
count identity `N(v) = r(v) + 2 + |A_v| (val - 2)` loses its correction term at
`val = 2`, and the surviving valency never exceeds the occurrence count. -/
theorem nonDanglingValency_sub_two_le_localRamification_of_divalent
    (point : data.SourceVertex)
    (hDivalent : (GluingDatum.incidentEdges point.1.1).card = 2) :
    (nonDanglingValency data point : ℤ) - 2 ≤
      data.localRamification point.1.1 ⟨point.1.2, point.2⟩ := by
  have hCard := NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data point
  rw [hDivalent] at hCard
  have hLe : (nonDanglingValency data point : ℤ) ≤
      (Fintype.card (IncidentSourceEdge data point) : ℤ) := by
    exact_mod_cast NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data point
  norm_num at hCard
  linarith

/-- **An active constituent above a target leaf carries at least two units.**
Above a leaf `r(v) = N(v) + |A_v| - 2` and `N(v) ≤ |A_v|`; a source vertex of a
connected datum never has surviving valency one, so an active leaf constituent
has `nd(v) ≥ 2` and hence `r(v) ≥ 2 nd(v) - 2 ≥ 2`.  This is the quantitative
half of `StableLocalProperties.leaf_block_dichotomy`, obtained from the index
balance alone. -/
theorem two_le_localRamification_of_target_leaf
    (hConnected : data.Connected) (point : data.SourceVertex)
    (hLeaf : (GluingDatum.incidentEdges point.1.1).card = 1)
    (hActive : nonDanglingValency data point ≠ 0) :
    2 ≤ data.localRamification point.1.1 ⟨point.1.2, point.2⟩ := by
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one data hConnected point
  have hTwo : (2 : ℤ) ≤ (nonDanglingValency data point : ℤ) := by
    have : 2 ≤ nonDanglingValency data point := by omega
    exact_mod_cast this
  have hDegree : (nonDanglingValency data point : ℤ) ≤
      (Fintype.card (IncidentSourceEdge data point) : ℤ) := by
    exact_mod_cast NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data point
  have hBlock := StableLocalProperties.card_incidentSourceEdge_le_blockCard_of_target_leaf data point hLeaf
  rw [StableLocalProperties.localRamification_eq_leaf_form data point hLeaf]
  linarith

end Constituents

/-! ## 2.  The fibre carries exactly the merged block's ramification -/

section Fibre

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- Summing a constituent ramification over the literal source vertices above
one endpoint is summing it over the fine blocks merged there. -/
theorem sum_localRamification_sideVertices (side : target.V)
    (block : (mergedPartition data a b).Blocks) :
    (∑ point ∈ sideVertices data (a := a) (b := b) side block,
        data.localRamification point.1.1 ⟨point.1.2, point.2⟩) =
      ∑ fine ∈ SheetPartition.blocksWithin (data.vertexPartition side)
          (mergedPartition data a b) block, data.localRamification side fine := by
  have hInj : ∀ first ∈ SheetPartition.blocksWithin (data.vertexPartition side)
        (mergedPartition data a b) block,
      ∀ second ∈ SheetPartition.blocksWithin (data.vertexPartition side)
        (mergedPartition data a b) block,
      StableLocalProperties.blockVertex data side first = StableLocalProperties.blockVertex data side second → first = second := by
    intro first _ second _ hEq
    exact Subtype.ext (congrArg (fun vertex : data.SourceVertex ↦ vertex.1.2) hEq)
  rw [show sideVertices data (a := a) (b := b) side block =
      (SheetPartition.blocksWithin (data.vertexPartition side)
        (mergedPartition data a b) block).image
          (StableLocalProperties.blockVertex data side) from rfl,
    Finset.sum_image hInj]
  rfl

/-- **The fibre sum is the merged residual.**  The actual full fibre above a
merged block is the disjoint union of the fine blocks it merges over the two
endpoints, and forest additivity of local ramification is exactly that
splitting. -/
theorem sum_localRamification_fibreVertices
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks) :
    (∑ point ∈ fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block),
        data.localRamification point.1.1 ⟨point.1.2, point.2⟩) =
      localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 := by
  rw [fibreVertices_mergedVertex data hc hab hOne block,
    Finset.sum_union (sideVertices_disjoint data hab block),
    sum_localRamification_sideVertices data a block,
    sum_localRamification_sideVertices data b block,
    localRamificationAt_contractDatum_merge data hc hab hOne hForest block]

/-- No single constituent of the fibre carries more than the merged residual. -/
theorem localRamification_le_of_mem_fibreVertices
    (hValid : data.Valid) (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks) (point : data.SourceVertex)
    (hMem : point ∈ fibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)) :
    data.localRamification point.1.1 ⟨point.1.2, point.2⟩ ≤
      localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 := by
  rw [← sum_localRamification_fibreVertices data hc hab hOne hForest block]
  exact Finset.single_le_sum
    (f := fun first : data.SourceVertex ↦
      data.localRamification first.1.1 ⟨first.1.2, first.2⟩)
    (fun first _ ↦ data.localRamification_nonneg first.1.1 (hValid.2 first.1.1)
      ⟨first.1.2, first.2⟩) hMem

/-- The pruned constituents carry at most the merged residual in total. -/
theorem sum_localRamification_activeFibreVertices_le
    (hValid : data.Valid) (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks) :
    (∑ point ∈ activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block),
        data.localRamification point.1.1 ⟨point.1.2, point.2⟩) ≤
      localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 := by
  rw [← sum_localRamification_fibreVertices data hc hab hOne hForest block]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro point hPoint
    exact (mem_fibreVertices data hc hab hOne _ point).mpr
      ((mem_activeFibreVertices data hc hab hOne _ point).mp hPoint).1
  · intro point _ _
    exact data.localRamification_nonneg point.1.1 (hValid.2 point.1.1)
      ⟨point.1.2, point.2⟩

end Fibre

/-! ## 3.  The two endpoint splits -/

section Splits

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include fd

/-- **Split `(2,2)`.**  Both endpoints divalent: every active constituent has
`nd(v) - 2 ≤ r(v)`, and the tree excess identity turns that into
`r₀(A) ≥ nd(A) - 2 = 2`. -/
theorem two_le_localRamification_of_divalent_endpoints
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 4) :
    2 ≤ localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 := by
  classical
  have hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0 := by omega
  have hTree := nonDanglingValency_mergedVertex_eq_sum data hc hab hOne hCompat
    hForest block hNonzero
  rw [hNd] at hTree
  have hCast : ((4 : ℕ) : ℤ) = 4 := by norm_num
  rw [hCast] at hTree
  have hStep : (∑ point ∈ activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block),
        ((nonDanglingValency data point : ℤ) - 2)) ≤
      ∑ point ∈ activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block),
        data.localRamification point.1.1 ⟨point.1.2, point.2⟩ := by
    refine Finset.sum_le_sum ?_
    intro point hPoint
    have hMem : point ∈ fibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block) :=
      (mem_fibreVertices data hc hab hOne _ point).mpr
        ((mem_activeFibreVertices data hc hab hOne _ point).mp hPoint).1
    have hSide := (mem_fibreVertices_mergedVertex_iff data hc hab hOne block point).mp hMem
    have hCard : (GluingDatum.incidentEdges point.1.1).card = 2 := by
      rcases hSide.1 with hPlace | hPlace
      · rw [hPlace]; exact hLeft
      · rw [hPlace]; exact hRight
    exact nonDanglingValency_sub_two_le_localRamification_of_divalent data point hCard
  have hTotal := sum_localRamification_activeFibreVertices_le data hc hab hOne
    fd.valid hForest block
  linarith

/-- **Splits `(1,3)` and `(3,1)`.**  One endpoint is a target leaf.  A merged
residual of at most one would exclude every active leaf constituent, hence
every internal surviving occurrence, hence collapse the connected pruned fibre
to a single incoming vertex of surviving valency at most three -- against the
anchor's surviving valency four. -/
theorem two_le_localRamification_of_leaf_endpoint
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 4) :
    2 ≤ localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 := by
  classical
  by_contra hNotTwo
  have hSmall : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 < 2 := by
    omega
  have hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0 := by omega
  have hNoLeaf : ∀ point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block),
      (GluingDatum.incidentEdges point.1.1).card ≠ 1 := by
    intro point hPoint hCard
    have hInfo := (mem_activeFibreVertices data hc hab hOne _ point).mp hPoint
    have hMem : point ∈ fibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block) :=
      (mem_fibreVertices data hc hab hOne _ point).mpr hInfo.1
    have hTwoLe := two_le_localRamification_of_target_leaf data fd.valid.1 point hCard hInfo.2
    have hLe := localRamification_le_of_mem_fibreVertices data hc hab hOne fd.valid
      hForest block point hMem
    omega
  have hEmpty : internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block) = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨edge, hEdge⟩
    have hEnds := W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hOne
      (mergedVertex data hc hab hOne block) edge hEdge
    have hActive := (sourceEnds_mem_activeFibre_iff data hc hab hOne
      (mergedVertex data hc hab hOne block) edge).mpr hEdge
    rcases hLeaf with hSide | hSide
    · exact hNoLeaf _ hActive.1 (by rw [hEnds.1]; exact hSide)
    · exact hNoLeaf _ hActive.2 (by rw [hEnds.2.1]; exact hSide)
  have hNonempty := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero
    data hc hab hOne hCompat _ hNonzero
  have hCount := internalEdges_card_add_one_eq_activeFibreVertices_card
    data hc hab hOne hForest block hNonempty
  rw [hEmpty, Finset.card_empty] at hCount
  have hOneCard : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).card = 1 := by omega
  have hTree := nonDanglingValency_mergedVertex_eq_sum data hc hab hOne hCompat
    hForest block hNonzero
  rw [hNd] at hTree
  have hCast : ((4 : ℕ) : ℤ) = 4 := by norm_num
  rw [hCast] at hTree
  have hBound : (∑ point ∈ activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block),
        ((nonDanglingValency data point : ℤ) - 2)) ≤
      ∑ _point ∈ activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block), (1 : ℤ) := by
    refine Finset.sum_le_sum ?_
    intro point _
    have hThree : (nonDanglingValency data point : ℤ) ≤ 3 := by
      exact_mod_cast fd.trivalent point
    linarith
  have hConst : (∑ _point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block), (1 : ℤ)) = 1 := by
    rw [Finset.sum_const, hOneCard, one_smul]
  rw [hConst] at hBound
  linarith

end Splits

/-! ## 4.  The rigidity statement and the classifier -/

section Rigidity

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include fd

/-- **Actual valency-two anchor rigidity, Part II `lemma-above-w0` at
`val w₀ = 2`.**  The four-valent merged source vertex carries both units of the
wall's change.  No prior identification of the disappearing stable row's branch
endpoints is required. -/
theorem localRamification_eq_two
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : W2R1Target.TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (block : (mergedPartition data a b).Blocks)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 4) :
    localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 = 2 := by
  classical
  have hGe : 2 ≤ localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 := by
    rcases SecondEquation.valencySplit_of_twoStar data hc hab hOne fd.valid
      fd.changeMinimal star with hBoth | hLeftLeaf | hRightLeaf
    · exact two_le_localRamification_of_divalent_endpoints data fd hc hab hOne hCompat
        hForest block hBoth.1 hBoth.2.1 hNd
    · exact two_le_localRamification_of_leaf_endpoint data fd hc hab hOne hCompat
        hForest block (Or.inl hLeftLeaf.1) hNd
    · exact two_le_localRamification_of_leaf_endpoint data fd hc hab hOne hCompat
        hForest block (Or.inr hRightLeaf.2.1) hNd
  have hValid := valid_contractDatum data hc hab hOne hForest fd.valid
  let wallBlock : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks :=
    ⟨block.1, by rw [contractDatum_vertexPartition_merge]; exact block.2⟩
  have hLe := Finset.single_le_sum
    (f := (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩)
    (fun other _ ↦ (contractDatum data hc hab hOne).localRamification_nonneg
      ⟨a, hab⟩ (hValid.2 ⟨a, hab⟩) other) (Finset.mem_univ wallBlock)
  change localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 ≤
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ at hLe
  rw [SecondEquation.targetChange_contractDatum_merge_eq_two data hc hab hOne
    fd.valid fd.changeMinimal hForest star] at hLe
  omega

/-- The same rigidity statement in the exact wall-block interface consumed by
`NonTrivalentValencyTwoAnchor`. -/
theorem localRamification_wallBlock_eq_two
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : W2R1Target.TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ block) = 4) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 2 := by
  let mergedBlock : (mergedPartition data a b).Blocks :=
    ⟨block.1, by rw [← contractDatum_vertexPartition_merge data hc hab hOne]; exact block.2⟩
  have hVertex : mergedVertex data hc hab hOne mergedBlock =
      WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ block := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact block.2.symm
  exact localRamification_eq_two data fd hc hab hOne hForest hCompat star mergedBlock
    (by rw [hVertex]; exact hNd)

/-- Every other actual wall block above a divalent wall is rigid: the
four-valent anchor consumes both units of available ramification. -/
theorem localRamification_eq_zero_of_ne_anchor
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : W2R1Target.TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (anchor : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) = 4)
    (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩) (hNe : block ≠ anchor) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 0 := by
  apply NonTrivalentWallSetup.localRamification_eq_zero_of_ne_anchor
    data hc hab hOne hForest fd.valid anchor ?_ block hNe
  rw [localRamification_wallBlock_eq_two data fd hc hab hOne hForest hCompat star anchor hNd,
    SecondEquation.targetChange_contractDatum_merge_eq_two data hc hab hOne
      fd.valid fd.changeMinimal hForest star]

/-- The actual incoming contraction produces the full valency-two anchor
classification: both target directions, direction index sums `|A|`, total
survivor index `2|A|`, and the `2+2` or `3+1` distribution. -/
theorem twoBranchAnchor
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : W2R1Target.TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (anchor : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) = 4) :
    NonTrivalentValencyTwoAnchor.TwoBranchAnchor
      (contractDatum data hc hab hOne) star anchor :=
  NonTrivalentValencyTwoAnchor.twoBranchAnchor (contractDatum data hc hab hOne) star
    (danglingEdgeNoGlue_contractDatum data hCompat.2 fd.danglingEdgeNoGlue) anchor
    (localRamification_wallBlock_eq_two data fd hc hab hOne hForest hCompat star anchor hNd) hNd

end Rigidity

/-! ## 5.  Non-vacuity of the two split arithmetics -/

section NonVacuity

/-- The `(2,2)` split on literal inputs: two active constituents of surviving
valency three give `nd(A) = (3-2) + (3-2) + 2 = 4`, and the constituent bound
`nd(v) - 2 ≤ r(v)` then forces `r₀(A) ≥ 2`, which is exactly the wall's total
change.  So the hypothesis `nd(A) = 4` is compatible with the identity it is
combined with. -/
theorem divalent_split_arithmetic :
    ((3 : ℤ) - 2) + ((3 : ℤ) - 2) + 2 = 4 ∧ (4 : ℤ) - 2 = 2 := by
  norm_num

/-- The leaf-split contradiction on literal inputs: a singleton active fibre of
surviving valency at most three gives `nd(A) ≤ (3-2) + 2 = 3`, which is the
strict inequality against `nd(A) = 4` used above. -/
theorem leaf_split_arithmetic :
    ((3 : ℤ) - 2) + 2 = 3 ∧ (3 : ℤ) < 4 := by
  norm_num

/-- The leaf-constituent bound on literal inputs: an active leaf constituent
with `nd = 2` and `N = |A| = 2` has `r = N + |A| - 2 = 2`, so the excluded
configuration really does carry two units. -/
theorem leaf_constituent_arithmetic :
    (2 : ℤ) + 2 - 2 = 2 ∧ (2 : ℤ) ≤ 2 := by
  norm_num

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentValencyTwoRigidity
