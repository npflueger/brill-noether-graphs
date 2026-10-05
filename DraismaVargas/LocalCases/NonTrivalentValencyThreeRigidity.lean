module

public import DraismaVargas.LocalCases.NonTrivalentWallSetup
public import DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
public import DraismaVargas.LocalCases.ThirdEquation
public import DraismaVargas.LocalCases.W4IncomingPrunedFibre

@[expose] public section

/-!
# Ramification of the actual four-valent anchor at a valency-three wall

Vargas, Part II, Lemma `lemma-above-w0`, proves that the four-valent anchor carries the
unit of ramification above a three-valent wall.  We prove the same local
assertion without naming the vanishing stable row: an unramified actual
fibre has at most one surviving internal occurrence by no-return.  A single
incoming vertex has surviving valency at most three; an internal occurrence
has an unramified divalent-target endpoint of surviving valency at most two,
so its contraction also has surviving valency at most three.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeRigidity

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties WallDegeneration ClassInjectivity
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree FullContractionFibre
open FullDimensionalSource NonDanglingValency

variable {target : CFGraph} {degree : ℕ}
variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include fd

/-- Forest ramification additivity is pointwise nonnegative.  Thus a zero
merged residual makes every literal incoming constituent unramified. -/
theorem localRamification_eq_zero_in_fibre
    (hForest : ContractionForest data a b contracted)
    (block : (mergedPartition data a b).Blocks)
    (hZero : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 = 0)
    (point : data.SourceVertex)
    (hMap : sourceVertexMap data hc hab hOne point = mergedVertex data hc hab hOne block) :
    data.localRamification point.1.1 ⟨point.1.2, point.2⟩ = 0 := by
  classical
  have hAdd := localRamificationAt_contractDatum_merge data hc hab hOne hForest block
  rw [hZero] at hAdd
  have hLeftNonneg := Finset.sum_nonneg (fun fine (_ : fine ∈
      SheetPartition.blocksWithin (data.vertexPartition a) (mergedPartition data a b) block) ↦
    data.localRamification_nonneg a (fd.valid.2 a) fine)
  have hRightNonneg := Finset.sum_nonneg (fun fine (_ : fine ∈
      SheetPartition.blocksWithin (data.vertexPartition b) (mergedPartition data a b) block) ↦
    data.localRamification_nonneg b (fd.valid.2 b) fine)
  have hLeftZero : ∀ fine ∈ SheetPartition.blocksWithin (data.vertexPartition a)
      (mergedPartition data a b) block, data.localRamification a fine = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun fine _ ↦
      data.localRamification_nonneg a (fd.valid.2 a) fine)).mp (by omega)
  have hRightZero : ∀ fine ∈ SheetPartition.blocksWithin (data.vertexPartition b)
      (mergedPartition data a b) block, data.localRamification b fine = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun fine _ ↦
      data.localRamification_nonneg b (fd.valid.2 b) fine)).mp (by omega)
  have hInfo := (mem_fibreVertices_mergedVertex_iff data hc hab hOne block point).mp
    ((mem_fibreVertices data hc hab hOne _ point).mpr hMap)
  rcases point with ⟨⟨place, sheet⟩, hRepr⟩
  change (place = a ∨ place = b) ∧ (mergedPartition data a b).repr sheet = block.1 at hInfo
  rcases hInfo with ⟨rfl | rfl, hSheet⟩
  · exact hLeftZero ⟨sheet, hRepr⟩
      ((SheetPartition.mem_blocksWithin _ _ _ _).mpr (Subtype.ext hSheet))
  · exact hRightZero ⟨sheet, hRepr⟩
      ((SheetPartition.mem_blocksWithin _ _ _ _).mpr (Subtype.ext hSheet))

/-- The source-local no-return lemma only needs this vertex's ramification
to vanish; it does not need the whole target fibre to be unramified. -/
theorem sourceEdge_eq_of_same_target_of_localRamification_zero
    (point : data.SourceVertex)
    (hZero : data.localRamification point.1.1 ⟨point.1.2, point.2⟩ = 0)
    (first second : data.SourceEdge)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first point) (hSecondInc : Incident data second point)
    (hTarget : first.1.1 = second.1.1) : first = second := by
  rcases fd.nonDanglingValency_trichotomy point with hNd | hNd | hNd
  · exact False.elim ((nonDanglingValency_ne_zero_of_incident data hFirst hFirstInc) hNd)
  · exact DivalentSourceLocal.sourceEdge_eq_of_same_target data fd.danglingEdgeNoGlue
      point hNd (by omega) first second hFirst hSecond hFirstInc hSecondInc hTarget
  · exact W4IncomingCensus.sourceEdge_eq_of_same_target_of_nd3_r0 data fd.danglingEdgeNoGlue
      point hNd hZero first second hFirst hSecond hFirstInc hSecondInc hTarget

section ZeroFibre

variable (vertex : (contractDatum data hc hab hOne).SourceVertex)
  (hZero : ∀ point : data.SourceVertex,
    sourceVertexMap data hc hab hOne point = vertex →
      data.localRamification point.1.1 ⟨point.1.2, point.2⟩ = 0)

include hZero

/-- No-return propagates along the actual surviving walk inside a zero
ramification fibre, identifying the literal internal occurrences. -/
theorem sourceEdge_eq_of_surviving_walk
    (first : data.SourceEdge) (hFirstTarget : first.1.1 = contracted)
    (hFirst : ¬ IsDangling data first)
    (left right : data.SourceVertex) (hFirstInc : Incident data first left)
    (hLeftMap : sourceVertexMap data hc hab hOne left = vertex)
    (hWalk : Relation.ReflTransGen (SurvivingFibreStep data contracted) left right)
    (second : data.SourceEdge) (hSecondTarget : second.1.1 = contracted)
    (hSecond : ¬ IsDangling data second) (hSecondInc : Incident data second right) :
    first = second := by
  induction hWalk generalizing second with
  | refl =>
    exact sourceEdge_eq_of_same_target_of_localRamification_zero data fd left
      (hZero left hLeftMap) first second hFirst hSecond hFirstInc hSecondInc
      (hFirstTarget.trans hSecondTarget.symm)
  | @tail previous last hWalk hStep ih =>
    obtain ⟨edge, hTarget, hSurvives, hEnds⟩ := hStep
    have hPrevious : Incident data edge previous := incident_of_sourceEnds data hEnds
    have hLast : Incident data edge last := incident_of_sourceEnds data hEnds.symm
    have hLastMap : sourceVertexMap data hc hab hOne last = vertex :=
      ((sourceVertexMap_eq_iff_surviving_walk data hc hab hOne
        (nonDanglingValency_ne_zero_of_incident data hFirst hFirstInc)
        (nonDanglingValency_ne_zero_of_incident data hSurvives hLast)).mpr
        (hWalk.tail ⟨edge, hTarget, hSurvives, hEnds⟩)).symm.trans hLeftMap
    exact (ih edge hTarget hSurvives hPrevious).trans
      (sourceEdge_eq_of_same_target_of_localRamification_zero data fd last
        (hZero last hLastMap) edge second hSurvives hSecond hLast hSecondInc
        (hTarget.trans hSecondTarget.symm))

/-- The connected pruned fibre has at most one actual internal occurrence. -/
theorem internalEdges_subsingleton :
    ∀ first ∈ internalEdges data hc hab hOne vertex,
      ∀ second ∈ internalEdges data hc hab hOne vertex, first = second := by
  intro first hFirst second hSecond
  obtain ⟨hFirstSurvives, hFirstTarget, hFirstMap⟩ :=
    (mem_internalEdges data hc hab hOne vertex first).mp hFirst
  obtain ⟨hSecondSurvives, hSecondTarget, hSecondMap⟩ :=
    (mem_internalEdges data hc hab hOne vertex second).mp hSecond
  have hWalk := (sourceVertexMap_eq_iff_surviving_walk data hc hab hOne
    (nonDanglingValency_ne_zero_of_incident data hFirstSurvives (Or.inl rfl))
    (nonDanglingValency_ne_zero_of_incident data hSecondSurvives (Or.inl rfl))).mp
      (hFirstMap.trans hSecondMap.symm)
  exact sourceEdge_eq_of_surviving_walk data fd hc hab hOne vertex hZero
    first hFirstTarget hFirstSurvives (data.sourceEnds first).1 (data.sourceEnds second).1
    (Or.inl rfl) hFirstMap hWalk second hSecondTarget hSecondSurvives (Or.inl rfl)

/-- If an internal occurrence exists, its two literal ends exhaust the
active fibre.  This uses pruned connectedness, not a stable-row receipt. -/
theorem activeFibreVertices_eq_endpoints
    (edge : data.SourceEdge) (hEdge : edge ∈ internalEdges data hc hab hOne vertex) :
    activeFibreVertices data hc hab hOne vertex =
      {(data.sourceEnds edge).1, (data.sourceEnds edge).2} := by
  classical
  have hEnds := (sourceEnds_mem_activeFibre_iff data hc hab hOne vertex edge).mpr hEdge
  have hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty := ⟨_, hEnds.1⟩
  have hUpper := activeFibreVertices_card_le_internalEdges_card_add_one
    data hc hab hOne vertex hNonempty
  have hEdgeCard : (internalEdges data hc hab hOne vertex).card ≤ 1 :=
    Finset.card_le_one.mpr (internalEdges_subsingleton data fd hc hab hOne vertex hZero)
  have hPair : {(data.sourceEnds edge).1, (data.sourceEnds edge).2} ⊆
      activeFibreVertices data hc hab hOne vertex := by
    intro point hPoint
    rcases Finset.mem_insert.mp hPoint with rfl | hPoint
    · exact hEnds.1
    · exact (Finset.mem_singleton.mp hPoint) ▸ hEnds.2
  symm
  apply Finset.eq_of_subset_of_card_le hPair
  rw [Finset.card_pair (data.sourceEnds_ne edge)]
  omega

/-- An unramified fibre over an internal contraction with a divalent
endpoint cannot create a source vertex of surviving valency four. -/
theorem nonDanglingValency_le_three
    (hCompat : DanglingCompatible data hc hab hOne)
    (hDivalent : (GluingDatum.incidentEdges a).card = 2 ∨
      (GluingDatum.incidentEdges b).card = 2) :
    nonDanglingValency (contractDatum data hc hab hOne) vertex ≤ 3 := by
  classical
  by_cases hNdZero : nonDanglingValency (contractDatum data hc hab hOne) vertex = 0
  · omega
  have hNonempty := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero
    data hc hab hOne hCompat vertex hNdZero
  have hAccount := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat vertex
  by_cases hEmpty : internalEdges data hc hab hOne vertex = ∅
  · have hCard := activeFibreVertices_card_le_internalEdges_card_add_one
      data hc hab hOne vertex hNonempty
    rw [hEmpty, Finset.card_empty] at hCard hAccount
    have hSum : (∑ point ∈ activeFibreVertices data hc hab hOne vertex,
        nonDanglingValency data point) ≤
        (activeFibreVertices data hc hab hOne vertex).card * 3 := by
      calc
        _ ≤ ∑ _point ∈ activeFibreVertices data hc hab hOne vertex, 3 :=
          Finset.sum_le_sum (fun point _ ↦ fd.trivalent point)
        _ = _ := by simp
    omega
  · obtain ⟨edge, hEdge⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hSingleton : internalEdges data hc hab hOne vertex = {edge} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hEdge, fun other hOther ↦
        internalEdges_subsingleton data fd hc hab hOne vertex hZero other hOther edge hEdge⟩
    have hEnds := W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hOne vertex edge hEdge
    rw [activeFibreVertices_eq_endpoints data fd hc hab hOne vertex hZero edge hEdge,
      Finset.sum_pair (data.sourceEnds_ne edge), hSingleton, Finset.card_singleton] at hAccount
    have hLeft := fd.trivalent (data.sourceEnds edge).1
    have hRight := fd.trivalent (data.sourceEnds edge).2
    rcases hDivalent with hDivalent | hDivalent
    · have hBound := nonDanglingValency_le_of_localRamification_zero data
        (data.sourceEnds edge).1 (hZero _ hEnds.2.2.1)
      rw [hEnds.1, hDivalent] at hBound
      norm_num at hBound
      omega
    · have hBound := nonDanglingValency_le_of_localRamification_zero data
        (data.sourceEnds edge).2 (hZero _ hEnds.2.2.2.1)
      rw [hEnds.2.1, hDivalent] at hBound
      norm_num at hBound
      omega

end ZeroFibre

/-- **Actual valency-three anchor rigidity, Part II `lemma-above-w0`.**
The four-valent merged source vertex carries the wall's entire unit of
ramification.  No prior identification of the disappearing stable row's
branch endpoints is required. -/
theorem localRamification_eq_one
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThirdEquation.ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (block : (mergedPartition data a b).Blocks)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 4) :
    localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 = 1 := by
  classical
  have hNotZero : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 ≠ 0 := by
    intro hZero
    have hDivalent : (GluingDatum.incidentEdges a).card = 2 ∨
        (GluingDatum.incidentEdges b).card = 2 := by
      rcases ThirdEquation.valencySplit_of_threeStar data hc hab hOne fd.valid fd.changeMinimal star
        with hLeft | hRight
      · exact Or.inl hLeft.1
      · exact Or.inr hRight.2.1
    have hBound := nonDanglingValency_le_three data fd hc hab hOne
      (mergedVertex data hc hab hOne block)
      (localRamification_eq_zero_in_fibre data fd hc hab hOne hForest block hZero)
      hCompat hDivalent
    omega
  have hValid := valid_contractDatum data hc hab hOne hForest fd.valid
  let wallBlock : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Blocks :=
    ⟨block.1, by rw [contractDatum_vertexPartition_merge]; exact block.2⟩
  have hNonneg : 0 ≤ localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 :=
    (contractDatum data hc hab hOne).localRamification_nonneg ⟨a, hab⟩
      (hValid.2 ⟨a, hab⟩) wallBlock
  have hLe := Finset.single_le_sum
    (f := (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩)
    (fun other _ ↦ (contractDatum data hc hab hOne).localRamification_nonneg
      ⟨a, hab⟩ (hValid.2 ⟨a, hab⟩) other) (Finset.mem_univ wallBlock)
  change localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ block.1 ≤
    (contractDatum data hc hab hOne).targetChange ⟨a, hab⟩ at hLe
  rw [ThirdEquation.targetChange_contractDatum_merge_eq_one data hc hab hOne
    fd.valid fd.changeMinimal hForest star] at hLe
  omega

/-- The same rigidity statement in the exact wall-block interface consumed
by `NonTrivalentValencyThreeAnchor`. -/
theorem localRamification_wallBlock_eq_one
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThirdEquation.ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ block) = 4) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 1 := by
  let mergedBlock : (mergedPartition data a b).Blocks :=
    ⟨block.1, by rw [← contractDatum_vertexPartition_merge data hc hab hOne]; exact block.2⟩
  have hVertex : mergedVertex data hc hab hOne mergedBlock =
      WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ block := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact block.2.symm
  exact localRamification_eq_one data fd hc hab hOne hForest hCompat star mergedBlock
    (by rw [hVertex]; exact hNd)

/-- Every other actual wall block is rigid: the four-valent anchor consumes
the entire available ramification. -/
theorem localRamification_eq_zero_of_ne_anchor
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThirdEquation.ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (anchor : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) = 4)
    (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩) (hNe : block ≠ anchor) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 0 := by
  apply NonTrivalentWallSetup.localRamification_eq_zero_of_ne_anchor
    data hc hab hOne hForest fd.valid anchor ?_ block hNe
  rw [localRamification_wallBlock_eq_one data fd hc hab hOne hForest hCompat star anchor hNd,
    ThirdEquation.targetChange_contractDatum_merge_eq_one data hc hab hOne
      fd.valid fd.changeMinimal hForest star]

/-- The actual incoming contraction produces the full valency-three anchor
classification: all three target directions, the exact 2+1+1 distribution,
and survivor-index sum `2|A|+1`. -/
theorem threeBranchAnchor
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (star : ThirdEquation.ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    (anchor : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) = 4) :
    NonTrivalentValencyThreeAnchor.ThreeBranchAnchor
      (contractDatum data hc hab hOne) star anchor :=
  NonTrivalentValencyThreeAnchor.threeBranchAnchor (contractDatum data hc hab hOne) star
    (danglingEdgeNoGlue_contractDatum data hCompat.2 fd.danglingEdgeNoGlue) anchor
    (localRamification_wallBlock_eq_one data fd hc hab hOne hForest hCompat star anchor hNd) hNd

end DraismaVargas.LocalCases.NonTrivalentValencyThreeRigidity

