import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent
import DraismaVargas.LocalCases.NonTrivalentValencyThreeRigidity
import DraismaVargas.LocalCases.NonTrivalentValencyTwoRigidity

/-!
# The anchor is four-valent at a valency-three and at a valency-two wall

Source: Vargas, Part II, arXiv:2609.09109, the combinatorial setup of the section on changing
combinatorial type (subsection `subsec-setup-determinants`): the rigidity lemma
above `w_0` (`lemma-above-w0`) and the observation that `H_0` has a unique
4-valent vertex `A`, all other vertices being trivalent.  It is used in the
valency-3 case (subsection `subsec-case-v3`) for `val w_0 = 3` and in the
valency-2 case (subsection `subsec-case-v2`) for `val w_0 = 2`.

## What is proved

`NonTrivalentUniqueFourValent` proves that uniqueness statement at a
**four-valent** wall.  Its
Section 8 identity `card_branchFibreVertices_add_two_eq_nonDanglingValency`
holds at a wall of any valency: `nd(B) = #{active incoming constituents of the
fibre of B with nd = 3} + 2`.  So `nd(A) = 4` says exactly that the anchor's
pruned fibre carries two incoming branch vertices.  This file produces that at
`val w_0 = 3` and at `val w_0 = 2`, discharging the hypothesis `hNd` that
`NonTrivalentValencyThreeRigidity.threeBranchAnchor` and
`NonTrivalentValencyTwoRigidity.twoBranchAnchor` carry.

*The vanishing class, and its two branch ends.*  With the wall metric of a Part
II open facet -- the contracted target occurrence at length zero
(`hZeroCoord`), every other target occurrence positive (`hPosCoord`), the row
`facet` vanishing (`hFacetZero`) -- every occurrence of the class `facet` lies
over the contracted target edge (`NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet`),
so the whole class lives in one pruned fibre.  At an end of such an occurrence
of surviving valency two the class continues into a *second* occurrence over
the contracted target edge at that same source vertex, which no-return
forbids.  Hence:

* `nonDanglingValency_eq_three_of_incident_row_facet` -- an end obeying
  no-return over the contracted edge is trivalent;
* `four_le_nonDanglingValency_of_two_branch` -- two distinct trivalent
  constituents of one fibre give `nd(B) ≥ 4`;
* `four_le_nonDanglingValency_of_row_facet` -- when no-return holds at *every*
  divalent constituent, the two literal ends of a vanishing-row occurrence
  already do it;
* `exists_two_branch_of_centre` and
  `four_le_nonDanglingValency_of_row_facet_of_centre` -- when exactly one
  constituent `c` above the wall may return, the class is the reduced
  fibre-tree path of length at most two through `c`, and its two far ends are
  two distinct trivalent constituents of that one fibre.

*The upper bound `nd ≤ 4`.*  Two disjoint arguments, matching the two shapes of
wall:

* `nonDanglingValency_le_four_of_star` -- if one side of the fibre admits at
  most one internal occurrence per vertex, the double count
  `card_filter_place_le_one` leaves exactly one vertex on the other side, so the
  fibre is a **star**; a divalent centre then carries at most two internal
  occurrences, and a trivalent centre at most one trivalent leaf, because such
  a leaf-edge is alone in its stable class and only `facet` may vanish
  (`hRows`).  `nonDanglingValency_le_four_of_changeZero_right` and
  `..._left` instantiate this at an endpoint of vanishing target change;
* `nonDanglingValency_le_localRamification_add_two` -- above two divalent target
  endpoints `N(v) = r(v) + 2`, so `nd(B) ≤ r_0(B) + 2`.

*The two walls.*  `nonDanglingValency_eq_four_of_row_facet_threeStar` and
`exists_wallBlock_nonDanglingValency_eq_four_of_threeStar` at `val w_0 = 3`;
`nonDanglingValency_eq_four_of_row_facet_twoStar` and
`exists_wallBlock_nonDanglingValency_eq_four_of_twoStar` at `val w_0 = 2`.  The
anchor is *identified*, as in `NonTrivalentUniqueFourValent`: it is the merged
block of the ends of the vanishing row, and
`exists_wallBlock_sourceVertex_eq_of_row_facet_threeStar` resp. `..._twoStar`
say so in the wall-block interface.  The splits are read off
`ThirdEquation.valencySplit_of_threeStar` and
`SecondEquation.valencySplit_of_twoStar`; the single returning constituent is
supplied by `atMostOne_ramified_of_changeZero`, because two ramified
constituents above one target vertex would together exceed its change
(`eq_of_place_eq_of_localRamification_sum_gt`).

*The non-anchor bound.*  `nonDanglingValency_wallBlock_le_three_of_threeStar`
and `nonDanglingValency_wallBlock_le_three_of_twoStar`, in exactly the
`NonTrivalentValencyFourBackground.OrdinaryBlockProfile.active_card` shape
(`¬ Rel anchor.1 block.1 → nd ≤ 3`).

*The classifiers.*  `threeBranchAnchor_of_single_row` and
`twoBranchAnchor_of_single_row` produce the anchor block together with its
`ThreeBranchAnchor` / `TwoBranchAnchor` classification and **no** surviving
valency hypothesis.

## What is not proved here

Nothing constructs a `FullDimensionalSourcePresentation`, a
`ContractionForest`, a star or the wall metric; every statement carries them.
The remaining hypotheses of the corollaries are exactly

* `fd : FullDimensionalSourcePresentation data coordinate`;
* `hForest : ContractionForest data a b contracted` (which supplies
  `DanglingCompatible` through `WallAdmissibility`);
* `star : ThirdEquation.ThreeStar ...` resp. `W2R1Target.TwoStar ...`;
* the wall metric `coordinates` with `hZeroCoord`, `hPosCoord`, `hFacetZero`
  and the single vanishing row `hRows`.

The **general** ramified fibre-tree path lemma -- in an arbitrary pruned fibre
tree, two incoming branch vertices are joined by a reduced path with divalent
interior -- is *not* proved here, and is not needed at these two wall
valencies.  What replaces it is the ramification budget: above a valency-three
wall, and above the leaf endpoint of a leaf-split valency-two wall, at most one
incoming constituent returns over the contracted target edge, so the vanishing
class is a path of length at most two and its two ends are read off directly.
In the `(2,2)` split of a valency-two wall no constituent of surviving valency
two returns at all, so the vanishing class is a single occurrence.  A wall at
which two independent constituents could return would need the general lemma.

## Consumers

`NonTrivalentValencyThreeRigidity.threeBranchAnchor` and
`NonTrivalentValencyTwoRigidity.twoBranchAnchor` (their `hNd`), and the
valency-three and valency-two ordinary-block census of the Part II wall
dispatcher.
-/

namespace DraismaVargas.LocalCases.NonTrivalentAnchorValency

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties WallDegeneration ClassInjectivity
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree FullContractionFibre
open FullDimensionalSource NonDanglingValency

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  The vanishing stable class, read at a divalent end -/

section Class

variable {data : GluingDatum target degree}

/-- **The other survivor at a divalent end lies on the same stable path.**
A surviving valency-two source vertex has exactly two incident survivors, and
they are consecutive. -/
theorem exists_other_stablePath_eq (edge : NonDanglingEdge data)
    (point : data.SourceVertex) (hIncident : Incident data edge.1 point)
    (hTwo : nonDanglingValency data point = 2) :
    ∃ other : NonDanglingEdge data, other.1 ≠ edge.1 ∧ Incident data other.1 point ∧
      other.stablePath = edge.stablePath := by
  classical
  obtain ⟨other, hOtherNe, hPair⟩ := nonDanglingIncident_eq_pair data hTwo edge.2 hIncident
  obtain ⟨hOtherSurvives, hOtherIncident⟩ :=
    (mem_nonDanglingIncident data point other).mp
      (hPair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self other))
  refine ⟨⟨other, hOtherSurvives⟩, hOtherNe, hOtherIncident, ?_⟩
  exact stablePath_eq_of_consecutive
    (⟨fun hEq ↦ hOtherNe (congrArg Subtype.val hEq), point, hOtherIncident, hIncident, hTwo⟩ :
      Consecutive data ⟨other, hOtherSurvives⟩ edge)

end Class

/-! ## 2.  No return at a divalent source vertex over the contracted edge -/

section NoReturn

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b))

include hc

/-- A source vertex meeting an occurrence over the contracted target edge lies
above one of its two endpoints. -/
theorem place_eq_of_incident_contracted
    (point : data.SourceVertex) (edge : data.SourceEdge)
    (hTarget : edge.1.1 = contracted) (hIncident : Incident data edge point) :
    point.1.1 = a ∨ point.1.1 = b := by
  have hAt := ((incident_iff_target_mem_and_rel data edge point).mp hIncident).1
  rw [hTarget] at hAt
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hAt
  rw [hc] at hAt
  exact hAt.imp Eq.symm Eq.symm

include fd

/-- **No return at a divalent source vertex above a non-leaf endpoint.**  Its
local ramification is at most one, so its two survivors take distinct target
directions; in particular at most one of them lies over the contracted target
occurrence. -/
theorem contracted_eq_of_divalent
    (hLeft : 2 ≤ (GluingDatum.incidentEdges a).card)
    (hRight : 2 ≤ (GluingDatum.incidentEdges b).card)
    (point : data.SourceVertex) (hTwo : nonDanglingValency data point = 2)
    (first second : data.SourceEdge)
    (hFirstTarget : first.1.1 = contracted) (hSecondTarget : second.1.1 = contracted)
    (hFirst : ¬ IsDangling data first) (hSecond : ¬ IsDangling data second)
    (hFirstInc : Incident data first point) (hSecondInc : Incident data second point) :
    first = second := by
  have hPlace := place_eq_of_incident_contracted data hc point first hFirstTarget hFirstInc
  have hNonleaf : 2 ≤ (GluingDatum.incidentEdges point.1.1).card := by
    rcases hPlace with hPlace | hPlace
    · rw [hPlace]; exact hLeft
    · rw [hPlace]; exact hRight
  exact DivalentSourceLocal.sourceEdge_eq_of_same_target data fd.danglingEdgeNoGlue point hTwo
    (DivalentSourceLocal.localRamification_le_one_of_nonleaf data fd.valid point
      (fd.changeMinimal point.1.1) hNonleaf)
    first second hFirst hSecond hFirstInc hSecondInc
    (hFirstTarget.trans hSecondTarget.symm)

end NoReturn

/-! ## 3.  The ends of a vanishing-row occurrence are branch vertices -/

section Branch

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b))
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

include fd hZeroCoord hPosCoord hFacetZero

/-- **Neither end of a vanishing-row occurrence is divalent.**  A divalent end
continues the vanishing stable class into a second surviving occurrence, which
again lies over the contracted target edge because the wall metric is
nonnegative; no-return at that source vertex forbids two of those. -/
theorem nonDanglingValency_eq_three_of_incident_row_facet
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet)
    (point : data.SourceVertex) (hIncident : Incident data edge.1 point)
    (hNoReturn : nonDanglingValency data point = 2 →
      ∀ first second : data.SourceEdge, first.1.1 = contracted → second.1.1 = contracted →
        ¬ IsDangling data first → ¬ IsDangling data second →
          Incident data first point → Incident data second point → first = second) :
    nonDanglingValency data point = 3 := by
  have hTargetEdge : edge.1.1.1 = contracted :=
    NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates
      facet hZeroCoord hPosCoord hFacetZero edge hRow
  have hActive : nonDanglingValency data point ≠ 0 :=
    nonDanglingValency_ne_zero_of_incident data edge.2 hIncident
  rcases fd.nonDanglingValency_trichotomy point with hValency | hValency | hValency
  · exact absurd hValency hActive
  · obtain ⟨other, hNe, hOtherInc, hPath⟩ :=
      exists_other_stablePath_eq edge point hIncident hValency
    have hOtherRow : fd.labelling.row other.stablePath = facet := by
      rw [hPath]; exact hRow
    have hOtherTarget : other.1.1.1 = contracted :=
      NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates
        facet hZeroCoord hPosCoord hFacetZero other hOtherRow
    exact absurd (hNoReturn hValency other.1 edge.1 hOtherTarget hTargetEdge
      other.2 edge.2 hOtherInc hIncident) hNe
  · exact hValency

end Branch

/-! ## 4.  Existence: the vanishing row's fibre carries two branch vertices -/

section Existence

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hEdgeOne)
  (hForest : ContractionForest data a b contracted)

include fd hCompat hForest

/-- **A nonempty pruned fibre has surviving wall valency at least two.**  Its
active constituents are at least divalent and its tree count leaves two
boundary occurrences over. -/
theorem two_le_nonDanglingValency_mergedVertex
    (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hEdgeOne
      (mergedVertex data hc hab hEdgeOne block)).Nonempty) :
    2 ≤ nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne block) := by
  classical
  have hCount := internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hEdgeOne
    hForest block hNonempty
  have hSum := sum_nonDanglingValency_activeFibre data hc hab hEdgeOne hCompat
    (mergedVertex data hc hab hEdgeOne block)
  have hLower : ∑ _point ∈ activeFibreVertices data hc hab hEdgeOne
      (mergedVertex data hc hab hEdgeOne block), 2 ≤
      ∑ point ∈ activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block), nonDanglingValency data point := by
    refine Finset.sum_le_sum ?_
    intro point hPoint
    have hActive := ((mem_activeFibreVertices data hc hab hEdgeOne _ point).mp hPoint).2
    have hNotOne := NonDanglingValency.nonDanglingValency_ne_one data fd.connected point
    omega
  rw [Finset.sum_const, smul_eq_mul] at hLower
  omega

/-- **Two incoming branch vertices in one fibre make the merged vertex
four-valent at least.**  This is `lemma-ndval-of-GqA0` of Draisma–Vargas Part I,
arXiv:1909.12924, read as
`nd(B) = #{branch} + 2`. -/
theorem four_le_nonDanglingValency_of_two_branch
    (point : data.SourceVertex) (hPlace : point.1.1 = a ∨ point.1.1 = b)
    (first second : data.SourceVertex) (hNe : first ≠ second)
    (hFirstThree : nonDanglingValency data first = 3)
    (hSecondThree : nonDanglingValency data second = 3)
    (hFirstMap : sourceVertexMap data hc hab hEdgeOne first =
      sourceVertexMap data hc hab hEdgeOne point)
    (hSecondMap : sourceVertexMap data hc hab hEdgeOne second =
      sourceVertexMap data hc hab hEdgeOne point) :
    ∃ block : (mergedPartition data a b).Blocks,
      sourceVertexMap data hc hab hEdgeOne point =
          mergedVertex data hc hab hEdgeOne block ∧
        4 ≤ nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (mergedVertex data hc hab hEdgeOne block) := by
  classical
  have hMerged : sourceVertexMap data hc hab hEdgeOne point =
      mergedVertex data hc hab hEdgeOne ((mergedPartition data a b).toBlock point.1.2) := by
    have hMem := (mem_fibreVertices_mergedVertex_iff data hc hab hEdgeOne
      ((mergedPartition data a b).toBlock point.1.2) point).mpr ⟨hPlace, rfl⟩
    rwa [mem_fibreVertices] at hMem
  refine ⟨(mergedPartition data a b).toBlock point.1.2, hMerged, ?_⟩
  have hFirstMem : first ∈ activeFibreVertices data hc hab hEdgeOne
      (mergedVertex data hc hab hEdgeOne ((mergedPartition data a b).toBlock point.1.2)) :=
    (mem_activeFibreVertices data hc hab hEdgeOne _ _).mpr
      ⟨hFirstMap.trans hMerged, by omega⟩
  have hSecondMem : second ∈ activeFibreVertices data hc hab hEdgeOne
      (mergedVertex data hc hab hEdgeOne ((mergedPartition data a b).toBlock point.1.2)) :=
    (mem_activeFibreVertices data hc hab hEdgeOne _ _).mpr
      ⟨hSecondMap.trans hMerged, by omega⟩
  have hNonzero : nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne ((mergedPartition data a b).toBlock point.1.2)) ≠ 0 := by
    have := two_le_nonDanglingValency_mergedVertex data fd hc hab hEdgeOne hCompat hForest
      ((mergedPartition data a b).toBlock point.1.2) ⟨first, hFirstMem⟩
    omega
  have hCount := NonTrivalentUniqueFourValent.card_branchFibreVertices_add_two_eq_nonDanglingValency
    data fd hc hab hEdgeOne hCompat hForest
    ((mergedPartition data a b).toBlock point.1.2) hNonzero
  have hPair : ({first, second} : Finset data.SourceVertex) ⊆
      (activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne
          ((mergedPartition data a b).toBlock point.1.2))).filter
        fun vertex ↦ nonDanglingValency data vertex = 3 := by
    intro vertex hVertex
    rcases Finset.mem_insert.mp hVertex with rfl | hVertex
    · exact Finset.mem_filter.mpr ⟨hFirstMem, hFirstThree⟩
    · rw [Finset.mem_singleton.mp hVertex]
      exact Finset.mem_filter.mpr ⟨hSecondMem, hSecondThree⟩
  have hCardPair : ({first, second} : Finset data.SourceVertex).card = 2 :=
    Finset.card_pair hNe
  have hLe := Finset.card_le_card hPair
  omega

end Existence

section ExistenceMain

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hEdgeOne)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  (hNoReturn : ∀ point : data.SourceVertex, nonDanglingValency data point = 2 →
    ∀ first second : data.SourceEdge, first.1.1 = contracted → second.1.1 = contracted →
      ¬ IsDangling data first → ¬ IsDangling data second →
        Incident data first point → Incident data second point → first = second)

include fd hCompat hForest hZeroCoord hPosCoord hFacetZero hNoReturn

/-- **The fibre of the vanishing stable row carries two incoming branch
vertices**, hence has surviving wall valency at least four.  This is the
existence half of Part II's unique four-valent vertex `A`, when no-return holds
at every divalent source vertex over the contracted occurrence: the two literal
ends of
a vanishing-row occurrence are then trivalent and distinct, so
`lemma-ndval-of-GqA0` reads `nd ≥ 2 + 2`. -/
theorem four_le_nonDanglingValency_of_row_facet
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    ∃ block : (mergedPartition data a b).Blocks,
      sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 =
          mergedVertex data hc hab hEdgeOne block ∧
        4 ≤ nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (mergedVertex data hc hab hEdgeOne block) := by
  have hTargetEdge : edge.1.1.1 = contracted :=
    NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates
      facet hZeroCoord hPosCoord hFacetZero edge hRow
  have hLeftThree : nonDanglingValency data (data.sourceEnds edge.1).1 = 3 :=
    nonDanglingValency_eq_three_of_incident_row_facet data fd coordinates facet hZeroCoord
      hPosCoord hFacetZero edge hRow _ (Or.inl rfl) fun hTwo ↦ hNoReturn _ hTwo
  have hRightThree : nonDanglingValency data (data.sourceEnds edge.1).2 = 3 :=
    nonDanglingValency_eq_three_of_incident_row_facet data fd coordinates facet hZeroCoord
      hPosCoord hFacetZero edge hRow _ (Or.inr rfl) fun hTwo ↦ hNoReturn _ hTwo
  exact four_le_nonDanglingValency_of_two_branch data fd hc hab hEdgeOne hCompat hForest
    (data.sourceEnds edge.1).1
    (place_eq_of_incident_contracted data hc _ edge.1 hTargetEdge (Or.inl rfl))
    (data.sourceEnds edge.1).1 (data.sourceEnds edge.1).2 (data.sourceEnds_ne edge.1)
    hLeftThree hRightThree rfl
    (sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hEdgeOne edge.1 hTargetEdge).symm

end ExistenceMain

/-! ## 5.  A pruned fibre with no-return on one side is a star -/

section Star

variable (data : GluingDatum target degree)

/-- The double count of incidences between a vertex set and an occurrence set
in which every occurrence has exactly one end in the vertex set. -/
theorem sum_card_filter_incident
    (vertices : Finset data.SourceVertex) (edges : Finset data.SourceEdge)
    (chosen : data.SourceEdge → data.SourceVertex)
    (hFilter : ∀ edge ∈ edges,
      (vertices.filter fun point ↦ Incident data edge point) = {chosen edge}) :
    ∑ point ∈ vertices, (edges.filter fun edge ↦ Incident data edge point).card
      = edges.card := by
  classical
  have hStep : ∀ point ∈ vertices,
      (edges.filter fun edge ↦ Incident data edge point).card
        = ∑ edge ∈ edges, if Incident data edge point then 1 else 0 := by
    intro point _
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl hStep, Finset.sum_comm]
  have hInner : ∀ edge ∈ edges,
      (∑ point ∈ vertices, if Incident data edge point then 1 else 0) = 1 := by
    intro edge hEdge
    rw [← Finset.card_filter, hFilter edge hEdge, Finset.card_singleton]
  rw [Finset.sum_congr rfl hInner, Finset.sum_const, smul_eq_mul, mul_one]

/-- **A pruned fibre with at most one internal occurrence at every vertex of
one side has at most one vertex on the other side.**  The occurrence count of
the side with no return is the whole edge count, and the tree identity leaves
exactly one vertex over. -/
theorem card_filter_place_le_one
    (vertices : Finset data.SourceVertex) (edges : Finset data.SourceEdge)
    (u v : target.V) (huv : u ≠ v)
    (endU endV : data.SourceEdge → data.SourceVertex)
    (hEndU : ∀ edge ∈ edges, endU edge ∈ vertices ∧ (endU edge).1.1 = u)
    (hEndV : ∀ edge ∈ edges, endV edge ∈ vertices ∧ (endV edge).1.1 = v)
    (hIncV : ∀ edge ∈ edges, Incident data edge (endV edge))
    (hOnly : ∀ edge ∈ edges, ∀ point, Incident data edge point →
      point = endU edge ∨ point = endV edge)
    (hPlace : ∀ point ∈ vertices, point.1.1 = u ∨ point.1.1 = v)
    (hCount : edges.card + 1 = vertices.card)
    (hDegV : ∀ point ∈ vertices, point.1.1 = v →
      (edges.filter fun edge ↦ Incident data edge point).card ≤ 1) :
    (vertices.filter fun point ↦ point.1.1 = u).card ≤ 1 := by
  classical
  have hFilter : ∀ edge ∈ edges,
      ((vertices.filter fun point ↦ point.1.1 = v).filter
        fun point ↦ Incident data edge point) = {endV edge} := by
    intro edge hEdge
    ext point
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hMem, hPlacePoint⟩, hInc⟩
      rcases hOnly edge hEdge point hInc with hCase | hCase
      · exact absurd (hPlacePoint.symm.trans (hCase ▸ (hEndU edge hEdge).2)) huv.symm
      · exact hCase
    · rintro rfl
      exact ⟨⟨(hEndV edge hEdge).1, (hEndV edge hEdge).2⟩, hIncV edge hEdge⟩
  have hSum := sum_card_filter_incident data (vertices.filter fun point ↦ point.1.1 = v)
    edges endV hFilter
  have hBound : ∑ point ∈ (vertices.filter fun point ↦ point.1.1 = v),
      (edges.filter fun edge ↦ Incident data edge point).card ≤
      ∑ _point ∈ (vertices.filter fun point ↦ point.1.1 = v), 1 := by
    refine Finset.sum_le_sum ?_
    intro point hPoint
    exact hDegV point (Finset.mem_filter.mp hPoint).1 (Finset.mem_filter.mp hPoint).2
  rw [Finset.sum_const, smul_eq_mul, mul_one] at hBound
  have hDisjoint : Disjoint (vertices.filter fun point ↦ point.1.1 = u)
      (vertices.filter fun point ↦ point.1.1 = v) := by
    rw [Finset.disjoint_left]
    intro point hLeft hRight
    exact huv ((Finset.mem_filter.mp hLeft).2.symm.trans (Finset.mem_filter.mp hRight).2)
  have hUnion : (vertices.filter fun point ↦ point.1.1 = u)
      ∪ (vertices.filter fun point ↦ point.1.1 = v) = vertices := by
    ext point
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (hCase | hCase) <;> exact hCase.1
    · intro hPoint
      exact (hPlace point hPoint).imp (fun hh ↦ ⟨hPoint, hh⟩) fun hh ↦ ⟨hPoint, hh⟩
  have hSplit : (vertices.filter fun point ↦ point.1.1 = u).card
      + (vertices.filter fun point ↦ point.1.1 = v).card = vertices.card :=
    (Finset.card_union_of_disjoint hDisjoint).symm.trans (congrArg Finset.card hUnion)
  omega

end Star

/-! ## 6.  The star bound `nd ≤ 4` -/

section StarBound

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)

/-- **Every active constituent of a pruned fibre with a second active
constituent meets an internal occurrence.**  The pruned walk between them
starts with one. -/
theorem exists_internalEdge_incident_of_ne
    (vertex : (contractDatum data hc hab hEdgeOne).SourceVertex)
    (point other : data.SourceVertex)
    (hPoint : point ∈ activeFibreVertices data hc hab hEdgeOne vertex)
    (hOther : other ∈ activeFibreVertices data hc hab hEdgeOne vertex)
    (hNe : point ≠ other) :
    ∃ edge ∈ internalEdges data hc hab hEdgeOne vertex, Incident data edge point := by
  obtain ⟨hPointMap, hPointActive⟩ :=
    (mem_activeFibreVertices data hc hab hEdgeOne vertex point).mp hPoint
  obtain ⟨hOtherMap, hOtherActive⟩ :=
    (mem_activeFibreVertices data hc hab hEdgeOne vertex other).mp hOther
  have hWalk := (sourceVertexMap_eq_iff_surviving_walk data hc hab hEdgeOne
    hPointActive hOtherActive).mp (hPointMap.trans hOtherMap.symm)
  rcases Relation.ReflTransGen.cases_head hWalk with hEq | ⟨middle, hStep, _⟩
  · exact absurd hEq hNe
  · obtain ⟨edge, hTarget, hSurvives, hEnds⟩ := hStep
    have hIncident : Incident data edge point := incident_of_sourceEnds data hEnds
    refine ⟨edge, (mem_internalEdges data hc hab hEdgeOne vertex edge).mpr
      ⟨hSurvives, hTarget, ?_⟩, hIncident⟩
    rcases hIncident with hCase | hCase
    · rw [hCase]; exact hPointMap
    · rw [sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hEdgeOne edge hTarget, hCase]
      exact hPointMap

variable (hCompat : DanglingCompatible data hc hab hEdgeOne)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)

include fd hCompat hForest hRows hZeroCoord

/-- **`nd(B) ≤ 4` above a wall whose pruned fibres are stars.**  If every
active constituent on one side of the fibre meets at most one internal
occurrence, the fibre is a star: its centre `c` carries every internal
occurrence.  A trivalent leaf of that star, together with a trivalent centre,
makes its edge alone in its stable class, hence the vanishing row; so at most
one leaf is trivalent, and the branch count is at most two. -/
theorem nonDanglingValency_le_four_of_star
    (block : (mergedPartition data a b).Blocks)
    (u v : target.V) (huv : u ≠ v)
    (endU endV : data.SourceEdge → data.SourceVertex)
    (hEndU : ∀ edge ∈ internalEdges data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block),
      endU edge ∈ activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block) ∧ (endU edge).1.1 = u)
    (hEndV : ∀ edge ∈ internalEdges data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block),
      endV edge ∈ activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block) ∧ (endV edge).1.1 = v)
    (hIncU : ∀ edge ∈ internalEdges data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block), Incident data edge (endU edge))
    (hIncV : ∀ edge ∈ internalEdges data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block), Incident data edge (endV edge))
    (hOnly : ∀ edge ∈ internalEdges data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block),
      ∀ point, Incident data edge point → point = endU edge ∨ point = endV edge)
    (hPlace : ∀ point ∈ activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block), point.1.1 = u ∨ point.1.1 = v)
    (hDegV : ∀ point ∈ activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block), point.1.1 = v →
      ((internalEdges data hc hab hEdgeOne (mergedVertex data hc hab hEdgeOne block)).filter
        fun edge ↦ Incident data edge point).card ≤ 1) :
    nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne block) ≤ 4 := by
  classical
  by_cases hNd : nonDanglingValency (contractDatum data hc hab hEdgeOne)
    (mergedVertex data hc hab hEdgeOne block) = 0
  · omega
  have hNonempty := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab
    hEdgeOne hCompat _ hNd
  have hCount := internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hEdgeOne
    hForest block hNonempty
  have hBranch := NonTrivalentUniqueFourValent.card_branchFibreVertices_add_two_eq_nonDanglingValency
    data fd hc hab hEdgeOne hCompat hForest block hNd
  by_cases hEmpty : (internalEdges data hc hab hEdgeOne
    (mergedVertex data hc hab hEdgeOne block)) = ∅
  · rw [hEmpty, Finset.card_empty] at hCount
    have hLe := Finset.card_le_card (Finset.filter_subset
      (fun point ↦ nonDanglingValency data point = 3)
      (activeFibreVertices data hc hab hEdgeOne (mergedVertex data hc hab hEdgeOne block)))
    omega
  obtain ⟨first, hFirst⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hCentre := card_filter_place_le_one data
    (activeFibreVertices data hc hab hEdgeOne (mergedVertex data hc hab hEdgeOne block))
    (internalEdges data hc hab hEdgeOne (mergedVertex data hc hab hEdgeOne block))
    u v huv endU endV hEndU hEndV hIncV hOnly hPlace hCount hDegV
  have hAll : ∀ edge ∈ internalEdges data hc hab hEdgeOne
      (mergedVertex data hc hab hEdgeOne block), endU edge = endU first := by
    intro edge hEdge
    refine Finset.card_le_one.mp hCentre _ ?_ _ ?_
    · exact Finset.mem_filter.mpr ⟨(hEndU edge hEdge).1, (hEndU edge hEdge).2⟩
    · exact Finset.mem_filter.mpr ⟨(hEndU first hFirst).1, (hEndU first hFirst).2⟩
  have hCentreMem : endU first ∈ activeFibreVertices data hc hab hEdgeOne
      (mergedVertex data hc hab hEdgeOne block) := (hEndU first hFirst).1
  have hFilterAll : ((internalEdges data hc hab hEdgeOne
      (mergedVertex data hc hab hEdgeOne block)).filter
      fun edge ↦ Incident data edge (endU first)) =
      internalEdges data hc hab hEdgeOne (mergedVertex data hc hab hEdgeOne block) := by
    apply Finset.filter_true_of_mem
    intro edge hEdge
    rw [← hAll edge hEdge]
    exact hIncU edge hEdge
  have hDegCentre : (internalEdges data hc hab hEdgeOne
      (mergedVertex data hc hab hEdgeOne block)).card ≤
      nonDanglingValency data (endU first) := by
    rw [← hFilterAll, ← card_nonDanglingIncident]
    refine Finset.card_le_card ?_
    intro edge hEdge
    obtain ⟨hEdgeMem, hEdgeInc⟩ := Finset.mem_filter.mp hEdge
    exact (mem_nonDanglingIncident data _ edge).mpr
      ⟨((mem_internalEdges data hc hab hEdgeOne _ edge).mp hEdgeMem).1, hEdgeInc⟩
  by_cases hCentreThree : nonDanglingValency data (endU first) = 3
  · have hSingle : (((activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block)).filter
        fun point ↦ nonDanglingValency data point = 3).erase (endU first)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro left hLeft right hRight
      obtain ⟨hLeftNe, hLeftMem⟩ := Finset.mem_erase.mp hLeft
      obtain ⟨hRightNe, hRightMem⟩ := Finset.mem_erase.mp hRight
      obtain ⟨hLeftActive, hLeftThree⟩ := Finset.mem_filter.mp hLeftMem
      obtain ⟨hRightActive, hRightThree⟩ := Finset.mem_filter.mp hRightMem
      obtain ⟨leftEdge, hLeftEdge, hLeftInc⟩ := exists_internalEdge_incident_of_ne data hc hab
        hEdgeOne _ left (endU first) hLeftActive hCentreMem hLeftNe
      obtain ⟨rightEdge, hRightEdge, hRightInc⟩ := exists_internalEdge_incident_of_ne data hc hab
        hEdgeOne _ right (endU first) hRightActive hCentreMem hRightNe
      have hEnds : ∀ edge ∈ internalEdges data hc hab hEdgeOne
          (mergedVertex data hc hab hEdgeOne block), ∀ point, Incident data edge point →
          point ≠ endU first → point = endV edge := by
        intro edge hEdge point hInc hPointNe
        rcases hOnly edge hEdge point hInc with hCase | hCase
        · exact absurd (hCase.trans (hAll edge hEdge)) hPointNe
        · exact hCase
      have hIsolated : ∀ edge ∈ internalEdges data hc hab hEdgeOne
          (mergedVertex data hc hab hEdgeOne block), ∀ point, Incident data edge point →
          point ≠ endU first → nonDanglingValency data point = 3 →
          ∀ hSurvives : ¬ IsDangling data edge,
            fd.labelling.row (NonDanglingEdge.stablePath ⟨edge, hSurvives⟩) = facet ∧
            ∀ other : NonDanglingEdge data,
              other.stablePath = NonDanglingEdge.stablePath ⟨edge, hSurvives⟩ →
                other.1 = edge := by
        intro edge hEdge point hInc hPointNe hPointThree hSurvives
        have hLeftEndNe : nonDanglingValency data (data.sourceEnds edge).1 ≠ 2 := by
          rcases hOnly edge hEdge (data.sourceEnds edge).1 (Or.inl rfl) with hCase | hCase
          · rw [hCase, hAll edge hEdge, hCentreThree]; omega
          · rw [hCase, ← hEnds edge hEdge point hInc hPointNe, hPointThree]; omega
        have hRightEndNe : nonDanglingValency data (data.sourceEnds edge).2 ≠ 2 := by
          rcases hOnly edge hEdge (data.sourceEnds edge).2 (Or.inr rfl) with hCase | hCase
          · rw [hCase, hAll edge hEdge, hCentreThree]; omega
          · rw [hCase, ← hEnds edge hEdge point hInc hPointNe, hPointThree]; omega
        have hIso := NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two
          (⟨edge, hSurvives⟩ : NonDanglingEdge data) hLeftEndNe hRightEndNe
        refine ⟨?_, fun other hOther ↦ congrArg Subtype.val (hIso other hOther)⟩
        refine NonTrivalentUniqueFourValent.row_eq_facet_of_isolated fd.labelling coordinates
          facet hRows ⟨edge, hSurvives⟩ hIso ?_
        have hTarget := ((mem_internalEdges data hc hab hEdgeOne _ edge).mp hEdge).2.1
        show coordinates (fd.labelling.targetEdge.symm edge.1.1) = 0
        rw [hTarget]
        exact hZeroCoord
      have hLeftSurvives := ((mem_internalEdges data hc hab hEdgeOne _ leftEdge).mp hLeftEdge).1
      have hRightSurvives := ((mem_internalEdges data hc hab hEdgeOne _ rightEdge).mp hRightEdge).1
      obtain ⟨hLeftRow, hLeftIso⟩ := hIsolated leftEdge hLeftEdge left hLeftInc hLeftNe
        hLeftThree hLeftSurvives
      obtain ⟨hRightRow, _⟩ := hIsolated rightEdge hRightEdge right hRightInc hRightNe
        hRightThree hRightSurvives
      have hEdgeEq : rightEdge = leftEdge :=
        hLeftIso ⟨rightEdge, hRightSurvives⟩
          (fd.labelling.row.injective (hRightRow.trans hLeftRow.symm))
      rw [hEnds leftEdge hLeftEdge left hLeftInc hLeftNe,
        hEnds rightEdge hRightEdge right hRightInc hRightNe, hEdgeEq]
    have hSubset : ((activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block)).filter
        fun point ↦ nonDanglingValency data point = 3) ⊆
        insert (endU first) (((activeFibreVertices data hc hab hEdgeOne
          (mergedVertex data hc hab hEdgeOne block)).filter
          fun point ↦ nonDanglingValency data point = 3).erase (endU first)) := by
      intro point hPoint
      by_cases hEq : point = endU first
      · exact Finset.mem_insert.mpr (Or.inl hEq)
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hEq, hPoint⟩)
    have hCardBound := Finset.card_le_card hSubset
    have hInsert := Finset.card_insert_le (endU first)
      ((((activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block)).filter
        fun point ↦ nonDanglingValency data point = 3).erase (endU first)))
    omega
  · have hCentreTwo : nonDanglingValency data (endU first) = 2 := by
      have hActive := ((mem_activeFibreVertices data hc hab hEdgeOne _ _).mp hCentreMem).2
      rcases fd.nonDanglingValency_trichotomy (endU first) with hCase | hCase | hCase
      · exact absurd hCase hActive
      · exact hCase
      · exact absurd hCase hCentreThree
    have hSubset : ((activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block)).filter
        fun point ↦ nonDanglingValency data point = 3) ⊆
        (activeFibreVertices data hc hab hEdgeOne
          (mergedVertex data hc hab hEdgeOne block)).erase (endU first) := by
      intro point hPoint
      obtain ⟨hPointMem, hPointThree⟩ := Finset.mem_filter.mp hPoint
      refine Finset.mem_erase.mpr ⟨?_, hPointMem⟩
      intro hEq
      rw [hEq, hCentreTwo] at hPointThree
      omega
    have hCardBound := Finset.card_le_card hSubset
    have hErase := Finset.card_erase_of_mem hCentreMem
    omega

end StarBound

/-! ## 7.  The star bound at a wall with a change-free endpoint -/

section ChangeZero

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)

include fd

/-- **No return at a change-free endpoint.**  Above a target vertex of zero
change every source vertex is unramified, so it meets at most one surviving
occurrence over the contracted target edge. -/
theorem internalDegree_le_one_of_changeZero
    (place : target.V) (hChange : data.targetChange place = 0)
    (vertex : (contractDatum data hc hab hEdgeOne).SourceVertex)
    (point : data.SourceVertex) (hPlace : point.1.1 = place) :
    ((internalEdges data hc hab hEdgeOne vertex).filter
      fun edge ↦ Incident data edge point).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro first hFirst second hSecond
  obtain ⟨hFirstMem, hFirstInc⟩ := Finset.mem_filter.mp hFirst
  obtain ⟨hSecondMem, hSecondInc⟩ := Finset.mem_filter.mp hSecond
  obtain ⟨hFirstSurvives, hFirstTarget, _⟩ :=
    (mem_internalEdges data hc hab hEdgeOne vertex first).mp hFirstMem
  obtain ⟨hSecondSurvives, hSecondTarget, _⟩ :=
    (mem_internalEdges data hc hab hEdgeOne vertex second).mp hSecondMem
  exact W4IncomingCensus.AnyWall.sourceEdge_eq_of_same_target_at_endpoint data fd point
    (by rw [hPlace]; exact hChange) first second hFirstSurvives hSecondSurvives
    hFirstInc hSecondInc (hFirstTarget.trans hSecondTarget.symm)

variable (hCompat : DanglingCompatible data hc hab hEdgeOne)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)

include hCompat hForest hRows hZeroCoord

/-- **`nd(B) ≤ 4` when the second endpoint of the contracted occurrence is
change-free.**  The fibre is then a star centred above the first endpoint. -/
theorem nonDanglingValency_le_four_of_changeZero_right
    (hChange : data.targetChange b = 0)
    (block : (mergedPartition data a b).Blocks) :
    nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne block) ≤ 4 := by
  classical
  refine nonDanglingValency_le_four_of_star data fd hc hab hEdgeOne hCompat hForest coordinates
    facet hRows hZeroCoord block a b hab (fun edge ↦ (data.sourceEnds edge).1)
    (fun edge ↦ (data.sourceEnds edge).2) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro edge hEdge
    exact ⟨((sourceEnds_mem_activeFibre_iff data hc hab hEdgeOne _ edge).mpr hEdge).1,
      (W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hEdgeOne _ edge hEdge).1⟩
  · intro edge hEdge
    exact ⟨((sourceEnds_mem_activeFibre_iff data hc hab hEdgeOne _ edge).mpr hEdge).2,
      (W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hEdgeOne _ edge hEdge).2.1⟩
  · intro edge _
    exact Or.inl rfl
  · intro edge _
    exact Or.inr rfl
  · intro edge _ point hInc
    exact hInc.imp Eq.symm Eq.symm
  · intro point hPoint
    have hMem : point ∈ fibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block) :=
      (mem_fibreVertices data hc hab hEdgeOne _ point).mpr
        ((mem_activeFibreVertices data hc hab hEdgeOne _ point).mp hPoint).1
    exact ((mem_fibreVertices_mergedVertex_iff data hc hab hEdgeOne block point).mp hMem).1
  · intro point _ hPointPlace
    exact internalDegree_le_one_of_changeZero data fd hc hab hEdgeOne b hChange _ point
      hPointPlace

/-- **`nd(B) ≤ 4` when the first endpoint of the contracted occurrence is
change-free.**  The mirror of the previous statement. -/
theorem nonDanglingValency_le_four_of_changeZero_left
    (hChange : data.targetChange a = 0)
    (block : (mergedPartition data a b).Blocks) :
    nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne block) ≤ 4 := by
  classical
  refine nonDanglingValency_le_four_of_star data fd hc hab hEdgeOne hCompat hForest coordinates
    facet hRows hZeroCoord block b a (Ne.symm hab) (fun edge ↦ (data.sourceEnds edge).2)
    (fun edge ↦ (data.sourceEnds edge).1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro edge hEdge
    exact ⟨((sourceEnds_mem_activeFibre_iff data hc hab hEdgeOne _ edge).mpr hEdge).2,
      (W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hEdgeOne _ edge hEdge).2.1⟩
  · intro edge hEdge
    exact ⟨((sourceEnds_mem_activeFibre_iff data hc hab hEdgeOne _ edge).mpr hEdge).1,
      (W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hEdgeOne _ edge hEdge).1⟩
  · intro edge _
    exact Or.inr rfl
  · intro edge _
    exact Or.inl rfl
  · intro edge _ point hInc
    exact (hInc.imp Eq.symm Eq.symm).symm
  · intro point hPoint
    have hMem : point ∈ fibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block) :=
      (mem_fibreVertices data hc hab hEdgeOne _ point).mpr
        ((mem_activeFibreVertices data hc hab hEdgeOne _ point).mp hPoint).1
    exact (((mem_fibreVertices_mergedVertex_iff data hc hab hEdgeOne block point).mp hMem).1).symm
  · intro point _ hPointPlace
    exact internalDegree_le_one_of_changeZero data fd hc hab hEdgeOne a hChange _ point
      hPointPlace

end ChangeZero

/-! ## 8.  Existence at a wall with a single ramified constituent -/

section CentreExistence

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)

/-- Two source vertices meeting one occurrence over the contracted target edge
have the same image at the wall. -/
theorem sourceVertexMap_eq_of_incident_contracted
    (edge : data.SourceEdge) (hTarget : edge.1.1 = contracted)
    (first second : data.SourceVertex)
    (hFirst : Incident data edge first) (hSecond : Incident data edge second) :
    sourceVertexMap data hc hab hEdgeOne first =
      sourceVertexMap data hc hab hEdgeOne second := by
  have hMap := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hEdgeOne edge hTarget
  rcases hFirst with hFirst | hFirst <;> rcases hSecond with hSecond | hSecond
  · rw [← hFirst, ← hSecond]
  · rw [← hFirst, ← hSecond]; exact hMap
  · rw [← hFirst, ← hSecond]; exact hMap.symm
  · rw [← hFirst, ← hSecond]

variable (hCompat : DanglingCompatible data hc hab hEdgeOne)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  (centre : data.SourceVertex)
  (hNoReturn : ∀ point : data.SourceVertex, point ≠ centre →
    ∀ first second : data.SourceEdge, first.1.1 = contracted → second.1.1 = contracted →
      ¬ IsDangling data first → ¬ IsDangling data second →
        Incident data first point → Incident data second point → first = second)

include fd hCompat hForest hZeroCoord hPosCoord hFacetZero hNoReturn

omit hCompat hForest in
/-- **The divalent-centre step.**  If one end of a vanishing-row occurrence is
divalent then it is the unique ramified constituent; the vanishing class
continues there into a second occurrence over the contracted target edge, and
the far ends of the two occurrences are two distinct trivalent constituents of
one fibre. -/
theorem exists_two_branch_of_centre
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet)
    (left right : data.SourceVertex)
    (hLeft : Incident data edge.1 left) (hRight : Incident data edge.1 right)
    (hNe : left ≠ right) (hCentre : left = centre)
    (hTwo : nonDanglingValency data left = 2) :
    ∃ first second : data.SourceVertex, first ≠ second ∧
      nonDanglingValency data first = 3 ∧ nonDanglingValency data second = 3 ∧
      sourceVertexMap data hc hab hEdgeOne first =
        sourceVertexMap data hc hab hEdgeOne left ∧
      sourceVertexMap data hc hab hEdgeOne second =
        sourceVertexMap data hc hab hEdgeOne left := by
  have hTargetEdge : edge.1.1.1 = contracted :=
    NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates
      facet hZeroCoord hPosCoord hFacetZero edge hRow
  have hRightNe : right ≠ centre := fun hBad ↦ hNe (hCentre.trans hBad.symm)
  have hRightThree : nonDanglingValency data right = 3 :=
    nonDanglingValency_eq_three_of_incident_row_facet data fd coordinates facet hZeroCoord
      hPosCoord hFacetZero edge hRow right hRight fun _ ↦ hNoReturn right hRightNe
  obtain ⟨other, hOtherNe, hOtherInc, hOtherPath⟩ :=
    exists_other_stablePath_eq edge left hLeft hTwo
  have hOtherRow : fd.labelling.row other.stablePath = facet := by
    rw [hOtherPath]; exact hRow
  have hOtherTarget : other.1.1.1 = contracted :=
    NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates
      facet hZeroCoord hPosCoord hFacetZero other hOtherRow
  have hFar : ∃ far : data.SourceVertex, far ≠ left ∧ Incident data other.1 far := by
    rcases hOtherInc with hCase | hCase
    · exact ⟨(data.sourceEnds other.1).2, fun hBad ↦ data.sourceEnds_ne other.1
        (hCase.trans hBad.symm), Or.inr rfl⟩
    · exact ⟨(data.sourceEnds other.1).1, fun hBad ↦ data.sourceEnds_ne other.1
        (hBad.trans hCase.symm), Or.inl rfl⟩
  obtain ⟨far, hFarNe, hFarInc⟩ := hFar
  have hFarCentre : far ≠ centre := fun hBad ↦ hFarNe (hBad.trans hCentre.symm)
  have hFarThree : nonDanglingValency data far = 3 :=
    nonDanglingValency_eq_three_of_incident_row_facet data fd coordinates facet hZeroCoord
      hPosCoord hFacetZero other hOtherRow far hFarInc fun _ ↦ hNoReturn far hFarCentre
  have hFarRight : far ≠ right := by
    intro hBad
    refine hOtherNe ?_
    exact hNoReturn right hRightNe other.1 edge.1 hOtherTarget hTargetEdge other.2 edge.2
      (hBad ▸ hFarInc) hRight
  refine ⟨right, far, Ne.symm hFarRight, hRightThree, hFarThree, ?_, ?_⟩
  · exact sourceVertexMap_eq_of_incident_contracted data hc hab hEdgeOne edge.1 hTargetEdge
      right left hRight hLeft
  · exact sourceVertexMap_eq_of_incident_contracted data hc hab hEdgeOne other.1 hOtherTarget
      far left hFarInc hOtherInc

/-- **The fibre of the vanishing stable row carries two incoming branch
vertices, at a wall with a single ramified incoming constituent.**  This is the
existence half of Part II's unique four-valent vertex `A` in the ramified case: the
vanishing class is a reduced fibre-tree path from a trivalent constituent
through the ramified centre to a second trivalent constituent. -/
theorem four_le_nonDanglingValency_of_row_facet_of_centre
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    ∃ block : (mergedPartition data a b).Blocks,
      sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 =
          mergedVertex data hc hab hEdgeOne block ∧
        4 ≤ nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (mergedVertex data hc hab hEdgeOne block) := by
  classical
  have hTargetEdge : edge.1.1.1 = contracted :=
    NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates
      facet hZeroCoord hPosCoord hFacetZero edge hRow
  have hPlace := place_eq_of_incident_contracted data hc (data.sourceEnds edge.1).1 edge.1
    hTargetEdge (Or.inl rfl)
  have hSwap : sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).2 =
      sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 :=
    (sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hEdgeOne edge.1 hTargetEdge).symm
  have hTrichotomy : ∀ point : data.SourceVertex, Incident data edge.1 point →
      nonDanglingValency data point = 2 ∨ nonDanglingValency data point = 3 := by
    intro point hInc
    have hActive := nonDanglingValency_ne_zero_of_incident data edge.2 hInc
    rcases fd.nonDanglingValency_trichotomy point with hCase | hCase | hCase
    · exact absurd hCase hActive
    · exact Or.inl hCase
    · exact Or.inr hCase
  have hMain : ∃ first second : data.SourceVertex, first ≠ second ∧
      nonDanglingValency data first = 3 ∧ nonDanglingValency data second = 3 ∧
      sourceVertexMap data hc hab hEdgeOne first =
        sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 ∧
      sourceVertexMap data hc hab hEdgeOne second =
        sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 := by
    by_cases hLeftCentre : (data.sourceEnds edge.1).1 = centre
    · rcases hTrichotomy _ (Or.inl rfl) with hCase | hCase
      · exact exists_two_branch_of_centre data fd hc hab hEdgeOne coordinates
          facet hZeroCoord hPosCoord hFacetZero centre hNoReturn edge hRow _ _ (Or.inl rfl)
          (Or.inr rfl) (data.sourceEnds_ne edge.1) hLeftCentre hCase
      · have hRightNe : (data.sourceEnds edge.1).2 ≠ centre := fun hBad ↦
          data.sourceEnds_ne edge.1 (hLeftCentre.trans hBad.symm)
        exact ⟨_, _, data.sourceEnds_ne edge.1, hCase,
          nonDanglingValency_eq_three_of_incident_row_facet data fd coordinates facet
            hZeroCoord hPosCoord hFacetZero edge hRow _ (Or.inr rfl)
            (fun _ ↦ hNoReturn _ hRightNe), rfl, hSwap⟩
    · have hLeftThree : nonDanglingValency data (data.sourceEnds edge.1).1 = 3 :=
        nonDanglingValency_eq_three_of_incident_row_facet data fd coordinates facet hZeroCoord
          hPosCoord hFacetZero edge hRow _ (Or.inl rfl) fun _ ↦ hNoReturn _ hLeftCentre
      by_cases hRightCentre : (data.sourceEnds edge.1).2 = centre
      · rcases hTrichotomy _ (Or.inr rfl) with hCase | hCase
        · obtain ⟨first, second, hNe, hFirst, hSecond, hFirstMap, hSecondMap⟩ :=
            exists_two_branch_of_centre data fd hc hab hEdgeOne coordinates
              facet hZeroCoord hPosCoord hFacetZero centre hNoReturn edge hRow _ _ (Or.inr rfl)
              (Or.inl rfl) (Ne.symm (data.sourceEnds_ne edge.1)) hRightCentre hCase
          exact ⟨first, second, hNe, hFirst, hSecond, hFirstMap.trans hSwap,
            hSecondMap.trans hSwap⟩
        · exact ⟨_, _, data.sourceEnds_ne edge.1, hLeftThree, hCase, rfl, hSwap⟩
      · exact ⟨_, _, data.sourceEnds_ne edge.1, hLeftThree,
          nonDanglingValency_eq_three_of_incident_row_facet data fd coordinates facet hZeroCoord
            hPosCoord hFacetZero edge hRow _ (Or.inr rfl) (fun _ ↦ hNoReturn _ hRightCentre),
          rfl, hSwap⟩
  obtain ⟨first, second, hNe, hFirst, hSecond, hFirstMap, hSecondMap⟩ := hMain
  exact four_le_nonDanglingValency_of_two_branch data fd hc hab hEdgeOne hCompat hForest
    (data.sourceEnds edge.1).1 hPlace first second hNe hFirst hSecond hFirstMap hSecondMap

end CentreExistence

/-! ## 9.  At most one ramified constituent above the wall -/

section Ramified

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)

/-- **Two constituents above one target vertex share its change.**  If their
ramifications together exceed the vertex's change they are the same
constituent. -/
theorem eq_of_place_eq_of_localRamification_sum_gt
    (hValid : data.Valid) (place : target.V)
    (first second : data.SourceVertex)
    (hFirstPlace : first.1.1 = place) (hSecondPlace : second.1.1 = place)
    (hSum : data.targetChange place <
      data.localRamification first.1.1 ⟨first.1.2, first.2⟩ +
        data.localRamification second.1.1 ⟨second.1.2, second.2⟩) :
    first = second := by
  classical
  by_contra hNe
  have hFirstRepr : (data.vertexPartition place).repr first.1.2 = first.1.2 := by
    rw [← hFirstPlace]; exact first.2
  have hSecondRepr : (data.vertexPartition place).repr second.1.2 = second.1.2 := by
    rw [← hSecondPlace]; exact second.2
  have hBlockNe : (⟨first.1.2, hFirstRepr⟩ : (data.vertexPartition place).Blocks) ≠
      ⟨second.1.2, hSecondRepr⟩ := by
    intro hEq
    exact hNe (Subtype.ext (Prod.ext (hFirstPlace.trans hSecondPlace.symm)
      (congrArg Subtype.val hEq)))
  have hNonneg : ∀ block : (data.vertexPartition place).Blocks,
      0 ≤ data.localRamification place block :=
    fun block ↦ data.localRamification_nonneg place (hValid.2 place) block
  have hUniv : ∑ block : (data.vertexPartition place).Blocks,
      data.localRamification place block = data.targetChange place := rfl
  have hLe : data.localRamification place ⟨first.1.2, hFirstRepr⟩
      + data.localRamification place ⟨second.1.2, hSecondRepr⟩
        ≤ data.targetChange place := by
    rw [← Finset.sum_pair (f := fun block ↦ data.localRamification place block) hBlockNe,
      ← hUniv]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun block _ _ ↦ hNonneg block)
  have hFirstEq : data.localRamification place ⟨first.1.2, hFirstRepr⟩
      = data.localRamification first.1.1 ⟨first.1.2, first.2⟩ := by
    show localRamificationAt data place first.1.2
      = localRamificationAt data first.1.1 first.1.2
    rw [hFirstPlace]
  have hSecondEq : data.localRamification place ⟨second.1.2, hSecondRepr⟩
      = data.localRamification second.1.1 ⟨second.1.2, second.2⟩ := by
    show localRamificationAt data place second.1.2
      = localRamificationAt data second.1.1 second.1.2
    rw [hSecondPlace]
  rw [hFirstEq, hSecondEq] at hLe
  omega

variable (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b))

include fd hc

/-- **The single-centre no-return datum.**  If at most one incoming constituent
above the two endpoints of the contracted occurrence is ramified, no-return over
the contracted target edge holds at every other source vertex. -/
theorem exists_centre_noReturn (fallback : data.SourceVertex)
    (hAtMostOne : ∀ first second : data.SourceVertex,
      nonDanglingValency data first ≠ 0 → nonDanglingValency data second ≠ 0 →
      (first.1.1 = a ∨ first.1.1 = b) → (second.1.1 = a ∨ second.1.1 = b) →
        data.localRamification first.1.1 ⟨first.1.2, first.2⟩ ≠ 0 →
          data.localRamification second.1.1 ⟨second.1.2, second.2⟩ ≠ 0 → first = second) :
    ∃ centre : data.SourceVertex, ∀ point : data.SourceVertex, point ≠ centre →
      ∀ first second : data.SourceEdge, first.1.1 = contracted → second.1.1 = contracted →
        ¬ IsDangling data first → ¬ IsDangling data second →
          Incident data first point → Incident data second point → first = second := by
  classical
  have hStep : ∀ centre : data.SourceVertex,
      (∀ point : data.SourceVertex, nonDanglingValency data point ≠ 0 →
        (point.1.1 = a ∨ point.1.1 = b) → point ≠ centre →
          data.localRamification point.1.1 ⟨point.1.2, point.2⟩ = 0) →
      ∀ point : data.SourceVertex, point ≠ centre →
        ∀ first second : data.SourceEdge, first.1.1 = contracted → second.1.1 = contracted →
          ¬ IsDangling data first → ¬ IsDangling data second →
            Incident data first point → Incident data second point → first = second := by
    intro centre hZero point hNe first second hFirstTarget hSecondTarget hFirst hSecond
      hFirstInc hSecondInc
    have hPlace := place_eq_of_incident_contracted data hc point first hFirstTarget hFirstInc
    have hActive := nonDanglingValency_ne_zero_of_incident data hFirst hFirstInc
    exact NonTrivalentValencyThreeRigidity.sourceEdge_eq_of_same_target_of_localRamification_zero
      data fd point (hZero point hActive hPlace hNe) first second hFirst hSecond hFirstInc
      hSecondInc (hFirstTarget.trans hSecondTarget.symm)
  by_cases hExists : ∃ point : data.SourceVertex, nonDanglingValency data point ≠ 0 ∧
      (point.1.1 = a ∨ point.1.1 = b) ∧
      data.localRamification point.1.1 ⟨point.1.2, point.2⟩ ≠ 0
  · obtain ⟨centre, hCentreActive, hCentrePlace, hCentreRamified⟩ := hExists
    refine ⟨centre, hStep centre ?_⟩
    intro point hActive hPlace hNe
    by_contra hBad
    exact hNe (hAtMostOne point centre hActive hCentreActive hPlace hCentrePlace hBad
      hCentreRamified)
  · refine ⟨fallback, hStep fallback ?_⟩
    intro point hActive hPlace _
    by_contra hBad
    exact hExists ⟨point, hActive, hPlace, hBad⟩

omit hc in
/-- **At most one ramified constituent above the two endpoints.**  One endpoint
is change-free, so its constituents are unramified; above the other, any two
ramified constituents would together exceed its change. -/
theorem atMostOne_ramified_of_changeZero (left right : target.V) (bound : ℤ)
    (hChange : data.targetChange right = 0)
    (hLower : ∀ point : data.SourceVertex, nonDanglingValency data point ≠ 0 →
      point.1.1 = left → data.localRamification point.1.1 ⟨point.1.2, point.2⟩ ≠ 0 →
        bound ≤ data.localRamification point.1.1 ⟨point.1.2, point.2⟩)
    (hBound : data.targetChange left < 2 * bound) :
    ∀ first second : data.SourceVertex,
      nonDanglingValency data first ≠ 0 → nonDanglingValency data second ≠ 0 →
      (first.1.1 = left ∨ first.1.1 = right) → (second.1.1 = left ∨ second.1.1 = right) →
        data.localRamification first.1.1 ⟨first.1.2, first.2⟩ ≠ 0 →
          data.localRamification second.1.1 ⟨second.1.2, second.2⟩ ≠ 0 → first = second := by
  intro first second hFirstActive hSecondActive hFirstPlace hSecondPlace hFirstRamified
    hSecondRamified
  have hFirstLeft : first.1.1 = left :=
    hFirstPlace.resolve_right fun hPlace ↦ hFirstRamified
      (W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd first
        (by rw [hPlace]; exact hChange))
  have hSecondLeft : second.1.1 = left :=
    hSecondPlace.resolve_right fun hPlace ↦ hSecondRamified
      (W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd second
        (by rw [hPlace]; exact hChange))
  have hFirstLower := hLower first hFirstActive hFirstLeft hFirstRamified
  have hSecondLower := hLower second hSecondActive hSecondLeft hSecondRamified
  exact eq_of_place_eq_of_localRamification_sum_gt data fd.valid left first second hFirstLeft
    hSecondLeft (by omega)

end Ramified

/-! ## 10.  The ramification bound at two divalent target endpoints -/

section DivalentEndpoints

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hEdgeOne)
  (hForest : ContractionForest data a b contracted)

include fd hCompat hForest

/-- **`nd(B) ≤ r₀(B) + 2` when both endpoints of the contracted occurrence are
divalent target vertices.**  There `N(v) = r(v) + 2`, so every incoming excess
`nd(v) - 2` is paid for by that constituent's ramification, and the pruned tree
identity turns the sum into the merged excess. -/
theorem nonDanglingValency_le_localRamification_add_two
    (block : (mergedPartition data a b).Blocks)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne block) ≠ 0) :
    (nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne block) : ℤ) ≤
      localRamificationAt (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ block.1 + 2 := by
  classical
  have hTree := nonDanglingValency_mergedVertex_eq_sum data hc hab hEdgeOne hCompat hForest
    block hNonzero
  have hStep : (∑ point ∈ activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block),
        ((nonDanglingValency data point : ℤ) - 2)) ≤
      ∑ point ∈ activeFibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block),
        data.localRamification point.1.1 ⟨point.1.2, point.2⟩ := by
    refine Finset.sum_le_sum ?_
    intro point hPoint
    have hMem : point ∈ fibreVertices data hc hab hEdgeOne
        (mergedVertex data hc hab hEdgeOne block) :=
      (mem_fibreVertices data hc hab hEdgeOne _ point).mpr
        ((mem_activeFibreVertices data hc hab hEdgeOne _ point).mp hPoint).1
    have hSide := (mem_fibreVertices_mergedVertex_iff data hc hab hEdgeOne block point).mp hMem
    have hCard : (GluingDatum.incidentEdges point.1.1).card = 2 := by
      rcases hSide.1 with hPlace | hPlace
      · rw [hPlace]; exact hLeft
      · rw [hPlace]; exact hRight
    exact NonTrivalentValencyTwoRigidity.nonDanglingValency_sub_two_le_localRamification_of_divalent
      data point hCard
  have hTotal := NonTrivalentValencyTwoRigidity.sum_localRamification_activeFibreVertices_le
    data hc hab hEdgeOne fd.valid hForest block
  linarith

end DivalentEndpoints

/-! ## 11.  `nd(A) = 4` at a wall with a change-free endpoint -/

section ChangeZeroAnchor

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hEdgeOne)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  (hAtMostOne : ∀ first second : data.SourceVertex,
    nonDanglingValency data first ≠ 0 → nonDanglingValency data second ≠ 0 →
    (first.1.1 = a ∨ first.1.1 = b) → (second.1.1 = a ∨ second.1.1 = b) →
      data.localRamification first.1.1 ⟨first.1.2, first.2⟩ ≠ 0 →
        data.localRamification second.1.1 ⟨second.1.2, second.2⟩ ≠ 0 → first = second)

include fd hCompat hForest hRows hZeroCoord hPosCoord hFacetZero hAtMostOne

/-- **`nd(A) = 4` at the vanishing row's fibre**, when the second endpoint of
the contracted occurrence is change-free and at most one incoming constituent
above the wall is ramified. -/
theorem nonDanglingValency_eq_four_of_row_facet_right
    (hChange : data.targetChange b = 0)
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    ∃ block : (mergedPartition data a b).Blocks,
      sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 =
          mergedVertex data hc hab hEdgeOne block ∧
        nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (mergedVertex data hc hab hEdgeOne block) = 4 := by
  obtain ⟨centre, hCentre⟩ := exists_centre_noReturn data fd hc (data.sourceEnds edge.1).1
    hAtMostOne
  obtain ⟨block, hMap, hFour⟩ := four_le_nonDanglingValency_of_row_facet_of_centre data fd hc hab
    hEdgeOne hCompat hForest coordinates facet hZeroCoord hPosCoord hFacetZero centre hCentre
    edge hRow
  have hLe := nonDanglingValency_le_four_of_changeZero_right data fd hc hab hEdgeOne hCompat
    hForest coordinates facet hRows hZeroCoord hChange block
  exact ⟨block, hMap, by omega⟩

/-- The mirror statement, when the first endpoint is change-free. -/
theorem nonDanglingValency_eq_four_of_row_facet_left
    (hChange : data.targetChange a = 0)
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    ∃ block : (mergedPartition data a b).Blocks,
      sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 =
          mergedVertex data hc hab hEdgeOne block ∧
        nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (mergedVertex data hc hab hEdgeOne block) = 4 := by
  obtain ⟨centre, hCentre⟩ := exists_centre_noReturn data fd hc (data.sourceEnds edge.1).1
    hAtMostOne
  obtain ⟨block, hMap, hFour⟩ := four_le_nonDanglingValency_of_row_facet_of_centre data fd hc hab
    hEdgeOne hCompat hForest coordinates facet hZeroCoord hPosCoord hFacetZero centre hCentre
    edge hRow
  have hLe := nonDanglingValency_le_four_of_changeZero_left data fd hc hab hEdgeOne hCompat
    hForest coordinates facet hRows hZeroCoord hChange block
  exact ⟨block, hMap, by omega⟩

end ChangeZeroAnchor

/-! ## 12.  The valency-three wall -/

section ValencyThree

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (star : ThirdEquation.ThreeStar (contract target hab hEdgeOne) ⟨a, hab⟩)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

include fd star hForest hRows hZeroCoord hPosCoord hFacetZero

/-- **The anchor of a valency-three wall is four-valent**, Part II's unique
four-valent vertex at `val w₀ = 3`, in the identified form: the merged block carrying
the vanishing stable row has surviving valency four. -/
theorem nonDanglingValency_eq_four_of_row_facet_threeStar
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    ∃ block : (mergedPartition data a b).Blocks,
      sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 =
          mergedVertex data hc hab hEdgeOne block ∧
        nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (mergedVertex data hc hab hEdgeOne block) = 4 := by
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hEdgeOne
    hForest
  have hLower : ∀ point : data.SourceVertex, nonDanglingValency data point ≠ 0 →
      ∀ place : target.V, point.1.1 = place →
        data.localRamification point.1.1 ⟨point.1.2, point.2⟩ ≠ 0 →
          (1 : ℤ) ≤ data.localRamification point.1.1 ⟨point.1.2, point.2⟩ := by
    intro point _ _ _ hRamified
    have := data.localRamification_nonneg point.1.1 (fd.valid.2 point.1.1)
      ⟨point.1.2, point.2⟩
    omega
  rcases ThirdEquation.valencySplit_of_threeStar data hc hab hEdgeOne fd.valid fd.changeMinimal
    star with ⟨_, _, hChA, hChB⟩ | ⟨_, _, hChA, hChB⟩
  · refine nonDanglingValency_eq_four_of_row_facet_right data fd hc hab hEdgeOne hCompat hForest
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero ?_ hChB edge hRow
    exact atMostOne_ramified_of_changeZero data fd a b 1 hChB
      (fun point hActive hPlace hRamified ↦ hLower point hActive a hPlace hRamified)
      (by rw [hChA]; norm_num)
  · refine nonDanglingValency_eq_four_of_row_facet_left data fd hc hab hEdgeOne hCompat hForest
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero ?_ hChA edge hRow
    intro first second hFirstActive hSecondActive hFirstPlace hSecondPlace hFirstRamified
      hSecondRamified
    exact atMostOne_ramified_of_changeZero data fd b a 1 hChA
      (fun point hActive hPlace hRamified ↦ hLower point hActive b hPlace hRamified)
      (by rw [hChB]; norm_num) first second hFirstActive hSecondActive hFirstPlace.symm
      hSecondPlace.symm hFirstRamified hSecondRamified

/-- **The four-valent anchor at a valency-three wall, identified.**  It is the
wall block of the two ends of the vanishing stable row. -/
theorem exists_wallBlock_sourceVertex_eq_of_row_facet_threeStar
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    ∃ anchorBlock : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩,
      WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchorBlock =
          sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 ∧
        nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchorBlock)
            = 4 := by
  classical
  have hTargetEdge : edge.1.1.1 = contracted :=
    NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates facet
      hZeroCoord hPosCoord hFacetZero edge hRow
  obtain ⟨block, hMap, hFour⟩ := nonDanglingValency_eq_four_of_row_facet_threeStar data fd hc hab
    hEdgeOne star hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero edge hRow
  obtain ⟨anchorBlock, hAnchorBlock⟩ := NonTrivalentUniqueFourValent.exists_wallBlock_sourceVertex_eq
    data hc hab hEdgeOne (data.sourceEnds edge.1).1
    (place_eq_of_incident_contracted data hc _ edge.1 hTargetEdge (Or.inl rfl))
  exact ⟨anchorBlock, hAnchorBlock, by rw [hAnchorBlock, hMap]; exact hFour⟩

/-- **Existence of the four-valent anchor at a valency-three wall.** -/
theorem exists_wallBlock_nonDanglingValency_eq_four_of_threeStar :
    ∃ anchorBlock : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hEdgeOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchorBlock) = 4 := by
  classical
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep (fd.labelling.row.symm facet)
  have hRow : fd.labelling.row edge.stablePath = facet := by
    show fd.labelling.row (Quot.mk _ edge) = facet
    rw [hEdge, Equiv.apply_symm_apply]
  obtain ⟨anchorBlock, _, hFour⟩ := exists_wallBlock_sourceVertex_eq_of_row_facet_threeStar data fd
    hc hab hEdgeOne star hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero edge hRow
  exact ⟨anchorBlock, hFour⟩

end ValencyThree

/-! ## 13.  The valency-two wall -/

section ValencyTwo

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (star : W2R1Target.TwoStar (contract target hab hEdgeOne) ⟨a, hab⟩)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

include fd star hForest hRows hZeroCoord hPosCoord hFacetZero

/-- **The anchor of a valency-two wall is four-valent**, Part II's unique
four-valent vertex at `val w₀ = 2`, in the identified form.  In the `(2,2)` split both
endpoints are divalent target vertices, so no-return holds at every divalent
constituent and the merged excess is bounded by the wall's change; in the two
leaf splits the change-free endpoint makes the fibre a star centred at the
unique ramified constituent above the leaf. -/
theorem nonDanglingValency_eq_four_of_row_facet_twoStar
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    ∃ block : (mergedPartition data a b).Blocks,
      sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 =
          mergedVertex data hc hab hEdgeOne block ∧
        nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (mergedVertex data hc hab hEdgeOne block) = 4 := by
  classical
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hEdgeOne
    hForest
  rcases SecondEquation.valencySplit_of_twoStar data hc hab hEdgeOne fd.valid fd.changeMinimal
    star with ⟨hValA, hValB, _, _⟩ | ⟨hValA, hValB, hChA, hChB⟩ | ⟨hValA, hValB, hChA, hChB⟩
  · obtain ⟨block, hMap, hFour⟩ := four_le_nonDanglingValency_of_row_facet data fd hc hab hEdgeOne
      hCompat hForest coordinates facet hZeroCoord hPosCoord hFacetZero
      (fun point hTwo first second hFirstTarget hSecondTarget hFirst hSecond hFirstInc
        hSecondInc ↦ contracted_eq_of_divalent data fd hc (by omega) (by omega) point hTwo
          first second hFirstTarget hSecondTarget hFirst hSecond hFirstInc hSecondInc)
      edge hRow
    refine ⟨block, hMap, ?_⟩
    have hBound := nonDanglingValency_le_localRamification_add_two data fd hc hab hEdgeOne hCompat
      hForest block hValA hValB (by omega)
    have hValidWall := valid_contractDatum data hc hab hEdgeOne hForest fd.valid
    have hLe := Finset.single_le_sum
      (f := (contractDatum data hc hab hEdgeOne).localRamification ⟨a, hab⟩)
      (fun other _ ↦ (contractDatum data hc hab hEdgeOne).localRamification_nonneg
        ⟨a, hab⟩ (hValidWall.2 ⟨a, hab⟩) other)
      (Finset.mem_univ (⟨block.1, by rw [contractDatum_vertexPartition_merge]; exact block.2⟩ :
        ((contractDatum data hc hab hEdgeOne).vertexPartition ⟨a, hab⟩).Blocks))
    change localRamificationAt (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ block.1 ≤
      (contractDatum data hc hab hEdgeOne).targetChange ⟨a, hab⟩ at hLe
    rw [SecondEquation.targetChange_contractDatum_merge_eq_two data hc hab hEdgeOne fd.valid
      fd.changeMinimal hForest star] at hLe
    omega
  · refine nonDanglingValency_eq_four_of_row_facet_right data fd hc hab hEdgeOne hCompat hForest
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero ?_ hChB edge hRow
    refine atMostOne_ramified_of_changeZero data fd a b 2 hChB ?_ (by rw [hChA]; norm_num)
    intro point hActive hPlace _
    exact NonTrivalentValencyTwoRigidity.two_le_localRamification_of_target_leaf data fd.connected
      point (by rw [hPlace]; exact hValA) hActive
  · refine nonDanglingValency_eq_four_of_row_facet_left data fd hc hab hEdgeOne hCompat hForest
      coordinates facet hRows hZeroCoord hPosCoord hFacetZero ?_ hChA edge hRow
    intro first second hFirstActive hSecondActive hFirstPlace hSecondPlace hFirstRamified
      hSecondRamified
    refine atMostOne_ramified_of_changeZero data fd b a 2 hChA ?_ (by rw [hChB]; norm_num)
      first second hFirstActive hSecondActive hFirstPlace.symm hSecondPlace.symm hFirstRamified
      hSecondRamified
    intro point hActive hPlace _
    exact NonTrivalentValencyTwoRigidity.two_le_localRamification_of_target_leaf data fd.connected
      point (by rw [hPlace]; exact hValB) hActive

/-- **The four-valent anchor at a valency-two wall, identified.**  It is the
wall block of the two ends of the vanishing stable row. -/
theorem exists_wallBlock_sourceVertex_eq_of_row_facet_twoStar
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    ∃ anchorBlock : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩,
      WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchorBlock =
          sourceVertexMap data hc hab hEdgeOne (data.sourceEnds edge.1).1 ∧
        nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchorBlock)
            = 4 := by
  classical
  have hTargetEdge : edge.1.1.1 = contracted :=
    NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates facet
      hZeroCoord hPosCoord hFacetZero edge hRow
  obtain ⟨block, hMap, hFour⟩ := nonDanglingValency_eq_four_of_row_facet_twoStar data fd hc hab
    hEdgeOne star hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero edge hRow
  obtain ⟨anchorBlock, hAnchorBlock⟩ := NonTrivalentUniqueFourValent.exists_wallBlock_sourceVertex_eq
    data hc hab hEdgeOne (data.sourceEnds edge.1).1
    (place_eq_of_incident_contracted data hc _ edge.1 hTargetEdge (Or.inl rfl))
  exact ⟨anchorBlock, hAnchorBlock, by rw [hAnchorBlock, hMap]; exact hFour⟩

/-- **Existence of the four-valent anchor at a valency-two wall.** -/
theorem exists_wallBlock_nonDanglingValency_eq_four_of_twoStar :
    ∃ anchorBlock : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hEdgeOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchorBlock) = 4 := by
  classical
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep (fd.labelling.row.symm facet)
  have hRow : fd.labelling.row edge.stablePath = facet := by
    show fd.labelling.row (Quot.mk _ edge) = facet
    rw [hEdge, Equiv.apply_symm_apply]
  obtain ⟨anchorBlock, _, hFour⟩ := exists_wallBlock_sourceVertex_eq_of_row_facet_twoStar data fd
    hc hab hEdgeOne star hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero edge hRow
  exact ⟨anchorBlock, hFour⟩

end ValencyTwo

/-! ## 14.  The non-anchor bound `nd ≤ 3` -/

section NonAnchor

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)

/-- The merged-partition block underlying a wall block. -/
def mergedBlockOfWallBlock
    (block : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩) :
    (mergedPartition data a b).Blocks :=
  ⟨block.1, by rw [← contractDatum_vertexPartition_merge data hc hab hEdgeOne]; exact block.2⟩

theorem mergedVertex_mergedBlockOfWallBlock
    (block : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩) :
    mergedVertex data hc hab hEdgeOne (mergedBlockOfWallBlock data hc hab hEdgeOne block) =
      WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ block := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact block.2.symm

end NonAnchor

section NonAnchorThree

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (star : ThirdEquation.ThreeStar (contract target hab hEdgeOne) ⟨a, hab⟩)
  (hForest : ContractionForest data a b contracted)

include fd star hForest

/-- **The non-anchor bound `nd ≤ 3` at a valency-three wall**, in the
`OrdinaryBlockProfile.active_card` shape.  Away from the anchor every wall
block is rigid (`lemma-above-w0`), and an unramified pruned fibre cannot reach
surviving valency four. -/
theorem nonDanglingValency_wallBlock_le_three_of_threeStar
    (anchor : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩)
    (hAnchor : nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchor) = 4)
    (block : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩)
    (hBlock : ¬ ((contractDatum data hc hab hEdgeOne).vertexPartition ⟨a, hab⟩).Rel
      anchor.1 block.1) :
    nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ block) ≤ 3 := by
  classical
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hEdgeOne
    hForest
  have hNe : block ≠ anchor := by
    intro hEq
    refine hBlock ?_
    rw [hEq]
    exact rfl
  have hZeroRam := NonTrivalentValencyThreeRigidity.localRamification_eq_zero_of_ne_anchor data fd
    hc hab hEdgeOne hForest hCompat star anchor hAnchor block hNe
  have hDivalent : (GluingDatum.incidentEdges a).card = 2 ∨
      (GluingDatum.incidentEdges b).card = 2 := by
    rcases ThirdEquation.valencySplit_of_threeStar data hc hab hEdgeOne fd.valid fd.changeMinimal
      star with hLeft | hRight
    · exact Or.inl hLeft.1
    · exact Or.inr hRight.2.1
  refine NonTrivalentValencyThreeRigidity.nonDanglingValency_le_three data fd hc hab hEdgeOne
    (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ block) ?_ hCompat
    hDivalent
  intro point hMap
  refine NonTrivalentValencyThreeRigidity.localRamification_eq_zero_in_fibre data fd hc hab
    hEdgeOne hForest (mergedBlockOfWallBlock data hc hab hEdgeOne block) hZeroRam point ?_
  rw [hMap, mergedVertex_mergedBlockOfWallBlock]

end NonAnchorThree

section NonAnchorTwo

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (star : W2R1Target.TwoStar (contract target hab hEdgeOne) ⟨a, hab⟩)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)

include fd star hForest hRows hZeroCoord

/-- **The non-anchor bound `nd ≤ 3` at a valency-two wall**, in the
`OrdinaryBlockProfile.active_card` shape.  Away from the anchor the wall block
is rigid; in the `(2,2)` split its merged excess is bounded by that vanishing
ramification, and in a leaf split a rigid block cannot be four-valent while the
star bound excludes anything larger. -/
theorem nonDanglingValency_wallBlock_le_three_of_twoStar
    (anchor : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩)
    (hAnchor : nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchor) = 4)
    (block : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩)
    (hBlock : ¬ ((contractDatum data hc hab hEdgeOne).vertexPartition ⟨a, hab⟩).Rel
      anchor.1 block.1) :
    nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ block) ≤ 3 := by
  classical
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hEdgeOne
    hForest
  have hNe : block ≠ anchor := by
    intro hEq
    refine hBlock ?_
    rw [hEq]
    exact rfl
  have hZeroRam := NonTrivalentValencyTwoRigidity.localRamification_eq_zero_of_ne_anchor data fd
    hc hab hEdgeOne hForest hCompat star anchor hAnchor block hNe
  have hZeroAt : localRamificationAt (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩
      (mergedBlockOfWallBlock data hc hab hEdgeOne block).1 = 0 := hZeroRam
  rw [← mergedVertex_mergedBlockOfWallBlock data hc hab hEdgeOne block]
  rcases SecondEquation.valencySplit_of_twoStar data hc hab hEdgeOne fd.valid fd.changeMinimal
    star with ⟨hValA, hValB, _, _⟩ | ⟨hValA, _, _, hChB⟩ | ⟨_, hValB, hChA, _⟩
  · by_cases hZero : nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne
        (mergedBlockOfWallBlock data hc hab hEdgeOne block)) = 0
    · omega
    · have hBound := nonDanglingValency_le_localRamification_add_two data fd hc hab hEdgeOne
        hCompat hForest (mergedBlockOfWallBlock data hc hab hEdgeOne block) hValA hValB hZero
      omega
  · have hLe := nonDanglingValency_le_four_of_changeZero_right data fd hc hab hEdgeOne hCompat
      hForest coordinates facet hRows hZeroCoord hChB
      (mergedBlockOfWallBlock data hc hab hEdgeOne block)
    by_cases hFour : nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne
        (mergedBlockOfWallBlock data hc hab hEdgeOne block)) = 4
    · have hTwoLe := NonTrivalentValencyTwoRigidity.two_le_localRamification_of_leaf_endpoint
        data fd hc hab hEdgeOne hCompat hForest
        (mergedBlockOfWallBlock data hc hab hEdgeOne block) (Or.inl hValA) hFour
      omega
    · omega
  · have hLe := nonDanglingValency_le_four_of_changeZero_left data fd hc hab hEdgeOne hCompat
      hForest coordinates facet hRows hZeroCoord hChA
      (mergedBlockOfWallBlock data hc hab hEdgeOne block)
    by_cases hFour : nonDanglingValency (contractDatum data hc hab hEdgeOne)
      (mergedVertex data hc hab hEdgeOne
        (mergedBlockOfWallBlock data hc hab hEdgeOne block)) = 4
    · have hTwoLe := NonTrivalentValencyTwoRigidity.two_le_localRamification_of_leaf_endpoint
        data fd hc hab hEdgeOne hCompat hForest
        (mergedBlockOfWallBlock data hc hab hEdgeOne block) (Or.inr hValB) hFour
      omega
    · omega

end NonAnchorTwo

/-! ## 15.  The classifiers, with no surviving-valency hypothesis -/

section Corollaries

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hEdgeOne : num_edges target a b = 1)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

include fd hForest hRows hZeroCoord hPosCoord hFacetZero

/-- **The valency-three anchor with no surviving-valency hypothesis.**  The
hypotheses are exactly those of
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row` adapted to a
`ThreeStar`, together with the existence side's positive wall metric; the
`nd(A) = 4` input of `NonTrivalentValencyThreeRigidity.threeBranchAnchor` is
discharged. -/
theorem threeBranchAnchor_of_single_row
    (star : ThirdEquation.ThreeStar (contract target hab hEdgeOne) ⟨a, hab⟩) :
    ∃ anchorBlock : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchorBlock) = 4 ∧
        NonTrivalentValencyThreeAnchor.ThreeBranchAnchor (contractDatum data hc hab hEdgeOne)
          star anchorBlock := by
  obtain ⟨anchorBlock, hAnchor⟩ := exists_wallBlock_nonDanglingValency_eq_four_of_threeStar data
    fd hc hab hEdgeOne star hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero
  exact ⟨anchorBlock, hAnchor, NonTrivalentValencyThreeRigidity.threeBranchAnchor data fd hc hab
    hEdgeOne hForest (WallAdmissibility.danglingCompatible_of_contractionForest data hc hab
      hEdgeOne hForest) star anchorBlock hAnchor⟩

/-- **The valency-two anchor with no surviving-valency hypothesis.** -/
theorem twoBranchAnchor_of_single_row
    (star : W2R1Target.TwoStar (contract target hab hEdgeOne) ⟨a, hab⟩) :
    ∃ anchorBlock : WallBlock (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hEdgeOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hEdgeOne) ⟨a, hab⟩ anchorBlock) = 4 ∧
        NonTrivalentValencyTwoAnchor.TwoBranchAnchor (contractDatum data hc hab hEdgeOne)
          star anchorBlock := by
  obtain ⟨anchorBlock, hAnchor⟩ := exists_wallBlock_nonDanglingValency_eq_four_of_twoStar data
    fd hc hab hEdgeOne star hForest coordinates facet hRows hZeroCoord hPosCoord hFacetZero
  exact ⟨anchorBlock, hAnchor, NonTrivalentValencyTwoRigidity.twoBranchAnchor data fd hc hab
    hEdgeOne hForest (WallAdmissibility.danglingCompatible_of_contractionForest data hc hab
      hEdgeOne hForest) star anchorBlock hAnchor⟩

end Corollaries

/-! ## 16.  Non-vacuity of the arithmetic -/

section NonVacuity

/-- The branch count at the anchor on literal inputs: two incoming branch
vertices give `2 + 2 = 4`, and the two extreme fibre shapes of a ramified wall
-- one internal occurrence with two trivalent ends, and a two-occurrence
reduced path through a divalent centre -- both realise it. -/
theorem anchor_branch_arithmetic :
    (2 : ℕ) + 2 = 4 ∧ (3 : ℕ) + 3 = 4 + 2 * 1 ∧ (3 : ℕ) + 2 + 3 = 4 + 2 * 2 := by
  norm_num

/-- The star bound on literal inputs: a divalent centre carries at most two
internal occurrences, so at most two leaves, while a trivalent centre admits at
most one trivalent leaf, since two would give two vanishing rows. -/
theorem star_bound_arithmetic :
    (0 : ℕ) + 2 ≤ 4 ∧ (2 : ℕ) + 2 = 4 ∧ (1 : ℕ) + 1 + 2 = 4 := by
  norm_num

/-- The ramification bound on literal inputs at a `(2,2)` divalent wall: the
merged excess `nd - 2` is at most the wall's whole change `2`. -/
theorem divalent_split_arithmetic :
    ((4 : ℤ) - 2 = 2) ∧ ((2 : ℤ) + 2 = 4) ∧ ((0 : ℤ) + 2 ≤ 3) := by
  norm_num

/-- The single-ramified-constituent count on literal inputs: two constituents
of ramification one exceed a change of one, and two of ramification two exceed a
change of two. -/
theorem ramified_count_arithmetic :
    ((1 : ℤ) < 1 + 1) ∧ ((2 : ℤ) < 2 + 2) := by
  norm_num

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentAnchorValency
