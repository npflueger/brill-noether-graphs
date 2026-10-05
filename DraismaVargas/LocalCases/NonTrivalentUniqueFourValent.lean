module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourBackground
public import DraismaVargas.LocalCases.W4IncomingPrunedFibre

@[expose] public section

/-!
# The unique four-valent vertex above a one-row wall

Source: Vargas, Part II, Section 5.1 (*Combinatorial setup and local
determinants*), in particular its statement that `H_0` has a unique 4-valent
vertex `A` while all other vertices are trivalent, together with its labelling
convention (1): the contracting source edge `h_1^(q)` has trivalent endpoints
`A_1^(q)`, `A_2^(q)`.

## What is proved

At an actual four-valent wall `M_0 = contractDatum data hc hab hOne` of an
incoming full-dimensional cover `data`, with the wall metric of a Part II open
facet:

* `nonDanglingValency_le_four` -- every merged source vertex has `nd ≤ 4`;
* `exists_internalEdge_of_nonDanglingValency_four` -- a merged vertex of
  `nd = 4` is the contraction of a *single* surviving occurrence over the
  contracted target edge, whose two literal ends are trivalent;
* `eq_of_stablePath_eq_of_ends_ne_two` -- such an occurrence is alone in its
  stable-path class, so `row_eq_facet_of_isolated` makes its stable row the
  vanishing one;
* `eq_of_nonDanglingValency_four` -- hence **at most one** merged vertex has
  `nd = 4`, because only `facet` may vanish;
* `nonDanglingValency_le_three_of_ne` and its wall-block form
  `nonDanglingValency_wallBlock_le_three` -- the non-anchor bound `nd ≤ 3`,
  which is exactly the `active_card` input of
  `NonTrivalentValencyFourBackground.OrdinaryBlockProfile` and the `hLe` of
  `NonDanglingValency.nonDanglingValency_eq_zero_or_two_or_three`;
* `exists_wallBlock_nonDanglingValency_eq_four` -- and the anchor **exists**:
  the vanishing row lies entirely over the contracted target occurrence
  (`target_eq_contracted_of_row_eq_facet`), neither of its ends is divalent
  (`nonDanglingValency_ne_two_of_incident_row_facet`, by no-return above a
  four-valent wall), so its contraction is a merged vertex of `nd = 4`;
* `ordinaryBlockProfile_of_single_row` and
  `exists_valid_candidate_of_single_row` -- the guarded ordinary-block census
  and the valid `K = 0` candidate of
  `NonTrivalentValencyFourBackground.exists_valid_candidate`, with **no**
  census, injectivity, background or trivalence receipt supplied.

The proof is local: a merged block of `nd = 4` produces a stable row that
vanishes at the wall, and a Part II wall has only one vanishing row.  Part II's
own argument, the rank count `|E(H_0)| = 3g - 4`, is not used, and no row
dictionary between `M` and `M_0` is needed.

## What is not proved here

Every statement carries its hypotheses explicitly; nothing constructs a
`FullDimensionalSourcePresentation` and nothing produces the wall metric.  The
hypothesis list of the corollaries is exactly the one
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row`
carries, namely

* `fd : FullDimensionalSourcePresentation data coordinate` (the incoming cover);
* `hForest : ContractionForest data a b contracted` (equivalently the non-loop
  simple end of `SingleRowForest.contractionForest_of_single_row`);
* `star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩`, i.e.
  wall valency four;
* `hCompat : DanglingCompatible data hc hab hOne`, which `hForest` supplies;
* the wall metric `coordinates`, with `hZeroCoord` (the contracted target
  occurrence has length zero);
* `hAnchor : nd(A) = 4` for the classifier statements, which
  `exists_wallBlock_nonDanglingValency_eq_four` itself produces.

The two halves of Part II's statement (a unique four-valent vertex, all others
trivalent) use disjoint metric hypotheses.  *Uniqueness*
(`eq_of_nonDanglingValency_four`, `nonDanglingValency_le_three_of_ne`,
`nonDanglingValency_wallBlock_le_three`) uses only `hRows`: no stable row other
than `facet` vanishes.  *Existence*
(`exists_wallBlock_nonDanglingValency_eq_four`) uses only `hPosCoord` (no
target occurrence other than the contracted one has length zero) together with
`hFacetZero` (the row `facet` does vanish); it needs no `hRows` and no
contraction forest.

Nothing here treats a wall of valency three or two.  `card_branchFibreVertices_add_two_eq_nonDanglingValency`
records, at a wall of *any* valency, that `nd(B)` is two plus the number of
incoming branch vertices in the fibre of `B`; so `nd(A) = 4` there says exactly
that the anchor's fibre carries two incoming branch vertices.  Turning that
into the valency-three and valency-two anchors' residual `nd(A) = 4` needs one
further ingredient which is *not* proved here: at a wall whose fibres may be
ramified, a fibre with two incoming branch vertices contains a whole stable
class, namely the reduced fibre-tree path between them.  Above a four-valent
wall that path is a single occurrence (`internalEdges_subsingleton`), which is
why the argument closes here and not there.

## Used by

`NonTrivalentValencyFourBackground` (its `OrdinaryBlockProfile.active_card`
input) and, through it, the boundary dispatcher for Part II case `{v4-nd4}`.
-/
namespace DraismaVargas.LocalCases.NonTrivalentUniqueFourValent

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource WallDegeneration ClassInjectivity
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree FullContractionFibre
open FullDimensionalSource PresentationDecomposition PrunedSource
open NonTrivalentValencyFourKZero

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  Occurrences alone in their stable class -/

section Isolated

variable {data : GluingDatum target degree}

/-- **An occurrence with no divalent end is alone in its stable class.**  A
stable path only continues through a surviving source vertex of surviving
valency two, so an occurrence whose two literal ends are not divalent is the
whole of its stable-path class. -/
theorem eq_of_stablePath_eq_of_ends_ne_two (edge : NonDanglingEdge data)
    (hLeft : nonDanglingValency data (data.sourceEnds edge.1).1 ≠ 2)
    (hRight : nonDanglingValency data (data.sourceEnds edge.1).2 ≠ 2)
    (other : NonDanglingEdge data) (hPath : other.stablePath = edge.stablePath) :
    other = edge := by
  have hIncident : ∀ vertex : data.SourceVertex, Incident data edge.1 vertex →
      nonDanglingValency data vertex ≠ 2 := by
    rintro vertex (h | h)
    · rw [← h]; exact hLeft
    · rw [← h]; exact hRight
  have hStep : ∀ first second : NonDanglingEdge data,
      Consecutive data first second → first ≠ edge ∧ second ≠ edge := by
    rintro first second ⟨_, vertex, hFirst, hSecond, hValency⟩
    exact ⟨fun hEq ↦ hIncident vertex (hEq ▸ hFirst) hValency,
      fun hEq ↦ hIncident vertex (hEq ▸ hSecond) hValency⟩
  have key : ∀ first second : NonDanglingEdge data,
      Relation.EqvGen (Consecutive data) first second →
        (first = edge ↔ second = edge) := by
    intro first second hChain
    induction hChain with
    | rel first second hRel =>
      exact ⟨fun hEq ↦ absurd hEq (hStep first second hRel).1,
        fun hEq ↦ absurd hEq (hStep first second hRel).2⟩
    | refl _ => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  exact (key other edge ((stablePath_eq_iff other edge).mp hPath)).mpr rfl

end Isolated

/-! ## 2.  The row of an occurrence over a zero-length target edge -/

section Row

variable {data : GluingDatum target degree} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]

/-- **An isolated occurrence over the contracted target edge carries the
vanishing row.**  Its stable class is the single occurrence, whose length is
the contracted target length, so its row length is zero; by `hRows` no row
other than `facet` can vanish. -/
theorem row_eq_facet_of_isolated
    (labelling : StableLengthMatrixLabelling data coordinate)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).mulVec
        coordinates row ≠ 0)
    (edge : NonDanglingEdge data)
    (hIsolated : ∀ other : NonDanglingEdge data,
      other.stablePath = edge.stablePath → other = edge)
    (hZero : coordinates (labelling.targetEdge.symm edge.1.1.1) = 0) :
    labelling.row edge.stablePath = facet := by
  by_contra hNe
  apply hRows _ hNe
  rw [GluingDatum.LengthMatrixPresentation.matrix_mulVec]
  unfold GluingDatum.sourcePathLength
  apply List.sum_eq_zero
  intro term hTerm
  obtain ⟨other, hOther, rfl⟩ := List.mem_map.mp hTerm
  obtain ⟨hSurvives, hRow⟩ := (mem_presentation_path_iff labelling _ other).mp hOther
  have hEq : (⟨other, hSurvives⟩ : NonDanglingEdge data) = edge :=
    hIsolated _ (labelling.row.injective hRow)
  have hVal : other = edge.1 := congrArg Subtype.val hEq
  simp only [GluingDatum.sourceEdgeLength, hVal,
    StableLengthMatrixLabelling.presentation, hZero, zero_div]

end Row

/-! ## 3.  The pruned fibre census above a four-valent wall -/

section Wall

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hCompat : DanglingCompatible data hc hab hOne)

include fd star hCompat

/-- **Every merged source vertex above a four-valent wall has surviving
valency at most four.**  The pruned fibre is a single incoming vertex or a
single surviving occurrence with two trivalent-or-less ends. -/
theorem nonDanglingValency_le_four
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    nonDanglingValency (contractDatum data hc hab hOne) vertex ≤ 4 := by
  classical
  by_cases hZero : nonDanglingValency (contractDatum data hc hab hOne) vertex = 0
  · omega
  have hAccount := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat vertex
  rcases W4IncomingPrunedFibre.census data fd hc hab hOne star vertex
    (activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne
      hCompat vertex hZero) with ⟨point, hPoint, hEmpty⟩ | ⟨edge, hSingleton, hEnds, hNe⟩
  · rw [hPoint, Finset.sum_singleton, hEmpty, Finset.card_empty] at hAccount
    have hPointBound := fd.trivalent point
    omega
  · rw [hEnds, Finset.sum_pair hNe, hSingleton, Finset.card_singleton] at hAccount
    have hLeft := fd.trivalent (data.sourceEnds edge).1
    have hRight := fd.trivalent (data.sourceEnds edge).2
    omega

/-- **A four-valent merged vertex is the contraction of one surviving
occurrence with two trivalent ends.**  No stable row is named: the tree count
of the pruned fibre forces the exact shape. -/
theorem exists_internalEdge_of_nonDanglingValency_four
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 4) :
    ∃ edge : data.SourceEdge,
      ¬ IsDangling data edge ∧ edge.1.1 = contracted ∧
        sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex ∧
        nonDanglingValency data (data.sourceEnds edge).1 = 3 ∧
        nonDanglingValency data (data.sourceEnds edge).2 = 3 := by
  classical
  have hZero : nonDanglingValency (contractDatum data hc hab hOne) vertex ≠ 0 := by omega
  have hAccount := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat vertex
  rcases W4IncomingPrunedFibre.census data fd hc hab hOne star vertex
    (activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne
      hCompat vertex hZero) with ⟨point, hPoint, hEmpty⟩ | ⟨edge, hSingleton, hEnds, hNe⟩
  · rw [hPoint, Finset.sum_singleton, hEmpty, Finset.card_empty] at hAccount
    have hPointBound := fd.trivalent point
    omega
  · rw [hEnds, Finset.sum_pair hNe, hSingleton, Finset.card_singleton] at hAccount
    have hLeft := fd.trivalent (data.sourceEnds edge).1
    have hRight := fd.trivalent (data.sourceEnds edge).2
    obtain ⟨hSurvives, hTarget, hMap⟩ := (mem_internalEdges data hc hab hOne vertex edge).mp
      (hSingleton ▸ Finset.mem_singleton_self edge)
    exact ⟨edge, hSurvives, hTarget, hMap, by omega, by omega⟩

end Wall

/-! ## 4.  Uniqueness of the four-valent vertex from the single vanishing row -/

section SingleRow

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hCompat : DanglingCompatible data hc hab hOne)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)

include fd star hCompat hRows hZeroCoord

/-- **A four-valent merged vertex carries the vanishing row.**  Its internal
occurrence has two trivalent ends, so it is alone in its stable class; that
class lies over the contracted target edge, whose length is zero. -/
theorem exists_facet_internalEdge_of_nonDanglingValency_four
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne) vertex = 4) :
    ∃ edge : data.SourceEdge, ∃ hSurvives : ¬ IsDangling data edge,
      sourceVertexMap data hc hab hOne (data.sourceEnds edge).1 = vertex ∧
        fd.labelling.row (NonDanglingEdge.stablePath ⟨edge, hSurvives⟩) = facet ∧
        ∀ other : NonDanglingEdge data,
          other.stablePath = NonDanglingEdge.stablePath ⟨edge, hSurvives⟩ →
            other.1 = edge := by
  obtain ⟨edge, hSurvives, hTarget, hMap, hLeft, hRight⟩ :=
    exists_internalEdge_of_nonDanglingValency_four data fd hc hab hOne star hCompat
      vertex hNd
  have hIsolated : ∀ other : NonDanglingEdge data,
      other.stablePath = NonDanglingEdge.stablePath ⟨edge, hSurvives⟩ →
        other = ⟨edge, hSurvives⟩ :=
    eq_of_stablePath_eq_of_ends_ne_two ⟨edge, hSurvives⟩
      (by show nonDanglingValency data (data.sourceEnds edge).1 ≠ 2; omega)
      (by show nonDanglingValency data (data.sourceEnds edge).2 ≠ 2; omega)
  refine ⟨edge, hSurvives, hMap, ?_,
    fun other hOther ↦ congrArg Subtype.val (hIsolated other hOther)⟩
  refine row_eq_facet_of_isolated fd.labelling coordinates facet hRows
    ⟨edge, hSurvives⟩ hIsolated ?_
  show coordinates (fd.labelling.targetEdge.symm edge.1.1) = 0
  rw [hTarget]
  exact hZeroCoord

/-- **At most one four-valent vertex.**  Two merged source vertices of
surviving valency four would produce two distinct vanishing stable rows, but
only `facet` may vanish. -/
theorem eq_of_nonDanglingValency_four
    (first second : (contractDatum data hc hab hOne).SourceVertex)
    (hFirst : nonDanglingValency (contractDatum data hc hab hOne) first = 4)
    (hSecond : nonDanglingValency (contractDatum data hc hab hOne) second = 4) :
    first = second := by
  obtain ⟨firstEdge, hFirstSurvives, hFirstMap, hFirstRow, hFirstIsolated⟩ :=
    exists_facet_internalEdge_of_nonDanglingValency_four data fd hc hab hOne star
      hCompat coordinates facet hRows hZeroCoord first hFirst
  obtain ⟨secondEdge, hSecondSurvives, hSecondMap, hSecondRow, _⟩ :=
    exists_facet_internalEdge_of_nonDanglingValency_four data fd hc hab hOne star
      hCompat coordinates facet hRows hZeroCoord second hSecond
  have hEdge : secondEdge = firstEdge :=
    hFirstIsolated ⟨secondEdge, hSecondSurvives⟩
      (fd.labelling.row.injective (hSecondRow.trans hFirstRow.symm))
  rw [← hFirstMap, ← hSecondMap, hEdge]

/-- **The non-anchor bound `nd ≤ 3`** (Part II, Section 5.1).  Every
merged source vertex other than a given four-valent one is trivalent. -/
theorem nonDanglingValency_le_three_of_ne
    (anchor : (contractDatum data hc hab hOne).SourceVertex)
    (hAnchor : nonDanglingValency (contractDatum data hc hab hOne) anchor = 4)
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (hNe : vertex ≠ anchor) :
    nonDanglingValency (contractDatum data hc hab hOne) vertex ≤ 3 := by
  by_contra hBad
  have hLe := nonDanglingValency_le_four data fd hc hab hOne star hCompat vertex
  exact hNe (eq_of_nonDanglingValency_four data fd hc hab hOne star hCompat
    coordinates facet hRows hZeroCoord vertex anchor (by omega) hAnchor)

/-- The wall-block form consumed by `NonTrivalentValencyFourBackground`:
distinct wall blocks are distinct merged source vertices. -/
theorem nonDanglingValency_wallBlock_le_three
    (anchorBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hAnchor : nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchorBlock) = 4)
    (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hBlock : ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      anchorBlock.1 block.1) :
    nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ block) ≤ 3 := by
  refine nonDanglingValency_le_three_of_ne data fd hc hab hOne star hCompat
    coordinates facet hRows hZeroCoord _ hAnchor _ ?_
  intro hEq
  exact hBlock (congrArg (fun point : (contractDatum data hc hab hOne).SourceVertex ↦
    point.1.2) hEq).symm

end SingleRow

/-! ## 5.  The wall metric: only the contracted occurrence has length zero -/

section Metric

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {contracted : target.edges}
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)

include fd hZeroCoord hPosCoord

/-- The wall metric is nonnegative: the contracted target occurrence has
length zero and every other target occurrence has positive length. -/
theorem coordinates_nonneg (column : coordinate) : 0 ≤ coordinates column := by
  by_cases hColumn : column = fd.labelling.targetEdge.symm contracted
  · rw [hColumn, hZeroCoord]
  · exact (hPosCoord column hColumn).le

/-- **Every occurrence of the vanishing row lies over the contracted target
edge.**  A vanishing row is a sum of nonnegative occurrence lengths, so each of
them vanishes, and the contracted occurrence is the only target occurrence of
length zero. -/
theorem target_eq_contracted_of_row_eq_facet
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0)
    (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet) :
    edge.1.1.1 = contracted := by
  classical
  have hMem : edge.1 ∈ fd.labelling.presentation.path facet :=
    (mem_presentation_path_iff fd.labelling facet edge.1).mpr ⟨edge.2, hRow⟩
  have hSum := (GluingDatum.LengthMatrixPresentation.matrix_mulVec
    fd.labelling.presentation coordinates facet).symm.trans hFacetZero
  unfold GluingDatum.sourcePathLength at hSum
  have hNonneg : ∀ value ∈ (fd.labelling.presentation.path facet).map
      (data.sourceEdgeLength fun occurrence ↦
        coordinates (fd.labelling.presentation.targetEdge.symm occurrence)),
      0 ≤ value := by
    intro value hValue
    obtain ⟨other, _, rfl⟩ := List.mem_map.mp hValue
    exact div_nonneg (coordinates_nonneg data fd coordinates hZeroCoord hPosCoord _)
      (by positivity)
  have hLe := List.single_le_sum hNonneg _ (List.mem_map.mpr ⟨edge.1, hMem, rfl⟩)
  rw [hSum] at hLe
  have hTerm : data.sourceEdgeLength (fun occurrence ↦
      coordinates (fd.labelling.presentation.targetEdge.symm occurrence)) edge.1 = 0 :=
    le_antisymm hLe
      (div_nonneg (coordinates_nonneg data fd coordinates hZeroCoord hPosCoord _)
        (by positivity))
  have hIndex : (data.sourceEdgeIndex edge.1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (GluingDatum.sourceEdgeIndex_pos data edge.1)
  have hCoord : coordinates (fd.labelling.targetEdge.symm edge.1.1.1) = 0 := by
    have hDiv : coordinates (fd.labelling.targetEdge.symm edge.1.1.1) /
        (data.sourceEdgeIndex edge.1 : ℚ) = 0 := hTerm
    rcases div_eq_zero_iff.mp hDiv with hValue | hValue
    · exact hValue
    · exact absurd hValue hIndex
  by_contra hNe
  refine absurd hCoord (ne_of_gt (hPosCoord _ ?_))
  intro hBad
  exact hNe (fd.labelling.targetEdge.symm.injective hBad)

end Metric

/-! ## 6.  Existence of the four-valent vertex -/

section WallBlockOfVertex

/-- Every merged source vertex over an endpoint of the contracted target edge
is the wall-block form of a block above the wall. -/
theorem exists_wallBlock_sourceVertex_eq (data : GluingDatum target degree)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (point : data.SourceVertex) (hPlace : point.1.1 = a ∨ point.1.1 = b) :
    ∃ wallBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ wallBlock =
        sourceVertexMap data hc hab hOne point := by
  classical
  have hRepr : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr
      ((mergedPartition data a b).toBlock point.1.2).1 =
      ((mergedPartition data a b).toBlock point.1.2).1 := by
    rw [contractDatum_vertexPartition_merge]
    exact ((mergedPartition data a b).toBlock point.1.2).2
  refine ⟨⟨((mergedPartition data a b).toBlock point.1.2).1, hRepr⟩, ?_⟩
  have hMerged : sourceVertexMap data hc hab hOne point =
      mergedVertex data hc hab hOne ((mergedPartition data a b).toBlock point.1.2) := by
    have hMem := (mem_fibreVertices_mergedVertex_iff data hc hab hOne
      ((mergedPartition data a b).toBlock point.1.2) point).mpr ⟨hPlace, rfl⟩
    rwa [mem_fibreVertices] at hMem
  rw [hMerged]
  exact Subtype.ext (Prod.ext rfl hRepr)

end WallBlockOfVertex

section Anchor

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hCompat : DanglingCompatible data hc hab hOne)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

include fd hc star hZeroCoord hPosCoord hFacetZero

/-- **No end of a vanishing-row occurrence is divalent.**  A divalent end
continues the stable class into a second occurrence, which then also lies over
the contracted target edge; no-return above the four-valent wall forbids two
such occurrences at one source vertex. -/
theorem nonDanglingValency_ne_two_of_incident_row_facet (edge : NonDanglingEdge data)
    (hRow : fd.labelling.row edge.stablePath = facet)
    (vertex : data.SourceVertex) (hIncident : Incident data edge.1 vertex) :
    nonDanglingValency data vertex ≠ 2 := by
  classical
  intro hTwo
  obtain ⟨other, hOtherNe, hPair⟩ :=
    nonDanglingIncident_eq_pair data hTwo edge.2 hIncident
  obtain ⟨hOtherSurvives, hOtherIncident⟩ :=
    (mem_nonDanglingIncident data vertex other).mp
      (hPair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self other))
  have hConsecutive : Consecutive data edge ⟨other, hOtherSurvives⟩ :=
    ⟨fun hEq ↦ hOtherNe (congrArg Subtype.val hEq).symm, vertex, hIncident,
      hOtherIncident, hTwo⟩
  have hOtherRow : fd.labelling.row
      (NonDanglingEdge.stablePath (⟨other, hOtherSurvives⟩ : NonDanglingEdge data)) =
      facet := by
    rw [← stablePath_eq_of_consecutive hConsecutive]
    exact hRow
  exact hOtherNe (W4IncomingPrunedFibre.contracted_sourceEdge_eq_of_incident data fd hc hab
    hOne star vertex other edge.1
    (target_eq_contracted_of_row_eq_facet data fd coordinates facet hZeroCoord hPosCoord
      hFacetZero ⟨other, hOtherSurvives⟩ hOtherRow)
    (target_eq_contracted_of_row_eq_facet data fd coordinates facet hZeroCoord hPosCoord
      hFacetZero edge hRow)
    hOtherSurvives edge.2 hOtherIncident hIncident)

include hCompat

/-- **The four-valent vertex exists** (Part II, Section 5.1).  The
vanishing row is one surviving occurrence over the contracted target edge with
two trivalent ends, and its contraction is a merged wall vertex of surviving
valency four. -/
theorem exists_wallBlock_nonDanglingValency_eq_four :
    ∃ anchorBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
          anchorBlock) = 4 := by
  classical
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep (fd.labelling.row.symm facet)
  have hRow : fd.labelling.row edge.stablePath = facet := by
    show fd.labelling.row (Quot.mk _ edge) = facet
    rw [hEdge, Equiv.apply_symm_apply]
  have hTarget : edge.1.1.1 = contracted :=
    target_eq_contracted_of_row_eq_facet data fd coordinates facet hZeroCoord hPosCoord
      hFacetZero edge hRow
  have hInternal : edge.1 ∈ internalEdges data hc hab hOne
      (sourceVertexMap data hc hab hOne (data.sourceEnds edge.1).1) :=
    (mem_internalEdges data hc hab hOne _ edge.1).mpr ⟨edge.2, hTarget, rfl⟩
  obtain ⟨hLeftPlace, _, _, _, hEndsNe⟩ :=
    W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hOne _ edge.1 hInternal
  have hEnds := W4IncomingPrunedFibre.activeFibreVertices_eq_endpoints data fd hc hab hOne
    star _ edge.1 hInternal
  have hSingleton : internalEdges data hc hab hOne
      (sourceVertexMap data hc hab hOne (data.sourceEnds edge.1).1) = {edge.1} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hInternal, fun other hOther ↦
      W4IncomingPrunedFibre.internalEdges_subsingleton data fd hc hab hOne star _
        other hOther edge.1 hInternal⟩
  have hAccount := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat
    (sourceVertexMap data hc hab hOne (data.sourceEnds edge.1).1)
  rw [hEnds, Finset.sum_pair hEndsNe, hSingleton, Finset.card_singleton] at hAccount
  have hLeftThree : nonDanglingValency data (data.sourceEnds edge.1).1 = 3 := by
    have hNe := nonDanglingValency_ne_two_of_incident_row_facet data fd hc hab hOne star
      coordinates facet hZeroCoord hPosCoord hFacetZero edge hRow _ (Or.inl rfl)
    have hZero := nonDanglingValency_ne_zero_of_incident data edge.2
      (Or.inl rfl : Incident data edge.1 (data.sourceEnds edge.1).1)
    have hOneNe := NonDanglingValency.nonDanglingValency_ne_one data fd.connected
      (data.sourceEnds edge.1).1
    have hBound := fd.trivalent (data.sourceEnds edge.1).1
    omega
  have hRightThree : nonDanglingValency data (data.sourceEnds edge.1).2 = 3 := by
    have hNe := nonDanglingValency_ne_two_of_incident_row_facet data fd hc hab hOne star
      coordinates facet hZeroCoord hPosCoord hFacetZero edge hRow _ (Or.inr rfl)
    have hZero := nonDanglingValency_ne_zero_of_incident data edge.2
      (Or.inr rfl : Incident data edge.1 (data.sourceEnds edge.1).2)
    have hOneNe := NonDanglingValency.nonDanglingValency_ne_one data fd.connected
      (data.sourceEnds edge.1).2
    have hBound := fd.trivalent (data.sourceEnds edge.1).2
    omega
  obtain ⟨anchorBlock, hAnchorBlock⟩ := exists_wallBlock_sourceVertex_eq data hc hab hOne
    (data.sourceEnds edge.1).1 (Or.inl hLeftPlace)
  refine ⟨anchorBlock, ?_⟩
  rw [hLeftThree, hRightThree] at hAccount
  rw [hAnchorBlock]
  omega

end Anchor

/-! ## 7.  The residual source input of the `K = 0` background, discharged -/

section Corollaries

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (anchorBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
  (hAnchor : nonDanglingValency (contractDatum data hc hab hOne)
    (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ anchorBlock) = 4)

include fd

/-- The contracted target is still connected. -/
theorem wall_target_connected : graph_connected (contract target hab hOne) :=
  graph_connected_contract target hab hOne fd.targetConnected

/-- The contracted target is still a tree. -/
theorem wall_target_genus : genus (contract target hab hOne) = 0 :=
  (genus_contract target hab hOne).trans fd.targetGenus

include hForest

/-- The wall datum is valid. -/
theorem wall_valid : (contractDatum data hc hab hOne).Valid :=
  valid_contractDatum data hc hab hOne hForest fd.valid

/-- Dangling-no-glue survives the contraction. -/
theorem wall_noGlue : DanglingEdgeNoGlue (contractDatum data hc hab hOne) :=
  danglingEdgeNoGlue_contractDatum data
    (WallAdmissibility.danglingReflected_of_contractionForest data hc hab hOne hForest)
    fd.danglingEdgeNoGlue

include star

/-- `r0(A) = 0` at a four-valent wall: the whole change vanishes. -/
theorem wall_ramification :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ anchorBlock = 0 :=
  NonTrivalentWallSetup.forall_localRamification_eq_zero_of_valency_four data hc hab hOne
    hForest fd.valid fd.changeMinimal star.card_incidentEdges anchorBlock

include hAnchor

/-- The actual four-branch anchor of the wall. -/
theorem wallFourBranchAnchor :
    FourBranchAnchor (contractDatum data hc hab hOne) star anchorBlock :=
  NonTrivalentValencyFourAnchor.fourBranchAnchor_of_contractionForest data fd hc hab hOne
    star hForest anchorBlock hAnchor

include hRows hZeroCoord

/-- **The guarded ordinary-block census, with no source receipt.**  This is
`NonTrivalentValencyFourBackground.ordinaryBlockProfile_of_contractionForest`
with its last input -- the trivalence of `H(M_0)` away from the anchor --
discharged from the single vanishing stable row. -/
noncomputable def ordinaryBlockProfile_of_single_row :
    NonTrivalentValencyFourBackground.OrdinaryBlockProfile
      (contractDatum data hc hab hOne) star anchorBlock.1 :=
  NonTrivalentValencyFourBackground.ordinaryBlockProfile_of_contractionForest data fd hc hab
    hOne star hForest (wall_noGlue data fd hc hab hOne hForest)
    (wall_valid data fd hc hab hOne hForest).1 anchorBlock
    (fun block hBlock ↦ nonDanglingValency_wallBlock_le_three data fd hc hab hOne star
      (WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne hForest)
      coordinates facet hRows hZeroCoord anchorBlock hAnchor block hBlock)

/-- **The `K = 0` candidate above an actual four-valent wall, with no supplied
background, census, injectivity or trivalence receipt.**  The remaining
hypotheses are exactly those of
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row`: an incoming
full-dimensional cover, the actual contraction forest, the nonnegative wall
metric with only the contracted target occurrence at zero, the single vanishing
stable row, and the anchor's `nd = 4`. -/
theorem exists_valid_candidate_of_single_row (pairing : Fin 3) :
    ∃ (source : FourBranchAnchor (contractDatum data hc hab hOne) star anchorBlock)
      (hNoGlue : DanglingEdgeNoGlue (contractDatum data hc hab hOne))
      (hRamification : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩
        anchorBlock = 0)
      (geometry : PrescribedPairing.PairingBackground source pairing hNoGlue hRamification)
      (hConnected : graph_connected (contract target hab hOne))
      (hGenus : genus (contract target hab hOne) = 0),
      (PrescribedPairing.candidate source pairing hNoGlue hRamification geometry hConnected
        hGenus).datum.Valid ∧
      (∀ sideValue : Bool,
        (if sideValue then
            ((PrescribedPairing.candidate source pairing hNoGlue hRamification geometry
              hConnected hGenus).resolution anchorBlock.1).right
          else ((PrescribedPairing.candidate source pairing hNoGlue hRamification geometry
            hConnected hGenus).resolution anchorBlock.1).left).blockCard
              (PrescribedPairing.selectedRepresentative source pairing) + 1 =
          if sideValue = PrescribedPairing.smallerSide source pairing then
            PrescribedPairing.sideIndex source pairing
              (PrescribedPairing.smallerSide source pairing)
          else ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
            anchorBlock.1 + 1) ∧
      (PrescribedPairing.candidate source pairing hNoGlue hRamification geometry hConnected
          hGenus).datum.sourceEdgeIndex
        ((PrescribedPairing.candidate source pairing hNoGlue hRamification geometry hConnected
          hGenus).newSourceEdge
            (PrescribedPairing.selectedRepresentative source pairing)) + 1 =
        PrescribedPairing.sideIndex source pairing
          (PrescribedPairing.smallerSide source pairing) := by
  refine ⟨wallFourBranchAnchor data fd hc hab hOne star hForest anchorBlock hAnchor,
    wall_noGlue data fd hc hab hOne hForest,
    wall_ramification data fd hc hab hOne star hForest anchorBlock, ?_⟩
  obtain ⟨geometry, hValid, hEndpoint, hBridge⟩ :=
    NonTrivalentValencyFourBackground.exists_valid_candidate
      (wallFourBranchAnchor data fd hc hab hOne star hForest anchorBlock hAnchor) pairing
      (wall_noGlue data fd hc hab hOne hForest)
      (wall_ramification data fd hc hab hOne star hForest anchorBlock)
      (ordinaryBlockProfile_of_single_row data fd hc hab hOne star hForest coordinates facet
        hRows hZeroCoord anchorBlock hAnchor)
      (wall_target_connected data fd hab hOne)
      (wall_target_genus data fd hab hOne)
      (wall_valid data fd hc hab hOne hForest)
  exact ⟨geometry, wall_target_connected data fd hab hOne,
    wall_target_genus data fd hab hOne, hValid, hEndpoint, hBridge⟩

end Corollaries

/-! ## 8.  The branch-vertex count of a wall fibre -/

section BranchCount

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)

include fd hCompat hForest

/-- **`nd(B) = (number of incoming branch vertices in the fibre of `B`) + 2`**,
at a wall of any valency.  This is Part I's `lemma-ndval-of-GqA0` with the valency
excesses evaluated: an active incoming vertex of a full-dimensional cover has
`nd ∈ {2, 3}`, so its excess is `0` or `1`.  In particular `nd(B) = 4` says
exactly that the fibre of `B` carries two incoming branch vertices, which is
the form in which the valency-three and valency-two anchors meet the
bound. -/
theorem card_branchFibreVertices_add_two_eq_nonDanglingValency
    (block : (mergedPartition data a b).Blocks)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0) :
    ((activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).filter
        fun point ↦ nonDanglingValency data point = 3).card + 2 =
      nonDanglingValency (contractDatum data hc hab hOne)
        (mergedVertex data hc hab hOne block) := by
  classical
  have hSum := nonDanglingValency_mergedVertex_eq_sum data hc hab hOne hCompat hForest block
    hNonzero
  have hTerm : ∀ point ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block),
      ((nonDanglingValency data point : ℤ) - 2) =
        if nonDanglingValency data point = 3 then (1 : ℤ) else 0 := by
    intro point hPoint
    have hActive := ((mem_activeFibreVertices data hc hab hOne _ point).mp hPoint).2
    rcases fd.nonDanglingValency_trichotomy point with hValency | hValency | hValency
    · exact absurd hValency hActive
    · rw [hValency]; norm_num
    · rw [hValency]; norm_num
  rw [Finset.sum_congr rfl hTerm, Finset.sum_boole] at hSum
  omega

end BranchCount

/-! ## 9.  Non-vacuity of the arithmetic -/

section NonVacuity

/-- The four-valent census on literal inputs: a pruned fibre that is one
surviving occurrence with two trivalent ends accounts for `3 + 3 = 4 + 2 * 1`,
so `nd = 4` really is attained, and `3 + 3 ≤ 4 + 2 * 1` is the only way for two
incoming trivalent ends to reach it. -/
theorem internalEdge_arithmetic : (3 : ℕ) + 3 = 4 + 2 * 1 ∧ (3 : ℕ) + 3 ≤ 3 + 3 := by
  norm_num

/-- The single-vertex alternative on literal inputs: an empty internal-edge set
leaves `nd = nd(point) ≤ 3`, strictly below four. -/
theorem singleton_fibre_arithmetic : (3 : ℕ) + 2 * 0 = 3 ∧ (3 : ℕ) < 4 := by
  norm_num

/-- The branch-vertex count on literal inputs: two branch vertices in the fibre
give `2 + 2 = 4`, one gives `1 + 2 = 3`, and none gives `0 + 2 = 2` -- the
`nd ∈ {0, 2, 3, 4}` census above a wall. -/
theorem branch_count_arithmetic :
    (2 : ℕ) + 2 = 4 ∧ (1 : ℕ) + 2 = 3 ∧ (0 : ℕ) + 2 = 2 := by
  norm_num

end NonVacuity

end DraismaVargas.LocalCases.NonTrivalentUniqueFourValent
