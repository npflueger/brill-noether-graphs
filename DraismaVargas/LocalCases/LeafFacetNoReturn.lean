import DraismaVargas.LocalCases.StablePathFacetContraction

/-!
# No contracted return off the facet row, at a leaf endpoint

Source: Vargas, Part II (arXiv:2609.09109), §5.1: the lemma on rigidity above
`w_0` (`lemma-above-w0`) and labelling convention (2).  The sentence of that
lemma's proof this module answers, in the case `val w_0 = 2`, is:

> If `\vale u = 1` and `\vale v = 3`, the edge connecting `A_1^{(q)}` and
> `A_2^{(q)}` passes above `u`, so a vertex with `r`-value equal to 2
> contracts to `A`.

At such a wall the contracting stable edge `h_1^{(q)}` really does run up over
`t_1`, fold at a divalent source vertex above the leaf `u`, and come back: the
predicate `StablePathFacetContraction.NoContractedReturn data contracted` is
**false** there, and `StablePathFacetContraction.noContractedReturn_of_nonleaf`
does not apply.  This module proves the weaker statement that is true, and
re-runs the chain of `StablePathFacetContraction` with it.

## What is proved

Let `M = data` be an incoming full-dimensional cover over a target tree `T`,
let `t_1 = contracted` join `a = u` to `b = v`, and suppose `u` is a **leaf**
of `T` while `v` is not.

* **§1, the local statement** (`noReturn_off_facet`).  Every surviving
  divalent source vertex carrying two distinct surviving occurrences over
  `t_1` carries them *on the vanishing row*.  The predicate it produces is

  `NoContractedReturnOffRow data contracted facetRow`: at a surviving divalent
  source vertex two surviving occurrences over `t_1` are equal **or** both lie
  on `facetRow`.

  The proof is Draisma--Vargas Part I, `rem-leaves-min-change`
  (`StableLocalProperties.leaf_block_dichotomy`) plus counting, not the
  paper's rigidity argument.  Above a target leaf `u` of a change-minimal
  cover `ch u = 2`, and every block above `u` is either a single sheet with a
  single incident occurrence and `r = 0`, or a two-sheet block with two
  incident occurrences and `r = 2`.  Since the `r`-values are nonnegative and
  sum to `2`, there is **at most one** block of the second kind, and a block
  of the first kind has surviving valency `0`
  (`NonDanglingValency.nonDanglingValency_ne_one`).  So *every* surviving
  occurrence over `t_1` meets the fold
  (`nonDanglingValency_eq_zero_of_ne_fold`, `incident_of_leaf_fold`), hence is
  one of its two survivors, hence lies on their common stable row; and the
  vanishing row lies entirely over `t_1`, so it is that row.  A return above
  the non-leaf endpoint `v` is excluded exactly as in
  `StablePathFacetContraction`, by
  `DivalentSourceLocal.localRamification_le_one_of_nonleaf`.

  In particular the rigidity statement Part II uses -- `r_0(A) = ch w_0` and
  `r_0(B) = 0` off the anchor,
  `NonTrivalentValencyTwoRigidity.localRamification_eq_zero_of_ne_anchor` -- is
  **not** needed: the count above the leaf already isolates the fold.  No
  `ContractionForest` and no `NoContractedCycle` enter.

* **§2--§3, the chain of `StablePathFacetContraction` re-run** with the weakened
  hypothesis. The chain invariant is refined to `AnchoredOn`, which also records
  the incoming stable row the chain is carried on; the only changed case of
  `StablePathFacetContraction.anchored_of_consecutive` is the one where both
  occurrences lie over `t_1`, and there the carried row is not the vanishing row
  (a retained occurrence starts the chain), so the weakened hypothesis still
  closes it. Everything downstream of
  `StablePathFacetContraction.incomingRow_injective` is then re-proved verbatim:
  `incomingRow_injective'`, `stablePath_descend_eq_iff'`, `rowEquiv'`,
  `wallRow'`, `stablePath_nonDanglingEmbedding_eq_iff'`, `wallRowIndex'`,
  `wallLabelling'`, `matrix_wallLabelling'`, `mem_path_wallLabelling_iff'` and
  `card_stablePath_wall_add_one'`. The declarations there that do **not**
  mention its hypothesis (`incomingRow`, `incomingRow_descend`,
  `incomingRow_ne_facet`, `exists_incomingRow_eq`, `punctureEquiv`,
  `punctureTargetEquiv`, `matrix_eq_sum_of_target`, `descend`,
  `consecutive_descend`, `stablePath_descend_eq_of_boundary_pair`,
  `anchored_self`, `Anchored`) are reused unchanged.

* **§4, the producers.**  `exists_wallLabelling_of_leaf_endpoint` and
  `exists_wallLabelling_of_valency_two_leaf` give the wall datum's own square
  honest labelling, the row dictionary
  `StablePath M_0 ≃ {row : StablePath M // row ≠ facet}` and the
  `AgreeOffColumn`-shaped matrix identity at a `val u = 1` wall, with the
  hypothesis list of `exists_wallLabelling_of_single_zero_row` and **no**
  no-return receipt.  `card_stablePath_wall_add_one_of_leaf_endpoint` is the
  count `|E(H_0)| = |E(H)| - 1` there.

## What is NOT proved

Every statement takes an incoming `FullDimensionalSourcePresentation` and the
Part II wall metric as hypotheses; nothing here constructs either, and nothing
here says anything about the outgoing candidate.  The hypotheses that remain
explicit in `exists_wallLabelling_of_valency_two_leaf` are exactly:

* `fd : FullDimensionalSourcePresentation data coordinate`;
* the contraction data `hc`, `hab`, `hOne`;
* `hValency`: the merged wall vertex is divalent, and `hLeaf`: `val u = 1`
  (`val v = 3` is then derived, `incidentEdges_card_eq_three_of_valency_two_leaf`);
* the wall metric `hZeroCoord`, `hPosCoord`, `hFacetZero`, `hRows` (only the
  contracted column vanishes, `facet` is the only vanishing stable row);
* `hEnd`: the vanishing row has a simple end
  (`SingleRowForest.HasSimpleEnd`), which is what supplies the contraction
  forest and the dangling compatibility.

`val u = 1` is *not* derived here: `NonTrivalentWallSetup` shows `val w_0 ≠ 1`
and `val w_0 ∈ {2, 3, 4}`, and the split of `val w_0 = 2` into `1 + 3` and
`2 + 2` is a case distinction the caller makes.  The `2 + 2` sub-case and the
`val w_0 ∈ {3, 4}` cases are handled by
`StablePathFacetContraction.noContractedReturn_of_nonleaf`.

## Consumers

The same consumers as `StablePathFacetContraction`: the `AgreeOffColumn` input
of `NonTrivalentLinkMatrix`, the K = 0 row descent of
`NonTrivalentValencyFourRows`, and the common-minor half of Part II's
`lm:change-comb-type` -- here at the `val w_0 = 2`, `val u = 1` wall,
Part II's base tree `T_∅`.
-/

namespace DraismaVargas.LocalCases.LeafFacetNoReturn

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource WallDegeneration ClassInjectivity
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree
open FullDimensionalSource PresentationDecomposition
open StablePathFacetContraction

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  No return off the facet row at a leaf endpoint -/

/-- The surviving valency never exceeds the number of incident occurrences. -/
theorem nonDanglingValency_le_card_incidentSourceEdge
    (data : GluingDatum target degree) (vertex : data.SourceVertex) :
    nonDanglingValency data vertex ≤ Fintype.card (IncidentSourceEdge data vertex) := by
  rw [← StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency data vertex]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- **Above a target leaf a fold is alone.** -/
theorem nonDanglingValency_eq_zero_of_ne_fold
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (fold other : data.SourceVertex) (hSame : other.1.1 = fold.1.1)
    (hLeaf : (GluingDatum.incidentEdges fold.1.1).card = 1)
    (hNd : nonDanglingValency data fold = 2) (hNe : other ≠ fold) :
    nonDanglingValency data other = 0 := by
  classical
  have hMinimal : data.ChangeMinimalAt fold.1.1 := fd.changeMinimal fold.1.1
  have hChange : data.targetChange fold.1.1 = 2 := by
    have h : data.targetChange fold.1.1
        + ((GluingDatum.incidentEdges fold.1.1).card : ℤ) - 3 = 0 := hMinimal
    rw [hLeaf] at h
    push_cast at h
    omega
  have hOtherRepr : (data.vertexPartition fold.1.1).repr other.1.2 = other.1.2 := by
    rw [← hSame]; exact other.2
  obtain ⟨foldBlock, hFoldBlock⟩ : ∃ block : (data.vertexPartition fold.1.1).Blocks,
      StableLocalProperties.blockVertex data fold.1.1 block = fold :=
    ⟨⟨fold.1.2, fold.2⟩, rfl⟩
  obtain ⟨otherBlock, hOtherBlock⟩ : ∃ block : (data.vertexPartition fold.1.1).Blocks,
      StableLocalProperties.blockVertex data fold.1.1 block = other := by
    refine ⟨⟨other.1.2, hOtherRepr⟩, ?_⟩
    apply Subtype.ext
    show (fold.1.1, other.1.2) = other.1
    rw [← hSame]
  have hBlockNe : otherBlock ≠ foldBlock := by
    intro hEq
    exact hNe (hOtherBlock.symm.trans (hEq.symm ▸ hFoldBlock))
  have hNonneg : ∀ item : (data.vertexPartition fold.1.1).Blocks,
      0 ≤ data.localRamification fold.1.1 item := fun item ↦
    data.localRamification_nonneg fold.1.1 (fd.valid.2 fold.1.1) item
  have hSum : (∑ item : (data.vertexPartition fold.1.1).Blocks,
      data.localRamification fold.1.1 item) = 2 := hChange
  have hDichFold := StableLocalProperties.leaf_block_dichotomy data fd.valid
    fd.noDanglingTargetFibres fold.1.1 hLeaf hMinimal foldBlock
  have hDichOther := StableLocalProperties.leaf_block_dichotomy data fd.valid
    fd.noDanglingTargetFibres fold.1.1 hLeaf hMinimal otherBlock
  rw [hFoldBlock] at hDichFold
  rw [hOtherBlock] at hDichOther
  have hFoldTwo : data.localRamification fold.1.1 foldBlock = 2 := by
    rcases hDichFold with ⟨hCard, -, -⟩ | ⟨-, -, hR, -⟩
    · exfalso
      have hLe := nonDanglingValency_le_card_incidentSourceEdge data fold
      rw [hCard, hNd] at hLe
      omega
    · exact hR
  have hPairSum : (∑ item ∈ ({otherBlock, foldBlock} :
        Finset (data.vertexPartition fold.1.1).Blocks),
      data.localRamification fold.1.1 item) ≤
      ∑ item : (data.vertexPartition fold.1.1).Blocks,
        data.localRamification fold.1.1 item :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hNonneg i)
  rw [Finset.sum_pair hBlockNe, hSum, hFoldTwo] at hPairSum
  have hOtherZero : data.localRamification fold.1.1 otherBlock = 0 := by
    have := hNonneg otherBlock
    omega
  rcases hDichOther with ⟨hCard, -, -⟩ | ⟨-, -, hR, -⟩
  · have hLe := nonDanglingValency_le_card_incidentSourceEdge data other
    rw [hCard] at hLe
    have hNeOne := NonDanglingValency.nonDanglingValency_ne_one data fd.connected other
    omega
  · rw [hOtherZero] at hR
    exact absurd hR (by norm_num)


/-- **Every surviving occurrence over a leaf edge meets the fold.** -/
theorem incident_of_leaf_fold
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a : target.V} {contracted : target.edges}
    (hcFst : (contracted : target.V × target.V).1 = a)
    (fold : data.SourceVertex) (hAbove : fold.1.1 = a)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1)
    (hNd : nonDanglingValency data fold = 2)
    (edge : data.SourceEdge) (hTarget : edge.1.1 = contracted)
    (hSurvives : ¬ IsDangling data edge) :
    Incident data edge fold := by
  have hEndTarget : ((data.sourceEnds edge).1).1.1 = fold.1.1 := by
    show (edge.1.1 : target.V × target.V).1 = fold.1.1
    rw [hTarget, hcFst, hAbove]
  have hActive : nonDanglingValency data (data.sourceEnds edge).1 ≠ 0 :=
    nonDanglingValency_ne_zero_of_incident data hSurvives (incident_left data edge)
  have hEqVertex : (data.sourceEnds edge).1 = fold := by
    by_contra hNe
    exact hActive (nonDanglingValency_eq_zero_of_ne_fold data fd fold
      ((data.sourceEnds edge).1) hEndTarget (by rw [hAbove]; exact hLeaf) hNd hNe)
  rw [← hEqVertex]
  exact incident_left data edge

/-- **The weakened no-return condition.** -/
def NoContractedReturnOffRow (data : GluingDatum target degree)
    (contracted : target.edges) (facetRow : StablePath data) : Prop :=
  ∀ vertex : data.SourceVertex, nonDanglingValency data vertex = 2 →
    ∀ first second : NonDanglingEdge data,
      first.1.1.1 = contracted → second.1.1.1 = contracted →
        Incident data first.1 vertex → Incident data second.1 vertex →
          first = second ∨ (first.stablePath = facetRow ∧ second.stablePath = facetRow)

/-- The strong no-return condition implies the weak one. -/
theorem noContractedReturnOffRow_of_noContractedReturn
    (data : GluingDatum target degree) (contracted : target.edges)
    (facetRow : StablePath data) (hNoReturn : NoContractedReturn data contracted) :
    NoContractedReturnOffRow data contracted facetRow := by
  intro vertex hNd first second hFirstT hSecondT hFirstI hSecondI
  exact Or.inl (Subtype.ext (hNoReturn vertex hNd first.1 second.1 hFirstT hSecondT
    first.2 second.2 hFirstI hSecondI))

/-- **No return off the facet row at a leaf endpoint.** -/
theorem noReturn_off_facet
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b))
    (hLeaf : (GluingDatum.incidentEdges a).card = 1)
    (hRight : 2 ≤ (GluingDatum.incidentEdges b).card)
    (facetRow : StablePath data)
    (hFacetOver : ∀ e : NonDanglingEdge data, e.stablePath = facetRow →
      e.1.1.1 = contracted) :
    NoContractedReturnOffRow data contracted facetRow := by
  intro vertex hNd first second hFirstT hSecondT hFirstI hSecondI
  by_cases hEq : first = second
  · exact Or.inl hEq
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hEq (Subtype.ext h)
  have hAt := ((incident_iff_target_mem_and_rel data first.1 vertex).mp hFirstI).1
  rw [hFirstT] at hAt
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hAt
  rw [hc] at hAt
  rcases hAt with hA | hB
  · right
    have hCons : Consecutive data first second := ⟨hEq, vertex, hFirstI, hSecondI, hNd⟩
    have hSamePath : first.stablePath = second.stablePath := stablePath_eq_of_consecutive hCons
    obtain ⟨g, hg⟩ := Quot.exists_rep facetRow
    have hgPath : g.stablePath = facetRow := hg
    have hgT : g.1.1.1 = contracted := hFacetOver g hgPath
    have hgInc : Incident data g.1 vertex :=
      incident_of_leaf_fold data fd (by rw [hc]) vertex hA.symm hLeaf hNd g.1 hgT g.2
    rcases eq_or_eq_of_nonDanglingValency_eq_two data hNd first.2 second.2 hFirstI hSecondI
      hNeVal g.2 hgInc with h | h
    · have hgf : g = first := Subtype.ext h
      rw [hgf] at hgPath
      exact ⟨hgPath, hSamePath.symm.trans hgPath⟩
    · have hgf : g = second := Subtype.ext h
      rw [hgf] at hgPath
      exact ⟨hSamePath.trans hgPath, hgPath⟩
  · exfalso
    apply hEq
    apply Subtype.ext
    refine DivalentSourceLocal.sourceEdge_eq_of_same_target data fd.danglingEdgeNoGlue
      vertex hNd ?_ first.1 second.1 first.2 second.2 hFirstI hSecondI
      (hFirstT.trans hSecondT.symm)
    exact DivalentSourceLocal.localRamification_le_one_of_nonleaf data fd.valid vertex
      (fd.changeMinimal vertex.1.1) (by rw [← hB]; exact hRight)


/-! ## 2.  The chain, re-run with the weakened hypothesis -/

section Chain

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (hCompat : DanglingCompatible data hc hab hOne)
  (facetRow : StablePath data)

/-- The chain invariant of `StablePathFacetContraction`, refined by the incoming
stable row it is carried on. -/
def AnchoredOn (row : StablePath (contractDatum data hc hab hOne))
    (base : StablePath data) (x : NonDanglingEdge data) : Prop :=
  x.stablePath = base ∧ Anchored data hc hab hOne hCompat row x

variable (hNoReturn : NoContractedReturnOffRow data contracted facetRow)

include hNoReturn in
/-- **The refined invariant is closed under stable adjacency.**  The only
changed case is the one where both occurrences lie over the contracted target
occurrence: the weakened hypothesis allows that, but only on the facet row,
which the carried row `base` is not. -/
theorem anchoredOn_of_consecutive (row : StablePath (contractDatum data hc hab hOne))
    (base : StablePath data) (hBase : base ≠ facetRow)
    (first second : NonDanglingEdge data) (hCons : Consecutive data first second)
    (hFirst : AnchoredOn data hc hab hOne hCompat row base first) :
    AnchoredOn data hc hab hOne hCompat row base second := by
  refine ⟨(stablePath_eq_of_consecutive hCons).symm.trans hFirst.1, ?_⟩
  by_cases hsT : second.1.1.1 = contracted
  · refine ⟨fun h ↦ absurd hsT h, ?_⟩
    intro _ z hz hCons2
    by_cases hfT : first.1.1.1 = contracted
    · exfalso
      rcases hNoReturn hCons.2.choose hCons.2.choose_spec.2.2 first second hfT hsT
        hCons.2.choose_spec.1 hCons.2.choose_spec.2.1 with h | ⟨hf, -⟩
      · exact hCons.1 h
      · exact hBase (hFirst.1.symm.trans hf)
    · refine Eq.trans ?_ (hFirst.2.1 hfT)
      exact stablePath_descend_eq_of_boundary_pair data hc hab hOne hCompat hsT hz hfT
        hCons2 (consecutive_symm hCons)
  · refine ⟨fun hst ↦ ?_, fun h ↦ absurd h hsT⟩
    by_cases hfT : first.1.1.1 = contracted
    · exact hFirst.2.2 hfT second hst hCons
    · rw [← stablePath_eq_of_consecutive
        (consecutive_descend data hc hab hOne hCompat hfT hst hCons)]
      exact hFirst.2.1 hfT

include hNoReturn in
/-- **Retained occurrences of one incoming stable row descend to one wall stable
row**, from the weakened hypothesis alone. -/
theorem stablePath_descend_eq_of_stablePath_eq'
    (hFacetOver : ∀ e : NonDanglingEdge data, e.stablePath = facetRow →
      e.1.1.1 = contracted)
    {x y : NonDanglingEdge data} (hx : x.1.1.1 ≠ contracted) (hy : y.1.1.1 ≠ contracted)
    (hEq : x.stablePath = y.stablePath) :
    (descend data hc hab hOne hCompat x hx).stablePath =
      (descend data hc hab hOne hCompat y hy).stablePath := by
  have hBase : x.stablePath ≠ facetRow := fun h ↦ hx (hFacetOver x h)
  have hClosed := eqvGen_iff_of_closed
    (property := AnchoredOn data hc hab hOne hCompat
      (descend data hc hab hOne hCompat x hx).stablePath x.stablePath)
    (anchoredOn_of_consecutive data hc hab hOne hCompat facetRow hNoReturn _ _ hBase)
    ((stablePath_eq_iff x y).mp hEq)
  exact ((hClosed.mp ⟨rfl, anchored_self data hc hab hOne hCompat x hx⟩).2.1 hy).symm

end Chain


/-! ## 3.  The facet dictionary under the weakened hypothesis -/

section Facet

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hNoReturn : NoContractedReturnOffRow data contracted (fd.labelling.row.symm facet))
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

include fd hZeroCoord hPosCoord hFacetZero in
/-- Every surviving occurrence of the vanishing row lies over the contracted
target occurrence, in the `StablePath`-valued shape the chain wants. -/
theorem facetRow_over_contracted (e : NonDanglingEdge data)
    (hRow : e.stablePath = fd.labelling.row.symm facet) : e.1.1.1 = contracted :=
  NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd coordinates
    facet hZeroCoord hPosCoord hFacetZero e (by rw [hRow, Equiv.apply_symm_apply])

include hNoReturn hZeroCoord hPosCoord hFacetZero in
/-- **The row map is injective**, from the weakened hypothesis. -/
theorem incomingRow_injective' :
    Function.Injective (incomingRow data fd hc hab hOne hCompat hForest) := by
  intro first second hEq
  obtain ⟨f, rfl⟩ := Quot.exists_rep first
  obtain ⟨g, rfl⟩ := Quot.exists_rep second
  have hEmb : (nonDanglingEmbedding data hCompat.1 f).stablePath =
      (nonDanglingEmbedding data hCompat.1 g).stablePath := hEq
  have hDescend := stablePath_descend_eq_of_stablePath_eq' data hc hab hOne hCompat
    (fd.labelling.row.symm facet) hNoReturn
    (facetRow_over_contracted data fd coordinates facet hZeroCoord hPosCoord hFacetZero)
    (sourceEdgeEmbedding_ne_contracted data hc hab hOne f.1)
    (sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1) hEmb
  show NonDanglingEdge.stablePath f = NonDanglingEdge.stablePath g
  calc NonDanglingEdge.stablePath f
      = NonDanglingEdge.stablePath (descend data hc hab hOne hCompat
          (nonDanglingEmbedding data hCompat.1 f)
          (sourceEdgeEmbedding_ne_contracted data hc hab hOne f.1)) :=
        congrArg NonDanglingEdge.stablePath
          (descend_nonDanglingEmbedding data hc hab hOne hCompat f _).symm
    _ = NonDanglingEdge.stablePath (descend data hc hab hOne hCompat
          (nonDanglingEmbedding data hCompat.1 g)
          (sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1)) := hDescend
    _ = NonDanglingEdge.stablePath g :=
        congrArg NonDanglingEdge.stablePath
          (descend_nonDanglingEmbedding data hc hab hOne hCompat g _)

include hNoReturn hZeroCoord hPosCoord hFacetZero in
/-- **The occurrence-level dictionary.** -/
theorem stablePath_descend_eq_iff' (e : NonDanglingEdge data) (he : e.1.1.1 ≠ contracted)
    (row : StablePath (contractDatum data hc hab hOne)) :
    (descend data hc hab hOne hCompat e he).stablePath = row ↔
      e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row := by
  constructor
  · rintro rfl
    exact (incomingRow_descend data fd hc hab hOne hCompat hForest e he).symm
  · intro hRow
    refine incomingRow_injective' data fd hc hab hOne hCompat hForest coordinates facet
      hNoReturn hZeroCoord hPosCoord hFacetZero ?_
    rw [incomingRow_descend]
    exact hRow

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The row dictionary at a one-zero-row facet.** -/
noncomputable def rowEquiv' :
    StablePath (contractDatum data hc hab hOne) ≃
      {row : StablePath data // row ≠ fd.labelling.row.symm facet} :=
  Equiv.ofBijective
    (fun wallRow ↦ ⟨incomingRow data fd hc hab hOne hCompat hForest wallRow,
      incomingRow_ne_facet data fd hc hab hOne hCompat hForest coordinates facet
        hZeroCoord hPosCoord hFacetZero wallRow⟩)
    ⟨fun first second hEq ↦ incomingRow_injective' data fd hc hab hOne hCompat hForest
        coordinates facet hNoReturn hZeroCoord hPosCoord hFacetZero
        (congrArg Subtype.val hEq),
      fun row ↦ by
        obtain ⟨wallRow, hWallRow⟩ := exists_incomingRow_eq data fd hc hab hOne hCompat
          hForest coordinates facet hRows hZeroCoord row.1 row.2
        exact ⟨wallRow, Subtype.ext hWallRow⟩⟩

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The Part II row map.** -/
noncomputable def wallRow' (row : StablePath data) :
    Option (StablePath (contractDatum data hc hab hOne)) :=
  if hFacet : row = fd.labelling.row.symm facet then none
  else some ((rowEquiv' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
    hRows hZeroCoord hPosCoord hFacetZero).symm ⟨row, hFacet⟩)

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
@[simp] theorem wallRow'_facet :
    wallRow' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn hRows
      hZeroCoord hPosCoord hFacetZero (fd.labelling.row.symm facet) = none :=
  dif_pos rfl

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
@[simp] theorem wallRow'_incomingRow (row : StablePath (contractDatum data hc hab hOne)) :
    wallRow' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn hRows
        hZeroCoord hPosCoord hFacetZero
        (incomingRow data fd hc hab hOne hCompat hForest row) = some row := by
  rw [wallRow', dif_neg (incomingRow_ne_facet data fd hc hab hOne hCompat hForest
    coordinates facet hZeroCoord hPosCoord hFacetZero row)]
  exact congrArg some (((rowEquiv' data fd hc hab hOne hCompat hForest coordinates
    facet hNoReturn hRows hZeroCoord hPosCoord hFacetZero).symm_apply_eq).mpr
    (Subtype.ext rfl))

include hNoReturn hZeroCoord hPosCoord hFacetZero in
/-- **The occurrence-set statement, on the wall datum's own occurrences.** -/
theorem stablePath_nonDanglingEmbedding_eq_iff'
    (row : StablePath (contractDatum data hc hab hOne))
    (g : NonDanglingEdge (contractDatum data hc hab hOne)) :
    g.stablePath = row ↔
      (nonDanglingEmbedding data hCompat.1 g).stablePath =
        incomingRow data fd hc hab hOne hCompat hForest row := by
  constructor
  · rintro rfl; rfl
  · intro hRow
    exact incomingRow_injective' data fd hc hab hOne hCompat hForest coordinates facet
      hNoReturn hZeroCoord hPosCoord hFacetZero hRow

/-! ### The square honest labelling of the wall datum -/

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- The wall rows, transported to the punctured index set. -/
noncomputable def wallRowIndex' :
    StablePath (contractDatum data hc hab hOne) ≃
      {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} :=
  ((rowEquiv' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn hRows
      hZeroCoord hPosCoord hFacetZero).trans
    ((Equiv.subtypeEquiv fd.labelling.row
        (fun _ ↦ not_congr (Equiv.eq_symm_apply fd.labelling.row)) :
      {row : StablePath data // row ≠ fd.labelling.row.symm facet} ≃
        {column : coordinate // column ≠ facet}))).trans
    (punctureEquiv facet (fd.labelling.targetEdge.symm contracted))

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The wall datum's own square honest stable length-matrix labelling.** -/
noncomputable def wallLabelling' :
    StableLengthMatrixLabelling (contractDatum data hc hab hOne)
      {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} where
  targetEdge := punctureTargetEquiv fd.labelling hc hab hOne
  row := wallRowIndex' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
    hRows hZeroCoord hPosCoord hFacetZero

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The wall matrix is the incoming matrix off the contracted column.** -/
theorem matrix_wallLabelling'
    (wallRowValue : StablePath (contractDatum data hc hab hOne))
    (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (wallLabelling' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
          hRows hZeroCoord hPosCoord hFacetZero).presentation
        (wallRowIndex' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
          hRows hZeroCoord hPosCoord hFacetZero wallRowValue) column =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row (incomingRow data fd hc hab hOne hCompat hForest wallRowValue))
        column.1 := by
  classical
  have hColT : fd.labelling.targetEdge column.1 ≠ contracted :=
    (not_congr (Equiv.eq_symm_apply fd.labelling.targetEdge)).mp column.2
  have hColSymm : (wallLabelling' data fd hc hab hOne hCompat hForest coordinates
      facet hNoReturn hRows hZeroCoord hPosCoord hFacetZero).targetEdge.symm
        (foldEdge hc hab hOne ⟨fd.labelling.targetEdge column.1, hColT⟩) = column := by
    rw [Equiv.symm_apply_eq]
    rfl
  calc GluingDatum.LengthMatrixPresentation.matrix
        (wallLabelling' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
          hRows hZeroCoord hPosCoord hFacetZero).presentation
        (wallRowIndex' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
          hRows hZeroCoord hPosCoord hFacetZero wallRowValue) column
      = GluingDatum.LengthMatrixPresentation.matrix
          (wallLabelling' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
            hRows hZeroCoord hPosCoord hFacetZero).presentation
          (wallRowIndex' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
            hRows hZeroCoord hPosCoord hFacetZero wallRowValue)
          ((wallLabelling' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
            hRows hZeroCoord hPosCoord hFacetZero).targetEdge.symm
              (foldEdge hc hab hOne ⟨fd.labelling.targetEdge column.1, hColT⟩)) := by
        rw [hColSymm]
    _ = ∑ edge ∈ (Finset.univ :
          Finset (contractDatum data hc hab hOne).SourceEdge).filter
            (fun edge ↦ (∃ hSurvives : ¬ IsDangling (contractDatum data hc hab hOne) edge,
                (wallLabelling' data fd hc hab hOne hCompat hForest coordinates facet
                  hNoReturn hRows hZeroCoord hPosCoord hFacetZero).row
                  (NonDanglingEdge.stablePath
                    (⟨edge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne))) =
                  wallRowIndex' data fd hc hab hOne hCompat hForest coordinates facet
                    hNoReturn hRows hZeroCoord hPosCoord hFacetZero wallRowValue) ∧
              edge.1.1 = foldEdge hc hab hOne ⟨fd.labelling.targetEdge column.1, hColT⟩),
          (1 : ℚ) / (contractDatum data hc hab hOne).sourceEdgeIndex edge :=
        matrix_eq_sum_of_target _ _ _
    _ = ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
            (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
                fd.labelling.row (NonDanglingEdge.stablePath
                  (⟨edge, hSurvives⟩ : NonDanglingEdge data)) =
                  fd.labelling.row
                    (incomingRow data fd hc hab hOne hCompat hForest wallRowValue)) ∧
              edge.1.1 = fd.labelling.targetEdge column.1),
          (1 : ℚ) / data.sourceEdgeIndex edge := by
        refine Finset.sum_nbij (sourceEdgeEmbedding data hc hab hOne) ?_ ?_ ?_ ?_
        · intro wallEdge hWallEdge
          obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (Finset.mem_filter.mp hWallEdge).2
          have hDown : NonDanglingEdge.stablePath
              (⟨wallEdge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne)) =
              wallRowValue := (wallRowIndex' data fd hc hab hOne hCompat hForest
                coordinates facet hNoReturn hRows hZeroCoord hPosCoord hFacetZero).injective
                hRow
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            ⟨(nonDanglingEmbedding data hCompat.1
              (⟨wallEdge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne))).2,
              congrArg fd.labelling.row
                ((stablePath_nonDanglingEmbedding_eq_iff' data fd hc hab hOne hCompat hForest
                  coordinates facet hNoReturn hZeroCoord hPosCoord hFacetZero wallRowValue
                  ⟨wallEdge, hSurvives⟩).mp hDown)⟩, ?_⟩
          have hVal := congrArg Prod.fst
            (IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne wallEdge)
          rw [hVal, hTarget, unfoldEdge_foldEdge]
        · exact fun first _ second _ hEq ↦
            (sourceEdgeEmbedding data hc hab hOne).injective hEq
        · intro edge hEdge
          obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ :=
            (Finset.mem_filter.mp (by exact hEdge : edge ∈ _)).2
          have hNe : edge.1.1 ≠ contracted := by rw [hTarget]; exact hColT
          obtain ⟨wallEdge, hWallEdge⟩ := exists_sourceEdgeEmbedding_eq data hc hab hOne hNe
          have hVal : edge.1.1 = unfoldEdge hc hab hOne wallEdge.1.1 := by
            rw [← hWallEdge]
            exact congrArg Prod.fst
              (IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne wallEdge)
          have hUnfold : unfoldEdge hc hab hOne wallEdge.1.1 ≠ contracted := by
            rw [← hVal]; exact hNe
          have hFold : foldEdge hc hab hOne ⟨fd.labelling.targetEdge column.1, hColT⟩ =
              wallEdge.1.1 := by
            rw [show (⟨fd.labelling.targetEdge column.1, hColT⟩ :
                {f : target.edges // f ≠ contracted}) =
              ⟨unfoldEdge hc hab hOne wallEdge.1.1, hUnfold⟩ from
                Subtype.ext (hTarget.symm.trans hVal)]
            exact foldEdge_unfoldEdge hc hab hOne wallEdge.1.1 hUnfold
          have hWallSurvives : ¬ IsDangling (contractDatum data hc hab hOne) wallEdge := by
            intro hBad
            exact hSurvives (hWallEdge ▸ hCompat.2.embedding wallEdge hBad)
          refine ⟨wallEdge, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            ⟨hWallSurvives, ?_⟩, hFold.symm⟩, hWallEdge⟩
          refine congrArg _ ((stablePath_nonDanglingEmbedding_eq_iff' data fd hc hab hOne
            hCompat hForest coordinates facet hNoReturn hZeroCoord hPosCoord hFacetZero
            wallRowValue ⟨wallEdge, hWallSurvives⟩).mpr ?_)
          refine Eq.trans ?_ (fd.labelling.row.injective hRow)
          exact congrArg NonDanglingEdge.stablePath (Subtype.ext hWallEdge)
        · intro wallEdge _
          rw [sourceEdgeIndex_sourceEdgeEmbedding]
    _ = GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
          (fd.labelling.row (incomingRow data fd hc hab hOne hCompat hForest wallRowValue))
          (fd.labelling.targetEdge.symm (fd.labelling.targetEdge column.1)) :=
        (matrix_eq_sum_of_target _ _ _).symm
    _ = _ := by rw [Equiv.symm_apply_apply]

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The occurrence list of a wall row is the retained part of the occurrence
list of its incoming row.** -/
theorem mem_path_wallLabelling_iff'
    (wallRowValue : StablePath (contractDatum data hc hab hOne))
    (edge : (contractDatum data hc hab hOne).SourceEdge) :
    edge ∈ (wallLabelling' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
        hRows hZeroCoord hPosCoord hFacetZero).path
        (wallRowIndex' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
          hRows hZeroCoord hPosCoord hFacetZero wallRowValue) ↔
      sourceEdgeEmbedding data hc hab hOne edge ∈
        fd.labelling.path (fd.labelling.row
          (incomingRow data fd hc hab hOne hCompat hForest wallRowValue)) := by
  rw [StableLengthMatrixLabelling.mem_path_iff, StableLengthMatrixLabelling.mem_path_iff]
  constructor
  · rintro ⟨hSurvives, hRow⟩
    have hDown : NonDanglingEdge.stablePath
        (⟨edge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne)) =
        wallRowValue := (wallRowIndex' data fd hc hab hOne hCompat hForest
          coordinates facet hNoReturn hRows hZeroCoord hPosCoord hFacetZero).injective hRow
    exact ⟨(nonDanglingEmbedding data hCompat.1
        (⟨edge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne))).2,
      congrArg fd.labelling.row ((stablePath_nonDanglingEmbedding_eq_iff' data fd hc hab hOne
        hCompat hForest coordinates facet hNoReturn hZeroCoord hPosCoord hFacetZero
        wallRowValue ⟨edge, hSurvives⟩).mp hDown)⟩
  · rintro ⟨hSurvives, hRow⟩
    have hWallSurvives : ¬ IsDangling (contractDatum data hc hab hOne) edge :=
      fun hBad ↦ hSurvives (hCompat.2.embedding edge hBad)
    refine ⟨hWallSurvives, congrArg _ ?_⟩
    exact (stablePath_nonDanglingEmbedding_eq_iff' data fd hc hab hOne hCompat hForest
      coordinates facet hNoReturn hZeroCoord hPosCoord hFacetZero wallRowValue
      ⟨edge, hWallSurvives⟩).mpr (fd.labelling.row.injective hRow)

include hCompat hForest hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **`|E(H₀)| = |E(H)| − 1`.** -/
theorem card_stablePath_wall_add_one' :
    Fintype.card (StablePath (contractDatum data hc hab hOne)) + 1 =
      Fintype.card (StablePath data) := by
  classical
  have hCongr := Fintype.card_congr (rowEquiv' data fd hc hab hOne hCompat hForest
    coordinates facet hNoReturn hRows hZeroCoord hPosCoord hFacetZero)
  have hCompl := Fintype.card_subtype_compl
    (p := fun row : StablePath data ↦ row = fd.labelling.row.symm facet)
  have hPoint : Fintype.card {row : StablePath data // row = fd.labelling.row.symm facet} = 1 :=
    Fintype.card_subtype_eq _
  have hPos : 0 < Fintype.card (StablePath data) :=
    Fintype.card_pos_iff.mpr ⟨fd.labelling.row.symm facet⟩
  have hSub : Fintype.card {row : StablePath data // row ≠ fd.labelling.row.symm facet} =
      Fintype.card (StablePath data) - 1 := by rw [hCompl, hPoint]
  omega

end Facet


/-! ## 4.  Producers -/

section Producer

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The Part II row dictionary and the common minor from the weakened
no-return hypothesis.**  The hypothesis list is exactly that of
`StablePathFacetContraction.exists_wallLabelling_of_noContractedReturn` with
`NoContractedReturn data contracted` replaced by
`NoContractedReturnOffRow data contracted (fd.labelling.row.symm facet)`. -/
theorem exists_wallLabelling_of_noContractedReturnOffRow
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hNoReturn : NoContractedReturnOffRow data contracted (fd.labelling.row.symm facet))
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm facet))
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    ∃ labelling : StableLengthMatrixLabelling (contractDatum data hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted},
      ∃ rowDictionary : StablePath (contractDatum data hc hab hOne) ≃
        {row : StablePath data // row ≠ fd.labelling.row.symm facet},
        ∀ (wallRowValue : StablePath (contractDatum data hc hab hOne))
          (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix labelling.presentation
              (labelling.row wallRowValue) column =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (rowDictionary wallRowValue).1) column.1 := by
  have hForest := SingleRowForest.contractionForest_of_single_row fd.labelling coordinates
    (NonTrivalentUniqueFourValent.coordinates_nonneg data fd coordinates hZeroCoord hPosCoord)
    facet hRows hEnd hc hZeroCoord
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne
    hForest
  exact ⟨wallLabelling' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn
      hRows hZeroCoord hPosCoord hFacetZero,
    rowEquiv' data fd hc hab hOne hCompat hForest coordinates facet hNoReturn hRows
      hZeroCoord hPosCoord hFacetZero,
    fun wallRowValue column ↦ matrix_wallLabelling' data fd hc hab hOne hCompat hForest
      coordinates facet hNoReturn hRows hZeroCoord hPosCoord hFacetZero wallRowValue column⟩

/-- **The row dictionary at a Part II open facet whose contracted target
occurrence has a leaf endpoint.**  Hypotheses: those of
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row` -- the
incoming full-dimensional cover, the wall metric, the single vanishing stable
row and its simple end -- together with `val u = 1` and `val v ≥ 2`.  No
no-return receipt is supplied: it is discharged by `noReturn_off_facet`. -/
theorem exists_wallLabelling_of_leaf_endpoint
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1)
    (hRight : 2 ≤ (GluingDatum.incidentEdges b).card)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm facet))
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    ∃ labelling : StableLengthMatrixLabelling (contractDatum data hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted},
      ∃ rowDictionary : StablePath (contractDatum data hc hab hOne) ≃
        {row : StablePath data // row ≠ fd.labelling.row.symm facet},
        ∀ (wallRowValue : StablePath (contractDatum data hc hab hOne))
          (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix labelling.presentation
              (labelling.row wallRowValue) column =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (rowDictionary wallRowValue).1) column.1 :=
  exists_wallLabelling_of_noContractedReturnOffRow data fd hc hab hOne coordinates facet
    (noReturn_off_facet data fd hc hLeaf hRight (fd.labelling.row.symm facet)
      (fun e hRow ↦ NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd
        coordinates facet hZeroCoord hPosCoord hFacetZero e
        (by rw [hRow, Equiv.apply_symm_apply])))
    hRows hEnd hZeroCoord hPosCoord hFacetZero

/-- **`val(u) = 1` at a valency-two wall forces `val(v) = 3`.** -/
theorem incidentEdges_card_eq_three_of_valency_two_leaf
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hValency : (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 2)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    (GluingDatum.incidentEdges b).card = 3 := by
  obtain ⟨hSum, -, -, -, -, -, -⟩ :=
    WallProgress.endpoints_of_contraction data hc hab hOne fd.valid fd.changeMinimal
  rw [hValency, hLeaf] at hSum
  omega

/-- **The `T_∅` sub-case: the whole dictionary at a `val(u) = 1, val(v) = 3`
valency-two wall, receipt-free apart from the wall metric.** -/
theorem exists_wallLabelling_of_valency_two_leaf
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hValency : (GluingDatum.incidentEdges
      (target := GraphContraction.contract target hab hOne) ⟨a, hab⟩).card = 2)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm facet))
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    ∃ labelling : StableLengthMatrixLabelling (contractDatum data hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted},
      ∃ rowDictionary : StablePath (contractDatum data hc hab hOne) ≃
        {row : StablePath data // row ≠ fd.labelling.row.symm facet},
        ∀ (wallRowValue : StablePath (contractDatum data hc hab hOne))
          (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix labelling.presentation
              (labelling.row wallRowValue) column =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (rowDictionary wallRowValue).1) column.1 :=
  exists_wallLabelling_of_leaf_endpoint data fd hc hab hOne hLeaf
    (by rw [incidentEdges_card_eq_three_of_valency_two_leaf data fd hc hab hOne hValency hLeaf]
        norm_num)
    coordinates facet hRows hEnd hZeroCoord hPosCoord hFacetZero

end Producer


/-! ## 5.  Non-vacuity -/

section NonVacuity

/-- A one-edge target tree. -/
def oneEdgeTarget : CFGraph where
  V := Fin 2
  edges := {((0 : Fin 2), (1 : Fin 2))}
  loopless := by decide

/-- Its unique target occurrence. -/
def oneEdgeTargetEdge : oneEdgeTarget.edges :=
  ⟨((0 : Fin 2), (1 : Fin 2)), ⟨0, by decide⟩⟩

/-- The degree-one cover of any target tree. -/
def unitDatum (base : CFGraph) : GluingDatum base 1 where
  degree_pos := Nat.one_pos
  vertexPartition := fun _ ↦ SheetPartition.discrete 1
  edgePartition := fun _ ↦ SheetPartition.discrete 1
  refines_left := fun _ ↦ SheetPartition.Refines.refl _
  refines_right := fun _ ↦ SheetPartition.Refines.refl _

/-- **Unconditional non-vacuity.**  A degree-one cover has exactly one
occurrence over each target occurrence, so no return is possible at all. -/
theorem noContractedReturnOffRow_of_degree_one
    (data : GluingDatum target 1) (contracted : target.edges)
    (facetRow : StablePath data) :
    NoContractedReturnOffRow data contracted facetRow := by
  intro vertex hNd first second hFirstT hSecondT hFirstI hSecondI
  refine Or.inl (Subtype.ext (Subtype.ext ?_))
  exact Prod.ext (hFirstT.trans hSecondT.symm) (Subsingleton.elim _ _)

/-- **A literal inhabitant of the weakened no-return condition**: the
degree-one cover of the one-edge target, at its unique target occurrence and
at every stable row. -/
theorem noContractedReturnOffRow_unitDatum
    (facetRow : StablePath (unitDatum oneEdgeTarget)) :
    NoContractedReturnOffRow (unitDatum oneEdgeTarget) oneEdgeTargetEdge facetRow :=
  noContractedReturnOffRow_of_degree_one _ _ _

/-- **Non-vacuity of the chain invariant.**  A retained occurrence is anchored
at its own wall row and at its own incoming row. -/
theorem anchoredOn_self (data : GluingDatum target degree) {a b : target.V}
    {contracted : target.edges} (hc : (contracted : target.V × target.V) = (a, b))
    (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (hCompat : DanglingCompatible data hc hab hOne)
    (e : NonDanglingEdge data) (he : e.1.1.1 ≠ contracted) :
    AnchoredOn data hc hab hOne hCompat
      (descend data hc hab hOne hCompat e he).stablePath e.stablePath e :=
  ⟨rfl, anchored_self data hc hab hOne hCompat e he⟩

end NonVacuity

/-! ## 6.  The count at a leaf wall -/

section Count

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`|E(H₀)| = |E(H)| − 1` at a leaf-endpoint facet**, with no no-return
receipt. -/
theorem card_stablePath_wall_add_one_of_leaf_endpoint
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1)
    (hRight : 2 ≤ (GluingDatum.incidentEdges b).card)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm facet))
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    Fintype.card (StablePath (contractDatum data hc hab hOne)) + 1 =
      Fintype.card (StablePath data) := by
  have hForest := SingleRowForest.contractionForest_of_single_row fd.labelling coordinates
    (NonTrivalentUniqueFourValent.coordinates_nonneg data fd coordinates hZeroCoord hPosCoord)
    facet hRows hEnd hc hZeroCoord
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne
    hForest
  exact card_stablePath_wall_add_one' data fd hc hab hOne hCompat hForest coordinates facet
    (noReturn_off_facet data fd hc hLeaf hRight (fd.labelling.row.symm facet)
      (fun e hRow ↦ NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd
        coordinates facet hZeroCoord hPosCoord hFacetZero e
        (by rw [hRow, Equiv.apply_symm_apply])))
    hRows hZeroCoord hPosCoord hFacetZero

end Count

end DraismaVargas.LocalCases.LeafFacetNoReturn
