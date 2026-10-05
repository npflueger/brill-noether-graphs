module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoRowDictionary
public import DraismaVargas.LocalCases.LeafFacetNoReturn

@[expose] public section

/-!
# The `1+3` sub-case of the valency-two common-minor identity, and the dispatcher

Source: Vargas, Part II, arXiv:2609.09109, Section 5.1 (rigidity above `w_0`, and
`lm:change-comb-type`: the wall matrix as the common minor `A_{\varphi_0}`),
Section 5.4 (the valency-two candidate), and the `val(u) = 1` case of
`lemma-above-w0` (the `1+3` sub-case, formalized in `LeafFacetNoReturn`).

`NonTrivalentValencyTwoRowDictionary` proves the valency-two `AgreeOffColumn` /
common-minor identity with `hNoReturn : NoContractedReturn` an explicit
hypothesis.  At a two-valent wall `val(w_0) = val(u) + val(v) - 2 = 2` splits
into `2 + 2` (`noContractedReturn_of_nonleaf` applies) and `1 + 3` (`u` a leaf,
where `NoContractedReturn` is genuinely false and `LeafFacetNoReturn` re-runs
the chain under the weaker `NoContractedReturnOffRow`).  This module covers the
`1 + 3` case: it composes the chart-labelling machinery of
`NonTrivalentValencyTwoRowDictionary` with the primed wall dictionary of
`LeafFacetNoReturn` to get the `1 + 3` common-minor identity, and then
dispatches the full valency-two headline (`val(w_0) = 2`, no no-return
hypothesis) over the case split on which endpoint (if either) is a leaf.

## What is proved

* **`matrix_chartLabelling_eq_incoming_leaf`**:
  `NonTrivalentValencyTwoRowDictionary.matrix_chartLabelling_eq_incoming`,
  verbatim, with the `.trans` target
  `StablePathFacetContraction.matrix_wallLabelling` replaced by
  `LeafFacetNoReturn.matrix_wallLabelling'` and `NoContractedReturn` replaced
  by `NoContractedReturnOffRow`.  No new proof: `matrix_chartLabelling`
  (`NonTrivalentValencyTwoRowDictionary`, §3) is already fully generic in the
  wall datum's own honest labelling `labelling₀ : StableLengthMatrixLabelling
  (contractDatum cover hc hab hOne) coordinate₀` -- it does not care whether
  that labelling was built from `StablePathFacetContraction.wallLabelling`
  (needing `NoContractedReturn`) or `LeafFacetNoReturn.wallLabelling'`
  (needing the weaker `NoContractedReturnOffRow`); both live at the exact same
  type, the common minor `A_{\varphi_0}`.  So this theorem is literally
  `matrix_chartLabelling` composed with `matrix_wallLabelling'` instead of
  `matrix_wallLabelling`; there is no separate "compatibility of the two
  chart matrices" lemma to prove.

* **Two "no-return-off-row" witnesses**, one at each possible leaf side.  Part
  II's own account (and `LeafFacetNoReturn`) treats `u = a`, the first
  coordinate of `hc : (contracted : V × V) = (a, b)`, as the leaf.  Since
  `contracted` is a fixed multiset occurrence carrying one baked-in order,
  `hc` cannot be "swapped": if the leaf is instead `b` (the second
  coordinate), the whole derivation of `NoContractedReturnOffRow` from
  `leaf_block_dichotomy` needs the mirror image, using `(sourceEnds edge).2`
  in place of `.1` and `incident_right` in place of `incident_left`.  Nothing
  downstream of `NoContractedReturnOffRow` (§3 of `LeafFacetNoReturn`:
  `wallLabelling'`, `wallRowIndex'`, `matrix_wallLabelling'`, ...) mentions
  `a`/`b` at all, so only this one derivation needs a genuine mirror, not the
  whole chain re-run:
  * `noContractedReturnOffRow_of_leaf` reuses `LeafFacetNoReturn.noReturn_off_facet`
    unchanged (`u = a` is the leaf), deriving its `2 ≤ card b` hypothesis from
    the two-valent star instead of taking it as a hypothesis.
  * `incident_of_leaf_fold_right` and `noReturn_off_facet_right` are the
    mirror images of `LeafFacetNoReturn.incident_of_leaf_fold` /
    `.noReturn_off_facet`, proved here by the identical argument with `.1`
    and `.2` (equivalently `incident_left`/`incident_right`) exchanged; then
    `noContractedReturnOffRow_of_leaf_right` packages it exactly as the `a`
    case, for `v = b` a leaf.

* **`exists_matrix_chartLabelling_eq_incoming_leaf`** /
  **`exists_matrix_chartLabelling_eq_incoming_leaf_right`**: the actual-wall
  `1 + 3` headline, at each leaf side, composing
  `NonTrivalentValencyTwoRowEquiv.exists_rowEquiv_of_wall_metric` with
  `matrix_chartLabelling_eq_incoming_leaf` exactly as
  `NonTrivalentValencyTwoRowDictionary.exists_matrix_chartLabelling_eq_incoming`
  composes with the unprimed
  identity, with `hNoReturn` replaced by `hLeaf : (incidentEdges a).card = 1`
  (resp. `b`) and the `2 ≤` bound on the other side derived from the incoming
  two-valent star `wallStar.card_incidentEdges` together with the endpoint
  sum identity `WallProgress.endpoints_of_contraction`.  No `hEnd`/simple-end
  hypothesis is needed here: `hForest` stays an explicit hypothesis (as in
  the headline of `NonTrivalentValencyTwoRowDictionary`), so there is nothing
  to derive it from.

* **`exists_matrix_chartLabelling_eq_incoming_two`**: the dispatcher -- the
  full valency-two headline, with **no** no-return hypothesis at all.  It
  case-splits on `(incidentEdges a).card = 1`, then `(incidentEdges b).card =
  1`; the remaining case has `2 ≤ (incidentEdges a).card` and
  `2 ≤ (incidentEdges b).card` (both endpoints non-leaf, `2 + 2`) directly
  from `1 ≤` (`WallProgress.endpoints_of_contraction`) and `≠ 1`, and is
  routed through `StablePathFacetContraction.noContractedReturn_of_nonleaf`
  into `NonTrivalentValencyTwoRowDictionary.exists_matrix_chartLabelling_eq_incoming`.
  Since the three branches build the required "wall datum's own honest
  labelling" from three different underlying constructions
  (`StablePathFacetContraction.wallLabelling`, `LeafFacetNoReturn.wallLabelling'`,
  and its right-mirror), the conclusion existentially quantifies over that
  labelling (and its row map) instead of naming one of the three
  constructions, matching the shape `LeafFacetNoReturn.exists_wallLabelling_of_noContractedReturnOffRow`
  already uses for the same reason; `matrix_chartLabelling` (fully generic in
  that labelling) supplies the chart identity uniformly across all three
  branches.

## What is not proved here

Exactly the hypotheses named above remain explicit: the incoming
`FullDimensionalSourcePresentation`, the contraction data `hc, hab, hOne`,
the actual contraction forest `hForest`, the incoming two-valent star
`wallStar`, and the Part II wall metric (`hRows, hZeroCoord, hPosCoord,
hFacetZero`).  `DanglingCompatible` is derived from `hForest`, as in
`NonTrivalentValencyTwoRowDictionary` and `LeafFacetNoReturn`.  Nothing here
constructs a `FullDimensionalSourcePresentation`, a `ContractionForest`, or a
`TwoStar`; those stay the caller's hypotheses.

## Consumers

The boundary dispatcher for Part II case `{v2-nd4}` at a two-valent wall, and
the nonsingularity and exit statements built on `NonTrivalentLinkMatrix`, whose
`AgreeOffColumn` input is available unconditionally in `val(w_0) = 2`, via
`exists_matrix_chartLabelling_eq_incoming_two`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoLeafDictionary

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoDescent
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowDictionary
open DraismaVargas.LocalCases.LeafFacetNoReturn
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.ClassInjectivity

noncomputable local instance {target : CFGraph} : DecidableEq target.edges := Classical.decEq _

/-! ## 0.  The mirror of `LeafFacetNoReturn`'s leaf-fold argument, at `v = b` -/

section RightLeaf

variable {target : CFGraph} {degree : ℕ}

/-- **Every surviving occurrence over a leaf edge at the second coordinate
meets the fold.**  The mirror of `LeafFacetNoReturn.incident_of_leaf_fold`,
with `(data.sourceEnds edge).1` / `incident_left` replaced by `.2` /
`incident_right`. -/
theorem incident_of_leaf_fold_right
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {b : target.V} {contracted : target.edges}
    (hcSnd : (contracted : target.V × target.V).2 = b)
    (fold : data.SourceVertex) (hAbove : fold.1.1 = b)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1)
    (hNd : nonDanglingValency data fold = 2)
    (edge : data.SourceEdge) (hTarget : edge.1.1 = contracted)
    (hSurvives : ¬ IsDangling data edge) :
    Incident data edge fold := by
  have hEndTarget : ((data.sourceEnds edge).2).1.1 = fold.1.1 := by
    show (edge.1.1 : target.V × target.V).2 = fold.1.1
    rw [hTarget, hcSnd, hAbove]
  have hActive : nonDanglingValency data (data.sourceEnds edge).2 ≠ 0 :=
    nonDanglingValency_ne_zero_of_incident data hSurvives (incident_right data edge)
  have hEqVertex : (data.sourceEnds edge).2 = fold := by
    by_contra hNe
    exact hActive (nonDanglingValency_eq_zero_of_ne_fold data fd fold
      ((data.sourceEnds edge).2) hEndTarget (by rw [hAbove]; exact hLeaf) hNd hNe)
  rw [← hEqVertex]
  exact incident_right data edge

/-- **No return off the facet row at a leaf endpoint `v = b`.**  The mirror of
`LeafFacetNoReturn.noReturn_off_facet`, with the two cases of
`rcases hAt with hA | hB` exchanged: the exfalso (rigidity) branch now uses
`hLeft : 2 ≤ card a`, and the leaf-fold branch uses `hLeaf : card b = 1`. -/
theorem noReturn_off_facet_right
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b))
    (hLeft : 2 ≤ (GluingDatum.incidentEdges a).card)
    (hLeaf : (GluingDatum.incidentEdges b).card = 1)
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
  · exfalso
    apply hEq
    apply Subtype.ext
    refine DivalentSourceLocal.sourceEdge_eq_of_same_target data fd.danglingEdgeNoGlue
      vertex hNd ?_ first.1 second.1 first.2 second.2 hFirstI hSecondI
      (hFirstT.trans hSecondT.symm)
    exact DivalentSourceLocal.localRamification_le_one_of_nonleaf data fd.valid vertex
      (fd.changeMinimal vertex.1.1) (by rw [← hA]; exact hLeft)
  · right
    have hCons : Consecutive data first second := ⟨hEq, vertex, hFirstI, hSecondI, hNd⟩
    have hSamePath : first.stablePath = second.stablePath := stablePath_eq_of_consecutive hCons
    obtain ⟨g, hg⟩ := Quot.exists_rep facetRow
    have hgPath : g.stablePath = facetRow := hg
    have hgT : g.1.1.1 = contracted := hFacetOver g hgPath
    have hgInc : Incident data g.1 vertex :=
      incident_of_leaf_fold_right data fd (by rw [hc]) vertex hB.symm hLeaf hNd g.1 hgT g.2
    rcases eq_or_eq_of_nonDanglingValency_eq_two data hNd first.2 second.2 hFirstI hSecondI
      hNeVal g.2 hgInc with h | h
    · have hgf : g = first := Subtype.ext h
      rw [hgf] at hgPath
      exact ⟨hgPath, hSamePath.symm.trans hgPath⟩
    · have hgf : g = second := Subtype.ext h
      rw [hgf] at hgPath
      exact ⟨hSamePath.trans hgPath, hgPath⟩

end RightLeaf

/-! ## 1.  The candidate's matrix off the new column, at the `1 + 3` sub-case -/

section AgreeOffColumnLeaf

variable {targetIn : CFGraph} {deg : ℕ} {chartIndex : Type*} [Fintype chartIndex]
  [DecidableEq chartIndex]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover chartIndex)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hCompat : DanglingCompatible cover hc hab hOne)
  (hForest : ContractionForest cover a b contracted)
  (coordinates : chartIndex → ℚ) (facet : chartIndex)
  (hNoReturn : NoContractedReturnOffRow cover contracted (fd.labelling.row.symm facet))
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  {wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (selBlk : Prescribed.Selection (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hValid : (contractDatum cover hc hab hOne).Valid)
  (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlk)

/-- **The outgoing honest matrix equals the incoming one off the contracted
column, at the `1 + 3` sub-case.**
`NonTrivalentValencyTwoRowDictionary.matrix_chartLabelling_eq_incoming`
verbatim, with `StablePathFacetContraction.wallLabelling` / `.wallRowIndex` /
`.matrix_wallLabelling` (needing `NoContractedReturn`) replaced by
`LeafFacetNoReturn.wallLabelling'` / `.wallRowIndex'` / `.matrix_wallLabelling'`
(needing the weaker `NoContractedReturnOffRow`).  `matrix_chartLabelling`
is fully generic in the wall datum's own labelling, so no new proof is
needed: this is the same composition with the `.trans` target swapped. -/
theorem matrix_chartLabelling_eq_incoming_leaf
    (chart : Option {column : chartIndex //
        column ≠ fd.labelling.targetEdge.symm contracted} ≃ chartIndex)
    (p : StablePath (contractDatum cover hc hab hOne))
    (column : {column : chartIndex //
      column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling src selBlk hValid hOrd
          (wallLabelling' cover fd hc hab hOne hCompat hForest coordinates facet hNoReturn
            hRows hZeroCoord hPosCoord hFacetZero)
          chart).presentation
        (chart (some (wallRowIndex' cover fd hc hab hOne hCompat hForest coordinates facet
          hNoReturn hRows hZeroCoord hPosCoord hFacetZero p)))
        (chart (some column)) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row (incomingRow cover fd hc hab hOne hCompat hForest p))
        column.1 :=
  (matrix_chartLabelling src selBlk hValid hOrd
    (wallLabelling' cover fd hc hab hOne hCompat hForest coordinates facet hNoReturn hRows
      hZeroCoord hPosCoord hFacetZero) chart p column).trans
    (matrix_wallLabelling' cover fd hc hab hOne hCompat hForest coordinates facet hNoReturn
      hRows hZeroCoord hPosCoord hFacetZero p column)

end AgreeOffColumnLeaf

/-! ## 2.  The actual-wall corollary at each leaf side -/

section ActualWallLeaf

variable {targetIn : CFGraph} {deg : ℕ} {chartIndex : Type*} [Fintype chartIndex]
  [DecidableEq chartIndex]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover chartIndex)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩)
  (coordinates : chartIndex → ℚ) (facet : chartIndex)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  (chart : Option {column : chartIndex //
      column ≠ fd.labelling.targetEdge.symm contracted} ≃ chartIndex)

include cover fd hc hab hOne wallStar in
/-- **`val(v) ≥ 2` from `val(u) = 1` and the incoming two-valent star.**  The
endpoint sum identity `WallProgress.endpoints_of_contraction` plus the star's
own count `wallStar.card_incidentEdges` (`val(w_0) = 2`). -/
theorem right_card_ge_two_of_left_leaf
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    2 ≤ (GluingDatum.incidentEdges b).card := by
  have hSum := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
    fd.changeMinimal).1
  have hValency := wallStar.card_incidentEdges
  omega

include cover fd hc hab hOne wallStar in
/-- **`val(u) ≥ 2` from `val(v) = 1` and the incoming two-valent star.** -/
theorem left_card_ge_two_of_right_leaf
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    2 ≤ (GluingDatum.incidentEdges a).card := by
  have hSum := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
    fd.changeMinimal).1
  have hValency := wallStar.card_incidentEdges
  omega

include hc hab hOne wallStar coordinates hZeroCoord hPosCoord hFacetZero in
/-- **The weakened no-return witness, `u = a` a leaf.** -/
theorem noContractedReturnOffRow_of_leaf
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    NoContractedReturnOffRow cover contracted (fd.labelling.row.symm facet) :=
  noReturn_off_facet cover fd hc hLeaf
    (right_card_ge_two_of_left_leaf cover fd hc hab hOne wallStar hLeaf)
    (fd.labelling.row.symm facet)
    (fun e hRow ↦ NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet cover fd
      coordinates facet hZeroCoord hPosCoord hFacetZero e
      (by rw [hRow, Equiv.apply_symm_apply]))

include hc hab hOne wallStar coordinates hZeroCoord hPosCoord hFacetZero in
/-- **The weakened no-return witness, `v = b` a leaf.** -/
theorem noContractedReturnOffRow_of_leaf_right
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    NoContractedReturnOffRow cover contracted (fd.labelling.row.symm facet) :=
  noReturn_off_facet_right cover fd hc
    (left_card_ge_two_of_right_leaf cover fd hc hab hOne wallStar hLeaf) hLeaf
    (fd.labelling.row.symm facet)
    (fun e hRow ↦ NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet cover fd
      coordinates facet hZeroCoord hPosCoord hFacetZero e
      (by rw [hRow, Equiv.apply_symm_apply]))

/-- **The `1 + 3` actual-wall headline, `u = a` a leaf.**
`NonTrivalentValencyTwoRowDictionary.exists_matrix_chartLabelling_eq_incoming`,
with `hNoReturn` replaced by `hLeaf : (incidentEdges a).card = 1`; no
`nd(A) = 4`, type, row-equivalence or trivalence hypothesis remains, exactly as
in that headline. -/
theorem exists_matrix_chartLabelling_eq_incoming_leaf
    (hLeaf : (GluingDatum.incidentEdges a).card = 1) :
    ∃ (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
      (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock)
      (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
        ∀ sel : Prescribed.Selection (contractDatum cover hc hab hOne)
            wallStar anchorBlock,
        (Prescribed.validCandidate sel).datum.Valid ∧
        genus (Prescribed.validCandidate sel).datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        ∀ (p : StablePath (contractDatum cover hc hab hOne))
          (column : {column : chartIndex //
            column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix
              (chartLabelling src sel
                (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
                (wallLabelling' cover fd hc hab hOne
                  (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                    hForest)
                  hForest coordinates facet
                  (noContractedReturnOffRow_of_leaf cover fd hc hab hOne wallStar coordinates
                    facet hZeroCoord hPosCoord hFacetZero hLeaf)
                  hRows hZeroCoord hPosCoord hFacetZero)
                chart).presentation
              (chart (some (wallRowIndex' cover fd hc hab hOne
                (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                  hForest)
                hForest coordinates facet
                (noContractedReturnOffRow_of_leaf cover fd hc hab hOne wallStar coordinates facet
                  hZeroCoord hPosCoord hFacetZero hLeaf)
                hRows hZeroCoord hPosCoord hFacetZero p)))
              (chart (some column)) =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (incomingRow cover fd hc hab hOne
                (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                  hForest)
                hForest p))
              column.1 := by
  obtain ⟨anchorBlock, src, hNd, hSelection⟩ :=
    exists_rowEquiv_of_wall_metric cover fd hc hab hOne hForest wallStar coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero
  obtain ⟨-, -, hOrd, -, -⟩ :=
    hSelection (NonTrivalentValencyTwoCandidate.Prescribed.Selection.default src)
  refine ⟨anchorBlock, src, hOrd, hNd, fun sel ↦
    ⟨(hSelection sel).1, (hSelection sel).2.1, fun p column ↦ ?_⟩⟩
  exact matrix_chartLabelling_eq_incoming_leaf cover fd hc hab hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
    hForest coordinates facet
    (noContractedReturnOffRow_of_leaf cover fd hc hab hOne wallStar coordinates facet
      hZeroCoord hPosCoord hFacetZero hLeaf)
    hRows hZeroCoord hPosCoord hFacetZero src sel
    (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd chart p column

/-- **The `1 + 3` actual-wall headline, `v = b` a leaf.**  The mirror of
`exists_matrix_chartLabelling_eq_incoming_leaf`. -/
theorem exists_matrix_chartLabelling_eq_incoming_leaf_right
    (hLeaf : (GluingDatum.incidentEdges b).card = 1) :
    ∃ (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
      (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock)
      (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
        ∀ sel : Prescribed.Selection (contractDatum cover hc hab hOne)
            wallStar anchorBlock,
        (Prescribed.validCandidate sel).datum.Valid ∧
        genus (Prescribed.validCandidate sel).datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        ∀ (p : StablePath (contractDatum cover hc hab hOne))
          (column : {column : chartIndex //
            column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix
              (chartLabelling src sel
                (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
                (wallLabelling' cover fd hc hab hOne
                  (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                    hForest)
                  hForest coordinates facet
                  (noContractedReturnOffRow_of_leaf_right cover fd hc hab hOne wallStar
                    coordinates facet hZeroCoord hPosCoord hFacetZero hLeaf)
                  hRows hZeroCoord hPosCoord hFacetZero)
                chart).presentation
              (chart (some (wallRowIndex' cover fd hc hab hOne
                (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                  hForest)
                hForest coordinates facet
                (noContractedReturnOffRow_of_leaf_right cover fd hc hab hOne wallStar coordinates
                  facet hZeroCoord hPosCoord hFacetZero hLeaf)
                hRows hZeroCoord hPosCoord hFacetZero p)))
              (chart (some column)) =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (incomingRow cover fd hc hab hOne
                (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                  hForest)
                hForest p))
              column.1 := by
  obtain ⟨anchorBlock, src, hNd, hSelection⟩ :=
    exists_rowEquiv_of_wall_metric cover fd hc hab hOne hForest wallStar coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero
  obtain ⟨-, -, hOrd, -, -⟩ :=
    hSelection (NonTrivalentValencyTwoCandidate.Prescribed.Selection.default src)
  refine ⟨anchorBlock, src, hOrd, hNd, fun sel ↦
    ⟨(hSelection sel).1, (hSelection sel).2.1, fun p column ↦ ?_⟩⟩
  exact matrix_chartLabelling_eq_incoming_leaf cover fd hc hab hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
    hForest coordinates facet
    (noContractedReturnOffRow_of_leaf_right cover fd hc hab hOne wallStar coordinates facet
      hZeroCoord hPosCoord hFacetZero hLeaf)
    hRows hZeroCoord hPosCoord hFacetZero src sel
    (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd chart p column

end ActualWallLeaf

/-! ## 3.  The dispatcher: the full valency-two headline, no no-return hypothesis -/

section Dispatcher

variable {targetIn : CFGraph} {deg : ℕ} {chartIndex : Type*} [Fintype chartIndex]
  [DecidableEq chartIndex]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover chartIndex)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩)
  (coordinates : chartIndex → ℚ) (facet : chartIndex)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)
  (chart : Option {column : chartIndex //
      column ≠ fd.labelling.targetEdge.symm contracted} ≃ chartIndex)

include coordinates facet hRows hZeroCoord hPosCoord hFacetZero in
/-- **The valency-two headline at an actual wall, with no no-return
hypothesis.**  `val(w_0) = val(u) + val(v) - 2 = 2` (from `wallStar`) forces
`val(u), val(v) ∈ {1, 2, 3}` with `val(u) + val(v) = 4`: either both are `2`
(the `2 + 2` sub-case, routed through
`StablePathFacetContraction.noContractedReturn_of_nonleaf` into
`NonTrivalentValencyTwoRowDictionary.exists_matrix_chartLabelling_eq_incoming`),
or one of them is `1` (the `1 + 3` sub-case, routed through
`exists_matrix_chartLabelling_eq_incoming_leaf` or its mirror).  Since the
three branches build the wall datum's own honest labelling from three
different underlying constructions, the conclusion existentially quantifies
over that labelling and its row map, exactly as
`LeafFacetNoReturn.exists_wallLabelling_of_noContractedReturnOffRow` does;
`NonTrivalentValencyTwoRowDictionary.matrix_chartLabelling` (fully generic in
that labelling) supplies the outer
chart identity uniformly in all three branches. -/
theorem exists_matrix_chartLabelling_eq_incoming_two :
    ∃ (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
      (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock)
      (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock)
      (labelling₀ : StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
        {column : chartIndex // column ≠ fd.labelling.targetEdge.symm contracted}),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
        ∀ sel : Prescribed.Selection (contractDatum cover hc hab hOne)
            wallStar anchorBlock,
        (Prescribed.validCandidate sel).datum.Valid ∧
        genus (Prescribed.validCandidate sel).datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        ∀ (p : StablePath (contractDatum cover hc hab hOne))
          (column : {column : chartIndex //
            column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix
              (chartLabelling src sel
                (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
                labelling₀ chart).presentation
              (chart (some (labelling₀.row p)))
              (chart (some column)) =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (incomingRow cover fd hc hab hOne
                (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                  hForest)
                hForest p))
              column.1 := by
  classical
  by_cases hA : (GluingDatum.incidentEdges a).card = 1
  · obtain ⟨anchorBlock, src, hOrd, hNd, hMatrix⟩ :=
      exists_matrix_chartLabelling_eq_incoming_leaf cover fd hc hab hOne hForest wallStar
        coordinates facet hRows hZeroCoord hPosCoord hFacetZero chart hA
    exact ⟨anchorBlock, src, hOrd,
      wallLabelling' cover fd hc hab hOne
        (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
        hForest coordinates facet
        (noContractedReturnOffRow_of_leaf cover fd hc hab hOne wallStar coordinates facet
          hZeroCoord hPosCoord hFacetZero hA)
        hRows hZeroCoord hPosCoord hFacetZero,
      hNd, hMatrix⟩
  · by_cases hB : (GluingDatum.incidentEdges b).card = 1
    · obtain ⟨anchorBlock, src, hOrd, hNd, hMatrix⟩ :=
        exists_matrix_chartLabelling_eq_incoming_leaf_right cover fd hc hab hOne hForest wallStar
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero chart hB
      exact ⟨anchorBlock, src, hOrd,
        wallLabelling' cover fd hc hab hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
          hForest coordinates facet
          (noContractedReturnOffRow_of_leaf_right cover fd hc hab hOne wallStar coordinates facet
            hZeroCoord hPosCoord hFacetZero hB)
          hRows hZeroCoord hPosCoord hFacetZero,
        hNd, hMatrix⟩
    · have hLeftMem := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
        fd.changeMinimal).2.1
      have hRightMem := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
        fd.changeMinimal).2.2.2.1
      have hLeft : 2 ≤ (GluingDatum.incidentEdges a).card := by omega
      have hRight : 2 ≤ (GluingDatum.incidentEdges b).card := by omega
      have hNoReturn : NoContractedReturn cover contracted :=
        StablePathFacetContraction.noContractedReturn_of_nonleaf cover fd hc hLeft hRight
      have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
        hForest
      obtain ⟨anchorBlock, src, hOrd, hNd, hMatrix⟩ :=
        NonTrivalentValencyTwoRowDictionary.exists_matrix_chartLabelling_eq_incoming cover fd
          hc hab hOne hForest hNoReturn wallStar coordinates facet hRows hZeroCoord hPosCoord
          hFacetZero chart
      exact ⟨anchorBlock, src, hOrd,
        StablePathFacetContraction.wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero,
        hNd, hMatrix⟩

end Dispatcher

end DraismaVargas.LocalCases.NonTrivalentValencyTwoLeafDictionary
