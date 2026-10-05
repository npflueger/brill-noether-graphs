module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv
public import DraismaVargas.LocalCases.StablePathFacetContraction

@[expose] public section

/-!
# The valency-two `AgreeOffColumn` / common-minor identity

Source: Vargas, Part II (arXiv:2609.09109), §5.1 (the lemma on rigidity above
`w_0` and the labelling convention (1)), `lm:change-comb-type` (the wall matrix
as the common minor `A_{\varphi_0}` of the incoming matrices), and §5.4 for the
valency-two candidate itself.

This is a one-for-one port of `NonTrivalentValencyFourRowDictionary` §4 to the
valency-two candidate of `NonTrivalentValencyTwoRowEquiv`.  At
valency two the candidate lives over the *unchanged* incoming wall datum --
there is no block-preserving sheet gauge -- so every step that in the
valency-four file transported a labelling across
`SheetRelabelStable.stablePathEquiv` (`relabelLabelling`,
`candidateLabelling`'s gauge half) simply disappears: `NonTrivalentValencyTwoRowEquiv.labelling`
is already the honest labelling of the candidate, with no separate
re-indexing step.

## What is proved

* **`occurrences_retainedRow`, `matrix_retainedRow`**: the surviving occurrences
  of a retained row over an old target occurrence are exactly the retained
  copies of the surviving occurrences of that row of the incoming wall datum,
  hence the candidate's natural matrix in a retained row and an old column is
  the wall datum's own entry. Proved exactly as
  `NonTrivalentValencyFourRowDictionary.occurrences_retainedRow` /
  `matrix_retainedRow`, with the wall datum `data` playing the role of the
  gauged datum there, `Function.Injective (retainedRow ...)` supplied as an
  explicit hypothesis, and `NonTrivalentValencyTwoRows.candidate_sourceGenus`
  for the pruning transport `ResolutionPruning.isDangling_oldSourceEdge_iff`.
* **`retainedRow_injective`**: that injectivity, from `rowEquiv` being an
  `Equiv` and `rowEquiv_retainedRow`.  Unlike valency four
  (`NonTrivalentValencyFourRetainedInjective`), this is immediate:
  `NonTrivalentValencyTwoRowEquiv.rowEquiv` is already unconditional, so its
  own bijectivity supplies the fact that valency four needs a separate
  `Function.Injective retainedRow` argument for.
* **`matrix_candidateLabelling`**: the candidate's honest matrix agrees with the
  wall datum's off the new column, in `Option coordinate` indexing. Same
  statement and proof shape as at valency four, with
  `NonTrivalentValencyTwoRowEquiv.labelling` in place of
  `NonTrivalentValencyFourRowDictionary.candidateLabelling` and the `row.symm`
  computation read off `NonTrivalentValencyTwoRowEquiv.labelling_row_retained`
  directly (no `relabeling`/gauge layer to compose through).
* **`reindexLabelling`, `matrix_reindexLabelling`, `chartLabelling`,
  `matrix_chartLabelling`**: the generic re-indexing machinery of
  `NonTrivalentValencyFourRowDictionary`, unchanged, specialised to the
  valency-two candidate. For `Equiv.optionSubtypeNe` this puts `Option.none` --
  the new target occurrence and the bridge row -- in the contracted column of
  the incoming chart.
* **`matrix_chartLabelling_eq_incoming`**: the `AgreeOffColumn`-shaped
  identity, entry by entry: in the incoming chart, the outgoing matrix entry
  in the row of a retained stable row of the wall datum and in a retained
  column is the wall datum's own entry.  One `.trans` with
  `StablePathFacetContraction.matrix_wallLabelling` composes this with the
  wall datum's own agreement with the incoming full-dimensional cover, giving
  the common minor `A_{\varphi_0}` of Part II `lm:change-comb-type`.
* **`exists_matrix_chartLabelling_eq_incoming`**: the actual-wall corollary,
  composing the above with `NonTrivalentValencyTwoRowEquiv.exists_rowEquiv_of_wall_metric`.
  The hypotheses are the incoming full-dimensional cover, the actual
  contraction forest, `TwoStar`, the wall metric of a Part II open facet with
  a single vanishing stable row, and `NoContractedReturn`.  No candidate,
  type, row-equivalence or trivalence receipt is needed: the anchor block, its
  `TwoBranchAnchor` classification, the candidate's validity and source
  genus, and the ordinary-block trivalence `OrdinaryTrivalent` are all
  produced.  `DanglingCompatible` is not a hypothesis either: it is derived
  from the contraction forest by
  `WallAdmissibility.danglingCompatible_of_contractionForest`.

## What is not proved here

`NoContractedReturn` itself is **not discharged** here.  At a two-valent wall
it splits into two sub-cases (Part II, §5.4, following the `val(w_0) =
val(u) + val(v) - 2` count of §5.1):

* the `2 + 2` sub-case (`val(u) = val(v) = 2`), where
  `StablePathFacetContraction.noContractedReturn_of_nonleaf` applies directly
  (neither endpoint of the contracted occurrence is a leaf of the target
  tree);
* the `1 + 3` sub-case (`val(u) = 1`, `val(v) = 3`), where
  `NoContractedReturn` is genuinely **false** -- Part II's own account has the
  contracting stable edge pass above the leaf `u` and back -- and the correct
  replacement predicate is `LeafFacetNoReturn.NoContractedReturnOffRow`, with
  its own re-run of the `StablePathFacetContraction` chain
  (`LeafFacetNoReturn.rowEquiv'`, `.matrix_wallLabelling'`, ...).  That chain
  lives in its own module and is not repeated here; `hNoReturn` is an explicit
  hypothesis of `exists_matrix_chartLabelling_eq_incoming`, discharged by the
  caller via `noContractedReturn_of_nonleaf` in the `2 + 2` sub-case, or
  replaced by `LeafFacetNoReturn.exists_wallLabelling_of_valency_two_leaf` in
  the `1 + 3` sub-case.

Nothing here constructs a `FullDimensionalSourcePresentation`, a
`ContractionForest`, a `TwoStar`, or the wall metric; those are the caller's
receipts, exactly as in `StablePathFacetContraction` and
`NonTrivalentValencyFourRowDictionary`.

## Consumers

The boundary dispatcher for Part II case `{v2-nd4}`
(`NonTrivalentValencyTwoDispatcher`), and the nonsingularity/exit package built
on `NonTrivalentLinkMatrix`, whose `AgreeOffColumn` input is
`matrix_chartLabelling_eq_incoming` /
`exists_matrix_chartLabelling_eq_incoming`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoRowDictionary

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

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall}
  (source : TwoBranchAnchor data star anchor)
  (sel : Prescribed.Selection data star anchor)

local notation "cand" => (Prescribed.validCandidate sel)

/-! ## 1.  Injectivity of the retained-row map, from the row equivalence -/

/-- **`retainedRow` is injective.**  Unlike valency four, this needs no
separate argument: `rowEquiv` is already the unconditional row equivalence of
`NonTrivalentValencyTwoRowEquiv`, and `rowEquiv_retainedRow` identifies its
action on retained rows. -/
theorem retainedRow_injective (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    Function.Injective (NonTrivalentValencyTwoDescent.retainedRow source sel hValid) := by
  intro r r' hEq
  have h := congrArg (rowEquiv source sel hValid hOrd) hEq
  simp only [rowEquiv_retainedRow] at h
  exact Option.some.inj h

/-! ## 2.  The candidate's matrix off the new column -/

/-- **The surviving occurrences of a retained row over an old target
occurrence** are exactly the retained copies of the surviving occurrences of
that row of the incoming wall datum. -/
theorem occurrences_retainedRow
    (hValid : data.Valid)
    (hInj : Function.Injective (NonTrivalentValencyTwoDescent.retainedRow source sel hValid))
    (r : StablePath data) (e : target.edges) :
    StableSourceMatrix.occurrences (cand).datum
        (NonTrivalentValencyTwoDescent.retainedRow source sel hValid r)
        (occurrenceEquiv target wall (cand).right (some e)) =
      (StableSourceMatrix.occurrences data r e).image (cand).oldSourceEdge := by
  classical
  ext f
  rw [StableSourceMatrix.mem_occurrences]
  constructor
  · rintro ⟨⟨hSurv, hRow⟩, hTarget⟩
    rcases ResolutionPruning.sourceEdge_cases (cand) f with ⟨old, rfl⟩ | ⟨s, rfl⟩
    · have hOldSurv : ¬ IsDangling data old := fun h ↦ hSurv
        ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand) hValid
          (candidate_sourceGenus sel) old).mpr h)
      have hOcc : occurrenceEquiv target wall (cand).right (some old.1.1) =
          occurrenceEquiv target wall (cand).right (some e) := hTarget
      have hTargetEq : old.1.1 = e :=
        Option.some.inj ((occurrenceEquiv target wall (cand).right).injective hOcc)
      refine Finset.mem_image.mpr ⟨old, ?_, rfl⟩
      rw [StableSourceMatrix.mem_occurrences]
      exact ⟨⟨hOldSurv, hInj ((NonTrivalentValencyTwoDescent.retainedRow_mk source sel hValid
        ⟨old, hOldSurv⟩).trans hRow)⟩, hTargetEq⟩
    · exfalso
      have hOcc : occurrenceEquiv target wall (cand).right none =
          occurrenceEquiv target wall (cand).right (some e) := hTarget
      have := (occurrenceEquiv target wall (cand).right).injective hOcc
      cases this
  · intro hMem
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hMem
    rw [StableSourceMatrix.mem_occurrences] at hg
    obtain ⟨⟨hgS, hgRow⟩, hgTarget⟩ := hg
    refine ⟨⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ hValid.1 _ hgS, ?_⟩, ?_⟩
    · exact (NonTrivalentValencyTwoDescent.retainedRow_mk source sel hValid ⟨g, hgS⟩).symm.trans
        (congrArg (NonTrivalentValencyTwoDescent.retainedRow source sel hValid) hgRow)
    · show occurrenceEquiv target wall (cand).right (some g.1.1) =
        occurrenceEquiv target wall (cand).right (some e)
      rw [hgTarget]

/-- **The candidate's natural matrix in a retained row and an old column is
the wall datum's.** -/
theorem matrix_retainedRow
    (hValid : data.Valid)
    (hInj : Function.Injective (NonTrivalentValencyTwoDescent.retainedRow source sel hValid))
    (r : StablePath data) (e : target.edges) :
    StableSourceMatrix.matrix (cand).datum
        (NonTrivalentValencyTwoDescent.retainedRow source sel hValid r)
        (occurrenceEquiv target wall (cand).right (some e)) =
      StableSourceMatrix.matrix data r e := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_retainedRow source sel hValid hInj r e,
    Finset.sum_image (fun _ _ _ _ h ↦ ResolutionCut.oldSourceEdge_injective (cand) h)]
  exact Finset.sum_congr rfl fun g _ ↦ by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]

section MatrixLabelling

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The candidate's honest matrix agrees with the wall datum's off the new
column.**  In the `Option coordinate` indexing, the entry of the candidate in
the retained row `some (labelling₀.row p)` and the retained column `some c`
is the wall datum's own entry in row `labelling₀.row p` and column `c`. -/
theorem matrix_candidateLabelling
    (hValid : data.Valid) (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (p : StablePath data) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (NonTrivalentValencyTwoRowEquiv.labelling source sel hValid hOrd labelling₀).presentation
        (some (labelling₀.row p)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) c := by
  classical
  have hInj := retainedRow_injective source sel hValid hOrd
  have hRowSymm :
      (NonTrivalentValencyTwoRowEquiv.labelling source sel hValid hOrd labelling₀).row.symm
          (some (labelling₀.row p)) =
        NonTrivalentValencyTwoDescent.retainedRow source sel hValid p := by
    rw [Equiv.symm_apply_eq]
    exact (labelling_row_retained source sel hValid hOrd labelling₀ p).symm
  have hTgt :
      (NonTrivalentValencyTwoRowEquiv.labelling source sel hValid hOrd labelling₀).targetEdge
          (some c) =
        occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) := rfl
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    hRowSymm, hTgt, Equiv.symm_apply_apply]
  exact matrix_retainedRow source sel hValid hInj p (labelling₀.targetEdge c)

end MatrixLabelling

/-! ## 3.  Re-indexing the `Option` coordinate onto the incoming chart

The generic re-indexing machinery of `NonTrivalentValencyFourRowDictionary`,
unchanged. -/

section Reindex

/-- Transport a square honest labelling along an equivalence of index sets. -/
def reindexLabelling {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {A B : Type*} (e : A ≃ B)
    (labelling : StableLengthMatrixLabelling datum A) :
    StableLengthMatrixLabelling datum B where
  targetEdge := e.symm.trans labelling.targetEdge
  row := labelling.row.trans e

@[simp] theorem reindexLabelling_row {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {A B : Type*} (e : A ≃ B)
    (labelling : StableLengthMatrixLabelling datum A)
    (path : StablePath datum) :
    (reindexLabelling e labelling).row path = e (labelling.row path) := rfl

@[simp] theorem reindexLabelling_targetEdge {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {A B : Type*} (e : A ≃ B)
    (labelling : StableLengthMatrixLabelling datum A) (b : B) :
    (reindexLabelling e labelling).targetEdge b =
      labelling.targetEdge (e.symm b) := rfl

theorem matrix_reindexLabelling {targetX : CFGraph} {deg : ℕ}
    {datum : GluingDatum targetX deg} {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B)
    (labelling : StableLengthMatrixLabelling datum A) (row column : A) :
    GluingDatum.LengthMatrixPresentation.matrix
        (reindexLabelling e labelling).presentation (e row) (e column) =
      GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
        column := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    reindexLabelling_targetEdge, Equiv.symm_apply_apply]
  congr 1
  rw [Equiv.symm_apply_eq, reindexLabelling_row, Equiv.apply_symm_apply]

end Reindex

section ActualChart

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The outgoing chart, indexed by the incoming one.**  The candidate's
honest labelling over `Option coordinate₀` is re-indexed along any
equivalence `Option coordinate₀ ≃ coordinate`; taking `coordinate₀` to be the
incoming coordinates with the contracted column removed and the equivalence
`Equiv.optionSubtypeNe`, the outgoing matrix is indexed by the incoming chart
with `Option.none` sitting in the contracted column. -/
noncomputable def chartLabelling {coordinate₀ : Type*} [Fintype coordinate₀]
    [DecidableEq coordinate₀]
    (hValid : data.Valid) (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate₀)
    (chart : Option coordinate₀ ≃ coordinate) :
    StableLengthMatrixLabelling (cand).datum coordinate :=
  reindexLabelling chart
    (NonTrivalentValencyTwoRowEquiv.labelling source sel hValid hOrd labelling₀)

include source in
/-- **The `AgreeOffColumn`-shaped identity, entry by entry, in the incoming
chart.** -/
theorem matrix_chartLabelling {coordinate₀ : Type*} [Fintype coordinate₀]
    [DecidableEq coordinate₀]
    (hValid : data.Valid) (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate₀)
    (chart : Option coordinate₀ ≃ coordinate)
    (p : StablePath data) (c : coordinate₀) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling source sel hValid hOrd labelling₀ chart).presentation
        (chart (some (labelling₀.row p))) (chart (some c)) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) c :=
  (matrix_reindexLabelling chart
    (NonTrivalentValencyTwoRowEquiv.labelling source sel hValid hOrd labelling₀) _ _).trans
    (matrix_candidateLabelling source sel hValid hOrd labelling₀ p c)

end ActualChart

/-! ## 4.  The common minor: the outgoing matrix against the incoming one -/

section AgreeOffColumn

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration

variable {targetIn : CFGraph} {deg : ℕ} {chartIndex : Type*} [Fintype chartIndex]
  [DecidableEq chartIndex]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover chartIndex)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hCompat : DanglingCompatible cover hc hab hOne)
  (hForest : ContractionForest cover a b contracted)
  (hNoReturn : NoContractedReturn cover contracted)
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
  {wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (selBlk : Prescribed.Selection (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hValid : (contractDatum cover hc hab hOne).Valid)
  (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlk)

/-- **The outgoing honest matrix equals the incoming one off the contracted
column**, entry by entry, once the row dictionary of the candidate is
supplied.  Rows correspond through `retainedRow` on the outgoing side and
`StablePathFacetContraction.incomingRow` on the incoming side; columns
through the chart equivalence, which puts `Option.none` -- the new target
occurrence and the bridge row -- in the contracted column.  This is the
common minor `A_{\varphi_0}` of Part II's `lm:change-comb-type`. -/
theorem matrix_chartLabelling_eq_incoming
    (chart : Option {column : chartIndex //
        column ≠ fd.labelling.targetEdge.symm contracted} ≃ chartIndex)
    (p : StablePath (contractDatum cover hc hab hOne))
    (column : {column : chartIndex //
      column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling src selBlk hValid hOrd
          (wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates facet
            hRows hZeroCoord hPosCoord hFacetZero)
          chart).presentation
        (chart (some (wallRowIndex cover fd hc hab hOne hCompat hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
        (chart (some column)) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row (incomingRow cover fd hc hab hOne hCompat hForest p))
        column.1 :=
  (matrix_chartLabelling src selBlk hValid hOrd
    (wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero) chart p column).trans
    (matrix_wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero p column)

end AgreeOffColumn

/-! ## 5.  The actual-wall corollary -/

section ActualWall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration

variable {targetIn : CFGraph} {deg : ℕ} {chartIndex : Type*} [Fintype chartIndex]
  [DecidableEq chartIndex]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover chartIndex)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (hNoReturn : NoContractedReturn cover contracted)
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

/-- **The actual-wall corollary: the outgoing chart labelling and the
entrywise common-minor identity, at an actual two-valent wall, with no
receipt about the candidate.**  Hypotheses: the incoming full-dimensional
cover, the actual contraction forest, `TwoStar`, the wall metric of a
Part II open facet with a single vanishing stable row, and
`NoContractedReturn` (see the module docstring for its two sub-cases at a
two-valent wall; it is **not discharged here**).  `DanglingCompatible` is not
a hypothesis: it is derived from the forest. -/
theorem exists_matrix_chartLabelling_eq_incoming :
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
                (wallLabelling cover fd hc hab hOne
                  (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                    hForest)
                  hForest hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero)
                chart).presentation
              (chart (some (wallRowIndex cover fd hc hab hOne
                (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                  hForest)
                hForest hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
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
  refine ⟨anchorBlock, src, hOrd, hNd, fun sel ↦ ⟨?_, ?_, fun p column ↦ ?_⟩⟩
  · exact (hSelection sel).1
  · exact (hSelection sel).2.1
  · exact matrix_chartLabelling_eq_incoming cover fd hc hab hOne
      (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
      hForest hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero src sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd chart p column

end ActualWall

end DraismaVargas.LocalCases.NonTrivalentValencyTwoRowDictionary
