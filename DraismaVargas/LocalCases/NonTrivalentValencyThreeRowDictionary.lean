module

public import DraismaVargas.LocalCases.NonTrivalentValencyThreeRowEquiv
public import DraismaVargas.LocalCases.StablePathFacetContraction

@[expose] public section

/-!
# The valency-three `AgreeOffColumn` / common-minor identity

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (rigidity above `w_0`,
the labelling convention (1), and `lm:change-comb-type`: the wall matrix as the
common minor `A_{\varphi_0}` of the incoming matrices), and Section 5.3 for the
valency-three candidate itself (Case {v3-nd4}, base tree `T_2`).

This follows `NonTrivalentValencyTwoRowDictionary` (itself modelled on §4 of
`NonTrivalentValencyFourRowDictionary`) one for one, for the valency-three
candidate of `NonTrivalentValencyThreeRowEquiv`.  As at valency
two, the candidate lives over the *unchanged* incoming wall datum -- there is
no block-preserving sheet gauge -- so every re-indexing step disappears; and
as the docstring of `NonTrivalentValencyThreeRowEquiv` records, the
valency-three `rowEquiv` carries **no** `OrdinaryTrivalent`-style hypothesis
at all (unlike valency two), because at valency three the row of a new
occurrence is always the row of its own fine class's doubled-direction
survivor, with no choice of side.  Consequently every lemma below drops the
valency-two `hOrd` argument outright, rather than discharging it.

## What is proved

* **`retainedRow_injective`**: immediate from `rowEquiv` being an `Equiv` and
  `rowEquiv_retainedRow`, exactly as at valency two -- and, as there, with no
  extra hypothesis beyond `hNoGlue`/`hValid` (the valency-three `rowEquiv` is
  already fully unconditional).
* **`occurrences_retainedRow`, `matrix_retainedRow`**: the surviving
  occurrences of a retained row over an old target occurrence are exactly the
  retained copies of the surviving occurrences of that row of the wall datum,
  hence the candidate's natural matrix in a retained row and an old column is
  the wall datum's own entry.  Proved exactly as
  `NonTrivalentValencyTwoRowDictionary.occurrences_retainedRow` /
  `matrix_retainedRow`, with the wall datum `data`
  playing the role of the gauged datum in the valency-four original,
  `Function.Injective (retainedRow ...)` supplied as an explicit hypothesis,
  and `NonTrivalentValencyThreeRows.candidate_sourceGenus` for the pruning
  transport `ResolutionPruning.isDangling_oldSourceEdge_iff`.
* **`matrix_candidateLabelling`**: the candidate's honest matrix agrees with
  the wall datum's off the new column, in `Option coordinate` indexing, with
  `NonTrivalentValencyThreeRowEquiv.labelling` in place of the two-valent
  `labelling` and no `OrdinaryTrivalent`/gauge layer to compose through.
* **`reindexLabelling`, `matrix_reindexLabelling`, `chartLabelling`,
  `matrix_chartLabelling`**: the generic re-indexing machinery of
  `NonTrivalentValencyFourRowDictionary`, specialised to the valency-three
  candidate.
* **`matrix_chartLabelling_eq_incoming`**: the `AgreeOffColumn`-shaped
  identity, entry by entry, one `.trans` with
  `StablePathFacetContraction.matrix_wallLabelling`, giving the common minor
  `A_{\varphi_0}` of Part II `lm:change-comb-type`.
* **`exists_matrix_chartLabelling_eq_incoming`**: the actual-wall corollary,
  composing the above with
  `NonTrivalentValencyThreeRowEquiv.exists_rowEquiv_of_wall_metric`.  The
  hypotheses are the incoming full-dimensional cover, the actual contraction
  forest, `ThreeStar`, the wall metric of a Part II open facet with a single
  vanishing stable row, and `NoContractedReturn`.  No candidate, type, row
  equivalence, `DanglingEdgeNoGlue` or wall-validity receipt remains: all four
  are produced, unlike valency two, where `OrdinaryTrivalent` is the only
  produced side-condition and `hValid` is folded directly into the return
  type via proof irrelevance.
* **`noContractedReturn_of_threeStar`, `exists_matrix_chartLabelling_eq_incoming_of_threeStar`**:
  **`NoContractedReturn` itself is discharged**, unconditionally, at an actual
  three-valent wall, which the valency-two file does not do.
  `ThirdEquation.valencySplit_of_threeStar` forces
  `(incidentEdges a).card + (incidentEdges b).card = 5` with both summands at
  most three, hence the split is `{2, 3}` in either order: **neither**
  endpoint of the contracted occurrence is a leaf of the target tree (unlike
  the `val(u) = 1` sub-case of a two-valent wall, which is genuinely a
  separate, harder problem, treated in `LeafFacetNoReturn`).  So
  `StablePathFacetContraction.noContractedReturn_of_nonleaf` applies directly
  in both branches of the split, and the whole common-minor identity holds at
  an actual three-valent wall with **no** remaining hypothesis beyond the
  incoming full-dimensional cover, its contraction forest, `ThreeStar` and the
  wall metric.

## What is NOT proved

Nothing here constructs a `FullDimensionalSourcePresentation`, a
`ContractionForest`, a `ThreeStar`, or the wall metric; those are the
caller's receipts, exactly as in `StablePathFacetContraction` and
`NonTrivalentValencyFourRowDictionary`.

## Consumers

The boundary dispatcher for Part II, Case {v3-nd4}
(`NonTrivalentValencyThreeDispatcher`), and the nonsingularity and exit
argument built on `NonTrivalentLinkMatrix`, whose
`AgreeOffColumn` input is `matrix_chartLabelling_eq_incoming` /
`exists_matrix_chartLabelling_eq_incoming_of_threeStar`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeRowDictionary

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionCoarseFine
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyThreeCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeRows
open DraismaVargas.LocalCases.NonTrivalentValencyThreeDescent
open DraismaVargas.LocalCases.NonTrivalentValencyThreeRowEquiv

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall}
  (source : ThreeBranchAnchor data star anchor)
  (hNoGlue : DanglingEdgeNoGlue data) (hValid : data.Valid)

local notation "cand" => (Prescribed.validCandidate source hNoGlue hValid)

/-! ## 1.  Injectivity of the retained-row map, from the row equivalence -/

/-- **`retainedRow` is injective.**  As at valency two, this needs no separate
argument: `rowEquiv` is already the unconditional row equivalence of
`NonTrivalentValencyThreeRowEquiv`, and `rowEquiv_retainedRow` identifies its
action on retained rows.  Unlike valency two there is no `OrdinaryTrivalent`
hypothesis to carry: the valency-three `rowEquiv` needs none at all. -/
theorem retainedRow_injective :
    Function.Injective (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid) := by
  intro r r' hEq
  have h := congrArg (rowEquiv source hNoGlue hValid) hEq
  simp only [rowEquiv_retainedRow] at h
  exact Option.some.inj h

/-! ## 2.  The candidate's matrix off the new column -/

/-- **The surviving occurrences of a retained row over an old target
occurrence** are exactly the retained copies of the surviving occurrences of
that row of the wall datum. -/
theorem occurrences_retainedRow
    (hInj : Function.Injective (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid))
    (r : StablePath data) (e : target.edges) :
    StableSourceMatrix.occurrences (cand).datum
        (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid r)
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
          (candidate_sourceGenus source hNoGlue hValid) old).mpr h)
      have hOcc : occurrenceEquiv target wall (cand).right (some old.1.1) =
          occurrenceEquiv target wall (cand).right (some e) := hTarget
      have hTargetEq : old.1.1 = e :=
        Option.some.inj ((occurrenceEquiv target wall (cand).right).injective hOcc)
      refine Finset.mem_image.mpr ⟨old, ?_, rfl⟩
      rw [StableSourceMatrix.mem_occurrences]
      exact ⟨⟨hOldSurv, hInj ((NonTrivalentValencyThreeDescent.retainedRow_mk source hNoGlue hValid
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
    · exact (NonTrivalentValencyThreeDescent.retainedRow_mk source hNoGlue hValid ⟨g, hgS⟩).symm.trans
        (congrArg (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid) hgRow)
    · show occurrenceEquiv target wall (cand).right (some g.1.1) =
        occurrenceEquiv target wall (cand).right (some e)
      rw [hgTarget]

/-- **The candidate's natural matrix in a retained row and an old column is
the wall datum's.** -/
theorem matrix_retainedRow
    (hInj : Function.Injective (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid))
    (r : StablePath data) (e : target.edges) :
    StableSourceMatrix.matrix (cand).datum
        (NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid r)
        (occurrenceEquiv target wall (cand).right (some e)) =
      StableSourceMatrix.matrix data r e := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_retainedRow source hNoGlue hValid hInj r e,
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
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (p : StablePath data) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (NonTrivalentValencyThreeRowEquiv.labelling source hNoGlue hValid labelling₀).presentation
        (some (labelling₀.row p)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) c := by
  classical
  have hInj := retainedRow_injective source hNoGlue hValid
  have hRowSymm :
      (NonTrivalentValencyThreeRowEquiv.labelling source hNoGlue hValid labelling₀).row.symm
          (some (labelling₀.row p)) =
        NonTrivalentValencyThreeDescent.retainedRow source hNoGlue hValid p := by
    rw [Equiv.symm_apply_eq]
    exact (labelling_row_retained source hNoGlue hValid labelling₀ p).symm
  have hTgt :
      (NonTrivalentValencyThreeRowEquiv.labelling source hNoGlue hValid labelling₀).targetEdge
          (some c) =
        occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) := rfl
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    hRowSymm, hTgt, Equiv.symm_apply_apply]
  exact matrix_retainedRow source hNoGlue hValid hInj p (labelling₀.targetEdge c)

end MatrixLabelling

/-! ## 3.  Re-indexing the `Option` coordinate onto the incoming chart

The generic re-indexing machinery of `NonTrivalentValencyFourRowDictionary`. -/

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
    (labelling₀ : StableLengthMatrixLabelling data coordinate₀)
    (chart : Option coordinate₀ ≃ coordinate) :
    StableLengthMatrixLabelling (cand).datum coordinate :=
  reindexLabelling chart
    (NonTrivalentValencyThreeRowEquiv.labelling source hNoGlue hValid labelling₀)

/-- **The `AgreeOffColumn`-shaped identity, entry by entry, in the incoming
chart.** -/
theorem matrix_chartLabelling {coordinate₀ : Type*} [Fintype coordinate₀]
    [DecidableEq coordinate₀]
    (labelling₀ : StableLengthMatrixLabelling data coordinate₀)
    (chart : Option coordinate₀ ≃ coordinate)
    (p : StablePath data) (c : coordinate₀) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling source hNoGlue hValid labelling₀ chart).presentation
        (chart (some (labelling₀.row p))) (chart (some c)) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) c :=
  (matrix_reindexLabelling chart
    (NonTrivalentValencyThreeRowEquiv.labelling source hNoGlue hValid labelling₀) _ _).trans
    (matrix_candidateLabelling source hNoGlue hValid labelling₀ p c)

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
  {wallStar : ThreeStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : ThreeBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hNoGlue : DanglingEdgeNoGlue (contractDatum cover hc hab hOne))
  (hValid : (contractDatum cover hc hab hOne).Valid)

/-- **The outgoing honest matrix equals the incoming one off the contracted
column**, entry by entry, once the row dictionary of the candidate is
supplied.  Rows correspond through `retainedRow` on the outgoing side and
`StablePathFacetContraction.incomingRow` on the incoming side; columns
through the chart equivalence, which puts `Option.none` -- the new target
occurrence and the bridge row -- in the contracted column.  This is the
common minor `A_{\varphi_0}` of Part II, `lm:change-comb-type` (Section 5.1). -/
theorem matrix_chartLabelling_eq_incoming
    (chart : Option {column : chartIndex //
        column ≠ fd.labelling.targetEdge.symm contracted} ≃ chartIndex)
    (p : StablePath (contractDatum cover hc hab hOne))
    (column : {column : chartIndex //
      column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling src hNoGlue hValid
          (wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates facet
            hRows hZeroCoord hPosCoord hFacetZero)
          chart).presentation
        (chart (some (wallRowIndex cover fd hc hab hOne hCompat hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
        (chart (some column)) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row (incomingRow cover fd hc hab hOne hCompat hForest p))
        column.1 :=
  (matrix_chartLabelling src hNoGlue hValid
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
  (wallStar : ThreeStar (contract targetIn hab hOne) ⟨a, hab⟩)
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
entrywise common-minor identity, at an actual three-valent wall, with no
receipt about the candidate.**  Hypotheses: the incoming full-dimensional
cover, the actual contraction forest, `ThreeStar`, the wall metric of a
Part II open facet with a single vanishing stable row, and
`NoContractedReturn`.  `DanglingEdgeNoGlue` and the wall datum's own validity
are not hypotheses: both are produced, together with the anchor block and its
`ThreeBranchAnchor` classification, from
`NonTrivalentValencyThreeRowEquiv.exists_rowEquiv_of_wall_metric`. -/
theorem exists_matrix_chartLabelling_eq_incoming :
    ∃ (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
      (src : ThreeBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock)
      (hNoGlue : DanglingEdgeNoGlue (contractDatum cover hc hab hOne))
      (hValid : (contractDatum cover hc hab hOne).Valid),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
        (Prescribed.validCandidate src hNoGlue hValid).datum.Valid ∧
        genus (Prescribed.validCandidate src hNoGlue hValid).datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        ∀ (p : StablePath (contractDatum cover hc hab hOne))
          (column : {column : chartIndex //
            column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix
              (chartLabelling src hNoGlue hValid
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
  obtain ⟨anchorBlock, src, hNoGlue, hValid, hNd, hCandValid, hGenus, -, -⟩ :=
    NonTrivalentValencyThreeRowEquiv.exists_rowEquiv_of_wall_metric cover fd hc hab hOne hForest
      wallStar coordinates facet hRows hZeroCoord hPosCoord hFacetZero
  exact ⟨anchorBlock, src, hNoGlue, hValid, hNd, hCandValid, hGenus, fun p column ↦
    matrix_chartLabelling_eq_incoming cover fd hc hab hOne
      (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
      hForest hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero src
      hNoGlue hValid chart p column⟩

/-! ## 6.  `NoContractedReturn` is unconditional at a three-valent wall

Unlike the two-valent wall's `val(u) = 1` sub-case (treated in
`LeafFacetNoReturn`), a three-valent wall never carries a leaf endpoint: the
target-valency split forced by a `ThreeStar` is always `{2, 3}`, so both
endpoints are non-leaves and `noContractedReturn_of_nonleaf` settles the whole
question. -/

/-- **`NoContractedReturn` needs no receipt at a three-valent wall.**  A
`ThreeStar` at the merged vertex forces
`(incidentEdges a).card + (incidentEdges b).card = 5` with both summands at
most three (`ThirdEquation.valencySplit_of_threeStar`, from the incoming
cover's own validity and change-minimality), so the split is `(2, 3)` or
`(3, 2)`; either way both endpoints have at least two incident occurrences,
i.e. neither is a leaf of the target tree, and
`StablePathFacetContraction.noContractedReturn_of_nonleaf` applies. -/
theorem noContractedReturn_of_threeStar
    (cover : GluingDatum targetIn deg)
    (fd : FullDimensionalSourcePresentation cover chartIndex)
    (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges targetIn a b = 1)
    (wallStar : ThreeStar (contract targetIn hab hOne) ⟨a, hab⟩) :
    NoContractedReturn cover contracted := by
  rcases ThirdEquation.valencySplit_of_threeStar cover hc hab hOne fd.valid fd.changeMinimal
      wallStar with ⟨hLeft, hRight, -, -⟩ | ⟨hLeft, hRight, -, -⟩
  · exact noContractedReturn_of_nonleaf cover fd hc (by omega) (by omega)
  · exact noContractedReturn_of_nonleaf cover fd hc (by omega) (by omega)

/-- **The actual-wall statement with every hypothesis discharged.**  Same
conclusion as `exists_matrix_chartLabelling_eq_incoming`, without
`NoContractedReturn` as a hypothesis: it is supplied by
`noContractedReturn_of_threeStar`.  So
the whole `AgreeOffColumn` / common-minor identity holds at an actual
three-valent wall from nothing but the incoming full-dimensional cover, its
contraction forest, `ThreeStar` and the wall metric. -/
theorem exists_matrix_chartLabelling_eq_incoming_of_threeStar :
    ∃ (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
      (src : ThreeBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock)
      (hNoGlue : DanglingEdgeNoGlue (contractDatum cover hc hab hOne))
      (hValid : (contractDatum cover hc hab hOne).Valid),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
        (Prescribed.validCandidate src hNoGlue hValid).datum.Valid ∧
        genus (Prescribed.validCandidate src hNoGlue hValid).datum.sourceGraph =
          genus (contractDatum cover hc hab hOne).sourceGraph ∧
        ∀ (p : StablePath (contractDatum cover hc hab hOne))
          (column : {column : chartIndex //
            column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix
              (chartLabelling src hNoGlue hValid
                (wallLabelling cover fd hc hab hOne
                  (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                    hForest)
                  hForest (noContractedReturn_of_threeStar cover fd hc hab hOne wallStar)
                  coordinates facet hRows hZeroCoord hPosCoord hFacetZero)
                chart).presentation
              (chart (some (wallRowIndex cover fd hc hab hOne
                (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                  hForest)
                hForest (noContractedReturn_of_threeStar cover fd hc hab hOne wallStar)
                coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
              (chart (some column)) =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (incomingRow cover fd hc hab hOne
                (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                  hForest)
                hForest p))
              column.1 :=
  exists_matrix_chartLabelling_eq_incoming cover fd hc hab hOne hForest
    (noContractedReturn_of_threeStar cover fd hc hab hOne wallStar) wallStar coordinates
    facet hRows hZeroCoord hPosCoord hFacetZero chart

end ActualWall

end DraismaVargas.LocalCases.NonTrivalentValencyThreeRowDictionary
