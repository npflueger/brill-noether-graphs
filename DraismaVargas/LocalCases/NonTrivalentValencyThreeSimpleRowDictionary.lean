import DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowEquiv
import DraismaVargas.LocalCases.NonTrivalentValencyThreeRowDictionary

/-!
# The common minor of the prescribed Type I / Type II valency-three candidates

Source: Vargas, Part II, Section 5.1 (rigidity above `w_0`, and the labelling
convention (1)), Lemma `lm:change-comb-type` (the wall matrix as the common
minor `A_{\varphi_0}` of the incoming matrices), and Section 5.3, case
`{v3-nd4}`, for the candidate itself (base trees `T_alpha` with `alpha`
simple).

This is the Type I / Type II analogue of
`NonTrivalentValencyThreeRowDictionary` (Type III).  The one new
ingredient is the **two-fold branch gauge**: the candidate lives over
`SimpleBase.gaugedData`, not over the wall datum itself, so the incoming chart
has to be carried across the gauge before the wall matrix identity applies.
That transport is
`NonTrivalentValencyThreeSimpleRowEquiv.gaugedLabelling` together with
`gaugedLabelling_matrix` (`RelabelFullDimensional.sheet_matrix_eq` twice, the
`K = 0` model being `NonTrivalentValencyFourRowDictionary.relabelLabelling`),
and `gaugeStablePath` / `gaugedLabelling_row` below match the row indices.
Everything else is the argument of `NonTrivalentValencyThreeRowDictionary`
verbatim, and its generic re-indexing machinery (`reindexLabelling`,
`matrix_reindexLabelling`) and its unconditional
`noContractedReturn_of_threeStar` are reused rather than re-proved.

## What is proved

* `retainedRow_injective`: immediate from `rowEquiv` and `rowEquiv_retainedRow`;
  no extra hypothesis.
* `gaugeStablePath`, `gaugedLabelling_row`: the incoming stable rows carried to
  the gauged datum, and the chart's row index unchanged by that transport.
* `occurrences_retainedRow`, `matrix_retainedRow`: the surviving occurrences of
  a retained row over an old target occurrence are exactly the retained copies
  of the surviving occurrences of that row of the gauged wall datum, so the
  candidate's natural matrix in a retained row and an old column is the gauged
  wall datum's entry.
* `matrix_candidateLabelling`, `chartLabelling`, `matrix_chartLabelling`: the
  honest matrix off the new column, then re-indexed onto the incoming chart
  with `Option.none` in the contracted column.
* `matrix_chartLabelling_eq_incoming`: the `AgreeOffColumn`-shaped identity,
  entry by entry, against the incoming full-dimensional matrix -- one `.trans`
  with `gaugedLabelling_matrix` and one with
  `StablePathFacetContraction.matrix_wallLabelling`.
* `MinorIdentity`, `minorIdentity`: the actual-wall headline.
  `DanglingCompatible` and `NoContractedReturn` are filled in by their canonical
  producers, so the hypotheses are the incoming full-dimensional cover, its
  contraction forest, the `ThreeStar` of the merged vertex, the wall metric of
  a Part II open facet with a single vanishing stable row, a chart equivalence,
  and the `SimpleBase` with the wall datum's validity.

## What is not proved here

Nothing here constructs a `FullDimensionalSourcePresentation`, a
`ContractionForest`, a `ThreeStar` or the wall metric; those are the caller's
receipts, exactly as in `StablePathFacetContraction` and
`NonTrivalentValencyThreeRowDictionary`.  No nonsingularity, positive initial
metric or pencil is opened here: that is the exit package built on
`NonTrivalentLinkMatrix`.

## Used by

The boundary dispatcher for Part II case `{v3-nd4}`, whose `AgreeOffColumn`
input is `matrix_chartLabelling_eq_incoming` / `minorIdentity`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowDictionary

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
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRows
open DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowEquiv

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable {data : GluingDatum target degree} {star : ThreeStar target wall}
  {anchor : WallBlock data wall} (base : SimpleBase data star anchor)

/-! ## 1.  Injectivity of the retained-row map -/

theorem retainedRow_injective (hValid : data.Valid) :
    Function.Injective (retainedRow base hValid) := by
  intro r r' hEq
  have h := congrArg (rowEquiv base hValid) hEq
  simp only [rowEquiv_retainedRow] at h
  exact Option.some.inj h

/-! ## 2.  The stable rows carried across the two branch gauges -/

/-- The incoming stable rows, carried to the gauged datum. -/
noncomputable def gaugeStablePath (hValid : data.Valid) :
    StablePath data ≃ StablePath base.gaugedData :=
  (SheetRelabelStable.stablePathEquiv base.firstRelabeling hValid.1).trans
    (SheetRelabelStable.stablePathEquiv base.secondRelabeling
      (middleData_connected base hValid))

theorem gaugedLabelling_row {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (p : StablePath data) :
    (gaugedLabelling base hValid labelling₀).row (gaugeStablePath base hValid p) =
      labelling₀.row p := by
  show labelling₀.row
      ((SheetRelabelStable.stablePathEquiv base.firstRelabeling hValid.1).symm
        ((SheetRelabelStable.stablePathEquiv base.secondRelabeling
            (middleData_connected base hValid)).symm
          ((SheetRelabelStable.stablePathEquiv base.secondRelabeling
              (middleData_connected base hValid))
            ((SheetRelabelStable.stablePathEquiv base.firstRelabeling hValid.1) p)))) =
    labelling₀.row p
  refine congrArg labelling₀.row ?_
  refine Eq.trans (congrArg
    (SheetRelabelStable.stablePathEquiv base.firstRelabeling hValid.1).symm
    (Equiv.symm_apply_apply (SheetRelabelStable.stablePathEquiv base.secondRelabeling
      (middleData_connected base hValid))
      ((SheetRelabelStable.stablePathEquiv base.firstRelabeling hValid.1) p))) ?_
  exact Equiv.symm_apply_apply (SheetRelabelStable.stablePathEquiv base.firstRelabeling
    hValid.1) p

/-! ## 3.  The candidate's matrix off the new column -/

/-- **The surviving occurrences of a retained row over an old target
occurrence** are exactly the retained copies of the surviving occurrences of
that row of the gauged wall datum. -/
theorem occurrences_retainedRow (hValid : data.Valid)
    (r : StablePath base.gaugedData) (e : target.edges) :
    StableSourceMatrix.occurrences (validCandidate base hValid).datum
        (retainedRow base hValid r)
        (occurrenceEquiv target wall (validCandidate base hValid).right (some e)) =
      (StableSourceMatrix.occurrences base.gaugedData r e).image
        (validCandidate base hValid).oldSourceEdge := by
  classical
  ext f
  rw [StableSourceMatrix.mem_occurrences]
  constructor
  · rintro ⟨⟨hSurv, hRow⟩, hTarget⟩
    rcases ResolutionPruning.sourceEdge_cases (validCandidate base hValid) f with
      ⟨old, rfl⟩ | ⟨s, rfl⟩
    · have hOldSurv : ¬ IsDangling base.gaugedData old := fun h ↦ hSurv
        ((retained_isDangling_iff base hValid old).mpr h)
      have hOcc : occurrenceEquiv target wall (validCandidate base hValid).right
          (some old.1.1) =
          occurrenceEquiv target wall (validCandidate base hValid).right (some e) :=
        hTarget
      have hTargetEq : old.1.1 = e :=
        Option.some.inj
          ((occurrenceEquiv target wall (validCandidate base hValid).right).injective hOcc)
      refine Finset.mem_image.mpr ⟨old, ?_, rfl⟩
      rw [StableSourceMatrix.mem_occurrences]
      exact ⟨⟨hOldSurv, retainedRow_injective base hValid
        ((retainedRow_mk base hValid ⟨old, hOldSurv⟩).trans hRow)⟩, hTargetEq⟩
    · exfalso
      have hOcc : occurrenceEquiv target wall (validCandidate base hValid).right none =
          occurrenceEquiv target wall (validCandidate base hValid).right (some e) := hTarget
      have hNone :=
        (occurrenceEquiv target wall (validCandidate base hValid).right).injective hOcc
      cases hNone
  · intro hMem
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hMem
    rw [StableSourceMatrix.mem_occurrences] at hg
    obtain ⟨⟨hgS, hgRow⟩, hgTarget⟩ := hg
    refine ⟨⟨retained_survives base hValid hgS, ?_⟩, ?_⟩
    · exact (retainedRow_mk base hValid ⟨g, hgS⟩).symm.trans
        (congrArg (retainedRow base hValid) hgRow)
    · show occurrenceEquiv target wall (validCandidate base hValid).right (some g.1.1) =
        occurrenceEquiv target wall (validCandidate base hValid).right (some e)
      rw [hgTarget]

/-- **The candidate's natural matrix in a retained row and an old column is the
gauged wall datum's.** -/
theorem matrix_retainedRow (hValid : data.Valid) (r : StablePath base.gaugedData)
    (e : target.edges) :
    StableSourceMatrix.matrix (validCandidate base hValid).datum
        (retainedRow base hValid r)
        (occurrenceEquiv target wall (validCandidate base hValid).right (some e)) =
      StableSourceMatrix.matrix base.gaugedData r e := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_retainedRow base hValid r e,
    Finset.sum_image (fun _ _ _ _ h ↦
      ResolutionCut.oldSourceEdge_injective (validCandidate base hValid) h)]
  exact Finset.sum_congr rfl fun g _ ↦ by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]

/-! ## 4.  The honest matrix off the new column -/

section MatrixLabelling

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The candidate's honest matrix agrees with the gauged wall datum's off the
new column.** -/
theorem matrix_candidateLabelling (hValid : data.Valid)
    (labellingG : StableLengthMatrixLabelling base.gaugedData coordinate)
    (p : StablePath base.gaugedData) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (labelling base hValid labellingG).presentation
        (some (labellingG.row p)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix labellingG.presentation
        (labellingG.row p) c := by
  classical
  have hRowSymm : (labelling base hValid labellingG).row.symm
        (some (labellingG.row p)) = retainedRow base hValid p := by
    rw [Equiv.symm_apply_eq]
    exact (labelling_row_retained base hValid labellingG p).symm
  have hTgt : (labelling base hValid labellingG).targetEdge (some c) =
      occurrenceEquiv target wall (validCandidate base hValid).right
        (some (labellingG.targetEdge c)) := rfl
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    hRowSymm, hTgt, Equiv.symm_apply_apply]
  exact matrix_retainedRow base hValid p (labellingG.targetEdge c)

/-- **The outgoing chart, indexed by the incoming one.** -/
noncomputable def chartLabelling {coordinate₀ : Type*} [Fintype coordinate₀]
    [DecidableEq coordinate₀] (hValid : data.Valid)
    (labellingG : StableLengthMatrixLabelling base.gaugedData coordinate₀)
    (chart : Option coordinate₀ ≃ coordinate) :
    StableLengthMatrixLabelling (validCandidate base hValid).datum coordinate :=
  NonTrivalentValencyThreeRowDictionary.reindexLabelling chart
    (labelling base hValid labellingG)

/-- **The `AgreeOffColumn`-shaped identity, entry by entry, in the incoming
chart.** -/
theorem matrix_chartLabelling {coordinate₀ : Type*} [Fintype coordinate₀]
    [DecidableEq coordinate₀] (hValid : data.Valid)
    (labellingG : StableLengthMatrixLabelling base.gaugedData coordinate₀)
    (chart : Option coordinate₀ ≃ coordinate)
    (p : StablePath base.gaugedData) (c : coordinate₀) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling base hValid labellingG chart).presentation
        (chart (some (labellingG.row p))) (chart (some c)) =
      GluingDatum.LengthMatrixPresentation.matrix labellingG.presentation
        (labellingG.row p) c :=
  (NonTrivalentValencyThreeRowDictionary.matrix_reindexLabelling chart
    (labelling base hValid labellingG) _ _).trans
    (matrix_candidateLabelling base hValid labellingG p c)

end MatrixLabelling

/-! ## 5.  The common minor: the outgoing matrix against the incoming one -/

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
  (simpleBase : SimpleBase (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hValid : (contractDatum cover hc hab hOne).Valid)

/-- **The outgoing honest matrix equals the incoming one off the contracted
column**, entry by entry.  Rows correspond through `retainedRow` composed with
the two branch gauges on the outgoing side and
`StablePathFacetContraction.incomingRow` on the incoming side; columns through
the chart equivalence, which puts `Option.none` -- the new target occurrence
`t_1` and the bridge row `h_1` -- in the contracted column.  This is the common
minor `A_{\varphi_0}` of Part II, Lemma `lm:change-comb-type` (Section 5.1). -/
theorem matrix_chartLabelling_eq_incoming
    (chart : Option {column : chartIndex //
        column ≠ fd.labelling.targetEdge.symm contracted} ≃ chartIndex)
    (p : StablePath (contractDatum cover hc hab hOne))
    (column : {column : chartIndex //
      column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling simpleBase hValid
          (gaugedLabelling simpleBase hValid
            (wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates
              facet hRows hZeroCoord hPosCoord hFacetZero))
          chart).presentation
        (chart (some (wallRowIndex cover fd hc hab hOne hCompat hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
        (chart (some column)) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row (incomingRow cover fd hc hab hOne hCompat hForest p))
        column.1 := by
  have hRow := gaugedLabelling_row simpleBase hValid
    (wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero) p
  have hStep := matrix_chartLabelling simpleBase hValid
    (gaugedLabelling simpleBase hValid
      (wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates facet
        hRows hZeroCoord hPosCoord hFacetZero))
    chart (gaugeStablePath simpleBase hValid p) column
  rw [hRow] at hStep
  refine hStep.trans ?_
  rw [gaugedLabelling_matrix simpleBase hValid]
  exact matrix_wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates
    facet hRows hZeroCoord hPosCoord hFacetZero p column

end AgreeOffColumn

/-! ## 6.  The actual-wall headlines -/

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

/-- The entrywise common-minor conclusion at an actual three-valent wall, with
`DanglingCompatible` and `NoContractedReturn` filled in by their canonical
producers. -/
def MinorIdentity
    {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
    (simpleBase : SimpleBase (contractDatum cover hc hab hOne) wallStar anchorBlk)
    (hValid : (contractDatum cover hc hab hOne).Valid) : Prop :=
  ∀ (p : StablePath (contractDatum cover hc hab hOne))
    (column : {column : chartIndex //
      column ≠ fd.labelling.targetEdge.symm contracted}),
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling simpleBase hValid
          (gaugedLabelling simpleBase hValid
            (wallLabelling cover fd hc hab hOne
              (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab
                hOne hForest)
              hForest
              (NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar
                cover fd hc hab hOne wallStar)
              coordinates facet hRows hZeroCoord hPosCoord hFacetZero))
          chart).presentation
        (chart (some (wallRowIndex cover fd hc hab hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
            hForest)
          hForest
          (NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar
            cover fd hc hab hOne wallStar)
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
        (chart (some column)) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row (incomingRow cover fd hc hab hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
            hForest)
          hForest p))
        column.1

theorem minorIdentity
    {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
    (simpleBase : SimpleBase (contractDatum cover hc hab hOne) wallStar anchorBlk)
    (hValid : (contractDatum cover hc hab hOne).Valid) :
    MinorIdentity cover fd hc hab hOne hForest wallStar coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero chart simpleBase hValid :=
  fun p column ↦ matrix_chartLabelling_eq_incoming cover fd hc hab hOne
    (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
    hForest
    (NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar cover fd hc
      hab hOne wallStar)
    coordinates facet hRows hZeroCoord hPosCoord hFacetZero simpleBase hValid chart p
    column

end ActualWall

end DraismaVargas.LocalCases.NonTrivalentValencyThreeSimpleRowDictionary
