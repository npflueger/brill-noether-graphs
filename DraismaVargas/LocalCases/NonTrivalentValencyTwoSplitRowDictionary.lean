module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowEquiv
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoExitFree

@[expose] public section

/-!
# The valency-two Base II **split** `AgreeOffColumn` / common-minor identity

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (rigidity above `w_0`,
Lemma `lemma-above-w0`) with the labelling convention (1), Lemma
`lm:change-comb-type` (the wall matrix is the common minor `A_{\varphi_0}` of
the incoming matrices), Section 5.4 (Configuration A of Case `{v2-nd4}`, Case
`{v2-nd4-t3}`, the Base II members in which a `t_thick`-class splits above `u`
because `k_alpha > k_delta`), and Draisma--Vargas Part I (arXiv:1909.12924),
Case `{w2}` of Section 6, for the base tree `T_2`.

This module is `NonTrivalentValencyTwoBaseOneRowDictionary` ported from the
Base I rows of `NonTrivalentValencyTwoBaseOneRowEquiv` to the **split** rows of
`NonTrivalentValencyTwoSplitRowEquiv`.  Base I is the closer template than the
merge member's `NonTrivalentValencyTwoRowDictionary` because,
like Base I and unlike the merge, the split candidate lives over a *gauged* wall
datum -- here `NonTrivalentValencyTwoSplitGauge.splitGaugedData`, the inclusion
alignment gauge `e_delta ⊆ e_alpha` on the `t_thin` branch -- so the wall datum's
own square labelling has to be transported across the gauge before the chart is
re-indexed.

## What is different from Base I

* The gauge is the *inclusion* gauge `NonTrivalentValencyTwoSplitGauge.splitRelabeling`,
  not the equal-size gauge of `NonTrivalentValencyTwoGauge` used at Base I, so
  the gauge leg is re-proved against `splitGaugedData`.
  Both are `SheetRelabeling`s, so `SheetRelabelStable.matrix_map` still changes
  no entry.
* The row equivalence carries one more hypothesis:
  `NonTrivalentValencyTwoRowEquiv.OrdinaryTrivalent` of the datum the candidate
  lives over.  It is a statement about that datum
  only and is discharged at an actual wall (see the companion exit module).
* The bridge row is the split's `bridgeEdge` (the class `e_alpha ∖ e_delta`),
  which is alone in its stable class by
  `NonTrivalentValencyTwoSplitRows.bridgeEdge_isolated`; both of
  its occurrences -- it has exactly one -- lie over the new target occurrence,
  so the outgoing matrix vanishes along it off the contracted column.

## What is proved

* `retainedRowFree_injective`: the split retained-row map is injective,
  immediately from `NonTrivalentValencyTwoSplitRowEquiv.rowEquiv` being an
  `Equiv`.
* `occurrences_retainedRow`, `matrix_retainedRow`: the surviving occurrences of a
  retained row over an old target occurrence are exactly the retained copies of
  the surviving occurrences of that row of the datum the candidate lives over,
  hence the candidate's natural matrix in a retained row and an old column is
  that datum's own entry.
* `matrix_candidateLabelling`: the same in the honest `Option coordinate`
  indexing of `NonTrivalentValencyTwoSplitRowEquiv.labelling`.
* `splitGaugeRowEquiv`, `matrix_splitGaugeRowEquiv`, `splitRelabelLabelling`,
  `matrix_splitRelabelLabelling`, `matrix_candidateLabelling_gauged`: the
  transport across the inclusion alignment gauge.
* `chartLabelling`, `matrix_chartLabelling_eq_incoming`: the outgoing honest
  labelling on the incoming chart index type, and the entrywise identity against
  the incoming full-dimensional matrix off the vanishing row and the contracted
  column.
* `chartLabelling_row_symm_facet`, `occurrences_bridgeRow_of_ne`,
  `matrix_chartLabelling_facet_eq_zero`, `matrix_chartLabelling_corner_pos`: the
  bridge row `h_1` sits in the vanishing row of the incoming chart, its outgoing
  row vanishes off the contracted column, and its corner entry is strictly
  positive.
* `agreeOffColumn_chartLabelling`: the `AgreeOffColumn` shape, in every row --
  the common minor `A_{\varphi_0}` of `lm:change-comb-type`.

## Hypotheses left explicit here

* The incoming `FullDimensionalSourcePresentation`, the contraction data
  `hc, hab, hOne`, the actual `ContractionForest`, the incoming `TwoStar` and the
  Part II wall metric (`hZeroCoord, hPosCoord, hFacetZero`) are the caller's
  receipts, exactly as in the other valency-two row dictionaries and exits.
  `DanglingCompatible` is derived from the forest.
* The wall datum's own square labelling is taken abstractly as `labelling₀` with
  the two facts `hRowVal` / `hMatrixWall`; they are discharged at **every**
  two-valent wall by `NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two`,
  which the companion exit module invokes.
* `SplitAnchor` (whose producer at the gauged datum is
  `NonTrivalentValencyTwoSplitRows.splitAnchor_gauged` from `k_delta < k_alpha`)
  and `OrdinaryTrivalent` stay hypotheses.  Configuration A and the strict index
  inequality are the caller's dispatch data: Part II, Subcase
  `{v2-nd4-t3-k2<k3}`, says the Base I morphism does not exist when the index
  equalities fail, and the split is the member that does.
* No `FullDimensionalSourcePresentation` of the **outgoing** candidate is built
  here: `det ≠ 0`, trivalence, `HasPathEnds`, the outgoing target facts and
  `OuterWalk.TypeChangeLink` are `NonTrivalentValencyTwoSplitExit`.
* This module introduces **no new structure**; every definition is a transport of
  an existing one (`SheetRelabelStable.stablePathEquiv`,
  `NonTrivalentValencyTwoExit.reindexLabelling₂`).  Inhabitation of the
  structures it consumes is `NonTrivalentValencyTwoSplitCandidate.SplitSetup`
  together with `NonTrivalentValencyTwoSplitGauge.splitSetup_gauged` /
  `exists_splitCandidate_of_indices` and the five-sheet model `splitModel_*`.

## Consumers

`NonTrivalentValencyTwoSplitExit` and, through it, `OuterWalk.TypeChangeLink` at
Part II Case `{v2-nd4}`, Configuration A, the outgoing split Types I and II.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowDictionary

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
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitGauge
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv (OrdinaryTrivalent)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## 1.  Injectivity of the retained-row map, from the row equivalence -/

section Candidate

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (ra : SplitAnchor data star anchor)

local notation "cand" => (validCandidate ra.setup)

theorem retainedRowFree_injective (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor) :
    Function.Injective (retainedRowFree ra hValid) := by
  intro r r' hEq
  have h := congrArg (rowEquiv ra hValid hOrd) hEq
  simp only [rowEquiv_retainedRow] at h
  exact Option.some.inj h

/-! ## 2.  The candidate's matrix off the new column -/

theorem occurrences_retainedRow (hValid : data.Valid)
    (hInj : Function.Injective (retainedRowFree ra hValid))
    (r : StablePath data) (e : target.edges) :
    StableSourceMatrix.occurrences (cand).datum (retainedRowFree ra hValid r)
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
          (candidate_sourceGenus ra) old).mpr h)
      have hOcc : occurrenceEquiv target wall (cand).right (some old.1.1) =
          occurrenceEquiv target wall (cand).right (some e) := hTarget
      have hTargetEq : old.1.1 = e :=
        Option.some.inj ((occurrenceEquiv target wall (cand).right).injective hOcc)
      refine Finset.mem_image.mpr ⟨old, ?_, rfl⟩
      rw [StableSourceMatrix.mem_occurrences]
      exact ⟨⟨hOldSurv, hInj ((retainedRowFree_mk ra hValid ⟨old, hOldSurv⟩).trans hRow)⟩,
        hTargetEq⟩
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
    · exact (retainedRowFree_mk ra hValid ⟨g, hgS⟩).symm.trans
        (congrArg (retainedRowFree ra hValid) hgRow)
    · show occurrenceEquiv target wall (cand).right (some g.1.1) =
        occurrenceEquiv target wall (cand).right (some e)
      rw [hgTarget]

theorem matrix_retainedRow (hValid : data.Valid)
    (hInj : Function.Injective (retainedRowFree ra hValid))
    (r : StablePath data) (e : target.edges) :
    StableSourceMatrix.matrix (cand).datum (retainedRowFree ra hValid r)
        (occurrenceEquiv target wall (cand).right (some e)) =
      StableSourceMatrix.matrix data r e := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_retainedRow ra hValid hInj r e,
    Finset.sum_image (fun _ _ _ _ h ↦ ResolutionCut.oldSourceEdge_injective (cand) h)]
  exact Finset.sum_congr rfl fun g _ ↦ by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]

section MatrixLabelling

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

theorem matrix_candidateLabelling (hValid : data.Valid)
    (hOrd : OrdinaryTrivalent data wall anchor)
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (p : StablePath data) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (labelling ra hValid hOrd labelling₀).presentation
        (some (labelling₀.row p)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) c := by
  classical
  have hInj := retainedRowFree_injective ra hValid hOrd
  have hRowSymm :
      (labelling ra hValid hOrd labelling₀).row.symm
          (some (labelling₀.row p)) = retainedRowFree ra hValid p := by
    rw [Equiv.symm_apply_eq]
    exact (labelling_row_retained ra hValid hOrd labelling₀ p).symm
  have hTgt :
      (labelling ra hValid hOrd labelling₀).targetEdge (some c) =
        occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) := rfl
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    hRowSymm, hTgt, Equiv.symm_apply_apply]
  exact matrix_retainedRow ra hValid hInj p (labelling₀.targetEdge c)

end MatrixLabelling

end Candidate

/-! ## 3.  Across the inclusion alignment gauge -/

section Gauge

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (base : GluingDatum target degree) (star : TwoStar target wall)
  (anchor : WallBlock base wall) (thickSheet thinSheet : Fin degree)
  (hConn : base.Connected)

/-- The stable rows of the gauged datum, read through the literal source-edge map
of the inclusion alignment gauge. -/
noncomputable def splitGaugeRowEquiv :
    StablePath base ≃ StablePath (splitGaugedData base star anchor thickSheet thinSheet) :=
  SheetRelabelStable.stablePathEquiv (splitRelabeling base star anchor thickSheet thinSheet)
    hConn

/-- Every natural matrix column is unchanged by the gauge. -/
theorem matrix_splitGaugeRowEquiv (q : StablePath base) (place : target.edges) :
    StableSourceMatrix.matrix (splitGaugedData base star anchor thickSheet thinSheet)
        (splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn q) place =
      StableSourceMatrix.matrix base q place :=
  SheetRelabelStable.matrix_map (splitRelabeling base star anchor thickSheet thinSheet)
    hConn q place

/-- A square honest labelling of the incoming wall datum, transported across the
inclusion alignment gauge.  The target is unchanged; the rows follow the literal
source-edge map. -/
noncomputable def splitRelabelLabelling
    (labelling₀ : StableLengthMatrixLabelling base coordinate) :
    StableLengthMatrixLabelling (splitGaugedData base star anchor thickSheet thinSheet)
      coordinate where
  targetEdge := labelling₀.targetEdge
  row := (splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn).symm.trans
    labelling₀.row

omit [Fintype coordinate] [DecidableEq coordinate] in
@[simp] theorem splitRelabelLabelling_targetEdge
    (labelling₀ : StableLengthMatrixLabelling base coordinate) (c : coordinate) :
    (splitRelabelLabelling base star anchor thickSheet thinSheet hConn labelling₀).targetEdge
        c = labelling₀.targetEdge c := rfl

omit [Fintype coordinate] [DecidableEq coordinate] in
@[simp] theorem splitRelabelLabelling_row
    (labelling₀ : StableLengthMatrixLabelling base coordinate) (q : StablePath base) :
    (splitRelabelLabelling base star anchor thickSheet thinSheet hConn labelling₀).row
        (splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn q) =
      labelling₀.row q := by
  show labelling₀.row ((splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn).symm
    ((splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn) q)) = _
  rw [Equiv.symm_apply_apply]

/-- The gauge changes no matrix entry: the rows are re-indexed by the literal
source-edge map, and `SheetRelabelStable.matrix_map` transports every column. -/
theorem matrix_splitRelabelLabelling
    (labelling₀ : StableLengthMatrixLabelling base coordinate)
    (q : StablePath base) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (splitRelabelLabelling base star anchor thickSheet thinSheet hConn
          labelling₀).presentation (labelling₀.row q) c =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row q) c := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    Equiv.symm_apply_apply]
  have hRow : (splitRelabelLabelling base star anchor thickSheet thinSheet hConn
      labelling₀).row.symm (labelling₀.row q) =
      splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn q := by
    rw [Equiv.symm_apply_eq]
    exact (splitRelabelLabelling_row base star anchor thickSheet thinSheet hConn
      labelling₀ q).symm
  rw [hRow, splitRelabelLabelling_targetEdge]
  exact matrix_splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn q
    (labelling₀.targetEdge c)

/-- **The split candidate's honest matrix against the incoming wall datum's,
across the gauge.** -/
theorem matrix_candidateLabelling_gauged
    (ra : SplitAnchor (splitGaugedData base star anchor thickSheet thinSheet) star
      (splitGaugedAnchor base star anchor thickSheet thinSheet))
    (hGauged : (splitGaugedData base star anchor thickSheet thinSheet).Valid)
    (hOrd : OrdinaryTrivalent (splitGaugedData base star anchor thickSheet thinSheet) wall
      (splitGaugedAnchor base star anchor thickSheet thinSheet))
    (labelling₀ : StableLengthMatrixLabelling base coordinate)
    (q : StablePath base) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (labelling ra hGauged hOrd
          (splitRelabelLabelling base star anchor thickSheet thinSheet hConn
            labelling₀)).presentation
        (some (labelling₀.row q)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row q) c := by
  have h := matrix_candidateLabelling ra hGauged hOrd
    (splitRelabelLabelling base star anchor thickSheet thinSheet hConn labelling₀)
    (splitGaugeRowEquiv base star anchor thickSheet thinSheet hConn q) c
  rw [splitRelabelLabelling_row] at h
  exact h.trans
    (matrix_splitRelabelLabelling base star anchor thickSheet thinSheet hConn labelling₀ q c)

end Gauge

/-! ## 4.  The outgoing chart at an actual two-valent wall -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyTwoExit (reindexLabelling₂
  matrix_reindexLabelling₂ rowChart colChart rowChart_none rowChart_some colChart_none
  colChart_some incoming_facet_eq_zero)

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (facet : coordinate)
  (wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩)
  (anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
  (thickSheet thinSheet : Fin deg)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
    {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted})

/-- **The outgoing honest labelling of a split candidate, in the incoming
chart.**  Rows and columns are re-indexed by two *different* equivalences, on
`NonTrivalentValencyTwoExit.reindexLabelling₂`'s convention: the new target
occurrence `t_1` goes into the vanishing column and the bridge row `h_1` into the
vanishing row `facet`. -/
noncomputable def chartLabelling
    (ra : SplitAnchor
      (splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet) wallStar
      (splitGaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet))
    (hGauged : (splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk
      thickSheet thinSheet).Valid)
    (hOrd : OrdinaryTrivalent (splitGaugedData (contractDatum cover hc hab hOne) wallStar
      anchorBlk thickSheet thinSheet) ⟨a, hab⟩
      (splitGaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet)) :
    StableLengthMatrixLabelling (validCandidate ra.setup).datum coordinate :=
  reindexLabelling₂ (rowChart cover fd facet) (colChart cover fd)
    (labelling ra hGauged hOrd
      (splitRelabelLabelling (contractDatum cover hc hab hOne) wallStar anchorBlk
        thickSheet thinSheet
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1 labelling₀))

/-- **The common minor, entry by entry.**  Off the vanishing row and the
contracted column the outgoing matrix is the incoming matrix. -/
theorem matrix_chartLabelling_eq_incoming
    (ra : SplitAnchor
      (splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet) wallStar
      (splitGaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet))
    (hGauged : (splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk
      thickSheet thinSheet).Valid)
    (hOrd : OrdinaryTrivalent (splitGaugedData (contractDatum cover hc hab hOne) wallStar
      anchorBlk thickSheet thinSheet) ⟨a, hab⟩
      (splitGaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet))
    (hRowVal : ∀ p : StablePath (contractDatum cover hc hab hOne),
      (labelling₀.row p).1 =
        Equiv.swap facet (fd.labelling.targetEdge.symm contracted)
          (fd.labelling.row (incomingRow cover fd hc hab hOne
            (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
              hForest) hForest p)))
    (hMatrixWall : ∀ (p : StablePath (contractDatum cover hc hab hOne))
      (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
          (labelling₀.row p) column =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
          (fd.labelling.row (incomingRow cover fd hc hab hOne
            (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
              hForest) hForest p)) column.1)
    (i j : coordinate) (hi : i ≠ facet)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
          thinSheet labelling₀ ra hGauged hOrd).presentation i j =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation i j := by
  classical
  have hd : Equiv.swap (fd.labelling.targetEdge.symm contracted) facet i ≠
      fd.labelling.targetEdge.symm contracted := by
    intro h
    apply hi
    have h2 := congrArg (Equiv.swap (fd.labelling.targetEdge.symm contracted) facet) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
  set d : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} :=
    ⟨Equiv.swap (fd.labelling.targetEdge.symm contracted) facet i, hd⟩ with hdDef
  set q := labelling₀.row.symm d with hqDef
  have hrow : labelling₀.row q = d := Equiv.apply_symm_apply _ _
  have hi' : rowChart cover fd facet (contracted := contracted) (some d) = i := by
    rw [rowChart_some]
    exact Equiv.swap_apply_self _ _ i
  have hMid := matrix_reindexLabelling₂ (rowChart cover fd facet)
    (colChart cover fd (contracted := contracted))
    (labelling ra hGauged hOrd
      (splitRelabelLabelling (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1
        labelling₀)) (some d) (some ⟨j, hj⟩)
  rw [hi'] at hMid
  have hPath : fd.labelling.row (incomingRow cover fd hc hab hOne
      (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
      hForest q) = i := by
    have hval := hRowVal q
    rw [hrow] at hval
    refine (Equiv.swap facet (fd.labelling.targetEdge.symm contracted)).injective ?_
    rw [← hval, Equiv.swap_comm]
  refine Eq.trans hMid ?_
  rw [← hrow]
  refine Eq.trans (matrix_candidateLabelling_gauged (contractDatum cover hc hab hOne) wallStar
    anchorBlk thickSheet thinSheet
    (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1 ra hGauged hOrd
    labelling₀ q ⟨j, hj⟩) ?_
  refine Eq.trans (hMatrixWall q ⟨j, hj⟩) ?_
  rw [hPath]

/-! ## 5.  The bridge row, and the `AgreeOffColumn` shape -/

section Bridge

variable (ra : SplitAnchor
    (splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet) wallStar
    (splitGaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet))
  (hGauged : (splitGaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk
    thickSheet thinSheet).Valid)
  (hOrd : OrdinaryTrivalent (splitGaugedData (contractDatum cover hc hab hOne) wallStar
    anchorBlk thickSheet thinSheet) ⟨a, hab⟩
    (splitGaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
      thinSheet))

/-- The bridge row `h_1` sits in the vanishing row of the incoming chart. -/
theorem chartLabelling_row_symm_facet :
    (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ ra hGauged hOrd).row.symm facet =
      bridgeRow ra hGauged := by
  have h : (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
      thinSheet labelling₀ ra hGauged hOrd).row (bridgeRow ra hGauged) = facet := by
    show (rowChart cover fd facet (contracted := contracted))
        ((labelling ra hGauged hOrd
          (splitRelabelLabelling (contractDatum cover hc hab hOne) wallStar anchorBlk
            thickSheet thinSheet
            (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1
            labelling₀)).row (bridgeRow ra hGauged)) = facet
    rw [labelling_row_bridge ra hGauged hOrd
      (splitRelabelLabelling (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1
        labelling₀)]
    rfl
  exact (Equiv.symm_apply_eq _).mpr h.symm

/-- The bridge is alone in its stable class and its single occurrence lies over
the new target occurrence `t_1`, so the bridge row of the outgoing matrix
vanishes off the contracted column. -/
theorem occurrences_bridgeRow_of_ne
    (t : (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate ra.setup).right).edges)
    (ht : t ≠ occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate ra.setup).right none) :
    StableSourceMatrix.occurrences (validCandidate ra.setup).datum
      (bridgeRow ra hGauged) t = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro e he
  obtain ⟨⟨hSurv, hRow⟩, hTarget⟩ := (StableSourceMatrix.mem_occurrences _ t e).mp he
  have hEq : e = bridgeEdge ra := bridgeEdge_isolated ra hGauged ⟨e, hSurv⟩ hRow
  apply ht
  rw [← hTarget, hEq]
  exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem chartLabelling_targetEdge_ne (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ ra hGauged hOrd).targetEdge j ≠
      occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (validCandidate ra.setup).right none := by
  classical
  have hSymm : (colChart cover fd (contracted := contracted)).symm j = some ⟨j, hj⟩ :=
    Equiv.optionSubtypeNe_symm_of_ne hj
  show occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩ (validCandidate ra.setup).right
      (Option.map _ ((colChart cover fd (contracted := contracted)).symm j)) ≠ _
  intro hBad
  have hNone := (occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
    (validCandidate ra.setup).right).injective hBad
  rw [hSymm] at hNone
  simp at hNone

theorem chartLabelling_targetEdge_contracted :
    (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ ra hGauged hOrd).targetEdge
        (fd.labelling.targetEdge.symm contracted) =
      occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (validCandidate ra.setup).right none := by
  classical
  have hSymm : (colChart cover fd (contracted := contracted)).symm
      (fd.labelling.targetEdge.symm contracted) = none :=
    Equiv.optionSubtypeNe_symm_self _
  show occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩ (validCandidate ra.setup).right
      (Option.map _ ((colChart cover fd (contracted := contracted)).symm
        (fd.labelling.targetEdge.symm contracted))) = _
  rw [hSymm]
  rfl

/-- **The vanishing row of the outgoing matrix.** -/
theorem matrix_chartLabelling_facet_eq_zero (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
          thinSheet labelling₀ ra hGauged hOrd).presentation facet j = 0 := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, chartLabelling_row_symm_facet]
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_of_ne cover hc hab hOne wallStar anchorBlk thickSheet
    thinSheet ra hGauged _
    (chartLabelling_targetEdge_ne cover fd hc hab hOne hForest facet wallStar anchorBlk
      thickSheet thinSheet labelling₀ ra hGauged hOrd j hj), Finset.sum_empty]

/-- **The corner entry is positive**: the bridge's only occurrence lies over the
new target occurrence. -/
theorem matrix_chartLabelling_corner_pos :
    0 < GluingDatum.LengthMatrixPresentation.matrix
      (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ ra hGauged hOrd).presentation facet
      (fd.labelling.targetEdge.symm contracted) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, chartLabelling_row_symm_facet,
    chartLabelling_targetEdge_contracted]
  unfold StableSourceMatrix.matrix
  refine Finset.sum_pos (fun e _ ↦ div_pos one_pos (by
    exact_mod_cast (validCandidate ra.setup).datum.sourceEdgeIndex_pos e)) ?_
  refine ⟨bridgeEdge ra, ?_⟩
  refine (StableSourceMatrix.mem_occurrences _ _ _).mpr
    ⟨⟨bridgeEdge_survives ra hGauged, rfl⟩, ?_⟩
  exact BalancedGlobal.Candidate.newSourceEdge_target _ _

/-- **The common minor in `AgreeOffColumn` shape**: the outgoing honest matrix
agrees with the incoming one in *every* row off the contracted column.  Off the
vanishing row this is `matrix_chartLabelling_eq_incoming`; in the vanishing row
both matrices are zero there. -/
theorem agreeOffColumn_chartLabelling
    (coordinates : coordinate → ℚ)
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0)
    (hRowVal : ∀ p : StablePath (contractDatum cover hc hab hOne),
      (labelling₀.row p).1 =
        Equiv.swap facet (fd.labelling.targetEdge.symm contracted)
          (fd.labelling.row (incomingRow cover fd hc hab hOne
            (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
              hForest) hForest p)))
    (hMatrixWall : ∀ (p : StablePath (contractDatum cover hc hab hOne))
      (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
          (labelling₀.row p) column =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
          (fd.labelling.row (incomingRow cover fd hc hab hOne
            (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
              hForest) hForest p)) column.1) :
    AgreeOffColumn (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
      (GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
          thinSheet labelling₀ ra hGauged hOrd).presentation)
      (fd.labelling.targetEdge.symm contracted) := by
  intro i j hj
  by_cases hi : i = facet
  · rw [hi, matrix_chartLabelling_facet_eq_zero cover fd hc hab hOne hForest facet wallStar
      anchorBlk thickSheet thinSheet labelling₀ ra hGauged hOrd j hj]
    exact incoming_facet_eq_zero cover fd coordinates facet hZeroCoord hPosCoord hFacetZero
      j hj
  · exact (matrix_chartLabelling_eq_incoming cover fd hc hab hOne hForest facet wallStar
      anchorBlk thickSheet thinSheet labelling₀ ra hGauged hOrd hRowVal hMatrixWall i j hi
      hj).symm

end Bridge

end Wall

end DraismaVargas.LocalCases.NonTrivalentValencyTwoSplitRowDictionary
