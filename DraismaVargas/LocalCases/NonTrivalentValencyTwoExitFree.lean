module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneExit

@[expose] public section

/-!
# The valency-two Base II link, with the strong no-return hypothesis removed

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (the labelling
convention at a non-trivalent wall and `lm:change-comb-type`) together with
Section 5.4 (Case {v2-nd4}, base tree `T_2` = Base II, all three incoming
sub-cases `2 + 2`, `1 + 3`, `3 + 1`).  The consumer interface is
`OuterWalk.TypeChangeLink`.

`NonTrivalentValencyTwoExit` and `WallDatumPathEnds.typeChangeLink_of_receipts'`
both take `hNoReturn : StablePathFacetContraction.NoContractedReturn wd.cover
wd.contracted`, the **strong** no-return condition.  It holds in the `2 + 2`
incoming sub-case (`NonTrivalentValencyTwoExit.noContractedReturn_of_two_two`)
but is **false** in the `1 + 3` / `3 + 1` leaf sub-cases (`LeafFacetNoReturn`),
where Base II is still the prescribed exit: the incoming `2 + 2` / `1 + 3` /
`3 + 1` trichotomy is orthogonal to Base I versus Base II, and Base I exists
only in Configuration A with equal index pairs
(`NonTrivalentValencyTwoBaseOneRowDictionary`, "Which sub-cases Base I is
prescribed for").  The Base I modules already provide the two
no-return-free ingredients this module carries over to Base II:

* `NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two` --
  the wall datum's own square honest labelling at **every** two-valent wall,
  with the two abstract facts (`hRowVal`: its row index is the incoming row
  with `facet` and the contracted column transposed; `hMatrixWall`: the
  `matrix_wallLabelling` identity), dispatching `2 + 2` via
  `StablePathFacetContraction.noContractedReturn_of_nonleaf` and `1 + 3` /
  `3 + 1` via the leaf witnesses of `NonTrivalentValencyTwoLeafDictionary`.  It
  does not depend on `BaseOneSetup` at all, so it is reused here verbatim.
* `NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two` -- the
  weakened no-return condition `LeafFacetNoReturn.NoContractedReturnOffRow`,
  at every two-valent wall, no sub-case hypothesis.

Together with `WallDatumPathEnds.hasPathEnds_candidate`, which only needs the
*weak* `NoContractedReturnOffRow` to produce `HasPathEnds` of the Base II
candidate, these remove the strong hypothesis from every field of
`NonTrivalentValencyTwoExit.outgoingFD` and hence from
`typeChangeLink_of_receipts` and its statement at the wall data.

## What is proved

* `outLabelling'`, and the lemmas `NonTrivalentValencyTwoExit` proves about
  `outLabelling`, re-proved for it with the wall labelling **abstracted** to a
  `labelling₀` argument (exactly the `hRowVal` / `hMatrixWall` shape of the
  Base I modules, dropping the gauge machinery Base I needs and Base II does
  not): `matrix_outLabelling'_eq_incoming`, `outLabelling'_row_symm_facet`,
  `matrix_outLabelling'_facet_eq_zero`, `matrix_outLabelling'_corner_pos`,
  `agreeOffColumn_outLabelling'`, `det_outLabelling'_ne_zero`.  The two bridge
  occurrence facts (`NonTrivalentValencyTwoExit.occurrences_bridgeRow_of_ne`,
  `.occurrences_bridgeRow_new`) do not mention the wall labelling at all, so
  they are reused unchanged rather than re-proved.
* `outLabelling'_eq_outLabelling`: under the strong `hNoReturn`, instantiating
  `labelling₀ := NonTrivalentValencyTwoExit.wallLab ...` makes `outLabelling'`
  **definitionally** `NonTrivalentValencyTwoExit.outLabelling` (`rfl`).
* `outgoingFD'`: `NonTrivalentValencyTwoExit.outgoingFD` with `hNoReturn`
  (strong) replaced by `labelling₀`, `hRowVal`, `hMatrixWall` and the **weak**
  `LeafFacetNoReturn.NoContractedReturnOffRow`; trivalence and the target
  facts are reused from `NonTrivalentValencyTwoExit` unchanged (they never
  depended on the wall labelling), and path ends come from
  `WallDatumPathEnds.hasPathEnds_candidate` directly, so `HasPathEnds` is
  **derived**, not carried as a hypothesis.
* `wallOutgoingFD'`: the same at the wall data of the outer walk, discharging
  the weak no-return hypothesis internally via
  `NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two`, so no
  no-return hypothesis of any kind reaches its interface.
* `typeChangeLink_of_receipts_free`: the Base II inhabitant of
  `OuterWalk.TypeChangeLink` at a two-valent wall with **no no-return
  hypothesis**, `tracks` the only hypothesis (the prescribed pair `sel` is
  carried exactly as in `NonTrivalentValencyTwoExit`).
* `exists_typeChangeLink_baseTwo_of_wallData`: the statement at the wall data,
  on the pattern of
  `NonTrivalentValencyTwoBaseOneExit.exists_typeChangeLink_baseOne_of_wallData`.
  From `wd` and the incoming `TwoStar` alone it produces the anchor block and
  `nd(A) = 4`; for **every** `sel : Prescribed.Selection ...` (Base II needs
  no Configuration-A dispatch data, unlike Base I) it produces the outgoing
  presentation `out`, the common minor
  `AgreeOffColumn wd.incomingMatrix (matrix out.labelling.presentation)
  wd.column`, and `∀ tracks : Tracks out (graph.move m) label, Nonempty
  (TypeChangeLink m wd)`.
* `wallOutgoingFD'_eq` and `tracks_wallOutgoingFD'_of_tracks_wallOutgoingFD`:
  under the strong `hNoReturn`, instantiating `labelling₀` by
  `NonTrivalentValencyTwoExit.wallLab` (and `hRowVal`/`hMatrixWall` by
  `wallLab_row_val` / `StablePathFacetContraction.matrix_wallLabelling`) makes
  `wallOutgoingFD'` **definitionally** `NonTrivalentValencyTwoExit.wallOutgoingFD`
  (`rfl`), so a `Tracks` proved against the latter transfers unchanged to
  `wallOutgoingFD'` with no re-proof.

## What is NOT proved -- the hypotheses that remain explicit

1. `hRowVal`, `hMatrixWall`: the two abstract facts about the wall labelling
   `labelling₀`.  They are discharged at every actual two-valent wall by
   `NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two`,
   which `exists_typeChangeLink_baseTwo_of_wallData` invokes;
   `outgoingFD'` / `wallOutgoingFD'` themselves stay generic over any
   labelling satisfying them.
2. `tracks : InteriorGraphTracking.Tracks (wallOutgoingFD' ...) (graph.move m)
   label`: the dart-level dictionary between the candidate's stable graph and
   the Whitehead move, exactly as in `NonTrivalentValencyTwoExit`.  Carried as
   a hypothesis of `typeChangeLink_of_receipts_free`, so the rest of the link
   is proved here.
3. The incoming `TwoStar` at the contracted wall, as in
   `NonTrivalentValencyTwoExit`, `WallDatumPathEnds` and the Base I exit.

Nothing here identifies a graph by a matrix.

## Consumers

`OuterWalk.TypeChangeLink` (hence `OuterWalk.coneEntry_of_reaches` and the
type-change link of the outer walk) at Part II, Case {v2-nd4}, in the `1 + 3`
and `3 + 1` incoming sub-cases, which
`NonTrivalentValencyTwoExit.typeChangeLink_of_receipts` does not reach.
`NonTrivalentValencyTwoTracks` builds `tracks` against
`NonTrivalentValencyTwoExit.wallOutgoingFD`; the transfer lemmas here let that
work feed `typeChangeLink_of_receipts_free` without change.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoExitFree

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.NonTrivalentValencyTwoAnchor
open DraismaVargas.LocalCases.NonTrivalentValencyTwoCandidate
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoRowEquiv

noncomputable section

/-! ## 1.  The outgoing honest labelling, with the wall labelling abstracted -/

section OutLabelling

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (facet : coordinate)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
    {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted})

variable {wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlk)

/-- **The outgoing honest labelling, with the wall labelling abstracted.**
Exactly `NonTrivalentValencyTwoExit.outLabelling`'s construction, with the
strong-no-return-built `wallLab` replaced by an arbitrary `labelling₀`
satisfying the two facts `matrix_outLabelling'_eq_incoming` below needs. -/
def outLabelling' :
    StableLengthMatrixLabelling (Prescribed.validCandidate sel).datum coordinate :=
  NonTrivalentValencyTwoExit.reindexLabelling₂ (NonTrivalentValencyTwoExit.rowChart cover fd
      facet) (NonTrivalentValencyTwoExit.colChart cover fd)
    (NonTrivalentValencyTwoRowEquiv.labelling src sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd labelling₀)

theorem matrix_outLabelling'_eq_incoming
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
        (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd).presentation
        i j =
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
  set p := labelling₀.row.symm d with hpDef
  have hrow : labelling₀.row p = d := Equiv.apply_symm_apply _ _
  have hi' : NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted)
      (some d) = i := by
    rw [NonTrivalentValencyTwoExit.rowChart_some]
    exact Equiv.swap_apply_self _ _ i
  have hMid := NonTrivalentValencyTwoExit.matrix_reindexLabelling₂
    (NonTrivalentValencyTwoExit.rowChart cover fd facet)
    (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted))
    (NonTrivalentValencyTwoRowEquiv.labelling src sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd labelling₀)
    (some d) (some ⟨j, hj⟩)
  rw [hi'] at hMid
  have hPath : fd.labelling.row (incomingRow cover fd hc hab hOne
      (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
      hForest p) = i := by
    have hval := hRowVal p
    rw [hrow] at hval
    refine (Equiv.swap facet (fd.labelling.targetEdge.symm contracted)).injective ?_
    rw [← hval, Equiv.swap_comm]
  refine Eq.trans hMid ?_
  rw [← hrow]
  refine Eq.trans (NonTrivalentValencyTwoRowDictionary.matrix_candidateLabelling src sel
    (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd labelling₀ p
    ⟨j, hj⟩) ?_
  refine Eq.trans (hMatrixWall p ⟨j, hj⟩) ?_
  rw [hPath]

/-! ### The bridge row -/

theorem outLabelling'_row_symm_facet :
    (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd).row.symm facet =
      NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) := by
  have h : (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd).row
      (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)) = facet := by
    show (NonTrivalentValencyTwoExit.rowChart cover fd facet (contracted := contracted))
        ((NonTrivalentValencyTwoRowEquiv.labelling src sel
          (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
          labelling₀).row
          (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
            (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest))) = facet
    have hb : (NonTrivalentValencyTwoRowEquiv.labelling src sel
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest) hOrd
        labelling₀).row
        (NonTrivalentValencyTwoRowEquiv.bridgeRow src sel
          (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest)) = none :=
      NonTrivalentValencyTwoRowEquiv.labelling_row_bridge src sel _ hOrd _
    rw [hb]
    rfl
  exact (Equiv.symm_apply_eq _).mpr h.symm

theorem matrix_outLabelling'_facet_eq_zero (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd).presentation
        facet j = 0 := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq,
    outLabelling'_row_symm_facet cover fd hc hab hOne hForest facet labelling₀ src sel hOrd]
  have hTarget : (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel
        hOrd).targetEdge j ≠
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate sel).right none := by
    have hSymm : (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm
        j = some ⟨j, hj⟩ := Equiv.optionSubtypeNe_symm_of_ne hj
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate sel).right
        (Option.map _ ((NonTrivalentValencyTwoExit.colChart cover fd
          (contracted := contracted)).symm j)) ≠ _
    intro hBad
    have hNone := (TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (Prescribed.validCandidate sel).right).injective hBad
    rw [hSymm] at hNone
    simp at hNone
  unfold StableSourceMatrix.matrix
  rw [NonTrivalentValencyTwoExit.occurrences_bridgeRow_of_ne cover fd hc hab hOne hForest src sel
    _ hTarget, Finset.sum_empty]

theorem matrix_outLabelling'_corner_pos :
    0 < GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd).presentation
        facet (fd.labelling.targetEdge.symm contracted) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq,
    outLabelling'_row_symm_facet cover fd hc hab hOne hForest facet labelling₀ src sel hOrd]
  have hSymm : (NonTrivalentValencyTwoExit.colChart cover fd (contracted := contracted)).symm
      (fd.labelling.targetEdge.symm contracted) = none :=
    Equiv.optionSubtypeNe_symm_self _
  have hTarget : (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel
        hOrd).targetEdge (fd.labelling.targetEdge.symm contracted) =
      TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate sel).right none := by
    show TargetExpansion.occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (Prescribed.validCandidate sel).right
        (Option.map _ ((NonTrivalentValencyTwoExit.colChart cover fd
          (contracted := contracted)).symm (fd.labelling.targetEdge.symm contracted))) = _
    rw [hSymm]
    rfl
  rw [hTarget]
  unfold StableSourceMatrix.matrix
  rw [NonTrivalentValencyTwoExit.occurrences_bridgeRow_new cover fd hc hab hOne hForest src sel,
    Finset.sum_singleton]
  exact div_pos one_pos
    (by exact_mod_cast (Prescribed.validCandidate sel).datum.sourceEdgeIndex_pos _)

/-! ### The common minor and nonsingularity -/

theorem agreeOffColumn_outLabelling'
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
    (coordinates : coordinate → ℚ)
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    AgreeOffColumn (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
      (GluingDatum.LengthMatrixPresentation.matrix
        (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd).presentation)
      (fd.labelling.targetEdge.symm contracted) := by
  intro i j hj
  by_cases hi : i = facet
  · rw [hi, matrix_outLabelling'_facet_eq_zero cover fd hc hab hOne hForest facet labelling₀
      src sel hOrd j hj]
    exact NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj
  · exact (matrix_outLabelling'_eq_incoming cover fd hc hab hOne hForest facet labelling₀ src
      sel hOrd hRowVal hMatrixWall i j hi hj).symm

/-- **Nonsingularity of the outgoing matrix**, by the common-minor expansion
along the bridge row (`NonTrivalentLinkMatrix.det_ne_zero`), exactly as
`NonTrivalentValencyTwoExit.det_outLabelling_ne_zero`. -/
theorem det_outLabelling'_ne_zero
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
    (coordinates : coordinate → ℚ)
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd).presentation).det
      ≠ 0 :=
  NonTrivalentLinkMatrix.det_ne_zero
    (agreeOffColumn_outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd
      hRowVal hMatrixWall coordinates hZeroCoord hPosCoord hFacetZero)
    (fun j hj ↦ NonTrivalentValencyTwoExit.incoming_facet_eq_zero cover fd coordinates facet
      hZeroCoord hPosCoord hFacetZero j hj)
    (fun j hj ↦ matrix_outLabelling'_facet_eq_zero cover fd hc hab hOne hForest facet labelling₀
      src sel hOrd j hj)
    fd.det_ne_zero
    (matrix_outLabelling'_corner_pos cover fd hc hab hOne hForest facet labelling₀ src sel
      hOrd).ne'

end OutLabelling

/-! ### `outLabelling'` under the strong no-return hypothesis is `outLabelling` -/

section OutLabellingEq

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (facet : coordinate)

variable {wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlk)

/-- **Under the strong no-return hypothesis, `outLabelling'` is
definitionally `NonTrivalentValencyTwoExit.outLabelling`.**  Instantiating the
abstract `labelling₀` by `NonTrivalentValencyTwoExit.wallLab` (built from
`hNoReturn`) makes the two constructions the same term. -/
theorem outLabelling'_eq_outLabelling
    (hNoReturn : NoContractedReturn cover contracted)
    (coordinates : coordinate → ℚ)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    outLabelling' cover fd hc hab hOne hForest facet
        (NonTrivalentValencyTwoExit.wallLab cover fd hc hab hOne hForest hNoReturn coordinates
          facet hRows hZeroCoord hPosCoord hFacetZero) src sel hOrd =
      NonTrivalentValencyTwoExit.outLabelling cover fd hc hab hOne hForest hNoReturn coordinates
        facet hRows hZeroCoord hPosCoord hFacetZero src sel hOrd := rfl

end OutLabellingEq

/-! ## 2.  The outgoing full-dimensional presentation, no strong no-return -/

section OutgoingFD

variable {targetIn : CFGraph} {deg : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum targetIn deg)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : targetIn.V} {contracted : targetIn.edges}
  (hc : (contracted : targetIn.V × targetIn.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges targetIn a b = 1)
  (hForest : ContractionForest cover a b contracted)
  (facet : coordinate)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
    {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted})

variable {wallStar : TwoStar (contract targetIn hab hOne) ⟨a, hab⟩}
  {anchorBlk : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩}
  (src : TwoBranchAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum cover hc hab hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlk)

/-- **The outgoing full-dimensional source presentation at a two-valent wall,
with no strong no-return hypothesis.**  Every field is derived exactly as in
`NonTrivalentValencyTwoExit.outgoingFD`, except that the labelling is the
abstract `labelling₀` and `HasPathEnds` is produced from the *weak*
`LeafFacetNoReturn.NoContractedReturnOffRow` by
`WallDatumPathEnds.hasPathEnds_candidate`, rather than carried as a
hypothesis. -/
def outgoingFD'
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
    (coordinates : coordinate → ℚ)
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0)
    (hNoReturn : LeafFacetNoReturn.NoContractedReturnOffRow cover contracted
      (fd.labelling.row.symm facet)) :
    FullDimensionalSourcePresentation (Prescribed.validCandidate sel).datum coordinate :=
  NonTrivalentValencyTwoExit.ofTypeChange fd
    (Prescribed.validCandidate_datum_valid sel
      (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest))
    (NonTrivalentValencyTwoExit.outgoing_targetConnected cover fd hc hab hOne sel)
    (NonTrivalentValencyTwoExit.outgoing_targetGenus cover fd hc hab hOne sel)
    (NonTrivalentValencyTwoExit.outgoing_targetEdgeCard cover hc hab hOne sel)
    ((NonTrivalentValencyTwoRows.candidate_sourceGenus sel).trans
      (NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum cover hc hab hOne hForest))
    (outLabelling' cover fd hc hab hOne hForest facet labelling₀ src sel hOrd)
    (det_outLabelling'_ne_zero cover fd hc hab hOne hForest facet labelling₀ src sel hOrd hRowVal
      hMatrixWall coordinates hZeroCoord hPosCoord hFacetZero)
    (NonTrivalentValencyTwoExit.candidate_trivalent cover fd hc hab hOne hForest src sel hOrd)
    (WallDatumPathEnds.hasPathEnds_candidate cover fd hc hab hOne hForest coordinates facet
      hNoReturn hZeroCoord hPosCoord hFacetZero src sel hOrd)

end OutgoingFD

end -- noncomputable section

/-! ## 3.  The link at a wall of the outer walk -/

section Link

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
    anchorBlk)
  (labelling₀ : StableLengthMatrixLabelling (contractDatum wd.cover wd.hc wd.hab wd.hOne)
    {column : coordinate // column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted})
  (hRowVal : ∀ p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne),
    (labelling₀.row p).1 =
      Equiv.swap (label m.base) (wd.fullDim.labelling.targetEdge.symm wd.contracted)
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)))
  (hMatrixWall : ∀ (p : StablePath (contractDatum wd.cover wd.hc wd.hab wd.hOne))
    (column : {column : coordinate //
      column ≠ wd.fullDim.labelling.targetEdge.symm wd.contracted}),
    GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) column =
      GluingDatum.LengthMatrixPresentation.matrix wd.fullDim.labelling.presentation
        (wd.fullDim.labelling.row (incomingRow wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (WallAdmissibility.danglingCompatible_of_contractionForest wd.cover wd.hc wd.hab
            wd.hOne (wd.hForest m)) (wd.hForest m) p)) column.1)

/-- **The outgoing presentation at the wall data of the outer walk, with no
no-return hypothesis of any kind.**  The weak `NoContractedReturnOffRow` is
discharged internally by
`NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two`. -/
def wallOutgoingFD' : FullDimensionalSourcePresentation (Prescribed.validCandidate sel).datum
    coordinate :=
  outgoingFD' wd.cover wd.fullDim wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) labelling₀
    src sel hOrd hRowVal hMatrixWall wd.coordinates wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    (NonTrivalentValencyTwoBaseOneExit.noContractedReturnOffRow_two wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne wd.coordinates (label m.base) wd.hZeroCoord wd.hPosCoord wd.hFacetZero
      wallStar)

/-- **The Base II inhabitant of `OuterWalk.TypeChangeLink` at a two-valent
wall, with no no-return hypothesis.**  The base of the outgoing payload is the
wall datum itself (no branch gauge, as in `NonTrivalentValencyTwoExit`), the
candidate is the Base
II merge member, the presentation is `wallOutgoingFD'` and the common minor is
`agreeOffColumn_outLabelling'`. -/
def typeChangeLink_of_receipts_free
    (tracks : Tracks (wallOutgoingFD' m wd src sel hOrd labelling₀ hRowVal hMatrixWall)
      (graph.move m) label) :
    TypeChangeLink m wd where
  base := wd.wallDatum
  baseValid := wd.wallDatum_valid m
  candidate := Prescribed.validCandidate sel
  outgoingFD := wallOutgoingFD' m wd src sel hOrd labelling₀ hRowVal hMatrixWall
  tracks := tracks
  agree := by
    have h := agreeOffColumn_outLabelling' wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (label m.base) labelling₀ src sel hOrd hRowVal hMatrixWall wd.coordinates
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    rw [wd.targetEdge_symm_contracted] at h
    exact h

end

end Link

/-! ## 4.  The `Tracks` transfer from `NonTrivalentValencyTwoExit.wallOutgoingFD` -/

section Transfer

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)
  {wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  {anchorBlk : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩}
  (src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar anchorBlk)
  (hOrd : OrdinaryTrivalent (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
    anchorBlk)
  (hNoReturn : NoContractedReturn wd.cover wd.contracted)

/-- **Under the strong no-return hypothesis, `wallOutgoingFD'` is
definitionally `NonTrivalentValencyTwoExit.wallOutgoingFD`.**  Instantiating
`labelling₀` by `NonTrivalentValencyTwoExit.wallLab` (built from `hNoReturn`)
and `hRowVal` / `hMatrixWall` by `wallLab_row_val` /
`StablePathFacetContraction.matrix_wallLabelling` makes the two presentations
the same term, `HasPathEnds` included
(`WallDatumPathEnds.hasPathEnds_wallData` unfolds to exactly the same call to
`WallDatumPathEnds.hasPathEnds_candidate` with the weak no-return condition
produced from `hNoReturn` by
`LeafFacetNoReturn.noContractedReturnOffRow_of_noContractedReturn`). -/
theorem wallOutgoingFD'_eq :
    wallOutgoingFD' m wd src sel hOrd
        (NonTrivalentValencyTwoExit.wallLab wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hForest m) hNoReturn wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
          wd.hPosCoord wd.hFacetZero)
        (fun p ↦ NonTrivalentValencyTwoExit.wallLab_row_val wd.cover wd.fullDim wd.hc wd.hab
          wd.hOne (wd.hForest m) hNoReturn wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
          wd.hPosCoord wd.hFacetZero p)
        (fun p column ↦ StablePathFacetContraction.matrix_wallLabelling wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) hNoReturn wd.coordinates
          (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero p column) =
      NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
        (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel hOrd) := rfl

/-- **The `Tracks` transfer.**  A tracking of the ambient graph proved against
`NonTrivalentValencyTwoExit.wallOutgoingFD` (as in
`NonTrivalentValencyTwoTracks`) is, unchanged, a tracking against
`wallOutgoingFD'`. -/
def tracks_wallOutgoingFD'_of_tracks_wallOutgoingFD
    (tracks : Tracks (NonTrivalentValencyTwoExit.wallOutgoingFD m wd hNoReturn src sel hOrd
        (WallDatumPathEnds.hasPathEnds_wallData m wd hNoReturn src sel hOrd))
      (graph.move m) label) :
    Tracks (wallOutgoingFD' m wd src sel hOrd
        (NonTrivalentValencyTwoExit.wallLab wd.cover wd.fullDim wd.hc wd.hab wd.hOne
          (wd.hForest m) hNoReturn wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
          wd.hPosCoord wd.hFacetZero)
        (fun p ↦ NonTrivalentValencyTwoExit.wallLab_row_val wd.cover wd.fullDim wd.hc wd.hab
          wd.hOne (wd.hForest m) hNoReturn wd.coordinates (label m.base) wd.hRows wd.hZeroCoord
          wd.hPosCoord wd.hFacetZero p)
        (fun p column ↦ StablePathFacetContraction.matrix_wallLabelling wd.cover wd.fullDim
          wd.hc wd.hab wd.hOne (wd.hCompat m) (wd.hForest m) hNoReturn wd.coordinates
          (label m.base) wd.hRows wd.hZeroCoord wd.hPosCoord wd.hFacetZero p column))
      (graph.move m) label := by
  rw [wallOutgoingFD'_eq]
  exact tracks

end

end Transfer

/-! ## 5.  The statement at the wall data -/

section Headline

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {graph : CubicDartGraph D V} {label : D → coordinate}
  (m : graph.MoveData) {arrival : FacetArrival degree graph label (label m.base)}
  (wd : WallData arrival)

/-- **The Base II type-changing exit at a two-valent wall of the outer walk,
with no hypothesis about the candidate and no no-return hypothesis of any
kind.**  From the wall data alone (and the incoming two-valent star) this
produces the anchor block and `nd(A) = 4`; for *every*
`sel : Prescribed.Selection ...` (Base II needs no Configuration-A dispatch
data, unlike Base I) it produces the outgoing `FullDimensionalSourcePresentation`
on the incoming chart, the common minor `AgreeOffColumn` that
`OuterWalk.TypeChangeLink.agree` asks for, and the link itself as soon as
`InteriorGraphTracking.Tracks` is supplied. -/
theorem exists_typeChangeLink_baseTwo_of_wallData
    (wallStar : TwoStar (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩) :
    ∃ (anchorBlock : WallBlock (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩)
      (_src : TwoBranchAnchor (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
        anchorBlock),
      nonDanglingValency (contractDatum wd.cover wd.hc wd.hab wd.hOne)
          (WallBlock.sourceVertex (contractDatum wd.cover wd.hc wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
            anchorBlock) = 4 ∧
      ∀ sel : Prescribed.Selection (contractDatum wd.cover wd.hc wd.hab wd.hOne) wallStar
          anchorBlock,
        ∃ out : FullDimensionalSourcePresentation (Prescribed.validCandidate sel).datum
            coordinate,
          AgreeOffColumn wd.incomingMatrix
              (GluingDatum.LengthMatrixPresentation.matrix out.labelling.presentation)
              wd.column ∧
            ∀ _tracks : Tracks out (graph.move m) label, Nonempty (TypeChangeLink m wd) := by
  classical
  obtain ⟨anchorBlock, src, hNd, hSelection⟩ :=
    NonTrivalentValencyTwoRowEquiv.exists_rowEquiv_of_wall_metric wd.cover wd.fullDim wd.hc
      wd.hab wd.hOne (wd.hForest m) wallStar wd.coordinates (label m.base) wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  obtain ⟨-, -, hOrd, -, -⟩ :=
    hSelection (NonTrivalentValencyTwoCandidate.Prescribed.Selection.default src)
  obtain ⟨labelling₀, hRowVal, hMatrixWall⟩ :=
    NonTrivalentValencyTwoBaseOneRowDictionary.exists_wallLabelling_two wd.cover wd.fullDim
      wd.hc wd.hab wd.hOne (wd.hForest m) (label m.base) wallStar wd.coordinates wd.hRows
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
  refine ⟨anchorBlock, src, hNd, fun sel ↦ ?_⟩
  refine ⟨wallOutgoingFD' m wd src sel hOrd labelling₀ hRowVal hMatrixWall, ?_, ?_⟩
  · have h := agreeOffColumn_outLabelling' wd.cover wd.fullDim wd.hc wd.hab wd.hOne
      (wd.hForest m) (label m.base) labelling₀ src sel hOrd hRowVal hMatrixWall wd.coordinates
      wd.hZeroCoord wd.hPosCoord wd.hFacetZero
    rw [wd.targetEdge_symm_contracted] at h
    exact h
  · exact fun tracks ↦ ⟨typeChangeLink_of_receipts_free m wd src sel hOrd labelling₀ hRowVal
      hMatrixWall tracks⟩

end

end Headline

end DraismaVargas.LocalCases.NonTrivalentValencyTwoExitFree
