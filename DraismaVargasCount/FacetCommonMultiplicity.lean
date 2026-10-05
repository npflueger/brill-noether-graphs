module

public import DraismaVargasCount.ValencyThreeRigidity
public import DraismaVargasCount.NonTrivalentNonfacetDenominator
public import DraismaVargasCount.StarCensusEngine

@[expose] public section

/-!
# Common multiplicity at a facet limit

**Source.**  Vargas, Part II (arXiv:2609.09109), `prop-signed-mult`(2) and
`lm:change-comb-type` (the wall matrix is the common minor of the incoming matrices),
and the labelling convention (1) of the subsection *Combinatorial setup and local
determinants* of the section on changing combinatorial type.  This module supplies the
common multiplicity at a facet limit, an input of the type-change parity (step 3 of
`Assembly`).

## What is proved

* **The glue (`absMult_eq_of_packages`).**  Two regrowths, over *any* two cores and at any two
  requests, whose limit data are geometrically isomorphic have the same multiplicity, as soon
  as each carries a `WallPackage`: the stable-row dictionary of its limit (Part II convention
  (1)) with the common-minor identity, read intrinsically through
  `StableSourceMatrix.matrix`, and its vanishing row supported on the degenerate column.
  The limit isomorphism re-indexes the second frame's presentation (`glueLabelling`: rows by
  `pathMap`, columns by `colPerm`, through the two dictionaries and
  `GeometricDatumIso.matrix_map`) so that it **agrees with the first off the degenerate
  column** (`glueLabelling_agree`), and `NonTrivalentNonfacetDenominator.signedMult_eq`
  (no residues) does the rest; multiplicity is labelling-independent
  (`absMult_labelling_indep`).
* **Every facet regrowth carries a package (`nonempty_wallPackage`)**, at a request with one
  vanishing slot `e₀`, positive elsewhere, provided `e₀` is not a loop of the core.  The
  dictionary is that of the contraction, dispatched on the endpoints of the contracted occurrence:
  both non-leaf (`StablePathFacetContraction.exists_wallLabelling_of_single_zero_row`), left
  leaf (`LeafFacetNoReturn.exists_wallLabelling_of_leaf_endpoint`), right leaf
  (`NonTrivalentValencyTwoLeafDictionary.noReturn_off_facet_right`); both leaves is excluded by
  the wall valency `2, 3, 4`
  (`NonTrivalentWallSetup.card_incidentEdges_merge_eq_two_three_or_four_of_noContractedCycle`).
  The simple end of the vanishing row comes from the core identification: a non-loop slot
  has incidence one at its tail.
* **Headlines.**  `absMult_eq_of_sameLimit` (regrowths, either core),
  `absMult_eq_of_specializes` (a class over `c` and a class over `c'` specialising to one
  coarse facet limit), `absMult_eq_of_mSpecializes` (metric form), the one-side forms
  `absMult_eq_of_specializesLeft_of_common` / `…Right…`, and `commonMult_of_facetDatum`
  (the common multiplicity at every facet datum whose slot is a non-loop of the far core).
* **The non-loop binder is free at a step** (`exists_facetDatum_nonloop`,
  `exists_facetDatum_commonMult`): every Whitehead step has a facet datum at the move's base
  slot, which is a non-loop of both cores (the reversed move, `FacetAdapterPilot.revMove`).
  At `cat_step`, an `example`.

## Inferences tested

* **"`signedMult_eq` plus one glue lemma": holds.**  The glue is not the
  matrix-level `ValencyThreeRigidity.exists_matrix_submatrix` / `transportLabelling` one
  might expect but the stable-row dictionary of the *contraction* (`StablePathFacetContraction`,
  `LeafFacetNoReturn`), which is what relates a frame's rows to its limit's rows; the limit
  isomorphism is then used only through `GeometricDatumIso.matrix_map`.  No valency case
  analysis beyond the leaf dispatch is needed, and nothing depends on the two cores being
  related by a step.
* **One further hypothesis**: the contracted slot must be a non-loop of each
  core (it supplies the vanishing row's simple end, hence the contraction forest).  On the
  near core it follows from `FacetDatum.shared` (`tail_ne_head_of_shared`); on the far core
  `SharedContractionSlot` as stated does not record it, so it is carried as `hl'`, and it is
  discharged at every Whitehead step for the move's own slot (`exists_facetDatum_nonloop`).

## What is NOT proved -- every hypothesis

* `hl'`: at an arbitrary `FacetMachine.FacetDatum` the slot is not shown to be a non-loop of
  the far core.  It holds at the datum `exists_facetDatum_nonloop` builds for each step,
  which is the one the `∃`-consumer uses.
* Nothing here counts classes; the census is `FacetCensus`.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.FacetCommonMultiplicity

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource (StablePath StableLengthMatrixLabelling)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.FacetMachine

variable {n p degree : ℕ}

/-- **The wall package of a regrowth**: the stable-row dictionary of its limit (Part II §5.1
convention (1)), with the limit's column dictionary, the common-minor identity read through
the intrinsic stable-source matrix, and the vanishing row `facet` supported on the degenerate
column.  Data, not a hypothesis: `nonempty_wallPackage` builds one at every regrowth with a
single vanishing request slot that is a non-loop of the core. -/
structure WallPackage {core : Core n p} {y : Fin p → ℚ} (w : Regrowth core y degree)
    (facet : Fin p) where
  col : {j : Fin p // j ≠ w.column} ≃ (w.frame.limitTarget w.column).edges
  row : StablePath w.limit ≃
    {P : StablePath w.frame.data // P ≠ w.frame.fullDim.labelling.row.symm facet}
  agree : ∀ (P : StablePath w.limit) (j : {j : Fin p // j ≠ w.column}),
    StableSourceMatrix.matrix w.limit P (col j) =
      StableSourceMatrix.matrix w.frame.data (row P).1
        (w.frame.fullDim.labelling.targetEdge j.1)
  supported : ∀ j, j ≠ w.column → w.frame.matrix facet j = 0

section Package

variable {core : Core n p} {y : Fin p → ℚ}

/-- **Every facet regrowth carries a wall package.** -/
theorem nonempty_wallPackage (w : Regrowth core y degree) {e₀ : Fin p}
    (hy : y e₀ = 0) (hpos : ∀ e, e ≠ e₀ → 0 < y e) (hloop : core.tail e₀ ≠ core.head e₀) :
    Nonempty (WallPackage w (w.frame.slot.symm e₀)) := by
  classical
  set k := w.frame with hk
  set fd := k.fullDim with hfd
  set contracted := k.edgeOf w.column with hcontracted
  have hc : (contracted : k.target.V × k.target.V) =
      ((contracted : k.target.V × k.target.V).1, (contracted : k.target.V × k.target.V).2) := rfl
  have hab := GluingContraction.fst_ne_snd contracted
  have hOne := k.numEdges_edgeOf w.column
  set coords := k.coordsAt y with hcoords
  set facet := k.slot.symm e₀ with hfacet
  have hsymm : fd.labelling.targetEdge.symm contracted = w.column := Equiv.symm_apply_apply _ _
  have hmul : ∀ r, (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coords r = y (k.slot r) := fun r ↦ congrFun (k.mulVec_coordsAt y) r
  have hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coords row ≠ 0 := by
    intro row hrow
    rw [hmul]
    refine (hpos _ fun h ↦ hrow ?_).ne'
    rw [hfacet, ← h, Equiv.symm_apply_apply]
  have hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coords facet = 0 := by
    rw [hmul, hfacet, Equiv.apply_symm_apply, hy]
  have hZeroCoord : coords (fd.labelling.targetEdge.symm contracted) = 0 := by
    rw [hsymm]; exact w.degenerate.1
  have hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coords column := by
    intro column hcol
    rw [hsymm] at hcol
    exact w.degenerate.2 column hcol
  have hNonneg : ∀ column, 0 ≤ coords column := by
    intro column
    by_cases h : column = fd.labelling.targetEdge.symm contracted
    · rw [h, hZeroCoord]
    · exact (hPosCoord column h).le
  have hrowFacet : fd.labelling.row.symm facet = k.ident.row.symm e₀ := by
    rw [hfacet]
    show fd.labelling.row.symm ((fd.labelling.row.symm.trans k.ident.row).symm e₀) = _
    simp
  have hEnd : SingleRowForest.HasSimpleEnd k.data (fd.labelling.row.symm facet) := by
    rw [hrowFacet]
    refine ⟨k.ident.vertex.symm (core.tail e₀), ?_⟩
    rw [k.ident.incidence, Equiv.apply_symm_apply]
    unfold coreIncidence
    simp [Ne.symm hloop]
  have hCycle := SingleRowForest.noContractedCycle_of_single_row fd.labelling coords hNonneg
    facet hRows hEnd
  have hVal := NonTrivalentWallSetup.card_incidentEdges_merge_eq_two_three_or_four_of_noContractedCycle
    fd coords hNonneg hCycle hc hab hOne hZeroCoord
  have hEnds := WallProgress.endpoints_of_contraction k.data hc hab hOne fd.valid fd.changeMinimal
  have hWall : ∃ labelling : StableLengthMatrixLabelling (GluingContraction.contractDatum k.data hc hab hOne)
        {column : Fin p // column ≠ fd.labelling.targetEdge.symm contracted},
      ∃ rowDictionary : StablePath (GluingContraction.contractDatum k.data hc hab hOne) ≃
        {row : StablePath k.data // row ≠ fd.labelling.row.symm facet},
        ∀ (wallRowValue : StablePath (GluingContraction.contractDatum k.data hc hab hOne))
          (column : {column : Fin p // column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix labelling.presentation
              (labelling.row wallRowValue) column =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (rowDictionary wallRowValue).1) column.1 := by
    by_cases hA : (GluingDatum.incidentEdges (contracted : k.target.V × k.target.V).1).card = 1
    · refine LeafFacetNoReturn.exists_wallLabelling_of_leaf_endpoint k.data fd hc hab hOne hA
        (by omega) coords facet hRows hEnd hZeroCoord hPosCoord hFacetZero
    · by_cases hB : (GluingDatum.incidentEdges (contracted : k.target.V × k.target.V).2).card = 1
      · exact LeafFacetNoReturn.exists_wallLabelling_of_noContractedReturnOffRow k.data fd hc hab
          hOne coords facet
          (NonTrivalentValencyTwoLeafDictionary.noReturn_off_facet_right k.data fd hc (by omega) hB
            (fd.labelling.row.symm facet)
            (fun e hRow ↦ NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet k.data
              fd coords facet hZeroCoord hPosCoord hFacetZero e
              (by rw [hRow, Equiv.apply_symm_apply])))
          hRows hEnd hZeroCoord hPosCoord hFacetZero
      · exact StablePathFacetContraction.exists_wallLabelling_of_single_zero_row k.data fd hc hab
          hOne (by omega) (by omega) coords facet hRows hEnd hZeroCoord hPosCoord hFacetZero
  obtain ⟨L, R, hL⟩ := hWall
  refine ⟨{ col := (Equiv.subtypeEquivRight fun j ↦ by rw [hsymm]).trans L.targetEdge
            row := R
            agree := fun P j ↦ ?_
            supported := fun j hj ↦ ValencyThreeRigidity.row_supported w hy j hj }⟩
  have h := hL P ⟨j.1, by rw [hsymm]; exact j.2⟩
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq] at h
  have e1 : L.row.symm (L.row P) = P := L.row.symm_apply_apply P
  rw [e1, Equiv.symm_apply_apply] at h
  exact h

end Package

section Glue

variable {c c' : Core n p} {y y' : Fin p → ℚ}

/-- The column permutation: the degenerate column to the degenerate column, a retained column
through the two column dictionaries and the limit isomorphism. -/
noncomputable def colPerm {w : Regrowth c y degree} {w' : Regrowth c' y' degree} {f f' : Fin p}
    (P : WallPackage w f) (P' : WallPackage w' f') (Ψ : GeometricDatumIso w.limit w'.limit) :
    Fin p ≃ Fin p :=
  (Equiv.optionSubtypeNe w.column).symm.trans
    ((Equiv.optionCongr (P.col.trans (Ψ.targetEdge.trans P'.col.symm))).trans
      (Equiv.optionSubtypeNe w'.column))

theorem colPerm_of_ne {w : Regrowth c y degree} {w' : Regrowth c' y' degree} {f f' : Fin p}
    (P : WallPackage w f) (P' : WallPackage w' f') (Ψ : GeometricDatumIso w.limit w'.limit)
    {j : Fin p} (hj : j ≠ w.column) :
    colPerm P P' Ψ j = (P'.col.symm (Ψ.targetEdge (P.col ⟨j, hj⟩))).1 := by
  simp only [colPerm, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hj,
    Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some]

theorem colPerm_ne {w : Regrowth c y degree} {w' : Regrowth c' y' degree} {f f' : Fin p}
    (P : WallPackage w f) (P' : WallPackage w' f') (Ψ : GeometricDatumIso w.limit w'.limit)
    {j : Fin p} (hj : j ≠ w.column) : colPerm P P' Ψ j ≠ w'.column := by
  rw [colPerm_of_ne P P' Ψ hj]
  exact (P'.col.symm _).2

/-- The stable-path bijection: the vanishing row to the vanishing row, a retained row through
the two row dictionaries and the limit isomorphism. -/
noncomputable def pathMap {w : Regrowth c y degree} {w' : Regrowth c' y' degree} {f f' : Fin p}
    (P : WallPackage w f) (P' : WallPackage w' f') (Ψ : GeometricDatumIso w.limit w'.limit) :
    StablePath w.frame.data ≃ StablePath w'.frame.data :=
  (Equiv.optionSubtypeNe (w.frame.fullDim.labelling.row.symm f)).symm.trans
    ((Equiv.optionCongr (P.row.symm.trans
      ((Ψ.stablePathEquiv (GluingContraction.connected_contractDatumAt _ _ _
        w.frame.fullDim.valid.1)).trans P'.row))).trans
      (Equiv.optionSubtypeNe (w'.frame.fullDim.labelling.row.symm f')))

theorem pathMap_facet {w : Regrowth c y degree} {w' : Regrowth c' y' degree} {f f' : Fin p}
    (P : WallPackage w f) (P' : WallPackage w' f') (Ψ : GeometricDatumIso w.limit w'.limit) :
    pathMap P P' Ψ (w.frame.fullDim.labelling.row.symm f) =
      w'.frame.fullDim.labelling.row.symm f' := by
  simp only [pathMap, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self,
    Equiv.optionCongr_apply, Option.map_none, Equiv.optionSubtypeNe_none]

theorem pathMap_of_ne {w : Regrowth c y degree} {w' : Regrowth c' y' degree} {f f' : Fin p}
    (P : WallPackage w f) (P' : WallPackage w' f') (Ψ : GeometricDatumIso w.limit w'.limit)
    {Q : StablePath w.frame.data} (hQ : Q ≠ w.frame.fullDim.labelling.row.symm f) :
    pathMap P P' Ψ Q = (P'.row (Ψ.stablePathEquiv (GluingContraction.connected_contractDatumAt _ _ _
        w.frame.fullDim.valid.1) (P.row.symm ⟨Q, hQ⟩))).1 := by
  simp only [pathMap, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hQ,
    Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some]

/-- The labelling of the second frame's datum on the first frame's rows and columns. -/
noncomputable def glueLabelling {w : Regrowth c y degree} {w' : Regrowth c' y' degree}
    {f f' : Fin p} (P : WallPackage w f) (P' : WallPackage w' f')
    (Ψ : GeometricDatumIso w.limit w'.limit) :
    StableLengthMatrixLabelling w'.frame.data (Fin p) where
  targetEdge := (colPerm P P' Ψ).trans w'.frame.fullDim.labelling.targetEdge
  row := (pathMap P P' Ψ).symm.trans w.frame.fullDim.labelling.row

/-- **The re-indexed presentation agrees with the first frame's off the degenerate column.** -/
theorem glueLabelling_agree {w : Regrowth c y degree} {w' : Regrowth c' y' degree}
    {f f' : Fin p} (P : WallPackage w f) (P' : WallPackage w' f')
    (Ψ : GeometricDatumIso w.limit w'.limit) :
    AgreeOffColumn w.frame.matrix
      (GluingDatum.LengthMatrixPresentation.matrix (glueLabelling P P' Ψ).presentation)
      w.column := by
  intro r j hj
  show GluingDatum.LengthMatrixPresentation.matrix w.frame.fullDim.labelling.presentation r j = _
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq]
  simp only [glueLabelling, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.trans_apply]
  by_cases hr : w.frame.fullDim.labelling.row.symm r = w.frame.fullDim.labelling.row.symm f
  · have hrf : r = f := w.frame.fullDim.labelling.row.symm.injective hr
    subst hrf
    rw [pathMap_facet]
    have h1 := P.supported j hj
    have h2 := P'.supported _ (colPerm_ne P P' Ψ hj)
    simp only [Frame.matrix] at h1 h2
    rw [StableSourceMatrix.labelling_matrix_eq] at h1 h2
    rw [h1, h2]
  · rw [pathMap_of_ne P P' Ψ hr, colPerm_of_ne P P' Ψ hj, ← P'.agree, Equiv.apply_symm_apply]
    have hW := P.agree (P.row.symm ⟨_, hr⟩) ⟨j, hj⟩
    rw [Equiv.apply_symm_apply] at hW
    exact hW.symm.trans (Ψ.matrix_map _ _ _).symm

/-- **The glue: geometrically isomorphic limits, equal multiplicity.** -/
theorem absMult_eq_of_packages {w : Regrowth c y degree} {w' : Regrowth c' y' degree}
    {f f' : Fin p} (P : WallPackage w f) (P' : WallPackage w' f')
    (Ψ : GeometricDatumIso w.limit w'.limit) : w.frame.absMult = w'.frame.absMult := by
  classical
  have hAgree := glueLabelling_agree P P' Ψ
  have hOut : ∀ j, j ≠ w.column → GluingDatum.LengthMatrixPresentation.matrix
      (StarCensusEngine.relabelFullDim w'.frame.fullDim
        (glueLabelling P P' Ψ)).labelling.presentation f j = 0 := fun j hj ↦ by
    rw [StarCensusEngine.relabelFullDim_labelling, ← hAgree f j hj]
    exact P.supported j hj
  have hEq := NonTrivalentNonfacetDenominator.signedMult_eq w.frame.fullDim
    (StarCensusEngine.relabelFullDim w'.frame.fullDim (glueLabelling P P' Ψ)) hAgree
    P.supported hOut
  show fdAbsMult w.frame.fullDim = fdAbsMult w'.frame.fullDim
  unfold fdAbsMult
  rw [absMult_labelling_indep w'.frame.fullDim.labelling (glueLabelling P P' Ψ)]
  exact congrArg abs hEq.symm

end Glue

section Facet

variable {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ}

/-- The multiplicity of a facet regrowth, on either side of the step. -/
noncomputable def regrowthMult : FacetRegrowth c c' y₀ degree → ℚ
  | Sum.inl w => w.frame.absMult
  | Sum.inr w => w.frame.absMult

/-- The contracted slot of a shared contraction is not a loop of the first core. -/
theorem tail_ne_head_of_shared (h : SharedContractionSlot c c' e₀) : c.tail e₀ ≠ c.head e₀ := by
  obtain ⟨v₀, v₁, hne, hends, -, -⟩ := h
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hne
  · rw [h1, h2]; exact hne.symm

/-- **Common multiplicity at a facet**: two facet regrowths, over either core, with the
same facet limit have the same multiplicity. -/
theorem absMult_eq_of_sameLimit (hpt : FacetPoint e₀ y₀) (hl : c.tail e₀ ≠ c.head e₀)
    (hl' : c'.tail e₀ ≠ c'.head e₀) {a b : FacetRegrowth c c' y₀ degree}
    (h : FacetRegrowth.SameLimit a b) : regrowthMult a = regrowthMult b := by
  obtain ⟨Ψ⟩ := h
  rcases a with w | w <;> rcases b with w' | w'
  · exact absMult_eq_of_packages (nonempty_wallPackage w hpt.1 hpt.2 hl).some
      (nonempty_wallPackage w' hpt.1 hpt.2 hl).some Ψ
  · exact absMult_eq_of_packages (nonempty_wallPackage w hpt.1 hpt.2 hl).some
      (nonempty_wallPackage w' hpt.1 hpt.2 hl').some Ψ
  · exact absMult_eq_of_packages (nonempty_wallPackage w hpt.1 hpt.2 hl').some
      (nonempty_wallPackage w' hpt.1 hpt.2 hl).some Ψ
  · exact absMult_eq_of_packages (nonempty_wallPackage w hpt.1 hpt.2 hl').some
      (nonempty_wallPackage w' hpt.1 hpt.2 hl').some Ψ

/-- **Common multiplicity at a facet datum**: it holds at every facet datum whose
contracted slot is also not a loop of the second core. -/
theorem commonMult_of_facetDatum {ε : ℚ} (hd : FacetDatum c c' degree e₀ y₀ ε)
    (hl' : c'.tail e₀ ≠ c'.head e₀) :
    ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b :=
  fun _ _ h ↦ absMult_eq_of_sameLimit hd.point (tail_ne_head_of_shared hd.shared) hl' h

end Facet

section Classes

open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight)

variable {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ}

/-- The class-level form, from the regrowth-level common multiplicity (across the sides). -/
theorem absMult_eq_of_specializes_of_common
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    {l : FacetLimit c c' y₀ degree} {x : FrameClass c degree} {x' : FrameClass c' degree}
    (hx : SpecializesLeft x l) (hx' : SpecializesRight x' l) : x.absMult = x'.absMult := by
  obtain ⟨w, rfl, hw⟩ := hx
  obtain ⟨w', rfl, hw'⟩ := hx'
  exact hmult (Sum.inl w) (Sum.inr w') (Quotient.exact (hw.trans hw'.symm))

/-- The same for two classes of the first core. -/
theorem absMult_eq_of_specializesLeft_of_common
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    {l : FacetLimit c c' y₀ degree} {x x' : FrameClass c degree}
    (hx : SpecializesLeft x l) (hx' : SpecializesLeft x' l) : x.absMult = x'.absMult := by
  obtain ⟨w, rfl, hw⟩ := hx
  obtain ⟨w', rfl, hw'⟩ := hx'
  exact hmult (Sum.inl w) (Sum.inl w') (Quotient.exact (hw.trans hw'.symm))

/-- The same for two classes of the second core. -/
theorem absMult_eq_of_specializesRight_of_common
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    {l : FacetLimit c c' y₀ degree} {x x' : FrameClass c' degree}
    (hx : SpecializesRight x l) (hx' : SpecializesRight x' l) : x.absMult = x'.absMult := by
  obtain ⟨w, rfl, hw⟩ := hx
  obtain ⟨w', rfl, hw'⟩ := hx'
  exact hmult (Sum.inr w) (Sum.inr w') (Quotient.exact (hw.trans hw'.symm))

/-- **Common multiplicity, class form**: a class over `c` and a class over `c'` specialising to one facet
limit have the same multiplicity. -/
theorem absMult_eq_of_specializes (hpt : FacetPoint e₀ y₀) (hl : c.tail e₀ ≠ c.head e₀)
    (hl' : c'.tail e₀ ≠ c'.head e₀) {l : FacetLimit c c' y₀ degree} {x : FrameClass c degree}
    {x' : FrameClass c' degree} (hx : SpecializesLeft x l) (hx' : SpecializesRight x' l) :
    x.absMult = x'.absMult :=
  absMult_eq_of_specializes_of_common (fun _ _ h ↦ absMult_eq_of_sameLimit hpt hl hl' h) hx hx'

/-- **Common multiplicity, metric form.** -/
theorem absMult_eq_of_mSpecializes (hpt : FacetPoint e₀ y₀) (hl : c.tail e₀ ≠ c.head e₀)
    (hl' : c'.tail e₀ ≠ c'.head e₀) {m : MetricFacetLimit c c' y₀ degree}
    {x : FrameClass c degree} {x' : FrameClass c' degree} (hx : MSpecializesLeft x m)
    (hx' : MSpecializesRight x' m) : x.absMult = x'.absMult :=
  absMult_eq_of_specializes hpt hl hl' hx.specializesLeft hx'.specializesRight

/-- Equal multiplicity, equal parity. -/
theorem isOdd_iff_of_absMult_eq {x : FrameClass c degree} {x' : FrameClass c' degree}
    (h : x.absMult = x'.absMult) : x.IsOdd ↔ x'.IsOdd := by
  simp only [FrameClass.IsOdd, h]

end Classes

section Step

open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)

/-- **The non-loop condition is free at a Whitehead step**: every step has a facet datum
whose contracted slot is a non-loop of both cores. -/
theorem exists_facetDatum_nonloop {c c' : CubicCore n p} (h : Step c c') (degree : ℕ) :
    ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core c'.core degree e₀ y₀ ε ∧
      c'.core.tail e₀ ≠ c'.core.head e₀ := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨y₀, ε, hd, -⟩ := FacetAdapterPilot.exists_facetDatum_generic m hm degree
  have hc' : c' = FacetAdapterPilot.farCore m :=
    CubicCore.graph_injective (hm.trans (FacetAdapterPilot.farCore_graph m).symm)
  subst hc'
  have hshared := FacetAdapterPilot.sharedContractionSlot_of_move (FacetAdapterPilot.revMove m)
    (FacetAdapterPilot.farCore_graph _)
  rw [FacetAdapterPilot.farCore_revMove, FacetAdapterPilot.revMove_base] at hshared
  exact ⟨_, y₀, ε, hd, tail_ne_head_of_shared hshared⟩

/-- At every step, some facet datum carries the common multiplicity, unconditionally. -/
theorem exists_facetDatum_commonMult {c c' : CubicCore n p} (h : Step c c') (degree : ℕ) :
    ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core c'.core degree e₀ y₀ ε ∧
      c'.core.tail e₀ ≠ c'.core.head e₀ ∧
      ∀ a b : FacetRegrowth c.core c'.core y₀ degree, FacetRegrowth.SameLimit a b →
        regrowthMult a = regrowthMult b := by
  obtain ⟨e₀, y₀, ε, hd, hl'⟩ := exists_facetDatum_nonloop h degree
  exact ⟨e₀, y₀, ε, hd, hl', commonMult_of_facetDatum hd hl'⟩

/-- At the genus-six caterpillar step there is a facet datum at which the common multiplicity
holds. -/
example : ∃ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
    FacetDatum StepSupplyGenusSix.catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε ∧
      ∀ a b : FacetRegrowth StepSupplyGenusSix.catCubicCore.core catLoopCore.core y₀ (2 + 2),
        FacetRegrowth.SameLimit a b → regrowthMult a = regrowthMult b := by
  obtain ⟨e₀, y₀, ε, hd, -, h⟩ := exists_facetDatum_commonMult cat_step (2 + 2)
  exact ⟨e₀, y₀, ε, hd, h⟩

end Step

end DraismaVargas.Count.FacetCommonMultiplicity
