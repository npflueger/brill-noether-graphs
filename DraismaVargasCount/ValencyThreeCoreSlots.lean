import DraismaVargasCount.ValencyThreeResolutionMatch
import DraismaVargasCount.ValencyThreeTypeMatch

set_option autoImplicit false

/-!
# Valency-three stage 3 from the core's pairing

**Source.**  Vargas, Part II (arXiv:2609.09109), Case `{v3-nd4}` of the valency-three limits
(`subsec-case-v3`): the three combinatorial types `H_{2,3}`, `H_{2,4}`, `H_{2,5}` (Types I, II,
III) are the three pairings of the four half-edges at the merged vertex, i.e. the three
Whitehead resolutions, and "exactly one morphism of each type" is per labelled limit.  Also
convention (1) of the subsection *Combinatorial setup and local determinants*
(`subsec-setup-determinants`): the stable edges of the incoming cover other than the
contracting one correspond to those of the limit.  Builds on `ValencyThreeSplit` (`shape`,
`Reads`, `Paired`, `paired_iff`, `TypeMatch`), `ValencyThreeTypeMatch` (`AnchoredUniqueness`),
`ValencyThreeResolutionMatch` (stage 4 in general) and `ValencyThreeGeneral` (labelled metric
limits, `slotColumn`).  The stages are those of `ValencyThreeSplit`.

## The result, in one paragraph

A labelled-metric isomorphism of two facet regrowths' limits carries every limit stable path
to the one over the **same core slot** (`row_inRow_map`: the two incoming rows agree off the
degenerate column by the common-minor identity and the slot-aligned columns, and the vanishing
request row, supported on that column, forbids two such distinct rows in a nonsingular
matrix).  On the other side, the pairing `Paired` that `ValencyThreeSplit.paired_iff`
identifies with the read split's type is **read on the core** (`paired_iff_coreShare`): the
survivors `i`, `j` lie at one incoming stable vertex exactly when their core slots meet at one
end of the vanishing slot `e₀` -- provided no core slot other than `e₀` meets both ends of
`e₀` (`NoParallel`).  Together: at a core with no slot parallel to `e₀`, every labelled-metric
isomorphism preserves the read type (`type_eq_of_metricIso`, the *universal* form of stage 3),
hence `TypeMatch` (`typeMatch_of_noParallel`) and, with `ValencyThreeResolutionMatch`,
anchored uniqueness (`anchoredUniqueness_of_noParallel`); `coreShare_iff_typePartner` says the
split every class reads -- its "own-split position" -- is fixed by the core and the labelled
limit.  §6 removes the oddness hypotheses from stages 3--5 (`frameClass_eq_of_metricIso`), as
the whole-fibre `FacetCensus.MetricCensus` needs.

## What is proved

* §1 `forest_of_facetPoint` (the contraction forest at every facet regrowth of a non-loop slot,
  any valency), `WallRows` (forest and no contracted return) with `WallRows.ofAnchor`, `inRow`,
  `inRow_ne_facet`, **`natural_limit_eq`** (a limit entry of the natural stable-source matrix
  is the frame's entry at the incoming row, in the occurrence's column).
* §2 `exists_limitCol_eq`, `corner_ne_zero`, **`row_inRow_map`** (limit-level pinning; valency
  generic given `WallRows`).
* §3 `AnchorFrame` (the two branch constituents `R`, `Y` of the anchor fibre and `e₁`),
  `nonempty_anchorFrame` (from both pictures of `ValencyThreeSplit.shape`), `Homed`,
  `exists_homed`, `paired_of_homed`, `homed_of_paired`.
* §4 `NoParallel` (decidable), `CoreShare`, `eq_of_noParallel`, `pathOf`,
  `incidence_pos_of_homed`, `eq_e₁_of_stablePath` (the contracting stable edge is the single
  occurrence `e₁`), `vertexOf_end`, `slot_ne`, **`paired_iff_coreShare`**.
* §5 **`row_e₁`** (the contracting stable edge is the vanishing core slot), `slot_transport`,
  `paired_iff_of_metricIso`, **`type_eq_of_metricIso`**, **`coreShare_iff_typePartner`**,
  **`typeMatch_of_noParallel`**, **`anchoredUniqueness_of_noParallel`**.
* §6 `resolutionMatch_all` (the proof of `ValencyThreeResolutionMatch.resolutionMatch`, oddness
  binders removed), `frameClass_eq_of_reads`, **`frameClass_eq_of_metricIso`**.

## Hypotheses

* **`NoParallel core e₀`** in `paired_iff_coreShare` (the `←` direction) and everything
  downstream.  It fails exactly when a slot `f ≠ e₀` joins the two ends of `e₀`, i.e. when the
  limit has a loop at the anchor coming from a digon through `e₀`; there Types I and II can be
  read over one labelled core and stage 3 needs a label-moving automorphism (the loop merge of
  `ValencyThreeLoopMerge`).  At a Whitehead step with a loop at the merged vertex of `c / e₀`,
  exactly one of the three resolutions has the loop at an end of `e₀` (and satisfies
  `NoParallel`), the other two have a digon; so a step fails `NoParallel` on some side iff
  `c / e₀` has a loop at the merged vertex (informal; not used).  At `cat_step` the near core
  satisfies it and the far core does not (`ValencyThreeCensus.noParallel_cat`,
  `not_noParallel_catLoop`).
* `FacetPoint e₀ y` (one vanishing request coordinate, positive elsewhere), and for stages 4--5
  `core.Connected`, `3 ≤ n` (the hypotheses of `ValencyThreeResolutionMatch.splitRigidity`,
  from stage 5).
* `WallRows` at a non-valency-three wall is not produced here.  At valency four it is
  `ValencyFourRigidity.wallRows4` (`noContractedReturn_of_fourStar` gives the same content);
  `noContractedReturn_of_nonleaf` gives it at the non-leaf valency two, and it fails at the
  leaf valency two (`DraismaVargas.LocalCases.LeafFacetNoReturn`).  That failure is harmless:
  `ValencyTwoPairing.noReturnOffRow` is a weaker off-row condition, true at **every** valency
  (leaf or not), and feeds the same row dictionary (`matrix_wallLabelling'`) that `WallRows`
  feeds, so row pinning needs no valency-two `WallRows`.
* **Duplication**: `resolutionMatch_all` repeats about 150 lines of
  `ValencyThreeResolutionMatch.resolutionMatch` verbatim, because `ResolutionMatch` /
  `AnchorExtension` / `SplitRigidity` carry two oddness hypotheses their proofs never use.
  Restating those three `Prop`s without the oddness binders would remove the copy.

## New `Prop`s

* `NoParallel`: consumer `typeMatch_of_noParallel` and
  `ValencyThreeCensus.metricCensus_clause_of_v3`; inhabited at the near core of `cat_step` and
  at both cores of the stem step (`ValencyThreeCensus.noParallel_cat`, `noParallel_stem`);
  strict: false at the far core of `cat_step` (`not_noParallel_catLoop`).
* `WallRows`: interface line in its docstring (the conjunction of two existing predicates);
  produced at every valency-three anchor (`WallRows.ofAnchor`).
* `CoreShare`, `Homed`: interface -- equivalent to `Paired` (`paired_iff_coreShare`,
  `homed_of_paired` / `paired_of_homed`).

## Four tempting inferences, checked

* *"Build the Type I, II and III positions"*: **not needed at valency three.**  The census index
  there is `Unit`; its "equal ranges" clause is the existence transfer of
  `ColumnReceiptExport` (made whole-fibre in `ValencyThreeCensus`), so no position has to be
  built.  The positions matter only where an index value must be *realised* on both sides,
  i.e. `K ≥ 1` at valency four (`ValencyFourRealisation`).
* *"Every odd class is isomorphic to its own-split position"*: this is
  `ValencyThreeResolutionMatch.splitRigidity`; the content beyond it is stage 3 (the own split
  is fixed by the core), proved here at `NoParallel` cores, and the removal of oddness (§6).
* *"The facet form of the pendant-automorphism lemmas, which assume `hy : Nondegenerate y`, is
  needed"*: **not needed** -- `ValencyThreeResolutionMatch` proves the one needed at valency
  three from the contraction forest (`ValencyThreeResolutionMatch.pendant_at_wall_forest`,
  `exists_realign_set`); nothing else here needs a pendant automorphism.
* *"The universal form of `TypeMatch` fails"* (as noted in `ValencyThreeSplit`): only where a
  core slot is parallel to `e₀`; at a `NoParallel` core the universal form holds
  (`type_eq_of_metricIso`).  At `cat_step`: `ValencyThreeCensus.typeMatch_cat'` derives
  `TypeMatch` at the near core by this route, and at the far core the hypothesis fails.

No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

namespace DraismaVargas.Count.ValencyThreeCoreSlots

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification W4StableSource
open FullDimensionalSource
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyThreeSplit (RegrowthAnchor anchorOf uOf IsMetricIso)
open ValencyThreeGeneral (slotColumn limitCol)

/-! ## 1.  The facet data of a regrowth, and the row dictionary across its contraction -/

section FacetData

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The contracted column of a regrowth is its degenerate column. -/
theorem targetEdge_symm_edgeOf (w : Regrowth core y degree) :
    w.frame.fullDim.labelling.targetEdge.symm (w.frame.edgeOf w.column) = w.column := by
  simp [Frame.edgeOf]

theorem mulVec_coordsAt_row (w : Regrowth core y degree) (row : Fin p) :
    (GluingDatum.LengthMatrixPresentation.matrix w.frame.fullDim.labelling.presentation).mulVec
      (w.frame.coordsAt y) row = y (w.frame.slot row) :=
  congrFun (w.frame.mulVec_coordsAt y) row

theorem rows_ne (w : Regrowth core y degree) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (row : Fin p) (hrow : row ≠ w.frame.slot.symm e₀) :
    (GluingDatum.LengthMatrixPresentation.matrix w.frame.fullDim.labelling.presentation).mulVec
      (w.frame.coordsAt y) row ≠ 0 := by
  rw [mulVec_coordsAt_row]
  refine ne_of_gt (hpt.2 _ ?_)
  intro h
  apply hrow
  rw [← h, Equiv.symm_apply_apply]

theorem facetZero (w : Regrowth core y degree) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y) :
    (GluingDatum.LengthMatrixPresentation.matrix w.frame.fullDim.labelling.presentation).mulVec
      (w.frame.coordsAt y) (w.frame.slot.symm e₀) = 0 := by
  rw [mulVec_coordsAt_row, Equiv.apply_symm_apply]
  exact hpt.1

theorem posCoord (w : Regrowth core y degree) (column : Fin p)
    (hne : column ≠ w.frame.fullDim.labelling.targetEdge.symm (w.frame.edgeOf w.column)) :
    0 < w.frame.coordsAt y column := by
  rw [targetEdge_symm_edgeOf] at hne
  exact w.degenerate.2 column hne

/-- **The contraction forest at every facet regrowth of a non-loop slot** (the single vanishing
row has a simple end): the derivation inside `ValencyThreeSplit.exists_regrowthAnchor`, which
does not use the wall's valency, exported. -/
theorem forest_of_facetPoint (w : Regrowth core y degree) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop : core.tail e₀ ≠ core.head e₀) :
    ContractionForest w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
      (w.frame.edgeOf w.column) := by
  have hNonneg : ∀ column, 0 ≤ w.frame.coordsAt y column := by
    intro column
    by_cases h : column = w.column
    · rw [h, ← targetEdge_symm_edgeOf, InheritedLimitRows.zero_coordinate w]
    · exact le_of_lt (w.degenerate.2 column h)
  have hEnd : SingleRowForest.HasSimpleEnd w.frame.data
      (w.frame.fullDim.labelling.row.symm (w.frame.slot.symm e₀)) := by
    have : w.frame.fullDim.labelling.row.symm (w.frame.slot.symm e₀) =
        w.frame.ident.row.symm e₀ := by
      simp [Frame.slot]
    rw [this]
    exact ValencyThreeSplit.hasSimpleEnd_of_ident w.frame e₀ hloop
  exact SingleRowForest.contractionForest_of_single_row w.frame.fullDim.labelling
    (w.frame.coordsAt y) hNonneg (w.frame.slot.symm e₀) (rows_ne w hpt) hEnd rfl
    (InheritedLimitRows.zero_coordinate w)

/-- **The row inputs of a regrowth's wall**: the contraction forest and the absence of a
contracted return -- exactly the hypotheses of `StablePathFacetContraction`'s row dictionary
(`incomingRow`, `rowEquiv`, `matrix_wallLabelling`) beyond the facet metric.

Interface: the conjunction of two existing predicates.  The forest holds at every facet regrowth
of a non-loop slot (`forest_of_facetPoint`); the no-return clause at a valency-three wall
(`WallRows.ofAnchor`), at a valency-four wall (`noContractedReturn_of_fourStar`) and at the
non-leaf valency-two wall (`noContractedReturn_of_nonleaf`); it is **false** at the leaf
valency-two wall (`DraismaVargas.LocalCases.LeafFacetNoReturn`). -/
structure WallRows (w : Regrowth core y degree) : Prop where
  forest : ContractionForest w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
    w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2
    (w.frame.edgeOf w.column)
  noReturn : StablePathFacetContraction.NoContractedReturn w.frame.data (w.frame.edgeOf w.column)

theorem WallRows.compat {w : Regrowth core y degree} (W : WallRows w) :
    WallDegeneration.DanglingCompatible w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) :=
  WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data rfl _ _ W.forest

/-- The row inputs at a valency-three anchor. -/
theorem WallRows.ofAnchor {w : Regrowth core y degree}
    {block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks}
    (H : RegrowthAnchor w block) : WallRows w :=
  ⟨H.forest, NonTrivalentValencyThreeRowDictionary.noContractedReturn_of_threeStar w.frame.data
    w.frame.fullDim rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    H.star⟩

variable {w : Regrowth core y degree}

/-- **The incoming stable path of a limit stable path** (Part II §5.1, convention (1)). -/
noncomputable abbrev inRow (W : WallRows w) :
    StablePath w.limit → StablePath w.frame.data :=
  StablePathFacetContraction.incomingRow w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) W.compat W.forest

/-- The incoming row of a limit row is not the vanishing row. -/
theorem inRow_ne_facet (W : WallRows w) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (Q : StablePath w.limit) :
    w.frame.fullDim.labelling.row (inRow W Q) ≠ w.frame.slot.symm e₀ := by
  intro h
  refine StablePathFacetContraction.incomingRow_ne_facet w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) W.compat W.forest
    (w.frame.coordsAt y) (w.frame.slot.symm e₀) (InheritedLimitRows.zero_coordinate w)
    (posCoord w) (facetZero w hpt) Q ?_
  rw [← h, Equiv.symm_apply_apply]

/-- **A limit entry is the incoming entry of the incoming row, in the column of the
occurrence.**  The natural stable-source matrix of the limit, at a limit row and a surviving
target occurrence, equals the frame's matrix at the incoming row and the occurrence's column
(`StablePathFacetContraction.matrix_wallLabelling`, read without its square labelling). -/
theorem natural_limit_eq (W : WallRows w) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (Q : StablePath w.limit)
    (t : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix w.limit Q t =
      w.frame.matrix (w.frame.fullDim.labelling.row (inRow W Q)) (limitCol w t) := by
  classical
  have hne : limitCol w t ≠
      w.frame.fullDim.labelling.targetEdge.symm (w.frame.edgeOf w.column) := by
    intro h
    apply unfoldEdge_ne_contracted rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) t
    have := congrArg w.frame.fullDim.labelling.targetEdge h
    simpa [limitCol] using this
  have hW := StablePathFacetContraction.matrix_wallLabelling w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) W.compat W.forest
    W.noReturn (w.frame.coordsAt y) (w.frame.slot.symm e₀) (rows_ne w hpt)
    (InheritedLimitRows.zero_coordinate w) (posCoord w) (facetZero w hpt) Q ⟨limitCol w t, hne⟩
  rw [StableSourceMatrix.labelling_matrix_eq] at hW
  refine Eq.trans ?_ hW
  congr 1
  · exact (Equiv.symm_apply_apply _ Q).symm
  · show t = StablePathFacetContraction.punctureTargetEquiv w.frame.fullDim.labelling rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
        ⟨limitCol w t, hne⟩
    rw [StablePathFacetContraction.punctureTargetEquiv_apply]
    have hT : w.frame.fullDim.labelling.targetEdge (limitCol w t) =
        unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) t := by
      simp [limitCol]
    refine (foldEdge_unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) t (unfoldEdge_ne_contracted _ _ _ t)).symm.trans ?_
    exact congrArg _ (Subtype.ext hT.symm)

end FacetData

/-! ## 2.  A labelled-metric limit isomorphism pins the core slot of every limit row -/

section Pinning

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- Every retained column of a regrowth is the column of a limit occurrence. -/
theorem exists_limitCol_eq (w : Regrowth core y degree) (j : Fin p) (hj : j ≠ w.column) :
    ∃ t, limitCol w t = j := by
  have hne : w.frame.edgeOf j ≠ w.frame.edgeOf w.column :=
    fun h ↦ hj (w.frame.fullDim.labelling.targetEdge.injective h)
  refine ⟨foldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    ⟨w.frame.edgeOf j, hne⟩, ?_⟩
  unfold limitCol
  rw [unfoldEdge_foldEdge]
  simp [Frame.edgeOf]

/-- The facet row's corner is nonzero. -/
theorem corner_ne_zero (w : Regrowth core y degree) {e₀ : Fin p} (hy : y e₀ = 0) :
    w.frame.matrix (w.frame.slot.symm e₀) w.column ≠ 0 := by
  intro h0
  apply w.frame.det_ne_zero
  refine Matrix.det_eq_zero_of_row_eq_zero (w.frame.slot.symm e₀) fun j ↦ ?_
  by_cases hj : j = w.column
  · rw [hj]; exact h0
  · exact ValencyThreeRigidity.row_supported w hy j hj

/-- **Limit-level pinning.**  Two regrowths of one core at a facet point, with valency-three
anchors, and a labelled-metric isomorphism `ψ` of their limits: `ψ` carries every limit stable
path to the limit stable path over the **same core slot** (read through each frame's core
identification of the incoming row).  The limit analogue of stage 5's
`ValencyThreeRigidity.overCore_row_of_columns`: the two incoming rows of the core slots agree
off the degenerate column, and the vanishing request row, supported on that column, forbids two
distinct such rows in a nonsingular matrix. -/
theorem row_inRow_map (w w' : Regrowth core y degree) (W : WallRows w) (W' : WallRows w') {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (ψ : GeometricDatumIso w.limit w'.limit)
    (hψ : IsMetricIso w w' ψ) (Q : StablePath w.limit) :
    w'.frame.ident.row (inRow W' (ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) Q)) =
      w.frame.ident.row (inRow W Q) := by
  classical
  set s := w'.frame.ident.row (inRow W' (ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) Q))
    with hs
  set r := w.frame.fullDim.labelling.row (inRow W Q) with hr
  have hslot' : w'.frame.slot.symm s =
      w'.frame.fullDim.labelling.row
        (inRow W' (ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) Q)) := by
    rw [hs]
    simp [Frame.slot]
  have hagree : ∀ j, j ≠ w.column → w.frame.matrix r j = w.frame.matrix (w.frame.slot.symm s) j := by
    intro j hj
    obtain ⟨t, rfl⟩ := exists_limitCol_eq w j hj
    rw [← natural_limit_eq W hpt Q t,
      ← GeometricDatumIso.matrix_map ψ (ValencyThreeSplit.connected_limit w) Q t,
      natural_limit_eq W' hpt _ (ψ.targetEdge t), ← hslot']
    have hm := congrFun (hψ t).2 s
    simpa only [slotColumn] using hm
  have hrs : r = w.frame.slot.symm s := by
    by_contra hne
    exact w.frame.det_ne_zero (ValencyThreeRigidity.det_eq_zero_of_agree_off w.frame.matrix
      w.column r (w.frame.slot.symm s) (w.frame.slot.symm e₀) hne (inRow_ne_facet W hpt Q)
      (ValencyThreeRigidity.row_supported w hpt.1) (corner_ne_zero w hpt.1) hagree)
  have h1 : w.frame.slot r = w.frame.ident.row (inRow W Q) := by
    rw [hr]; simp [Frame.slot]
  rw [← h1, hrs, Equiv.apply_symm_apply]

end Pinning

/-! ## 3.  The anchor fibre's two branch constituents, and where each survivor lives -/

section AnchorFrame

open ValencyThreeSplit

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

variable (data hc hab hOne block) in
/-- **The two branch constituents of the anchor fibre** (`A_u`, `A_v` of Part II's Case
`{v3-nd4}`), joined
by the surviving occurrence `e₁` over the contracted target occurrence.  Every other active
constituent is divalent (the `A'` of the three-vertex picture), there is at most one such, and
it is joined to `R` by an internal occurrence.  Both pictures of `ValencyThreeSplit.shape`
give one (`nonempty_anchorFrame`). -/
structure AnchorFrame where
  R : data.SourceVertex
  Y : data.SourceVertex
  e₁ : data.SourceEdge
  R_mem : R ∈ fib data hc hab hOne block
  Y_mem : Y ∈ fib data hc hab hOne block
  R_ne_Y : R ≠ Y
  R_nd : nonDanglingValency data R = 3
  Y_nd : nonDanglingValency data Y = 3
  e₁_mem : e₁ ∈ intl data hc hab hOne block
  e₁_R : e₁ ∈ ndAt data R
  e₁_Y : e₁ ∈ ndAt data Y
  three : ∀ X ∈ fib data hc hab hOne block, nonDanglingValency data X = 3 → X = R ∨ X = Y
  two : ∀ X ∈ fib data hc hab hOne block, nonDanglingValency data X = 2 →
    ∃ e ∈ intl data hc hab hOne block, e ∈ ndAt data X ∧ e ∈ ndAt data R
  two_unique : ∀ X ∈ fib data hc hab hOne block, ∀ X' ∈ fib data hc hab hOne block,
    nonDanglingValency data X = 2 → nonDanglingValency data X' = 2 → X = X'

/-- Both pictures carry an anchor frame. -/
theorem nonempty_anchorFrame (fd : FullDimensionalSourcePresentation data coordinate)
    (H : AnchorInput data hc hab hOne block) :
    Nonempty (AnchorFrame data hc hab hOne block) := by
  classical
  obtain ⟨huv, hu2, -, hchu, hchv⟩ := H.sides fd
  obtain ⟨-, -, huv'⟩ := side_of_huv hab huv
  rcases shape data fd hc hab hOne block (divEnd a b) (triEnd a b) H.forest H.compat H.nd4 huv
    hu2 hchu hchv with ⟨⟨P⟩⟩ | ⟨⟨P⟩⟩
  · have hRY : P.R ≠ P.Y := fun h ↦ huv' (P.R_over.symm.trans ((congrArg (·.1.1) h).trans P.Y_over))
    refine ⟨{ R := P.R, Y := P.Y, e₁ := P.e₁, R_mem := P.R_mem, Y_mem := P.Y_mem, R_ne_Y := hRY
              R_nd := P.R_nd, Y_nd := P.Y_nd, e₁_mem := ?_, e₁_R := P.e₁_R, e₁_Y := P.e₁_Y
              three := ?_, two := ?_, two_unique := ?_ }⟩
    · rw [P.intl_eq]; exact Finset.mem_singleton_self _
    · intro X hX _
      rw [P.fib_eq] at hX
      simpa using hX
    · intro X hX h2
      rw [P.fib_eq] at hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl
      · rw [P.R_nd] at h2; exact absurd h2 (by norm_num)
      · rw [P.Y_nd] at h2; exact absurd h2 (by norm_num)
    · intro X hX X' _ h2 _
      rw [P.fib_eq] at hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl
      · rw [P.R_nd] at h2; exact absurd h2 (by norm_num)
      · rw [P.Y_nd] at h2; exact absurd h2 (by norm_num)
  · have hRY : P.R ≠ P.Y := fun h ↦ huv' (P.R_over.symm.trans ((congrArg (·.1.1) h).trans P.Y_over))
    have hZ : ∀ X ∈ fib data hc hab hOne block, nonDanglingValency data X = 2 → X = P.Z := by
      intro X hX h2
      rw [P.fib_eq] at hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl
      · rw [P.R_nd] at h2; exact absurd h2 (by norm_num)
      · rw [P.Y_nd] at h2; exact absurd h2 (by norm_num)
      · rfl
    refine ⟨{ R := P.R, Y := P.Y, e₁ := P.e₁, R_mem := P.R_mem, Y_mem := P.Y_mem, R_ne_Y := hRY
              R_nd := P.R_nd, Y_nd := P.Y_nd, e₁_mem := P.e₁_mem, e₁_R := P.e₁_R, e₁_Y := P.e₁_Y
              three := ?_, two := ?_, two_unique := ?_ }⟩
    · intro X hX h3
      rw [P.fib_eq] at hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rw [P.Z_nd] at h3; exact absurd h3 (by norm_num)
    · intro X hX h2
      rw [hZ X hX h2]
      exact ⟨P.e', P.e'_mem, P.e'_Z, P.e'_R⟩
    · intro X hX X' hX' h2 h2'
      rw [hZ X hX h2, hZ X' hX' h2']

variable (fd : FullDimensionalSourcePresentation data coordinate)

include fd in
/-- An active constituent is divalent or trivalent. -/
theorem nd_two_or_three {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    nonDanglingValency data X = 2 ∨ nonDanglingValency data X = 3 := by
  have h0 := ((mem_fib_iff data hc hab hOne block X).mp hX).2.2
  have h2 := nonDanglingValency_two_le data fd h0
  have h3 := fd.trivalent X
  omega

/-- **Where a survivor lives**: the survivor `i` sits at the constituent `B`, or at a divalent
constituent joined to `B` by an internal occurrence (then its stable path runs on to `B`). -/
def Homed (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (i : Fin 4) (B : data.SourceVertex) : Prop :=
  lift L i ∈ ndAt data B ∨ ∃ Z ∈ fib data hc hab hOne block, nonDanglingValency data Z = 2 ∧
    lift L i ∈ ndAt data Z ∧ ∃ e ∈ intl data hc hab hOne block, e ∈ ndAt data Z ∧ e ∈ ndAt data B

variable (Fr : AnchorFrame data hc hab hOne block)
  (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

include fd in
/-- Every survivor is homed at one of the two branch constituents. -/
theorem exists_homed (hCompat : WallDegeneration.DanglingCompatible data hc hab hOne) (i : Fin 4) :
    ∃ B, (B = Fr.R ∨ B = Fr.Y) ∧ Homed L i B := by
  obtain ⟨X, hX, hbd⟩ := exists_fib_of_lift L hCompat i
  have hnd := ((mem_bdAt data X _).mp hbd).1
  rcases nd_two_or_three fd hX with h2 | h3
  · obtain ⟨e, he, heX, heR⟩ := Fr.two X hX h2
    exact ⟨Fr.R, Or.inl rfl, Or.inr ⟨X, hX, h2, hnd, e, he, heX, heR⟩⟩
  · exact ⟨X, Fr.three X hX h3, Or.inl hnd⟩

/-- Two survivors homed at one branch constituent are paired. -/
theorem paired_of_homed {B : data.SourceVertex} (hB : B = Fr.R ∨ B = Fr.Y) {i j : Fin 4}
    (hi : Homed L i B) (hj : Homed L j B) : Paired L i j := by
  have hBmem : B ∈ fib data hc hab hOne block := by
    rcases hB with rfl | rfl
    · exact Fr.R_mem
    · exact Fr.Y_mem
  rcases hi with hi | ⟨Z, hZ, hZ2, hiZ, e, he, heZ, heB⟩ <;>
    rcases hj with hj | ⟨Z', hZ', hZ2', hjZ, e', he', heZ', heB'⟩
  · exact ⟨B, hBmem, B, hBmem, hi, hj, Or.inl rfl⟩
  · exact ⟨B, hBmem, Z', hZ', hi, hjZ, Or.inr ⟨e', he', heB', heZ', Or.inr hZ2'⟩⟩
  · exact ⟨Z, hZ, B, hBmem, hiZ, hj, Or.inr ⟨e, he, heZ, heB, Or.inl hZ2⟩⟩
  · have := Fr.two_unique Z hZ Z' hZ' hZ2 hZ2'
    subst this
    exact ⟨Z, hZ, Z, hZ, hiZ, hjZ, Or.inl rfl⟩

include fd in
/-- Two paired survivors are homed at one branch constituent. -/
theorem homed_of_paired {i j : Fin 4} (h : Paired L i j) :
    ∃ B, (B = Fr.R ∨ B = Fr.Y) ∧ Homed L i B ∧ Homed L j B := by
  obtain ⟨X, hX, X', hX', hi, hj, hjoin⟩ := h
  -- a divalent constituent carrying both: home them at `R` through its internal occurrence
  have viaTwo : ∀ {Z : data.SourceVertex}, Z ∈ fib data hc hab hOne block →
      nonDanglingValency data Z = 2 → lift L i ∈ ndAt data Z → lift L j ∈ ndAt data Z →
      ∃ B, (B = Fr.R ∨ B = Fr.Y) ∧ Homed L i B ∧ Homed L j B := by
    intro Z hZ hZ2 hiZ hjZ
    obtain ⟨e, he, heZ, heR⟩ := Fr.two Z hZ hZ2
    exact ⟨Fr.R, Or.inl rfl, Or.inr ⟨Z, hZ, hZ2, hiZ, e, he, heZ, heR⟩,
      Or.inr ⟨Z, hZ, hZ2, hjZ, e, he, heZ, heR⟩⟩
  rcases hjoin with rfl | ⟨e, he, heX, heX', hdiv⟩
  · rcases nd_two_or_three fd hX with h2 | h3
    · exact viaTwo hX h2 hi hj
    · exact ⟨X, Fr.three X hX h3, Or.inl hi, Or.inl hj⟩
  · rcases nd_two_or_three fd hX with h2 | h3 <;> rcases nd_two_or_three fd hX' with h2' | h3'
    · have := Fr.two_unique X hX X' hX' h2 h2'
      subst this
      exact viaTwo hX h2 hi hj
    · exact ⟨X', Fr.three X' hX' h3', Or.inr ⟨X, hX, h2, hi, e, he, heX, heX'⟩, Or.inl hj⟩
    · exact ⟨X, Fr.three X hX h3, Or.inl hi, Or.inr ⟨X', hX', h2', hj, e, he, heX', heX⟩⟩
    · rcases hdiv with h | h
      · rw [h3] at h; exact absurd h (by norm_num)
      · rw [h3'] at h; exact absurd h (by norm_num)

end AnchorFrame

/-! ## 4.  The pairing read on the core -/

section CoreReading

variable {n p : ℕ}

/-- **`e₀` has no parallel slot**: no core slot other than `e₀` meets both ends of `e₀`.  At a
Whitehead step this says that the contracted core `c / e₀` has no loop at the merged vertex
coming from a digon through `e₀` -- exactly the configuration in which Types I and II can be
reached over one labelled core (the loop merge of `ValencyThreeLoopMerge`).  Decidable, and a
property of the core alone.

Interface: the hypothesis of `paired_iff_coreShare`; consumed by `typeMatch_of_noParallel`;
inhabited at the near core of `cat_step` (`noParallel_cat`) and false at its far core
(`not_noParallel_catLoop`). -/
def NoParallel (core : Core n p) (e₀ : Fin p) : Prop :=
  ∀ s, s ≠ e₀ → coreIncidence core (core.tail e₀) s = 0 ∨ coreIncidence core (core.head e₀) s = 0

instance (core : Core n p) (e₀ : Fin p) : Decidable (NoParallel core e₀) := by
  unfold NoParallel; infer_instance

/-- **Two core slots meet at one end of `e₀`.** -/
def CoreShare (core : Core n p) (e₀ s t : Fin p) : Prop :=
  ∃ x, (x = core.tail e₀ ∨ x = core.head e₀) ∧ 0 < coreIncidence core x s ∧
    0 < coreIncidence core x t

theorem end_of_coreIncidence_pos {core : Core n p} {x : Fin n} {s : Fin p}
    (h : 0 < coreIncidence core x s) : x = core.tail s ∨ x = core.head s := by
  unfold coreIncidence at h
  by_cases ht : core.tail s = x
  · exact Or.inl ht.symm
  · by_cases hh : core.head s = x
    · exact Or.inr hh.symm
    · simp [ht, hh] at h

/-- Under `NoParallel`, a slot other than `e₀` meets at most one end of `e₀`. -/
theorem eq_of_noParallel {core : Core n p} {e₀ s : Fin p} (hpar : NoParallel core e₀)
    (hs : s ≠ e₀) {x x' : Fin n} (hx : x = core.tail e₀ ∨ x = core.head e₀)
    (hx' : x' = core.tail e₀ ∨ x' = core.head e₀) (h : 0 < coreIncidence core x s)
    (h' : 0 < coreIncidence core x' s) : x = x' := by
  rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
  · rfl
  · rcases hpar s hs with h0 | h0 <;> omega
  · rcases hpar s hs with h0 | h0 <;> omega
  · rfl

open ValencyThreeSplit

variable {core : Core n p}
variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (hCompat : WallDegeneration.DanglingCompatible data hc hab hOne)
  (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

include hCompat in
/-- A labelled survivor's incoming occurrence survives. -/
theorem lift_survives (i : Fin 4) : ¬ IsDangling data (lift L i) := by
  obtain ⟨X, -, hbd⟩ := exists_fib_of_lift L hCompat i
  exact ((mem_ndAt data X _).mp ((mem_bdAt data X _).mp hbd).1).1

/-- The incoming stable path of the survivor `i`. -/
noncomputable def pathOf (i : Fin 4) : StablePath data :=
  NonDanglingEdge.stablePath ⟨lift L i, lift_survives hCompat L i⟩

/-- A survivor's stable path reaches its home. -/
theorem incidence_pos_of_homed {i : Fin 4} {B : data.SourceVertex} (h : Homed L i B) :
    0 < StablePathCount.incidenceCount data B (pathOf hCompat L i) := by
  rw [StablePathCount.incidenceCount_pos_iff]
  rcases h with h | ⟨Z, -, hZ2, hiZ, e, he, heZ, heB⟩
  · exact ⟨⟨lift L i, lift_survives hCompat L i⟩, ((mem_ndAt data B _).mp h).2, rfl⟩
  · have heS := ((mem_ndAt data B _).mp heB).1
    have hne : (⟨lift L i, lift_survives hCompat L i⟩ : NonDanglingEdge data) ≠ ⟨e, heS⟩ := by
      intro h
      apply lift_ne L i
      have := congrArg (fun x : NonDanglingEdge data ↦ x.1.1.1) h
      simp only at this
      rw [this]
      exact (intl_ends data hc hab hOne block he).2.2.2.2.1
    have hcons : Consecutive data ⟨lift L i, lift_survives hCompat L i⟩ ⟨e, heS⟩ :=
      ⟨hne, Z, ((mem_ndAt data Z _).mp hiZ).2, ((mem_ndAt data Z _).mp heZ).2, hZ2⟩
    exact ⟨⟨e, heS⟩, ((mem_ndAt data B _).mp heB).2, (stablePath_eq_of_consecutive hcons).symm⟩

variable (Fr : AnchorFrame data hc hab hOne block)

theorem e₁_survives : ¬ IsDangling data Fr.e₁ := ((mem_ndAt data Fr.R _).mp Fr.e₁_R).1

/-- The contracting occurrence's ends are `R` and `Y`. -/
theorem eq_R_or_Y_of_incident {V : data.SourceVertex} (h : Incident data Fr.e₁ V) :
    V = Fr.R ∨ V = Fr.Y := by
  have hR := ((mem_ndAt data Fr.R _).mp Fr.e₁_R).2
  have hY := ((mem_ndAt data Fr.Y _).mp Fr.e₁_Y).2
  unfold Incident at h hR hY
  rcases h with h | h <;> rcases hR with hR | hR <;> rcases hY with hY | hY
  all_goals first
    | exact Or.inl (h.symm.trans hR)
    | exact Or.inr (h.symm.trans hY)
    | exact absurd (hR.symm.trans hY) Fr.R_ne_Y

/-- **The contracting stable edge is the single occurrence `e₁`**: both of its ends are
trivalent, so no occurrence is consecutive to it. -/
theorem eq_e₁_of_stablePath (f : NonDanglingEdge data)
    (hf : f.stablePath = NonDanglingEdge.stablePath ⟨Fr.e₁, e₁_survives Fr⟩) : f.1 = Fr.e₁ := by
  have hClosed : ∀ x y : NonDanglingEdge data, Consecutive data x y → x.1 = Fr.e₁ → y.1 = Fr.e₁ := by
    rintro x y ⟨-, V, hxV, -, hV2⟩ hx
    rw [hx] at hxV
    rcases eq_R_or_Y_of_incident Fr hxV with rfl | rfl
    · rw [Fr.R_nd] at hV2; exact absurd hV2 (by norm_num)
    · rw [Fr.Y_nd] at hV2; exact absurd hV2 (by norm_num)
  exact (eqvGen_iff_of_closed hClosed ((stablePath_eq_iff _ _).mp hf.symm)).mp rfl

/-- A survivor's stable path is not the contracting one. -/
theorem pathOf_ne (i : Fin 4) :
    pathOf hCompat L i ≠ NonDanglingEdge.stablePath ⟨Fr.e₁, e₁_survives Fr⟩ := by
  intro h
  have := eq_e₁_of_stablePath Fr _ h
  apply lift_ne L i
  rw [show lift L i = Fr.e₁ from this]
  exact (intl_ends data hc hab hOne block Fr.e₁_mem).2.2.2.2.1

variable (ident : Count.CoreIdentification core data)

/-- The core vertex of a trivalent constituent. -/
noncomputable def vertexOf (B : data.SourceVertex) (hB : nonDanglingValency data B = 3) : Fin n :=
  ident.vertex ⟨B, le_of_eq hB.symm⟩

theorem coreIncidence_vertexOf (B : data.SourceVertex) (hB : nonDanglingValency data B = 3)
    (P : StablePath data) :
    coreIncidence core (vertexOf ident B hB) (ident.row P) =
      StablePathCount.incidenceCount data B P := by
  have := ident.incidence ⟨B, le_of_eq hB.symm⟩ (ident.row P)
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

variable {e₀ : Fin p}
  (he₁ : ident.row (NonDanglingEdge.stablePath ⟨Fr.e₁, e₁_survives Fr⟩) = e₀)

include he₁ in
/-- Both branch constituents lie over ends of `e₀`. -/
theorem vertexOf_end (B : data.SourceVertex) (hB : B = Fr.R ∨ B = Fr.Y)
    (h3 : nonDanglingValency data B = 3) :
    vertexOf ident B h3 = core.tail e₀ ∨ vertexOf ident B h3 = core.head e₀ := by
  apply end_of_coreIncidence_pos
  rw [← he₁, coreIncidence_vertexOf, StablePathCount.incidenceCount_pos_iff]
  refine ⟨⟨Fr.e₁, e₁_survives Fr⟩, ?_, rfl⟩
  rcases hB with rfl | rfl
  · exact ((mem_ndAt data _ _).mp Fr.e₁_R).2
  · exact ((mem_ndAt data _ _).mp Fr.e₁_Y).2

theorem nd_of_R_or_Y {B : data.SourceVertex} (hB : B = Fr.R ∨ B = Fr.Y) :
    nonDanglingValency data B = 3 := by
  rcases hB with rfl | rfl
  · exact Fr.R_nd
  · exact Fr.Y_nd

include he₁ in
/-- A survivor's core slot is not `e₀`. -/
theorem slot_ne (i : Fin 4) : ident.row (pathOf hCompat L i) ≠ e₀ := by
  rw [← he₁]
  exact fun h ↦ pathOf_ne hCompat L Fr i (ident.row.injective h)

variable (fd : FullDimensionalSourcePresentation data coordinate)

include fd he₁ in
/-- **The pairing of `e₂` is read on the core** (Part II, Case `{v3-nd4}`): when no core slot is parallel
to `e₀`, the survivors `0` and `k` lie at one incoming stable vertex exactly when their core
slots meet at one end of `e₀`. -/
theorem paired_iff_coreShare (hpar : NoParallel core e₀) (i j : Fin 4) :
    Paired L i j ↔
      CoreShare core e₀ (ident.row (pathOf hCompat L i)) (ident.row (pathOf hCompat L j)) := by
  constructor
  · intro h
    obtain ⟨B, hB, hi, hj⟩ := homed_of_paired fd Fr L h
    have h3 := nd_of_R_or_Y Fr hB
    refine ⟨vertexOf ident B h3, vertexOf_end Fr ident he₁ B hB h3, ?_, ?_⟩
    · rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed hCompat L hi
    · rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed hCompat L hj
  · rintro ⟨x, hx, hxi, hxj⟩
    obtain ⟨Bi, hBi, hi⟩ := exists_homed fd Fr L hCompat i
    obtain ⟨Bj, hBj, hj⟩ := exists_homed fd Fr L hCompat j
    have hi3 := nd_of_R_or_Y Fr hBi
    have hj3 := nd_of_R_or_Y Fr hBj
    have hvi : vertexOf ident Bi hi3 = x := by
      refine eq_of_noParallel hpar (slot_ne hCompat L Fr ident he₁ i)
        (vertexOf_end Fr ident he₁ Bi hBi hi3) hx ?_ hxi
      rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed hCompat L hi
    have hvj : vertexOf ident Bj hj3 = x := by
      refine eq_of_noParallel hpar (slot_ne hCompat L Fr ident he₁ j)
        (vertexOf_end Fr ident he₁ Bj hBj hj3) hx ?_ hxj
      rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed hCompat L hj
    have hB : Bi = Bj := by
      have := ident.vertex.injective (hvi.trans hvj.symm)
      exact congrArg Subtype.val this
    subst hB
    exact paired_of_homed Fr L hBi hi hj

end CoreReading

/-! ## 5.  Stage 3 at a core with no slot parallel to `e₀` -/

section Regrowths

open ValencyThreeSplit
open DraismaVargas.Count.CrossCoreTransport (FrameClass)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The anchor frame of a regrowth's anchor. -/
abbrev RegrowthFrame (w : Regrowth core y degree)
    (block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks) :=
  AnchorFrame w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) block

variable {w : Regrowth core y degree}
  {block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks}

/-- **The contracting stable edge of a regrowth is the vanishing core slot.**  Its only
occurrence lies over the contracted target occurrence (`eq_e₁_of_stablePath`), so its matrix row
is supported on the degenerate column, as is the vanishing request row; in a nonsingular matrix
two such rows coincide. -/
theorem row_e₁ (Fr : RegrowthFrame w block) {e₀ : Fin p} (hy : y e₀ = 0) :
    w.frame.ident.row (NonDanglingEdge.stablePath ⟨Fr.e₁, e₁_survives Fr⟩) = e₀ := by
  classical
  set P₁ := NonDanglingEdge.stablePath (⟨Fr.e₁, e₁_survives Fr⟩ : NonDanglingEdge w.frame.data)
    with hP₁
  set r := w.frame.fullDim.labelling.row P₁ with hr
  have hsupp : ∀ j, j ≠ w.column → w.frame.matrix r j = 0 := by
    intro j hj
    show GluingDatum.LengthMatrixPresentation.matrix _ r j = 0
    rw [StableSourceMatrix.labelling_matrix_eq, hr, Equiv.symm_apply_apply]
    unfold StableSourceMatrix.matrix
    refine Finset.sum_eq_zero fun e he ↦ absurd ?_ hj
    obtain ⟨⟨hS, hP⟩, hT⟩ := (StableSourceMatrix.mem_occurrences _ _ _).mp he
    have he₁ : e = Fr.e₁ := eq_e₁_of_stablePath Fr ⟨e, hS⟩ hP
    apply w.frame.fullDim.labelling.targetEdge.injective
    rw [← hT, he₁]
    exact (intl_ends w.frame.data rfl _ _ block Fr.e₁_mem).2.2.2.2.1
  have hrs : r = w.frame.slot.symm e₀ := by
    by_contra hne
    exact w.frame.det_ne_zero (ValencyThreeRigidity.det_eq_zero_of_two_supported w.frame.matrix
      w.column r _ hne hsupp (ValencyThreeRigidity.row_supported w hy) (corner_ne_zero w hy))
  have h1 : w.frame.slot r = w.frame.ident.row P₁ := by
    rw [hr]; simp [Frame.slot]
  rw [← h1, hrs, Equiv.apply_symm_apply]

/-- The incoming path of a survivor is the incoming row of its limit stable path. -/
theorem pathOf_eq_inRow (H : RegrowthAnchor w block) (L : AnchorLabelling w.limit (anchorOf w block))
    (i : Fin 4) :
    pathOf H.compat L i = inRow (WallRows.ofAnchor H) (NonDanglingEdge.stablePath
      (⟨L.e i, ((mem_ndAt _ _ _).mp (L.mem i)).1⟩ : NonDanglingEdge w.limit)) :=
  rfl

/-- **A labelled-metric limit isomorphism preserves the core slot of every survivor**, for
labellings transported along it. -/
theorem slot_transport {w' : Regrowth core y degree} {block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block') {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (ψ : GeometricDatumIso w.limit w'.limit)
    (hψ : IsMetricIso w w' ψ) (L : AnchorLabelling w.limit (anchorOf w block))
    (L' : AnchorLabelling w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) (i : Fin 4) :
    w'.frame.ident.row (pathOf H'.compat L' i) = w.frame.ident.row (pathOf H.compat L i) := by
  have hQ : NonDanglingEdge.stablePath
      (⟨L'.e i, ((mem_ndAt _ _ _).mp (L'.mem i)).1⟩ : NonDanglingEdge w'.limit) =
      ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) (NonDanglingEdge.stablePath
        (⟨L.e i, ((mem_ndAt _ _ _).mp (L.mem i)).1⟩ : NonDanglingEdge w.limit)) := by
    refine Eq.trans ?_ (GeometricDatumIso.stablePathEquiv_mk ψ _ _).symm
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext (hL i))
  rw [pathOf_eq_inRow H' L' i, hQ, row_inRow_map w w' (WallRows.ofAnchor H) (WallRows.ofAnchor H') hpt ψ hψ]
  rfl

/-- **The pairing is invariant under every labelled-metric limit isomorphism** when no core slot
is parallel to `e₀`: both pairings are read off the same core slots
(`paired_iff_coreShare`, `slot_transport`). -/
theorem paired_iff_of_metricIso {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hpar : NoParallel core e₀) {w' : Regrowth core y degree} {block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit) (hψ : IsMetricIso w w' ψ)
    (L : AnchorLabelling w.limit (anchorOf w block))
    (L' : AnchorLabelling w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) (i j : Fin 4) :
    Paired L i j ↔ Paired L' i j := by
  obtain ⟨Fr⟩ := nonempty_anchorFrame w.frame.fullDim H
  obtain ⟨Fr'⟩ := nonempty_anchorFrame w'.frame.fullDim H'
  rw [paired_iff_coreShare H.compat L Fr w.frame.ident (row_e₁ Fr hpt.1) w.frame.fullDim hpar,
    paired_iff_coreShare H'.compat L' Fr' w'.frame.ident (row_e₁ Fr' hpt.1) w'.frame.fullDim hpar,
    slot_transport H H' hpt ψ hψ L L' hL i, slot_transport H H' hpt ψ hψ L L' hL j]

/-- **The universal form of stage 3 at a core with no slot parallel to `e₀`**: along *every*
labelled-metric isomorphism of two anchored regrowths' limits, transported labellings read
splits of the same type.  (`ValencyThreeSplit` notes that the universal form fails where a
label-moving automorphism meets a `simple` split; this says that cannot happen unless a core
slot is parallel to `e₀`.) -/
theorem type_eq_of_metricIso {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hpar : NoParallel core e₀) {w' : Regrowth core y degree} {block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit) (hψ : IsMetricIso w w' ψ)
    (L : AnchorLabelling w.limit (anchorOf w block))
    (L' : AnchorLabelling w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i))
    (s s' : ValencyThreeGeneral.Split7.Split) (hs : Reads L (uOf w) s)
    (hs' : Reads L' (uOf w') s') : s.type = s'.type := by
  have h0 := (paired_iff w.frame.fullDim H L hs _ (typePartner_ne_zero s.type)).mpr rfl
  have h1 := (paired_iff_of_metricIso hpt hpar H H' ψ hψ L L' hL 0 _).mp h0
  exact typePartner_injective ((paired_iff w'.frame.fullDim H' L' hs' _
    (typePartner_ne_zero _)).mp h1)

/-- **The own-split position is read off the core**: over a core with no slot parallel to
`e₀`, the partner of `e₂` in the split read off any anchored regrowth (its type, `typePartner`)
is the unique other survivor whose core slot meets `e₂`'s at an end of `e₀`.  So the split of
every class at a labelled metric limit is determined by the core and the limit's labelling
(`split_eq_of_indices_eq`), not by the class. -/
theorem coreShare_iff_typePartner {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hpar : NoParallel core e₀) (H : RegrowthAnchor w block)
    (L : AnchorLabelling w.limit (anchorOf w block)) {s : ValencyThreeGeneral.Split7.Split}
    (hs : Reads L (uOf w) s) (k : Fin 4) (hk : k ≠ 0) :
    CoreShare core e₀ (w.frame.ident.row (pathOf H.compat L 0))
        (w.frame.ident.row (pathOf H.compat L k)) ↔ k = typePartner s.type := by
  obtain ⟨Fr⟩ := nonempty_anchorFrame w.frame.fullDim H
  rw [← paired_iff_coreShare H.compat L Fr w.frame.ident (row_e₁ Fr hpt.1) w.frame.fullDim hpar]
  exact paired_iff w.frame.fullDim H L hs k hk

/-- **Stage 3 (`TypeMatch`) at every facet point of a core with no slot parallel to the
vanishing slot.** -/
theorem typeMatch_of_noParallel {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hpar : NoParallel core e₀) : TypeMatch core y degree := by
  intro w w' block block' H H' hsame _ _
  obtain ⟨ψ, hψ⟩ := hsame
  exact ⟨ψ, hψ, fun L L' hL s s' hs hs' ↦
    type_eq_of_metricIso hpt hpar H H' ψ hψ L L' hL s s' hs hs'⟩

/-- **Anchored uniqueness (stages 3--5) at every facet point of a connected core with at least
three vertices and no slot parallel to the vanishing slot**: stage 3 here, stages 4--5
`ValencyThreeResolutionMatch.splitRigidity`. -/
theorem anchoredUniqueness_of_noParallel (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hpar : NoParallel core e₀) :
    ValencyThreeTypeMatch.AnchoredUniqueness core y degree :=
  ValencyThreeTypeMatch.anchoredUniqueness_of_stages (typeMatch_of_noParallel hpt hpar)
    (ValencyThreeResolutionMatch.splitRigidity hconn hn hpt.1)

end Regrowths

/-! ## 6.  Stages 3--5 for every class, not only the odd ones

`FacetCensus.MetricCensus` labels the **whole** fibres at a metric limit.
`ValencyThreeResolutionMatch.resolutionMatch` never uses its two oddness hypotheses, but
`ResolutionMatch`, `AnchorExtension` and `SplitRigidity` carry them in their statements;
`resolutionMatch_all` is that proof with the two unused binders removed (verbatim otherwise),
and the rest of stages 4--5 is re-assembled from the oddness-free
`extendsMetric_of_transportFree`, `columnIso_of_extendsMetric` and `frameIso_of_columns`. -/

section AllClasses

open ValencyThreeSplit ValencyThreeRigidity ValencyThreeResolutionMatch
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open W3Nd2SourceCandidates (rightOf)
open W3Nd2StarExhaustionProof (edge_rel_iff edgePerm_agree incident_iff)
open ValencyThreeGeneral.Split7

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Stage 4 (`ValencyThreeResolutionMatch.resolutionMatch`) without the oddness
hypotheses**, which its proof does not use. -/
theorem resolutionMatch_all (w w' : Regrowth core y degree) {block block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit) (hψ : IsMetricIso w w' ψ)
    (L : AnchorLabelling w.limit (anchorOf w block))
    (L' : AnchorLabelling w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) (s : Split)
    (hs : Reads L (uOf w) s) (hs' : Reads L' (uOf w') s) :
    ∃ (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second)
      (second' : (w'.frame.limitTarget w'.column).edges → Bool) (h' : IsPlacement w' second')
      (ψ' : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ' ∧
      Nonempty (ResolutionExpansionFree.TransportFree ψ'
        ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
        ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ second second'
        (resolutionOf w second h) (resolutionOf w' second' h')) := by
  classical
  have hlim := sourceVertexEquiv_limA w w' H H' ψ
  have hWall : ψ.targetVertex ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ =
      ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ :=
    congrArg (fun x : w'.limit.SourceVertex ↦ x.1.1) hlim
  have hA : (w'.limit.vertexPartition ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩).Rel
      block'.1 (ψ.vertexPerm ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ block.1) := by
    have h2 : ψ.vertexPerm ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ block.1 = block'.1 :=
      congrArg (fun x : w'.limit.SourceVertex ↦ x.1.2) hlim
    change (w'.limit.vertexPartition _).repr block'.1 =
      (w'.limit.vertexPartition _).repr (ψ.vertexPerm _ block.1)
    rw [h2]
  have hLe : ∀ i, (L'.e i).1.1 = ψ.targetEdge (L.e i).1.1 :=
    fun i ↦ congrArg (fun x : w'.limit.SourceEdge ↦ x.1.1) (hL i)
  have hLm : ∀ i, (L'.e i).1.2 = ψ.edgePerm (L.e i).1.1 (L.e i).1.2 :=
    fun i ↦ congrArg (fun x : w'.limit.SourceEdge ↦ x.1.2) (hL i)
  rcases s with _ | ⟨α4, δ5⟩
  · -- base tree `T₂`: no coherence is needed
    obtain ⟨hP, hl, hn, hr, href⟩ := cover_two w.frame.fullDim H L hs
    obtain ⟨hP', hl', hn', hr', -⟩ := cover_two w'.frame.fullDim H' L' hs'
    refine ⟨rightOf (L.e 0).1.1, hP, rightOf (L'.e 0).1.1, hP', ψ, hψ, ?_⟩
    refine transportFree_two ψ hWall (L.e 0).1.1 (label_mem L 0) (L'.e 0).1.1 (hLe 0).symm
      _ _ (L.e 0).1.2 (L.e 3).1.2 (L'.e 0).1.2 (L'.e 3).1.2 hl hl' hn hn' hr hr' href ?_ ?_
    · rw [hLm 0]; exact rfl
    · rw [hLm 3, ← L.dir25]; exact rfl
  · -- base tree `T_α`: realign `A'` on the third direction's branch
    obtain ⟨hP, hl, hr, hn, hZR, hZA, hDang⟩ := cover_three w.frame.fullDim H L α4 δ5 hs
    obtain ⟨hP', hl', hr', hn', hZR', hZA', hDang'⟩ := cover_three w'.frame.fullDim H' L' α4 δ5 hs'
    set wall : (w.frame.limitTarget w.column).V := ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
    set wall' : (w'.frame.limitTarget w'.column).V :=
      ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩
    set U := (L.e (alphaIdx α4)).1.1
    set Δ := (L.e (deltaIdx δ5)).1.1
    set mα := (L.e (alphaIdx α4)).1.2
    set mδ := (L.e (deltaIdx δ5)).1.2
    have hUΔ : U ≠ Δ := by
      have d25 := L.dir25
      have d3 := L.dir3
      have d4 := L.dir4
      have hα : alphaIdx α4 = 1 ∨ alphaIdx α4 = 2 := by cases α4 <;> simp [alphaIdx]
      have hδ : deltaIdx δ5 = 0 ∨ deltaIdx δ5 = 3 := by cases δ5 <;> simp [deltaIdx]
      show (L.e (alphaIdx α4)).1.1 ≠ (L.e (deltaIdx δ5)).1.1
      rcases hα with h | h <;> rcases hδ with h' | h' <;> rw [h, h']
      · exact d3
      · rw [← d25]; exact d3
      · exact d4
      · rw [← d25]; exact d4
    have memU : U ∈ GluingDatum.incidentEdges wall := label_mem L _
    have memΔ : Δ ∈ GluingDatum.incidentEdges wall := label_mem L _
    have hcard3 : (GluingDatum.incidentEdges wall).card = 3 := H.valency
    have hrest : (((GluingDatum.incidentEdges wall).erase U).erase Δ).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hUΔ.symm, memΔ⟩),
        Finset.card_erase_of_mem memU, hcard3]
    obtain ⟨X, hXset⟩ := Finset.card_eq_one.mp hrest
    have hXmem : X ∈ ((GluingDatum.incidentEdges wall).erase U).erase Δ := by
      rw [hXset]; exact Finset.mem_singleton_self X
    obtain ⟨hXΔ, hX1⟩ := Finset.mem_erase.mp hXmem
    obtain ⟨hXU, memX⟩ := Finset.mem_erase.mp hX1
    have hEdges : ∀ e, e ∈ GluingDatum.incidentEdges wall ↔ e = U ∨ e = Δ ∨ e = X := by
      intro e
      constructor
      · intro he
        by_cases h1 : e = U
        · exact Or.inl h1
        by_cases h2 : e = Δ
        · exact Or.inr (Or.inl h2)
        have : e ∈ ((GluingDatum.incidentEdges wall).erase U).erase Δ :=
          Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, he⟩⟩
        rw [hXset] at this
        exact Or.inr (Or.inr (Finset.mem_singleton.mp this))
      · rintro (rfl | rfl | rfl)
        · exact memU
        · exact memΔ
        · exact memX
    -- the images on the second side
    have hU' : (L'.e (alphaIdx α4)).1.1 = ψ.targetEdge U := hLe _
    have hΔ' : (L'.e (deltaIdx δ5)).1.1 = ψ.targetEdge Δ := hLe _
    have hmα' : (L'.e (alphaIdx α4)).1.2 = ψ.edgePerm U mα := hLm _
    have hmδ' : (L'.e (deltaIdx δ5)).1.2 = ψ.edgePerm Δ mδ := hLm _
    have hX' : ψ.targetEdge X ∈ GluingDatum.incidentEdges wall' :=
      (incident_iff ψ hWall X).mp (ends_of_mem memX)
    have hXU' : ψ.targetEdge X ≠ (L'.e (alphaIdx α4)).1.1 := by
      rw [hU']; exact fun h ↦ hXU (ψ.targetEdge.injective h)
    have hXΔ' : ψ.targetEdge X ≠ (L'.e (deltaIdx δ5)).1.1 := by
      rw [hΔ']; exact fun h ↦ hXΔ (ψ.targetEdge.injective h)
    -- the two copies of `A'`, and the realignment
    set Z := Finset.univ.filter fun x ↦ (w.limit.edgePartition Δ).Rel mδ x
    set P := Z.image (ψ.edgePerm X)
    set Q := Finset.univ.filter fun x ↦
      (w'.limit.edgePartition (L'.e (deltaIdx δ5)).1.1).Rel (L'.e (deltaIdx δ5)).1.2 x
    have hZmap : ∀ x, (w.limit.edgePartition Δ).Rel mδ x ↔
        (w'.limit.edgePartition (L'.e (deltaIdx δ5)).1.1).Rel (L'.e (deltaIdx δ5)).1.2
          (ψ.edgePerm Δ x) := by
      intro x
      rw [edge_rel_iff ψ Δ, hΔ', hmδ']
    have hQ : Q = Z.image (ψ.edgePerm Δ) := by
      ext q
      simp only [Q, Z, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        exact ⟨(ψ.edgePerm Δ).symm q, (hZmap _).mpr (by rw [Equiv.apply_symm_apply]; exact h),
          Equiv.apply_symm_apply _ _⟩
      · rintro ⟨x, hx, rfl⟩
        exact (hZmap x).mp hx
    have hcard : P.card = Q.card := by
      rw [hQ, Finset.card_image_of_injective _ (ψ.edgePerm X).injective,
        Finset.card_image_of_injective _ (ψ.edgePerm Δ).injective]
    have hZA_s : ∀ x ∈ Z, (w.limit.vertexPartition wall).Rel block.1 x := by
      intro x hx
      have hx' : (w.limit.edgePartition Δ).Rel mδ x := by simpa [Z] using hx
      exact hZA.trans ((StableLocalProperties.refines_of_mem_incidentEdges w.limit memΔ).rel hx')
    have hPD : ∀ q ∈ P, (w'.limit.vertexPartition wall').Rel block'.1 q ∧
        IsDangling w'.limit (w'.limit.sourceEdge (ψ.targetEdge X) q) := by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      have hx' : (w.limit.edgePartition Δ).Rel mδ x := by simpa [Z] using hx
      refine ⟨(anchor_iff ψ hWall block.1 block'.1 hA (ψ.edgePerm X)
        (edgePerm_agree ψ hWall X hX') x).mp (hZA_s x hx), ?_⟩
      exact (W3ShiftStarExhaustionProof.isDangling_sourceEdge_iff ψ
        (connected_limit w) X x).mpr (hDang x hx' X memX hXU hXΔ)
    have hQD : ∀ q ∈ Q, (w'.limit.vertexPartition wall').Rel block'.1 q ∧
        IsDangling w'.limit (w'.limit.sourceEdge (ψ.targetEdge X) q) := by
      intro q hq
      have hq' : (w'.limit.edgePartition (L'.e (deltaIdx δ5)).1.1).Rel
          (L'.e (deltaIdx δ5)).1.2 q := by simpa [Q] using hq
      refine ⟨hZA'.trans ((StableLocalProperties.refines_of_mem_incidentEdges w'.limit
        (label_mem L' _)).rel hq'), hDang' q hq' _ hX' hXU' hXΔ'⟩
    have hPos : 0 < nonDanglingValency w'.limit (w'.limit.sourceEndpoint wall' block'.1) := by
      have hEq : w'.limit.sourceEndpoint wall' block'.1 = anchorOf w' block' :=
        Subtype.ext (Prod.ext rfl (anchorOf w' block').2)
      have h4 : nonDanglingValency w'.limit (anchorOf w' block') = 4 := H'.nd4
      rw [hEq, h4]
      norm_num
    obtain ⟨ψ', h₁, h₂, h₃, h₄, h₅⟩ := exists_realign_set w' H'.forest
      (H'.noGlue w'.frame.fullDim) ψ (ψ.targetEdge X) hX' block'.1 hPos P Q hPD hQD hcard
    refine ⟨rightOf U, hP, rightOf (L'.e (alphaIdx α4)).1.1, hP', ψ', fun e ↦ ?_, ?_⟩
    · rw [h₁ e]; exact hψ e
    have hWall' : ψ'.targetVertex wall = wall' := (h₂ wall).trans hWall
    have hUn : ψ.targetEdge U ≠ ψ.targetEdge X := fun h ↦ hXU (ψ.targetEdge.injective h).symm
    have hΔn : ψ.targetEdge Δ ≠ ψ.targetEdge X := fun h ↦ hXΔ (ψ.targetEdge.injective h).symm
    have hψU : ψ'.edgePerm U = ψ.edgePerm U :=
      h₄ U ((incident_iff ψ hWall U).mp (ends_of_mem memU)) hUn
    have hψΔ : ψ'.edgePerm Δ = ψ.edgePerm Δ :=
      h₄ Δ ((incident_iff ψ hWall Δ).mp (ends_of_mem memΔ)) hΔn
    refine transportFree_three ψ' hWall' U Δ X hEdges hUΔ hXU.symm
      (L'.e (alphaIdx α4)).1.1 (L'.e (deltaIdx δ5)).1.1 ((h₁ U).trans hU'.symm)
      ((h₁ Δ).trans hΔ'.symm) _ _ block.1 block'.1 mα mδ (L'.e (alphaIdx α4)).1.2
      (L'.e (deltaIdx δ5)).1.2 hl hr hn hZR hl' hr' hn' hZR' ?_ ?_ ?_ ?_
    · rw [h₃ wall hWall]; exact hA
    · rw [hψU, hmα']; exact rfl
    · rw [hψΔ, hmδ']; exact rfl
    · intro x _
      have h5 := h₅ X rfl x
      simp only [Q, P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at h5
      rw [h5]
      constructor
      · intro hx
        exact ⟨x, by simpa [Z] using hx, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        rw [← (ψ.edgePerm X).injective hzx]
        simpa [Z] using hz

/-- **Stages 4--5 for every class**: two anchored regrowths of one connected core with at least
three vertices, at a request with a vanishing coordinate, reading the same split for labellings
transported along a labelled-metric isomorphism of their limits, are one class. -/
theorem frameClass_eq_of_reads (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hy : y e₀ = 0) (w w' : Regrowth core y degree) {block block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit) (hψ : IsMetricIso w w' ψ)
    (L : AnchorLabelling w.limit (anchorOf w block))
    (L' : AnchorLabelling w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) (s : Split)
    (hs : Reads L (uOf w) s) (hs' : Reads L' (uOf w') s) :
    FrameClass.mk w.frame = FrameClass.mk w'.frame := by
  obtain ⟨second, hp, second', hp', ψ', hψ', ⟨T⟩⟩ :=
    resolutionMatch_all w w' H H' ψ hψ L L' hL s hs hs'
  obtain ⟨Φ, hcol⟩ := columnIso_of_extendsMetric
    (extendsMetric_of_transportFree w w' second hp second' hp' ψ' hψ' T)
  exact FrameClass.mk_eq_mk_iff.mpr ⟨frameIso_of_columns w w'.frame hconn hn hy Φ hcol⟩

/-- **Anchored uniqueness for every class** (stages 3--5, no oddness): over a connected core
with at least three vertices and no slot parallel to the vanishing slot, two anchored regrowths
at a facet point whose limits are labelled-metric isomorphic are one class. -/
theorem frameClass_eq_of_metricIso (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hpar : NoParallel core e₀)
    (w w' : Regrowth core y degree) {block block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block')
    (hsame : ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ) :
    FrameClass.mk w.frame = FrameClass.mk w'.frame := by
  obtain ⟨ψ, hψ⟩ := hsame
  obtain ⟨L⟩ := nonempty_anchorLabelling w.frame.fullDim H
  obtain ⟨L', hL, hsplit⟩ := regrowth_split_eq w w' H H' ψ L
  obtain ⟨s, hsR, -, -⟩ := existsUnique_reads w.frame.fullDim H L
  obtain ⟨s', hsR', -, -⟩ := existsUnique_reads w'.frame.fullDim H' L'
  have hss : s = s' :=
    hsplit s s' hsR hsR' (type_eq_of_metricIso hpt hpar H H' ψ hψ L L' hL s s' hsR hsR')
  subst hss
  exact frameClass_eq_of_reads hconn hn hpt.1 w w' H H' ψ hψ L L' hL s hsR hsR'

end AllClasses

end DraismaVargas.Count.ValencyThreeCoreSlots
