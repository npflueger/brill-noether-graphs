module

public import DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowEquiv
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoLeafDictionary
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoExit

@[expose] public section

/-!
# The valency-two **Base I** `AgreeOffColumn` / common-minor identity

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1 (rigidity above `w_0`,
the labelling convention (1), and `lm:change-comb-type`: the wall matrix as the
common minor `A_{\varphi_0}` of the incoming matrices), Section 5.4
(Configuration A of Case {v2-nd4}, i.e. Case {v2-nd4-t3}), and Draisma--Vargas
Part I (arXiv:1909.12924), Case {w2-r2}, Base I.

This follows `NonTrivalentValencyTwoRowDictionary`, moved from the Base II
rows of `NonTrivalentValencyTwoRowEquiv` to the **Base I** rows of
`NonTrivalentValencyTwoBaseOneRowEquiv`, with two differences:

* the Base I candidate lives over the gauged datum
  `NonTrivalentValencyTwoGauge.gaugedData`, not over the wall datum itself, so
  the wall datum's own square labelling has to be transported across the
  `t_3`-branch alignment gauge first (`relabelLabelling`, on the pattern of
  `NonTrivalentValencyFourRowDictionary.relabelLabelling`); and
* the outgoing chart re-indexes rows and columns by *two* equivalences
  (`NonTrivalentValencyTwoExit.reindexLabelling₂`), so the new target occurrence
  `t_1` sits in the vanishing **column** and the bridge row `h_1` in the
  vanishing **row** `facet`.  With this convention the identity is literally the
  `AgreeOffColumn` predicate the exit and `NonTrivalentLinkMatrix` consume, not
  just an entrywise identity in two re-indexed charts.

## Which sub-cases Base I is prescribed for

Two independent case distinctions meet here; they must not be confused.

* **Outgoing.**  Base I is the outgoing base tree `T_∅`, with `val(u) = 1` and
  `val(v) = 3`, as in Draisma--Vargas Part I, Case {w2}.  (This library follows
  Part I's description of the two base trees; the description at the start of
  Part II, Section 5.4 differs from it.)  A Base I morphism exists **only** in
  Configuration A (`{v2-nd4-t3}`, two non-dangling edges above each of `t_2`,
  `t_3`) and only when the four indices pair up across the two directions,
  `|e_α| = |e_β|` and `|e_γ| = |e_δ|` (Part II, Section 5.4).  Concretely it
  exists in subcases `{v2-nd4-t3-k2=k4}` (two Base I morphisms: Types I and II)
  and `{v2-nd4-t3-k2=k3}` (one Base I morphism: Type I), and it does **not**
  exist in `{v2-nd4-t3-k2<k3}` (no two incident edges on opposite sides have
  equal cardinality there) nor anywhere in Configuration B `{v2-nd4-t2}` (only
  one edge lies above `t_3` there).  This is exactly why Configuration A
  (`hSplit`) and the two index equalities stay explicit *dispatch data* of the
  main theorem: they are not hypotheses about the candidate, they are the
  hypothesis under which a Base I candidate exists at all.
* **Incoming.**  The `2 + 2` / `1 + 3` / `3 + 1` no-return trichotomy is a
  property of the **incoming** cover and the contracted target occurrence -- of
  `val(a)`, `val(b)` in the incoming target tree -- not of the outgoing base
  tree.  So it is orthogonal to Base I versus Base II, and all three branches
  have to be covered, exactly as `NonTrivalentValencyTwoRowDictionary`
  (`2 + 2`) and `NonTrivalentValencyTwoLeafDictionary` (`1 + 3`, `3 + 1`)
  cover them for Base II.  `exists_wallLabelling_two` does that here: it
  produces the wall datum's own square honest labelling with **no** no-return
  hypothesis, by dispatching on which endpoint (if either) is a leaf.

## What is proved

* `retainedRow_injective`: the Base I retained-row map is injective, immediately
  from `NonTrivalentValencyTwoBaseOneRowEquiv.rowEquiv` being an `Equiv`.
* `occurrences_retainedRow`, `matrix_retainedRow`: the surviving occurrences of a
  retained row over an old target occurrence are exactly the retained copies of
  the surviving occurrences of that row of the datum the candidate lives over,
  hence the candidate's natural matrix in a retained row and an old column is
  that datum's own entry.
* `matrix_candidateLabelling`: the same in the honest `Option coordinate`
  indexing of `NonTrivalentValencyTwoBaseOneRowEquiv.labelling`.
* `gaugeRowEquiv`, `matrix_gaugeRowEquiv`, `relabelLabelling`,
  `matrix_relabelLabelling`, `matrix_candidateLabelling_gauged`: the transport
  across the `t_3`-branch alignment gauge of `NonTrivalentValencyTwoGauge`.  The
  gauge is a `SheetRelabeling`, so `SheetRelabelStable.matrix_map` changes no
  entry.
* `chartLabelling`, `matrix_chartLabelling_eq_incoming`: the outgoing honest
  labelling on the incoming chart index type, and the entrywise identity against
  the incoming full-dimensional matrix off the vanishing row and the contracted
  column.
* `chartLabelling_row_symm_facet`, `occurrences_bridgeRow_of_ne`,
  `matrix_chartLabelling_facet_eq_zero`, `matrix_chartLabelling_corner_pos`: the
  bridge row `h_1` of the Base I candidate is `A_1 → F → A_2`; both its
  occurrences lie over the new target occurrence, so its outgoing row vanishes
  off the contracted column and its corner entry is strictly positive.
* `agreeOffColumn_chartLabelling`: the `AgreeOffColumn` shape, in every row.
* `exists_wallLabelling_two`: the wall datum's own square honest labelling at
  **every** two-valent wall, with no no-return hypothesis (the three incoming
  sub-cases above), together with the two facts the Base I chart needs from it.
* `exists_matrix_chartLabelling_eq_incoming_baseOne`: the statement at an
  actual wall.

## What is NOT proved -- the hypotheses that remain explicit

* The incoming `FullDimensionalSourcePresentation`, the contraction data
  `hc, hab, hOne`, the actual `ContractionForest`, the incoming `TwoStar` and the
  Part II wall metric (`hRows, hZeroCoord, hPosCoord, hFacetZero`) are inputs
  from the caller, exactly as in `NonTrivalentValencyTwoRowDictionary`,
  `NonTrivalentValencyTwoLeafDictionary` and
  `NonTrivalentValencyTwoBaseOneRowEquiv`.  `DanglingCompatible` is derived
  from the forest.
* Configuration A (`hSplit`) and the prescribed cross pairing with its two index
  equalities remain the caller's dispatch data; see "Which sub-cases" above.
  Nothing here claims a Base I morphism exists in `{v2-nd4-t3-k2<k3}` or in
  Configuration B, where the paper says it does not.
* No `FullDimensionalSourcePresentation` of the **outgoing** candidate is built
  here: `det ≠ 0`, trivalence, `HasPathEnds`, the outgoing target facts and
  `OuterWalk.TypeChangeLink` are the Base I exit, the companion module
  `NonTrivalentValencyTwoBaseOneExit`.
* This module introduces **no new structure**; every definition is a transport
  of an existing one (`SheetRelabelStable.stablePathEquiv`,
  `NonTrivalentValencyTwoExit.reindexLabelling₂`).  The structures it consumes
  are inhabited by `NonTrivalentValencyTwoBaseOne.BaseOneSetup` together with
  `NonTrivalentValencyTwoGauge.gauge_model_exists` /
  `exists_gauged_candidate_of_contraction`.

## Consumers

The Base I exit at Part II, Case {v2-nd4}, Configuration A, outgoing Types I
and II, and through it `OuterWalk.TypeChangeLink`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowDictionary

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
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOne
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRows
open DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowEquiv

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

section Candidate

variable {data : GluingDatum target degree} {star : TwoStar target wall}
  {anchor : WallBlock data wall} (setup : BaseOneSetup data star anchor)

local notation "cand" => (validCandidate setup)

/-! ## 1.  Injectivity of the retained-row map, from the row equivalence -/

theorem retainedRow_injective (hValid : data.Valid) :
    Function.Injective (retainedRow setup hValid) := by
  intro r r' hEq
  have h := congrArg (rowEquiv setup hValid) hEq
  simp only [rowEquiv_retainedRow] at h
  exact Option.some.inj h

/-! ## 2.  The candidate's matrix off the new column -/

theorem occurrences_retainedRow (hValid : data.Valid)
    (hInj : Function.Injective (retainedRow setup hValid))
    (r : StablePath data) (e : target.edges) :
    StableSourceMatrix.occurrences (cand).datum (retainedRow setup hValid r)
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
          (candidate_sourceGenus setup) old).mpr h)
      have hOcc : occurrenceEquiv target wall (cand).right (some old.1.1) =
          occurrenceEquiv target wall (cand).right (some e) := hTarget
      have hTargetEq : old.1.1 = e :=
        Option.some.inj ((occurrenceEquiv target wall (cand).right).injective hOcc)
      refine Finset.mem_image.mpr ⟨old, ?_, rfl⟩
      rw [StableSourceMatrix.mem_occurrences]
      exact ⟨⟨hOldSurv, hInj ((retainedRow_mk setup hValid ⟨old, hOldSurv⟩).trans hRow)⟩,
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
    · exact (retainedRow_mk setup hValid ⟨g, hgS⟩).symm.trans
        (congrArg (retainedRow setup hValid) hgRow)
    · show occurrenceEquiv target wall (cand).right (some g.1.1) =
        occurrenceEquiv target wall (cand).right (some e)
      rw [hgTarget]

theorem matrix_retainedRow (hValid : data.Valid)
    (hInj : Function.Injective (retainedRow setup hValid))
    (r : StablePath data) (e : target.edges) :
    StableSourceMatrix.matrix (cand).datum (retainedRow setup hValid r)
        (occurrenceEquiv target wall (cand).right (some e)) =
      StableSourceMatrix.matrix data r e := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_retainedRow setup hValid hInj r e,
    Finset.sum_image (fun _ _ _ _ h ↦ ResolutionCut.oldSourceEdge_injective (cand) h)]
  exact Finset.sum_congr rfl fun g _ ↦ by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]

section MatrixLabelling

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

theorem matrix_candidateLabelling (hValid : data.Valid)
    (labelling₀ : StableLengthMatrixLabelling data coordinate)
    (p : StablePath data) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hValid labelling₀).presentation
        (some (labelling₀.row p)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row p) c := by
  classical
  have hInj := retainedRow_injective setup hValid
  have hRowSymm :
      (NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hValid labelling₀).row.symm
          (some (labelling₀.row p)) = retainedRow setup hValid p := by
    rw [Equiv.symm_apply_eq]
    exact (labelling_row_retained setup hValid labelling₀ p).symm
  have hTgt :
      (NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hValid labelling₀).targetEdge
          (some c) =
        occurrenceEquiv target wall (cand).right (some (labelling₀.targetEdge c)) := rfl
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    hRowSymm, hTgt, Equiv.symm_apply_apply]
  exact matrix_retainedRow setup hValid hInj p (labelling₀.targetEdge c)

end MatrixLabelling

end Candidate

/-! ## 3.  Across the `t₃`-branch alignment gauge -/

section Gauge

open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (base : GluingDatum target degree) (star : TwoStar target wall)
  (anchor : WallBlock base wall) (thickSheet thinSheet : Fin degree)
  (hConn : base.Connected)

/-- The stable rows of the gauged datum, read through the literal source-edge map
of the `t₃`-branch alignment gauge of `NonTrivalentValencyTwoGauge`. -/
noncomputable def gaugeRowEquiv :
    StablePath base ≃ StablePath (gaugedData base star anchor thickSheet thinSheet) :=
  SheetRelabelStable.stablePathEquiv (relabeling base star anchor thickSheet thinSheet) hConn

/-- Every natural matrix column is unchanged by the gauge. -/
theorem matrix_gaugeRowEquiv (q : StablePath base) (place : target.edges) :
    StableSourceMatrix.matrix (gaugedData base star anchor thickSheet thinSheet)
        (gaugeRowEquiv base star anchor thickSheet thinSheet hConn q) place =
      StableSourceMatrix.matrix base q place :=
  SheetRelabelStable.matrix_map (relabeling base star anchor thickSheet thinSheet) hConn q place

/-- A square honest labelling of the incoming wall datum, transported across the
`t₃`-branch alignment gauge of `NonTrivalentValencyTwoGauge`.  The target is
unchanged; the rows follow the literal source-edge map. -/
noncomputable def relabelLabelling
    (labelling₀ : StableLengthMatrixLabelling base coordinate) :
    StableLengthMatrixLabelling (gaugedData base star anchor thickSheet thinSheet)
      coordinate where
  targetEdge := labelling₀.targetEdge
  row := (gaugeRowEquiv base star anchor thickSheet thinSheet hConn).symm.trans labelling₀.row

omit [Fintype coordinate] [DecidableEq coordinate] in
@[simp] theorem relabelLabelling_targetEdge
    (labelling₀ : StableLengthMatrixLabelling base coordinate) (c : coordinate) :
    (relabelLabelling base star anchor thickSheet thinSheet hConn labelling₀).targetEdge c =
      labelling₀.targetEdge c := rfl

omit [Fintype coordinate] [DecidableEq coordinate] in
@[simp] theorem relabelLabelling_row
    (labelling₀ : StableLengthMatrixLabelling base coordinate) (q : StablePath base) :
    (relabelLabelling base star anchor thickSheet thinSheet hConn labelling₀).row
        (gaugeRowEquiv base star anchor thickSheet thinSheet hConn q) =
      labelling₀.row q := by
  show labelling₀.row ((gaugeRowEquiv base star anchor thickSheet thinSheet hConn).symm
    ((gaugeRowEquiv base star anchor thickSheet thinSheet hConn) q)) = _
  rw [Equiv.symm_apply_apply]

/-- The gauge changes no matrix entry: the rows are re-indexed by the literal
source-edge map, and `SheetRelabelStable.matrix_map` transports every column. -/
theorem matrix_relabelLabelling
    (labelling₀ : StableLengthMatrixLabelling base coordinate)
    (q : StablePath base) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (relabelLabelling base star anchor thickSheet thinSheet hConn
          labelling₀).presentation (labelling₀.row q) c =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row q) c := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq,
    Equiv.symm_apply_apply]
  have hRow : (relabelLabelling base star anchor thickSheet thinSheet hConn
      labelling₀).row.symm (labelling₀.row q) =
      gaugeRowEquiv base star anchor thickSheet thinSheet hConn q := by
    rw [Equiv.symm_apply_eq]
    exact (relabelLabelling_row base star anchor thickSheet thinSheet hConn labelling₀ q).symm
  rw [hRow, relabelLabelling_targetEdge]
  exact matrix_gaugeRowEquiv base star anchor thickSheet thinSheet hConn q
    (labelling₀.targetEdge c)

/-- **The Base I candidate's honest matrix against the incoming wall datum's,
across the gauge.** -/
theorem matrix_candidateLabelling_gauged
    (setup : BaseOneSetup (gaugedData base star anchor thickSheet thinSheet) star
      (gaugedAnchor base star anchor thickSheet thinSheet))
    (hGauged : (gaugedData base star anchor thickSheet thinSheet).Valid)
    (labelling₀ : StableLengthMatrixLabelling base coordinate)
    (q : StablePath base) (c : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix
        (NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hGauged
          (relabelLabelling base star anchor thickSheet thinSheet hConn
            labelling₀)).presentation
        (some (labelling₀.row q)) (some c) =
      GluingDatum.LengthMatrixPresentation.matrix labelling₀.presentation
        (labelling₀.row q) c := by
  have h := matrix_candidateLabelling setup hGauged
    (relabelLabelling base star anchor thickSheet thinSheet hConn labelling₀)
    (gaugeRowEquiv base star anchor thickSheet thinSheet hConn q) c
  rw [relabelLabelling_row] at h
  exact h.trans
    (matrix_relabelLabelling base star anchor thickSheet thinSheet hConn labelling₀ q c)

end Gauge

/-! ## 4.  The outgoing chart at an actual two-valent wall -/

section Wall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StablePathFacetContraction
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.NonTrivalentValencyTwoGauge
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

/-- **The outgoing honest labelling of a Base I candidate, in the incoming
chart.**  Rows and columns are re-indexed by two *different* equivalences, on
`NonTrivalentValencyTwoExit.reindexLabelling₂`'s convention: the new target
occurrence `t₁` goes into the vanishing column and the bridge row `h₁` into the
vanishing row `facet`. -/
noncomputable def chartLabelling
    (setup : BaseOneSetup
      (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet thinSheet)
      wallStar
      (gaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet thinSheet))
    (hGauged : (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk
      thickSheet thinSheet).Valid) :
    StableLengthMatrixLabelling (validCandidate setup).datum coordinate :=
  reindexLabelling₂ (rowChart cover fd facet) (colChart cover fd)
    (NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hGauged
      (relabelLabelling (contractDatum cover hc hab hOne) wallStar anchorBlk
        thickSheet thinSheet
        (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1 labelling₀))

/-- **The common minor, entry by entry.**  Off the vanishing row and the
contracted column the outgoing matrix is the incoming matrix. -/
theorem matrix_chartLabelling_eq_incoming
    (setup : BaseOneSetup
      (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet thinSheet)
      wallStar
      (gaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet thinSheet))
    (hGauged : (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk
      thickSheet thinSheet).Valid)
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
          thinSheet labelling₀ setup hGauged).presentation i j =
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
    (NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hGauged
      (relabelLabelling (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
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
    (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1 setup hGauged
    labelling₀ q ⟨j, hj⟩) ?_
  refine Eq.trans (hMatrixWall q ⟨j, hj⟩) ?_
  rw [hPath]

/-! ## 5.  The bridge row, and the `AgreeOffColumn` shape -/

section Bridge

variable (setup : BaseOneSetup
    (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet thinSheet)
    wallStar
    (gaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet thinSheet))
  (hGauged : (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlk
    thickSheet thinSheet).Valid)

/-- The bridge row `h₁` sits in the vanishing row of the incoming chart. -/
theorem chartLabelling_row_symm_facet :
    (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ setup hGauged).row.symm facet =
      bridgeRow setup hGauged := by
  have h : (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
      thinSheet labelling₀ setup hGauged).row (bridgeRow setup hGauged) = facet := by
    show (rowChart cover fd facet (contracted := contracted))
        ((NonTrivalentValencyTwoBaseOneRowEquiv.labelling setup hGauged
          (relabelLabelling (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
            thinSheet (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1
            labelling₀)).row (bridgeRow setup hGauged)) = facet
    rw [labelling_row_bridge setup hGauged
      (relabelLabelling (contractDatum cover hc hab hOne) wallStar anchorBlk thickSheet
        thinSheet (NonTrivalentValencyTwoRows.wall_valid cover fd hc hab hOne hForest).1
        labelling₀)]
    rfl
  exact (Equiv.symm_apply_eq _).mpr h.symm

/-- Both occurrences of the bridge row lie over the new target occurrence `t₁`,
so the bridge row of the outgoing matrix vanishes off the contracted column. -/
theorem occurrences_bridgeRow_of_ne
    (t : (TargetExpansion.graph (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate setup).right).edges)
    (ht : t ≠ occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
      (validCandidate setup).right none) :
    StableSourceMatrix.occurrences (validCandidate setup).datum
      (bridgeRow setup hGauged) t = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro e he
  obtain ⟨⟨hSurv, hRow⟩, hTarget⟩ := (StableSourceMatrix.mem_occurrences _ t e).mp he
  have hEq := bridgeRow_isolated setup hGauged ⟨e, hSurv⟩ hRow
  apply ht
  rw [← hTarget]
  rcases hEq with hCase | hCase
  · have hCase' : e = (validCandidate setup).newSourceEdge setup.foldFirst := hCase
    rw [hCase']
    exact BalancedGlobal.Candidate.newSourceEdge_target _ _
  · have hCase' : e = (validCandidate setup).newSourceEdge setup.foldSecond := hCase
    rw [hCase']
    exact BalancedGlobal.Candidate.newSourceEdge_target _ _

theorem chartLabelling_targetEdge_ne (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ setup hGauged).targetEdge j ≠
      occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (validCandidate setup).right none := by
  classical
  have hSymm : (colChart cover fd (contracted := contracted)).symm j = some ⟨j, hj⟩ :=
    Equiv.optionSubtypeNe_symm_of_ne hj
  show occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩ (validCandidate setup).right
      (Option.map _ ((colChart cover fd (contracted := contracted)).symm j)) ≠ _
  intro hBad
  have hNone := (occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
    (validCandidate setup).right).injective hBad
  rw [hSymm] at hNone
  simp at hNone

theorem chartLabelling_targetEdge_contracted :
    (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ setup hGauged).targetEdge
        (fd.labelling.targetEdge.symm contracted) =
      occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩
        (validCandidate setup).right none := by
  classical
  have hSymm : (colChart cover fd (contracted := contracted)).symm
      (fd.labelling.targetEdge.symm contracted) = none :=
    Equiv.optionSubtypeNe_symm_self _
  show occurrenceEquiv (contract targetIn hab hOne) ⟨a, hab⟩ (validCandidate setup).right
      (Option.map _ ((colChart cover fd (contracted := contracted)).symm
        (fd.labelling.targetEdge.symm contracted))) = _
  rw [hSymm]
  rfl

/-- **The vanishing row of the outgoing matrix.** -/
theorem matrix_chartLabelling_facet_eq_zero (j : coordinate)
    (hj : j ≠ fd.labelling.targetEdge.symm contracted) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
          thinSheet labelling₀ setup hGauged).presentation facet j = 0 := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, chartLabelling_row_symm_facet]
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_of_ne cover hc hab hOne wallStar anchorBlk thickSheet thinSheet
    setup hGauged _
    (chartLabelling_targetEdge_ne cover fd hc hab hOne hForest facet wallStar anchorBlk
      thickSheet thinSheet labelling₀ setup hGauged j hj), Finset.sum_empty]

/-- **The corner entry is positive**: the bridge row's two occurrences both lie
over the new target occurrence. -/
theorem matrix_chartLabelling_corner_pos :
    0 < GluingDatum.LengthMatrixPresentation.matrix
      (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlk thickSheet
        thinSheet labelling₀ setup hGauged).presentation facet
      (fd.labelling.targetEdge.symm contracted) := by
  classical
  rw [StableSourceMatrix.labelling_matrix_eq, chartLabelling_row_symm_facet,
    chartLabelling_targetEdge_contracted]
  unfold StableSourceMatrix.matrix
  refine Finset.sum_pos (fun e _ ↦ div_pos one_pos (by
    exact_mod_cast (validCandidate setup).datum.sourceEdgeIndex_pos e)) ?_
  refine ⟨(validCandidate setup).newSourceEdge setup.foldFirst, ?_⟩
  refine (StableSourceMatrix.mem_occurrences _ _ _).mpr ⟨⟨?_, rfl⟩, ?_⟩
  · exact newSourceEdge_foldFirst_survives setup hGauged
  · exact BalancedGlobal.Candidate.newSourceEdge_target _ _

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
          thinSheet labelling₀ setup hGauged).presentation)
      (fd.labelling.targetEdge.symm contracted) := by
  intro i j hj
  by_cases hi : i = facet
  · rw [hi, matrix_chartLabelling_facet_eq_zero cover fd hc hab hOne hForest facet wallStar
      anchorBlk thickSheet thinSheet labelling₀ setup hGauged j hj]
    exact incoming_facet_eq_zero cover fd coordinates facet hZeroCoord hPosCoord hFacetZero
      j hj
  · exact (matrix_chartLabelling_eq_incoming cover fd hc hab hOne hForest facet wallStar
      anchorBlk thickSheet thinSheet labelling₀ setup hGauged hRowVal hMatrixWall i j hi
      hj).symm

end Bridge

/-! ## 6.  The wall datum's own labelling, in all three incoming sub-cases -/

section Dispatcher

include wallStar in
/-- **Every two-valent wall carries the wall datum's own square honest
labelling, with no no-return hypothesis.**  `val(w₀) = val(u) + val(v) - 2 = 2`
splits into `2 + 2` (neither endpoint of the contracted occurrence is a leaf, so
`StablePathFacetContraction.noContractedReturn_of_nonleaf` applies), `1 + 3`
(`u = a` a leaf) and `3 + 1` (`v = b` a leaf); the last two run through the
weaker `LeafFacetNoReturn.NoContractedReturnOffRow` and its primed chain,
exactly as the dispatcher of `NonTrivalentValencyTwoLeafDictionary` does.  The
two conclusions are the only facts the Base I chart needs:
the row index is the incoming row with the vanishing row and the contracted
column transposed, and every entry off the contracted column is the incoming
entry. -/
theorem exists_wallLabelling_two
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
    ∃ wallLab : StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted},
      (∀ p : StablePath (contractDatum cover hc hab hOne),
        (wallLab.row p).1 =
          Equiv.swap facet (fd.labelling.targetEdge.symm contracted)
            (fd.labelling.row (incomingRow cover fd hc hab hOne
              (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                hForest) hForest p))) ∧
      ∀ (p : StablePath (contractDatum cover hc hab hOne))
        (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
        GluingDatum.LengthMatrixPresentation.matrix wallLab.presentation
            (wallLab.row p) column =
          GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
            (fd.labelling.row (incomingRow cover fd hc hab hOne
              (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
                hForest) hForest p)) column.1 := by
  classical
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne
    hForest
  by_cases hA : (GluingDatum.incidentEdges a).card = 1
  · refine ⟨LeafFacetNoReturn.wallLabelling' cover fd hc hab hOne hCompat hForest coordinates
      facet (NonTrivalentValencyTwoLeafDictionary.noContractedReturnOffRow_of_leaf cover fd
        hc hab hOne wallStar coordinates facet hZeroCoord hPosCoord hFacetZero hA)
      hRows hZeroCoord hPosCoord hFacetZero, fun _ ↦ rfl, ?_⟩
    exact fun p column ↦ LeafFacetNoReturn.matrix_wallLabelling' cover fd hc hab hOne hCompat
      hForest coordinates facet _ hRows hZeroCoord hPosCoord hFacetZero p column
  · by_cases hB : (GluingDatum.incidentEdges b).card = 1
    · refine ⟨LeafFacetNoReturn.wallLabelling' cover fd hc hab hOne hCompat hForest coordinates
        facet (NonTrivalentValencyTwoLeafDictionary.noContractedReturnOffRow_of_leaf_right
          cover fd hc hab hOne wallStar coordinates facet hZeroCoord hPosCoord hFacetZero hB)
        hRows hZeroCoord hPosCoord hFacetZero, fun _ ↦ rfl, ?_⟩
      exact fun p column ↦ LeafFacetNoReturn.matrix_wallLabelling' cover fd hc hab hOne hCompat
        hForest coordinates facet _ hRows hZeroCoord hPosCoord hFacetZero p column
    · have hLeftMem := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
        fd.changeMinimal).2.1
      have hRightMem := (WallProgress.endpoints_of_contraction cover hc hab hOne fd.valid
        fd.changeMinimal).2.2.2.1
      have hLeft : 2 ≤ (GluingDatum.incidentEdges a).card := by omega
      have hRight : 2 ≤ (GluingDatum.incidentEdges b).card := by omega
      have hNoReturn : NoContractedReturn cover contracted :=
        noContractedReturn_of_nonleaf cover fd hc hLeft hRight
      refine ⟨wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn coordinates facet
        hRows hZeroCoord hPosCoord hFacetZero, fun _ ↦ rfl, ?_⟩
      exact fun p column ↦ matrix_wallLabelling cover fd hc hab hOne hCompat hForest hNoReturn
        coordinates facet hRows hZeroCoord hPosCoord hFacetZero p column

end Dispatcher

/-! ## 7.  The actual-wall headline -/

section Headline

include wallStar in
/-- **The valency-two Base I common-minor identity at an actual two-valent
wall.**  Hypotheses: the incoming full-dimensional cover, the actual contraction
forest, the incoming two-valent star, the wall metric of a Part II open facet
with a single vanishing stable row, and -- as the caller's *dispatch* data, not
hypotheses about the candidate -- Configuration A (`hSplit`) together with the
prescribed cross pairing and its two index equalities `|e_α| = |e_β|`,
`|e_γ| = |e_δ|` (Part II, Section 5.4: the condition for a Base I morphism to
exist at all).  Everything else is produced: the anchor block, `nd(A) = 4`, the
wall datum's own honest labelling in **all three** incoming sub-cases (`2 + 2`,
`1 + 3`, `3 + 1` -- no no-return hypothesis), the `t₃`-branch alignment
gauge, the Base I candidate over the gauged datum with its validity and source
genus, the outgoing honest labelling in the incoming chart, the
`AgreeOffColumn` common minor and the positive corner entry. -/
theorem exists_matrix_chartLabelling_eq_incoming_baseOne
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
    ∃ (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
      (wallLab : StableLengthMatrixLabelling (contractDatum cover hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
      nonDanglingValency (contractDatum cover hc hab hOne)
          (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
            anchorBlock) = 4 ∧
      ∀ (_ : ∀ label : Fin 2,
          (directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock
            label).card = 2)
        (thickFirst thickSecond thinFirst thinSecond :
          IncidentSourceEdge (contractDatum cover hc hab hOne)
            (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩ anchorBlock)),
        thickFirst ∈
            directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock 0 →
        thickSecond ∈
            directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock 0 →
        thinFirst ∈
            directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock 1 →
        thinSecond ∈
            directionSurvivors (contractDatum cover hc hab hOne) wallStar anchorBlock 1 →
        thickFirst ≠ thickSecond → thinFirst ≠ thinSecond →
        (contractDatum cover hc hab hOne).sourceEdgeIndex thickFirst.1 =
            (contractDatum cover hc hab hOne).sourceEdgeIndex thinFirst.1 →
        (contractDatum cover hc hab hOne).sourceEdgeIndex thickSecond.1 =
            (contractDatum cover hc hab hOne).sourceEdgeIndex thinSecond.1 →
        ∃ (gauged : BaseOneSetup
            (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlock
              (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)) wallStar
            (gaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock
              (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)))
          (hGauged : (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlock
            (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)).Valid),
          (validCandidate gauged).datum.Valid ∧
            genus (validCandidate gauged).datum.sourceGraph =
              genus (gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlock
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)).sourceGraph ∧
            nonDanglingValency (validCandidate gauged).datum
                (leafVertex gauged gauged.foldFirst) = 2 ∧
            (∀ s, ((gaugedData (contractDatum cover hc hab hOne) wallStar anchorBlock
                (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)).vertexPartition
                  ⟨a, hab⟩).Rel
                (gaugedAnchor (contractDatum cover hc hab hOne) wallStar anchorBlock
                  (occurrenceSheet thickFirst) (occurrenceSheet thinFirst)).1 s →
              nonDanglingValency (validCandidate gauged).datum
                (branchVertex gauged s) = 3) ∧
            AgreeOffColumn
                (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
                (GluingDatum.LengthMatrixPresentation.matrix
                  (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlock
                    (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) wallLab gauged
                    hGauged).presentation)
                (fd.labelling.targetEdge.symm contracted) ∧
            0 < GluingDatum.LengthMatrixPresentation.matrix
                (chartLabelling cover fd hc hab hOne hForest facet wallStar anchorBlock
                  (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) wallLab gauged
                  hGauged).presentation facet
                (fd.labelling.targetEdge.symm contracted) := by
  classical
  obtain ⟨wallLab, hRowVal, hMatrixWall⟩ :=
    exists_wallLabelling_two cover fd hc hab hOne hForest facet wallStar coordinates hRows
      hZeroCoord hPosCoord hFacetZero
  obtain ⟨anchorBlock, hNd, hRest⟩ :=
    NonTrivalentValencyTwoBaseOneRowEquiv.exists_rowEquiv_of_wall_metric cover fd hc hab hOne
      hForest
      (WallAdmissibility.danglingCompatible_of_contractionForest cover hc hab hOne hForest)
      wallStar coordinates facet hRows hZeroCoord hPosCoord hFacetZero
  refine ⟨anchorBlock, wallLab, hNd, ?_⟩
  intro hSplit thickFirst thickSecond thinFirst thinSecond hTF hTS hNF hNS hTNe hNNe
    hIndexFirst hIndexSecond
  obtain ⟨gauged, hGauged, hValid, hGenus, hLeaf, hBranch, -, -⟩ :=
    hRest hSplit thickFirst thickSecond thinFirst thinSecond hTF hTS hNF hNS hTNe hNNe
      hIndexFirst hIndexSecond
  refine ⟨gauged, hGauged, hValid, hGenus, hLeaf, hBranch, ?_, ?_⟩
  · exact agreeOffColumn_chartLabelling cover fd hc hab hOne hForest facet wallStar
      anchorBlock (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) wallLab gauged
      hGauged coordinates hZeroCoord hPosCoord hFacetZero hRowVal hMatrixWall
  · exact matrix_chartLabelling_corner_pos cover fd hc hab hOne hForest facet wallStar
      anchorBlock (occurrenceSheet thickFirst) (occurrenceSheet thinFirst) wallLab gauged
      hGauged

end Headline

end Wall

end DraismaVargas.LocalCases.NonTrivalentValencyTwoBaseOneRowDictionary
