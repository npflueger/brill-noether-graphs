module

public import DraismaVargasCount.M11StarParityFree

@[expose] public section

/-!
# A family-generic engine for star censuses

Source: Vargas, Part II (arXiv:2609.09109), the star of a codimension-one wall and the
balancing condition `prop-signed-mult`; and Draisma--Vargas Part I (arXiv:1909.12924), the
regrowing of a wall vertex to an edge, that is, the one-vertex target expansion at a wall
vertex (section "Constructions", subsection "Trees contracting to T₀", `sub-graphs-to-T0`).

Every non-W4 family clause of `RegrowthWallInput.FamilyStarParity` is a *census*: the star
of a wall is in bijection with the nonsingular members of the family's balance equation,
each class carrying its member's multiplicity.  This file is the part of that census that
does not depend on the family.  It serves the star censuses of the trivalent walls (step 2
of `DraismaVargasCount.Assembly`) and, through `FacetCommonMultiplicity`, the type changes
(step 3).

## API guide (for a family)

A family provides, at a regrowth `w`, each balance member as a gluing datum `D` on a
one-vertex target expansion `graph (w.frame.limitTarget w.column) (mergeVertex w) right`,
with a stable-graph equivalence `E : StableGraphIncidence.Equivalence w.limit D` (the
family's own row/branch dictionary) whose retained columns reproduce the limit's natural
matrix (`hRetained`, usually the family's `matrix_retained`).  Then:

1. `frame w hy D E fd` is a frame for **any** full-dimensional presentation `fd` of `D`
   (its labelling is replaced by the wall-inherited `labelling`, which is automatically
   nonsingular, `relabelFullDim`); it has the wall's slot order (`frame_slot`) and the
   wall's coordinates (`frame_coordsAt`), so `regrowth w hy fd hRetained` degenerates in
   the wall's column.
2. Anchor the position: name the datum `M` its regrown occurrence contracts to, with the
   three partition conditions `hMerge`/`hOld`/`hEdge` (for a blockwise candidate these are
   `join_eq_of_isJoin_join` plus the `GlobalResolution` partition lemmas), and an arbitrary
   `φ : GeometricDatumIso M w.limit` (`refl` when wall-anchored; a sheet relabelling such
   as a branch swap otherwise).  Prove the two anchor squares `BranchSquare` (use
   `sourceEndpoint_contract`) and `RowSquare`.  `starMember` is then a member of the
   wall's star with `multNat_starMember` its labelling's multiplicity (`rfl`).
3. Separate positions with §5: any frame isomorphism between two positions of one wall
   sends the regrown occurrence to the regrown occurrence (`frameIso_newEdge`), fixes
   every inherited row (`frameIso_row`), and so preserves the regrown column
   (`frameIso_matrix_new`) and the valencies of its ends (`frameIso_valencies`).
4. Exhaust with §6: present each position as a resolution expansion of its anchor
   (`hD`, `rfl` for a blockwise candidate) and, for each star member, its own normal form
   (`M11WallExhaustion.normIso` and its two dictionary lemmas at a divalent wall) and a
   `ResolutionExpansionFree.TransportFree` along its limit isomorphism composed with
   `φ.symm`; `cls_eq_of_transport` puts it in the position's class.
5. Close with `starParityAt_of_census` over the family's index type.

The one family-specific input the engine cannot supply is the **transport** of step 4
(a classification of member local resolutions); see "What is NOT proved".

## What is proved

* §1 `starParityAt_of_census` -- the star clause from a vanishing integral balance over
  any finite index type and a census by its nonsingular terms.
* §2 `labelling`, `relabelFullDim`, `ident`, `frame`, `frame_slot`,
  `labelling_matrix_retained`, `labelling_mulVec_coordsAt`, `frame_coordsAt`,
  `frame_degenerate`, `frame_edgeOf`, `regrowth` -- the position frame.
* §3 `contractIso`, `limitIso`, `BranchSquare`, `RowSquare`, `limitIso_branch`,
  `overCore_vertex`, `limitIso_row`, `overCore_row`, `starLimitIso`, `starMember`,
  `multNat_starMember` -- the "star member by position" constructor through an arbitrary
  anchor isomorphism (not necessarily wall-anchored).
* §4 `join_eq_of_isJoin_join` (a join is determined by its relation when the other side
  is a constructed join -- representatives included) and `sourceEndpoint_contract`.
* §5 `agreeOffColumnSlot`, `frameIso_newEdge`, `frameIso_row`, `frameIso_matrix_new`,
  `frameIso_valencies` -- the separation invariants.
* §6 `anchoredDatum`, `anchored_source_square`, `anchored_edge_square`,
  `anchoredFrameIso`, `cls_eq_of_transport` (and `sourceVertexEquiv_symm_apply`,
  `sourceEdgeEquiv_symm_apply`, `symm_source*Equiv_apply`) -- the exhaustion skeleton: the
  anchored form of `ResolutionExpansionFree.frameIsoFree`, which reaches positions whose
  anchor is not the wall.

`BranchSquare` and `RowSquare` are hypotheses that each family proves, not constructions:
they are exactly the two fields `overCore_vertex` and `overCore_row` of
`GeometricStar.LimitIso` for `limitIso`, reduced to the anchor.  Both are inhabited at all
three M-11 positions
(`M11StarCensusProof.split_branchSquare`, `remote_branchSquare`, `refl_rowSquare`,
`remote_rowSquare`).

## What is not proved here (every hypothesis, explicitly)

* **Exhaustion.**  Nothing here says every star member is a frame isomorph of some
  position; that is proved family by family (for example in `M11StarExhaustionProof`).
  §6 reduces it to one
  `ResolutionExpansionFree.TransportFree` per member (the `transport` argument of
  `cls_eq_of_transport`), i.e. to a classification of the member's local resolution up to
  the relabellings `TransportFree` allows.  No transport is constructed here.
* No family, valency or figure enters any statement of this file.
-/

namespace DraismaVargas.Count.StarCensusEngine

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource
open WallStar (Regrowth Nondegenerate)
open SegmentWalls (Frame)
open GeometricSegmentWalls (FrameIso)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  The star clause from a balance and a census, over any index type -/

section Parity

variable {hy : Nondegenerate y} {w : Regrowth core y degree}

/-- **The star clause from a vanishing integral balance and a census of the star by the
balance's nonsingular terms**, over an arbitrary finite index type.  The terms outside
`S` must vanish; the census identifies `S` with the star, each class carrying the
numerator of its term. -/
theorem starParityAt_of_census {ι : Type*} [Fintype ι] (m : ι → ℚ)
    (hint : ∀ i, ∃ value : ℤ, m i = (value : ℚ)) (hbal : ∑ i, m i = 0)
    (S : ι → Prop) (hzero : ∀ i, ¬ S i → m i = 0)
    (e : {i // S i} ≃ GeometricStar.Star hy w)
    (hmult : ∀ i, (GeometricStar.Star.toFibre (e i)).multNat = (m i.1).num.natAbs) :
    RegrowthWallInput.StarParityAt hy w := by
  classical
  refine StarParityFromBalance.even_card_starClass_odd_of_equiv e ?_
  have hEven := StarParityFromBalance.even_sum_num_natAbs_of_sum_eq_zero m hint hbal
  have hSplit := Fintype.sum_subtype_add_sum_subtype S (fun i ↦ (m i).num.natAbs)
  have hRest : ∑ i : {i // ¬ S i}, (m i.1).num.natAbs = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by rw [hzero i.1 i.2]; rfl
  rw [hRest, add_zero] at hSplit
  rw [← hSplit] at hEven
  simpa only [hmult] using hEven

end Parity

/-! ## 2.  A position frame: a regrowth read through a stable-graph equivalence of its wall

Fix a regrowth `w` and a gluing datum `D` on a one-vertex target expansion of its limit
target at the merged vertex, together with a stable-graph equivalence `E : w.limit ≃ D`
whose retained columns reproduce the limit's natural matrix (`hRetained`).  Then `D`,
labelled by the wall's own inherited rows and columns, is a frame with the wall's slot
order and the wall's coordinates at the request, so it degenerates in the wall's column. -/

section Position

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  {right : (w.frame.limitTarget w.column).edges → Bool}
  (D : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right) degree)
  (E : StableGraphIncidence.Equivalence w.limit D)

/-- The position labelling: rows through `E` and the wall's inherited row labels, columns
through the wall's own coordinates (`W4StarParity.columnEquiv`), the collapsed coordinate
naming the regrown occurrence. -/
noncomputable def labelling : StableLengthMatrixLabelling D (Fin p) where
  row := E.row.symm.trans (InheritedLimitRows.rowLabel w hy)
  targetEdge := (W4StarParity.columnEquiv w).trans
    (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right)

/-- A full-dimensional presentation with its labelling replaced: any labelling of a
full-dimensional datum is nonsingular (multiplicity is labelling-independent). -/
noncomputable def relabelFullDim {target : CFGraph} {data : GluingDatum target degree}
    (fd : FullDimensionalSourcePresentation data (Fin p))
    (labelling : StableLengthMatrixLabelling data (Fin p)) :
    FullDimensionalSourcePresentation data (Fin p) where
  valid := fd.valid
  targetConnected := fd.targetConnected
  targetGenus := fd.targetGenus
  saturated := fd.saturated
  labelling := labelling
  det_ne_zero := by
    have h := absMult_labelling_indep fd.labelling labelling
    have hfd := (W4StarParity.absMult_ne_zero_iff fd.labelling.presentation).mpr fd.det_ne_zero
    exact (W4StarParity.absMult_ne_zero_iff labelling.presentation).mp (h ▸ hfd)
  trivalent := fd.trivalent
  pathEnds := fd.pathEnds

@[simp] theorem relabelFullDim_labelling {target : CFGraph} {data : GluingDatum target degree}
    (fd : FullDimensionalSourcePresentation data (Fin p))
    (labelling : StableLengthMatrixLabelling data (Fin p)) :
    (relabelFullDim fd labelling).labelling = labelling := rfl

/-- The core labels of the position, inherited from the wall through `E`. -/
noncomputable def ident : CoreIdentification core D where
  vertex := E.vertex.symm.trans (InheritedLimitIncidence.coreIdentification w hy).vertex
  row := E.row.symm.trans (InheritedLimitIncidence.coreIdentification w hy).row
  incidence v slot := by
    have h := E.incidence (E.vertex.symm v)
      ((InheritedLimitIncidence.coreIdentification w hy).row.symm slot)
    have ho := (InheritedLimitIncidence.coreIdentification w hy).incidence (E.vertex.symm v) slot
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_symm] using h.symm.trans ho

theorem ident_row : (ident w hy D E).row = (labelling w hy D E).row := rfl

variable (fd : FullDimensionalSourcePresentation D (Fin p))

/-- The position frame. -/
noncomputable def frame : Frame core degree :=
  ⟨_, D, relabelFullDim fd (labelling w hy D E), ident w hy D E⟩

theorem frame_slot : (frame w hy D E fd).slot = Equiv.refl (Fin p) := by
  apply Equiv.ext
  intro r
  change (ident w hy D E).row ((labelling w hy D E).row.symm r) = r
  rw [ident_row, Equiv.apply_symm_apply]

variable {D E} (hRetained : ∀ (path : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges),
    StableSourceMatrix.matrix D (E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some place)) =
      StableSourceMatrix.matrix w.limit path place)

include hRetained in
/-- Off the wall column the position's matrix is the wall's own, in the wall's slot
order. -/
theorem labelling_matrix_retained (r c : Fin p) (hc : c ≠ w.column) :
    GluingDatum.LengthMatrixPresentation.matrix (labelling w hy D E).presentation r c =
      w.frame.matrix (w.frame.slot.symm r) c := by
  rw [StableSourceMatrix.labelling_matrix_eq]
  change StableSourceMatrix.matrix D (E.row ((InheritedLimitRows.rowLabel w hy).symm r))
      (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right
        (W4StarParity.columnEquiv w c)) = _
  rw [W4StarParity.columnEquiv_retained w c hc, hRetained]
  exact InheritedLimitRows.matrix_retained w hy r ⟨c, hc⟩

include hRetained in
/-- **The position's labelling realizes the request at the wall's own coordinates.** -/
theorem labelling_mulVec_coordsAt :
    (GluingDatum.LengthMatrixPresentation.matrix (labelling w hy D E).presentation).mulVec
        (w.frame.coordsAt y) = y := by
  funext r
  have hw := congrFun (w.frame.mulVec_coordsAt y) (w.frame.slot.symm r)
  simp only [Equiv.apply_symm_apply] at hw
  rw [← hw]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases hc : c = w.column
  · subst hc
    rw [w.degenerate.1, mul_zero, mul_zero]
  · rw [labelling_matrix_retained w hy hRetained r c hc]

include hRetained in
/-- **The position's coordinates at the request are the wall's own.** -/
theorem frame_coordsAt : (frame w hy D E fd).coordsAt y = w.frame.coordsAt y := by
  have hM : (frame w hy D E fd).matrix =
      GluingDatum.LengthMatrixPresentation.matrix (labelling w hy D E).presentation := rfl
  have h : (fun r ↦ y ((frame w hy D E fd).slot r)) =
      (frame w hy D E fd).matrix.mulVec (w.frame.coordsAt y) := by
    rw [frame_slot, hM, labelling_mulVec_coordsAt w hy hRetained]
    rfl
  rw [SegmentWalls.Frame.coordsAt, h, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (frame w hy D E fd).isUnit_det, Matrix.one_mulVec]

include hRetained in
theorem frame_degenerate : (frame w hy D E fd).DegenerateAt y w.column := by
  rw [SegmentWalls.Frame.DegenerateAt, frame_coordsAt w hy fd hRetained]
  exact w.degenerate

theorem frame_edgeOf : (frame w hy D E fd).edgeOf w.column =
    occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right none := by
  change (labelling w hy D E).targetEdge w.column = _
  change occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right
    (W4StarParity.columnEquiv w w.column) = _
  rw [W4StarParity.columnEquiv_wall]

/-- **The position regrowth**: same request, same vanishing column as the wall. -/
noncomputable def regrowth : Regrowth core y degree :=
  ⟨frame w hy D E fd, w.column, frame_degenerate w hy fd hRetained⟩

end Position

/-! ## 3.  The position's limit, anchored at the wall through an arbitrary datum isomorphism

The position's limit is compared with an **anchor** datum `M` on the wall's limit target
by the literal contraction dictionaries (`W4LimitContraction.limitIso`), and `M` with the
wall's limit by an arbitrary geometric isomorphism `φ`.  At a wall-anchored position
`M = w.limit` and `φ = refl`; at Figure 32's remote split `M` is the branch-swapped datum
and `φ` is the inverse branch swap.  The two inherited-label squares reduce to one
statement about branch vertices (`hV`) and one about retained rows (`hR`), both at the
level of `M`. -/

section Limit

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  {right : (w.frame.limitTarget w.column).edges → Bool}
  {D : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right) degree}
  {E : StableGraphIncidence.Equivalence w.limit D}
  (fd : FullDimensionalSourcePresentation D (Fin p))
  (hRetained : ∀ (path : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges),
    StableSourceMatrix.matrix D (E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some place)) =
      StableSourceMatrix.matrix w.limit path place)
  (M : GluingDatum (w.frame.limitTarget w.column) degree) (φ : GeometricDatumIso M w.limit)
  (hMerge : SheetPartition.join
      (D.vertexPartition (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)))
      (D.vertexPartition (freshVertex (w.frame.limitTarget w.column))) =
    M.vertexPartition (mergeVertex w))
  (hOld : ∀ vertex : (w.frame.limitTarget w.column).V, vertex ≠ mergeVertex w →
    D.vertexPartition (oldVertex (w.frame.limitTarget w.column) vertex) = M.vertexPartition vertex)
  (hEdge : ∀ edge : (w.frame.limitTarget w.column).edges,
    D.edgePartition (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right
      (some edge)) = M.edgePartition edge)

/-- The literal contraction of the position onto its anchor. -/
noncomputable def contractIso : GeometricDatumIso (regrowth w hy fd hRetained).limit M :=
  W4LimitContraction.limitIso rfl (fst_ne_snd ((frame w hy D E fd).edgeOf w.column))
    ((frame w hy D E fd).numEdges_edgeOf w.column) (frame_edgeOf w hy fd) M D
    hMerge hOld hEdge

/-- **The position's limit dictionary to the wall**: contraction, then the anchor. -/
noncomputable def limitIso : GeometricDatumIso (regrowth w hy fd hRetained).limit w.limit :=
  (contractIso w hy fd hRetained M hMerge hOld hEdge).trans φ

include φ in
theorem anchor_connected : M.Connected :=
  φ.symm.connected (InheritedLimitRows.limit_connected w)

/-- The branch half of the anchor condition: `E` sends each wall branch to a source
vertex whose contraction, read in the anchor and carried to the wall by `φ`, is that
branch. -/
def BranchSquare : Prop :=
  ∀ v : StableGraphIncidence.BranchVertex w.limit,
    φ.sourceVertexEquiv (M.sourceEndpoint
      (contractVertex (w.frame.limitTarget w.column) (mergeVertex w) (E.vertex v).1.1.1)
      (E.vertex v).1.1.2) = v.1

/-- The row half: the row of a surviving anchor occurrence, carried to the wall by `φ`
and back up by `E`, is the row of its literal retained copy. -/
def RowSquare : Prop :=
  ∀ (e : NonDanglingEdge M) (e' : NonDanglingEdge D),
    e'.1.1 = (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right
      (some e.1.1.1), e.1.1.2) →
    E.row (φ.stablePathEquiv (anchor_connected w M φ) e.stablePath) = e'.stablePath

variable {w hy fd hRetained M φ hMerge hOld hEdge}

theorem limitIso_branch (hV : BranchSquare w M φ (E := E))
    (v : StableGraphIncidence.BranchVertex w.limit) :
    (limitIso w hy fd hRetained M φ hMerge hOld hEdge).branchVertexEquiv
        (InheritedLimitRows.limit_connected (regrowth w hy fd hRetained))
        (InheritedLimitBranches.branchEquiv (regrowth w hy fd hRetained) hy (E.vertex v)) = v := by
  apply Subtype.ext
  change φ.sourceVertexEquiv ((contractIso w hy fd hRetained M hMerge hOld hEdge).sourceVertexEquiv
    (InheritedLimitBranches.vertexMap (regrowth w hy fd hRetained) (E.vertex v).1)) = v.1
  have h := W4LimitContraction.sourceVertexEquiv_sourceVertexMap rfl
    (fst_ne_snd ((frame w hy D E fd).edgeOf w.column))
    ((frame w hy D E fd).numEdges_edgeOf w.column) (frame_edgeOf w hy fd) M D
    hMerge hOld hEdge (E.vertex v).1
  rw [show (contractIso w hy fd hRetained M hMerge hOld hEdge).sourceVertexEquiv
      (InheritedLimitBranches.vertexMap (regrowth w hy fd hRetained) (E.vertex v).1) =
      M.sourceEndpoint (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
        (E.vertex v).1.1.1) (E.vertex v).1.1.2 from h]
  exact hV v

theorem overCore_vertex (hV : BranchSquare w M φ (E := E))
    (branch : StableGraphIncidence.BranchVertex (regrowth w hy fd hRetained).limit) :
    (InheritedLimitIncidence.coreIdentification w hy).vertex
        ((limitIso w hy fd hRetained M φ hMerge hOld hEdge).branchVertexEquiv
          (InheritedLimitRows.limit_connected (regrowth w hy fd hRetained)) branch) =
      (InheritedLimitIncidence.coreIdentification (regrowth w hy fd hRetained) hy).vertex
        branch := by
  obtain ⟨old, rfl⟩ :=
    (InheritedLimitBranches.branchEquiv (regrowth w hy fd hRetained) hy).surjective branch
  obtain ⟨v, rfl⟩ := E.vertex.surjective old
  rw [limitIso_branch hV v]
  exact (congrArg (InheritedLimitIncidence.coreIdentification w hy).vertex
      (E.vertex.symm_apply_apply v)).symm.trans
    (congrArg (ident w hy D E).vertex
      ((InheritedLimitBranches.branchEquiv (regrowth w hy fd hRetained) hy).symm_apply_apply
        (E.vertex v))).symm

theorem limitIso_row (hR : RowSquare w M φ (E := E))
    (row : StablePath (regrowth w hy fd hRetained).limit) :
    E.row ((limitIso w hy fd hRetained M φ hMerge hOld hEdge).stablePathEquiv
        (InheritedLimitRows.limit_connected (regrowth w hy fd hRetained)) row) =
      InheritedLimitRows.rowEquiv (regrowth w hy fd hRetained) hy row := by
  refine Quot.inductionOn row ?_
  intro edge
  have hTrans := congrArg (fun f : StablePath (regrowth w hy fd hRetained).limit ≃
      StablePath w.limit ↦ f edge.stablePath)
    (GeometricDatumIso.stablePathEquiv_trans (contractIso w hy fd hRetained M hMerge hOld hEdge) φ
      (InheritedLimitRows.limit_connected (regrowth w hy fd hRetained))
      (anchor_connected w M φ))
  change E.row ((limitIso w hy fd hRetained M φ hMerge hOld hEdge).stablePathEquiv
      (InheritedLimitRows.limit_connected (regrowth w hy fd hRetained)) edge.stablePath) =
    InheritedLimitRows.rowEquiv (regrowth w hy fd hRetained) hy edge.stablePath
  rw [show limitIso w hy fd hRetained M φ hMerge hOld hEdge =
    (contractIso w hy fd hRetained M hMerge hOld hEdge).trans φ from rfl]
  refine (congrArg E.row hTrans).trans ?_
  simp only [Equiv.trans_apply]
  refine Eq.trans (congrArg (fun r ↦ E.row (φ.stablePathEquiv (anchor_connected w M φ) r))
    ((contractIso w hy fd hRetained M hMerge hOld hEdge).stablePathEquiv_mk
      (InheritedLimitRows.limit_connected (regrowth w hy fd hRetained)) edge)) ?_
  refine Eq.trans (hR _ ⟨InheritedLimitRows.edgeEmbedding (regrowth w hy fd hRetained) edge.1,
    fun h ↦ edge.2 ((InheritedLimitRows.edgeEmbedding_dangling (regrowth w hy fd hRetained) hy
      edge.1).mp h)⟩ ?_) (InheritedLimitRows.rowEquiv_mk (regrowth w hy fd hRetained) hy edge).symm
  have h1 := (InheritedLimitRows.edgeEmbedding_target (regrowth w hy fd hRetained) edge.1).trans
      (W4LimitContraction.occurrenceEquiv_edgeEquiv rfl
        (fst_ne_snd ((frame w hy D E fd).edgeOf w.column))
        ((frame w hy D E fd).numEdges_edgeOf w.column) (frame_edgeOf w hy fd)
        edge.1.1.1).symm
  have h2 : (InheritedLimitRows.edgeEmbedding (regrowth w hy fd hRetained) edge.1).1.2 =
      edge.1.1.2 :=
    congrArg Prod.snd (IncomingNormalizationRows.sourceEdgeEmbedding_val D rfl
      (fst_ne_snd ((frame w hy D E fd).edgeOf w.column))
      ((frame w hy D E fd).numEdges_edgeOf w.column) edge.1)
  exact Prod.ext h1 h2

theorem overCore_row (hR : RowSquare w M φ (E := E))
    (row : StablePath (regrowth w hy fd hRetained).limit) :
    (InheritedLimitIncidence.coreIdentification w hy).row
        ((limitIso w hy fd hRetained M φ hMerge hOld hEdge).stablePathEquiv
          (InheritedLimitRows.limit_connected (regrowth w hy fd hRetained)) row) =
      (InheritedLimitIncidence.coreIdentification (regrowth w hy fd hRetained) hy).row row := by
  change (InheritedLimitIncidence.coreIdentification w hy).row _ =
    (ident w hy D E).row (InheritedLimitRows.rowEquiv (regrowth w hy fd hRetained) hy row)
  change _ = (InheritedLimitIncidence.coreIdentification w hy).row (E.row.symm
    (InheritedLimitRows.rowEquiv (regrowth w hy fd hRetained) hy row))
  rw [← limitIso_row hR row, Equiv.symm_apply_apply]

/-- **The position is a labelled member of the wall's geometric star.** -/
noncomputable def starLimitIso (hV : BranchSquare w M φ (E := E))
    (hR : RowSquare w M φ (E := E)) :
    GeometricStar.LimitIso hy (regrowth w hy fd hRetained) w where
  datum := limitIso w hy fd hRetained M φ hMerge hOld hEdge
  overCore_vertex := overCore_vertex hV
  overCore_row := overCore_row hR

noncomputable def starMember (hV : BranchSquare w M φ (E := E))
    (hR : RowSquare w M φ (E := E)) : GeometricStar.StarMember hy w :=
  ⟨regrowth w hy fd hRetained, ⟨starLimitIso (hMerge := hMerge) (hOld := hOld) (hEdge := hEdge)
    hV hR⟩⟩

/-- The multiplicity of the position's star class is its own labelling's. -/
theorem multNat_starMember (hV : BranchSquare w M φ (E := E))
    (hR : RowSquare w M φ (E := E)) :
    (GeometricStar.Star.toFibre
        (starMember (hy := hy) (fd := fd) (hRetained := hRetained) (hMerge := hMerge) (hOld := hOld) (hEdge := hEdge) hV hR).cls).multNat =
      (signedMult (labelling w hy D E).presentation).num.natAbs := rfl

end Limit

/-! ## 4.  Two anchor helpers: canonical joins and contracted endpoints -/

section Helpers

/-- **A join is determined by its relation, representatives included**, when the other
side is itself a constructed join: both choose the least sheet of each class.  This is
what turns a resolution's `ContractsTo` (relation level) into the literal `hMerge`
equation at a contracted limit, whose merged partition is a constructed join. -/
theorem join_eq_of_isJoin_join {d : ℕ} {left right a b : SheetPartition d}
    (h : SheetPartition.IsJoin left right (SheetPartition.join a b)) :
    SheetPartition.join left right = SheetPartition.join a b := by
  apply SheetPartition.ext_repr
  funext i
  change SheetPartition.joinRepr left right i = SheetPartition.joinRepr a b i
  have hClass : SheetPartition.joinClass left right i = SheetPartition.joinClass a b i := by
    ext k
    rw [SheetPartition.mem_joinClass, SheetPartition.mem_joinClass,
      ← SheetPartition.join_rel_iff a b, ← SheetPartition.join_rel_iff left right]
    exact ((h i k).trans (SheetPartition.join_rel_iff left right i k).symm).symm
  unfold SheetPartition.joinRepr
  congr 1

/-- A source vertex of an expansion, contracted and read in a base datum whose partition
it refines, is the base source endpoint of its own place and sheet. -/
theorem sourceEndpoint_contract {target : CFGraph} {wallV : target.V}
    {right : target.edges → Bool} (D : GluingDatum (graph target wallV right) degree)
    (M : GluingDatum target degree) (place : Vertex target) (sheet : Fin degree)
    (hRefines : (D.vertexPartition place).Refines
      (M.vertexPartition (contractVertex target wallV place))) :
    M.sourceEndpoint (contractVertex target wallV (D.sourceEndpoint place sheet).1.1)
        (D.sourceEndpoint place sheet).1.2 =
      M.sourceEndpoint (contractVertex target wallV place) sheet := by
  apply (M.sourceEndpoint_eq_iff _ _ _).mpr
  refine ⟨rfl, ?_⟩
  change (M.vertexPartition (contractVertex target wallV place)).repr
      ((D.vertexPartition place).repr sheet) =
    (M.vertexPartition (contractVertex target wallV place)).repr
      ((M.vertexPartition (contractVertex target wallV place)).repr sheet)
  rw [(M.vertexPartition (contractVertex target wallV place)).repr_idem]
  exact hRefines.rel ((D.vertexPartition place).rel_repr_left sheet)

end Helpers

/-! ## 5.  Separation tools: what a frame isomorphism between two positions preserves

Two position frames of one wall have the wall's slot order and agree off the wall
column, so any frame isomorphism between them fixes every column
(`FrameColumnRigidity`), sends the regrown occurrence to the regrown occurrence
(`frameIso_newEdge`), fixes every inherited row (`frameIso_row`), hence preserves the
regrown column entry by entry (`frameIso_matrix_new`) and the valencies of the regrown
occurrence's two ends (`frameIso_valencies`).  Distinct positions are separated by
exhibiting a difference in one of these. -/

section Separation

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  {right right' : (w.frame.limitTarget w.column).edges → Bool}
  {D : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right) degree}
  {D' : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right') degree}
  {E : StableGraphIncidence.Equivalence w.limit D}
  {E' : StableGraphIncidence.Equivalence w.limit D'}
  (fd : FullDimensionalSourcePresentation D (Fin p))
  (fd' : FullDimensionalSourcePresentation D' (Fin p))
  (hRetained : ∀ (path : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges),
    StableSourceMatrix.matrix D (E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some place)) =
      StableSourceMatrix.matrix w.limit path place)
  (hRetained' : ∀ (path : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges),
    StableSourceMatrix.matrix D' (E'.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right' (some place)) =
      StableSourceMatrix.matrix w.limit path place)

include hRetained hRetained' in
theorem agreeOffColumnSlot :
    FrameColumnRigidity.AgreeOffColumnSlot (frame w hy D E fd) (frame w hy D' E' fd') w.column := by
  intro s j hj
  rw [frame_slot, frame_slot]
  change GluingDatum.LengthMatrixPresentation.matrix (labelling w hy D' E').presentation s j =
    GluingDatum.LengthMatrixPresentation.matrix (labelling w hy D E).presentation s j
  rw [labelling_matrix_retained w hy hRetained' s j hj,
    labelling_matrix_retained w hy hRetained s j hj]

variable {w hy fd fd'}

include hRetained hRetained' in
/-- **A frame isomorphism between two positions sends the regrown occurrence to the
regrown occurrence.** -/
theorem frameIso_newEdge (fi : FrameIso (frame w hy D E fd) (frame w hy D' E' fd')) :
    fi.datum.targetEdge (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right none) =
      occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right' none := by
  have h := FrameIso.targetEdge_map_of_agreeOffColumn fi
    (agreeOffColumnSlot w hy fd fd' hRetained hRetained') w.column
  rw [show (frame w hy D E fd).fullDim.labelling.targetEdge w.column =
      occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right none from
      frame_edgeOf w hy fd,
    show (frame w hy D' E' fd').fullDim.labelling.targetEdge w.column =
      occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right' none from
      frame_edgeOf w hy fd'] at h
  exact h

/-- **A frame isomorphism between two positions fixes every inherited row.** -/
theorem frameIso_row (fi : FrameIso (frame w hy D E fd) (frame w hy D' E' fd'))
    (path : StablePath w.limit) :
    fi.datum.stablePathEquiv (frame w hy D E fd).fullDim.valid.1 (E.row path) = E'.row path := by
  have h := fi.overCore_row (E.row path)
  change InheritedLimitRows.rowLabel w hy (E'.row.symm
      (fi.datum.stablePathEquiv (frame w hy D E fd).fullDim.valid.1 (E.row path))) =
    InheritedLimitRows.rowLabel w hy (E.row.symm (E.row path)) at h
  rw [Equiv.symm_apply_apply] at h
  exact (Equiv.symm_apply_eq _).mp ((InheritedLimitRows.rowLabel w hy).injective h)

include hRetained hRetained' in
/-- **The regrown column is a class invariant of positions**, row by inherited row. -/
theorem frameIso_matrix_new (fi : FrameIso (frame w hy D E fd) (frame w hy D' E' fd'))
    (path : StablePath w.limit) :
    StableSourceMatrix.matrix D' (E'.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right' none) =
      StableSourceMatrix.matrix D (E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right none) := by
  rw [← frameIso_row fi path, ← frameIso_newEdge hRetained hRetained' fi]
  exact fi.datum.matrix_map _ _ _

include hRetained hRetained' in
/-- **The valencies of the regrown occurrence's two ends are a class invariant**, up to
the order of the ends. -/
theorem frameIso_valencies (fi : FrameIso (frame w hy D E fd) (frame w hy D' E' fd')) :
    ((GluingDatum.incidentEdges (target := graph (w.frame.limitTarget w.column) (mergeVertex w) right)
        (oldVertex (w.frame.limitTarget w.column) (mergeVertex w))).card =
        (GluingDatum.incidentEdges
          (target := graph (w.frame.limitTarget w.column) (mergeVertex w) right')
          (oldVertex (w.frame.limitTarget w.column) (mergeVertex w))).card ∧
      (GluingDatum.incidentEdges (target := graph (w.frame.limitTarget w.column) (mergeVertex w) right)
        (freshVertex (w.frame.limitTarget w.column))).card =
        (GluingDatum.incidentEdges
          (target := graph (w.frame.limitTarget w.column) (mergeVertex w) right')
          (freshVertex (w.frame.limitTarget w.column))).card) ∨
    ((GluingDatum.incidentEdges (target := graph (w.frame.limitTarget w.column) (mergeVertex w) right)
        (oldVertex (w.frame.limitTarget w.column) (mergeVertex w))).card =
        (GluingDatum.incidentEdges
          (target := graph (w.frame.limitTarget w.column) (mergeVertex w) right')
          (freshVertex (w.frame.limitTarget w.column))).card ∧
      (GluingDatum.incidentEdges (target := graph (w.frame.limitTarget w.column) (mergeVertex w) right)
        (freshVertex (w.frame.limitTarget w.column))).card =
        (GluingDatum.incidentEdges
          (target := graph (w.frame.limitTarget w.column) (mergeVertex w) right')
          (oldVertex (w.frame.limitTarget w.column) (mergeVertex w))).card) := by
  have hEnds := fi.datum.ends
    (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right none)
  rw [frameIso_newEdge hRetained hRetained' fi] at hEnds
  have hOld := fi.datum.incidentEdges_card_map
    (oldVertex (w.frame.limitTarget w.column) (mergeVertex w))
  have hFresh := fi.datum.incidentEdges_card_map (freshVertex (w.frame.limitTarget w.column))
  rcases hEnds with h | h
  · have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [occurrenceEquiv_none, newEnds] at h1 h2
    left
    rw [← h1] at hOld
    rw [← h2] at hFresh
    exact ⟨hOld.symm, hFresh.symm⟩
  · have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [occurrenceEquiv_none, newEnds] at h1 h2
    right
    rw [← h2] at hOld
    rw [← h1] at hFresh
    exact ⟨hOld.symm, hFresh.symm⟩

end Separation

/-! ## 6.  Exhaustion skeleton: an anchored upward frame isomorphism from a decoupled transport

The anchored form of `ResolutionExpansionFree.frameIsoFree`.  A star member `other`,
normalized onto the resolution expansion of its own limit (`N`, with its two dictionary
facts `hNV`, `hNE` -- `M11WallExhaustion.sourceVertexMap_datumIso` and
`retainedSourceEdge_datumIso` at a divalent wall), whose limit isomorphism **composed with
the anchor's inverse** admits a `ResolutionExpansionFree.TransportFree` onto a position
presented as a resolution expansion of its anchor (`hD`), is a frame isomorph of that
position.  At a wall-anchored position (`φ = refl`) this is `frameIsoFree`; the anchored
form is what reaches Figure 32's remote split, whose anchor isomorphism is incoherent. -/

section Anchored

variable {w : Regrowth core y degree} {hy : Nondegenerate y}
  {right : (w.frame.limitTarget w.column).edges → Bool}
  {D : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right) degree}
  {E : StableGraphIncidence.Equivalence w.limit D}
  {fd : FullDimensionalSourcePresentation D (Fin p)}
  {hRetained : ∀ (path : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges),
    StableSourceMatrix.matrix D (E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some place)) =
      StableSourceMatrix.matrix w.limit path place}
  {M : GluingDatum (w.frame.limitTarget w.column) degree} {φ : GeometricDatumIso M w.limit}
  {hMerge : SheetPartition.join
      (D.vertexPartition (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)))
      (D.vertexPartition (freshVertex (w.frame.limitTarget w.column))) =
    M.vertexPartition (mergeVertex w)}
  {hOld : ∀ vertex : (w.frame.limitTarget w.column).V, vertex ≠ mergeVertex w →
    D.vertexPartition (oldVertex (w.frame.limitTarget w.column) vertex) = M.vertexPartition vertex}
  {hEdge : ∀ edge : (w.frame.limitTarget w.column).edges,
    D.edgePartition (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right
      (some edge)) = M.edgePartition edge}
  (hV : BranchSquare w M φ (E := E)) (hR : RowSquare w M φ (E := E))
  {res : ResolutionM11.LocalResolution degree}
  {compat : GlobalResolution.OldCompatible M (mergeVertex w) right res}
  (hD : D = GlobalResolution.datum M (mergeVertex w) right res compat)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
  {plM : (other.frame.limitTarget other.column).edges → Bool}
  {resM : ResolutionM11.LocalResolution degree}
  {compatM : GlobalResolution.OldCompatible other.limit (mergeVertex other) plM resM}
  (N : GeometricDatumIso other.frame.data
    (GlobalResolution.datum other.limit (mergeVertex other) plM resM compatM))
  (hNV : ∀ vertex : other.frame.data.SourceVertex,
    InheritedLimitBranches.vertexMap other vertex =
      GlobalResolution.sourceVertexMap other.limit (mergeVertex other) plM resM compatM
        (N.sourceVertexEquiv vertex))
  (hNE : ∀ edge : other.limit.SourceEdge,
    N.sourceEdgeEquiv (InheritedLimitRows.edgeEmbedding other edge) =
      ResolutionExpansion.retainedSourceEdge other.limit (mergeVertex other) plM resM compatM edge)
  (transport : ResolutionExpansionFree.TransportFree (ψ.datum.trans φ.symm) (mergeVertex other)
    (mergeVertex w) plM right resM res)

/-- The datum half of the anchored upward lift. -/
noncomputable def anchoredDatum : GeometricDatumIso other.frame.data D :=
  (N.trans (ResolutionExpansionFree.liftFree (ψ.datum.trans φ.symm) (mergeVertex other)
    (mergeVertex w) plM right resM res compatM compat transport)).trans
    (UniformExpansionRecognition.ofEq hD.symm)

theorem symm_sourceVertexEquiv_apply {T₁ T₂ : CFGraph} {first : GluingDatum T₁ degree}
    {second : GluingDatum T₂ degree} (iso : GeometricDatumIso first second)
    (x : first.SourceVertex) : iso.symm.sourceVertexEquiv (iso.sourceVertexEquiv x) = x :=
  Subtype.ext (Prod.ext (iso.targetVertex.symm_apply_apply _) (by
    change (iso.vertexPerm (iso.targetVertex.symm (iso.targetVertex x.1.1))).symm
      (iso.vertexPerm x.1.1 x.1.2) = x.1.2
    rw [iso.targetVertex.symm_apply_apply, Equiv.symm_apply_apply]))

theorem symm_sourceEdgeEquiv_apply {T₁ T₂ : CFGraph} {first : GluingDatum T₁ degree}
    {second : GluingDatum T₂ degree} (iso : GeometricDatumIso first second)
    (x : first.SourceEdge) : iso.symm.sourceEdgeEquiv (iso.sourceEdgeEquiv x) = x :=
  Subtype.ext (Prod.ext (iso.targetEdge.symm_apply_apply _) (by
    change (iso.edgePerm (iso.targetEdge.symm (iso.targetEdge x.1.1))).symm
      (iso.edgePerm x.1.1 x.1.2) = x.1.2
    rw [iso.targetEdge.symm_apply_apply, Equiv.symm_apply_apply]))

theorem sourceVertexEquiv_symm_apply {T₁ T₂ : CFGraph} {first : GluingDatum T₁ degree}
    {second : GluingDatum T₂ degree} (iso : GeometricDatumIso first second)
    (x : second.SourceVertex) : iso.sourceVertexEquiv (iso.symm.sourceVertexEquiv x) = x :=
  Subtype.ext (Prod.ext (iso.targetVertex.apply_symm_apply _) (Equiv.apply_symm_apply _ _))

theorem sourceEdgeEquiv_symm_apply {T₁ T₂ : CFGraph} {first : GluingDatum T₁ degree}
    {second : GluingDatum T₂ degree} (iso : GeometricDatumIso first second)
    (x : second.SourceEdge) : iso.sourceEdgeEquiv (iso.symm.sourceEdgeEquiv x) = x :=
  Subtype.ext (Prod.ext (iso.targetEdge.apply_symm_apply _) (Equiv.apply_symm_apply _ _))

include hD hNV in
/-- **The anchored branch square.** -/
theorem anchored_source_square (vertex : other.frame.data.SourceVertex) :
    (starLimitIso (fd := fd) (hRetained := hRetained) (hMerge := hMerge) (hOld := hOld)
        (hEdge := hEdge) hV hR).datum.sourceVertexEquiv
        (InheritedLimitBranches.vertexMap (regrowth w hy fd hRetained)
          ((anchoredDatum hD other ψ N transport).sourceVertexEquiv vertex)) =
      ψ.datum.sourceVertexEquiv (InheritedLimitBranches.vertexMap other vertex) := by
  change φ.sourceVertexEquiv ((contractIso w hy fd hRetained M hMerge hOld hEdge).sourceVertexEquiv
    (InheritedLimitBranches.vertexMap (regrowth w hy fd hRetained)
      ((anchoredDatum hD other ψ N transport).sourceVertexEquiv vertex))) = _
  rw [show (contractIso w hy fd hRetained M hMerge hOld hEdge).sourceVertexEquiv
      (InheritedLimitBranches.vertexMap (regrowth w hy fd hRetained)
        ((anchoredDatum hD other ψ N transport).sourceVertexEquiv vertex)) =
      M.sourceEndpoint (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
        ((anchoredDatum hD other ψ N transport).sourceVertexEquiv vertex).1.1)
        ((anchoredDatum hD other ψ N transport).sourceVertexEquiv vertex).1.2 from
      W4LimitContraction.sourceVertexEquiv_sourceVertexMap rfl
        (fst_ne_snd ((frame w hy D E fd).edgeOf w.column))
        ((frame w hy D E fd).numEdges_edgeOf w.column) (frame_edgeOf w hy fd) M D
        hMerge hOld hEdge _]
  have hVal := UniformExpansionRecognition.ofEq_sourceVertexEquiv hD.symm
    ((ResolutionExpansionFree.liftFree (ψ.datum.trans φ.symm) (mergeVertex other)
      (mergeVertex w) plM right resM res compatM compat transport).sourceVertexEquiv
      (N.sourceVertexEquiv vertex))
  have hLift := ResolutionExpansionFree.sourceVertexMap_liftFree (ψ.datum.trans φ.symm)
    (mergeVertex other) (mergeVertex w) plM right resM res compatM compat transport
    (N.sourceVertexEquiv vertex)
  change φ.sourceVertexEquiv (M.sourceEndpoint (contractVertex (w.frame.limitTarget w.column)
    (mergeVertex w) ((UniformExpansionRecognition.ofEq hD.symm).sourceVertexEquiv
      ((ResolutionExpansionFree.liftFree (ψ.datum.trans φ.symm) (mergeVertex other)
      (mergeVertex w) plM right resM res compatM compat transport).sourceVertexEquiv
      (N.sourceVertexEquiv vertex))).1.1)
      ((UniformExpansionRecognition.ofEq hD.symm).sourceVertexEquiv
      ((ResolutionExpansionFree.liftFree (ψ.datum.trans φ.symm) (mergeVertex other)
      (mergeVertex w) plM right resM res compatM compat transport).sourceVertexEquiv
      (N.sourceVertexEquiv vertex))).1.2) = _
  rw [hVal]
  change φ.sourceVertexEquiv (GlobalResolution.sourceVertexMap M (mergeVertex w) right res compat
    ((ResolutionExpansionFree.liftFree (ψ.datum.trans φ.symm) (mergeVertex other)
      (mergeVertex w) plM right resM res compatM compat transport).sourceVertexEquiv
      (N.sourceVertexEquiv vertex))) = _
  rw [← hLift, ← hNV]
  change φ.sourceVertexEquiv (φ.symm.sourceVertexEquiv
    (ψ.datum.sourceVertexEquiv (InheritedLimitBranches.vertexMap other vertex))) = _
  exact sourceVertexEquiv_symm_apply φ _

include hD hNE in
/-- **The anchored row square.** -/
theorem anchored_edge_square (edge : other.limit.SourceEdge) :
    (anchoredDatum hD other ψ N transport).sourceEdgeEquiv
        (InheritedLimitRows.edgeEmbedding other edge) =
      InheritedLimitRows.edgeEmbedding (regrowth w hy fd hRetained)
        (StarFrameIso.transfer ψ (starLimitIso (fd := fd) (hRetained := hRetained)
          (hMerge := hMerge) (hOld := hOld) (hEdge := hEdge) hV hR) edge) := by
  set Λ := starLimitIso (fd := fd) (hRetained := hRetained) (hMerge := hMerge) (hOld := hOld)
    (hEdge := hEdge) hV hR
  set e' := StarFrameIso.transfer ψ Λ edge
  have hT : Λ.datum.sourceEdgeEquiv e' = ψ.datum.sourceEdgeEquiv edge :=
    StarFrameIso.datum_sourceEdgeEquiv_transfer ψ Λ edge
  have hC : (contractIso w hy fd hRetained M hMerge hOld hEdge).sourceEdgeEquiv e' =
      φ.symm.sourceEdgeEquiv (ψ.datum.sourceEdgeEquiv edge) := by
    rw [← hT]
    exact (symm_sourceEdgeEquiv_apply φ _).symm
  apply Subtype.ext
  have h0 := UniformExpansionRecognition.ofEq_sourceEdgeEquiv hD.symm
    ((ResolutionExpansionFree.liftFree (ψ.datum.trans φ.symm) (mergeVertex other)
      (mergeVertex w) plM right resM res compatM compat transport).sourceEdgeEquiv
      (N.sourceEdgeEquiv (InheritedLimitRows.edgeEmbedding other edge)))
  change ((UniformExpansionRecognition.ofEq hD.symm).sourceEdgeEquiv
    ((ResolutionExpansionFree.liftFree (ψ.datum.trans φ.symm) (mergeVertex other)
      (mergeVertex w) plM right resM res compatM compat transport).sourceEdgeEquiv
      (N.sourceEdgeEquiv (InheritedLimitRows.edgeEmbedding other edge)))).1 = _
  rw [h0, hNE, ResolutionExpansionFree.retainedSourceEdge_liftFree]
  change (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right
      (some (φ.symm.sourceEdgeEquiv (ψ.datum.sourceEdgeEquiv edge)).1.1),
    (φ.symm.sourceEdgeEquiv (ψ.datum.sourceEdgeEquiv edge)).1.2) = _
  rw [← hC]
  have h1 := (InheritedLimitRows.edgeEmbedding_target (regrowth w hy fd hRetained) e').trans
      (W4LimitContraction.occurrenceEquiv_edgeEquiv rfl
        (fst_ne_snd ((frame w hy D E fd).edgeOf w.column))
        ((frame w hy D E fd).numEdges_edgeOf w.column) (frame_edgeOf w hy fd) e'.1.1).symm
  have h2 : (InheritedLimitRows.edgeEmbedding (regrowth w hy fd hRetained) e').1.2 = e'.1.2 :=
    congrArg Prod.snd (IncomingNormalizationRows.sourceEdgeEmbedding_val D rfl
      (fst_ne_snd ((frame w hy D E fd).edgeOf w.column))
      ((frame w hy D E fd).numEdges_edgeOf w.column) e')
  exact (Prod.ext h1 h2).symm

include hD hNV hNE in
/-- **The anchored upward frame isomorphism**: a member receiving a decoupled transport
onto a position is in the position's star class. -/
noncomputable def anchoredFrameIso : FrameIso other.frame (regrowth w hy fd hRetained).frame :=
  StarFrameIso.ofLimitSquare ψ (starLimitIso (fd := fd) (hRetained := hRetained)
      (hMerge := hMerge) (hOld := hOld) (hEdge := hEdge) hV hR)
    (anchoredDatum hD other ψ N transport) (anchored_source_square hV hR hD other ψ N hNV transport)
    (anchored_edge_square hV hR hD other ψ N hNE transport)

include hD in
theorem cls_eq_of_transport (member : GeometricStar.StarMember hy w)
    (ψ' : GeometricStar.LimitIso hy member.member w)
    {plM : (member.member.frame.limitTarget member.member.column).edges → Bool}
    {resM : ResolutionM11.LocalResolution degree}
    {compatM : GlobalResolution.OldCompatible member.member.limit (mergeVertex member.member)
      plM resM}
    (N : GeometricDatumIso member.member.frame.data
      (GlobalResolution.datum member.member.limit (mergeVertex member.member) plM resM compatM))
    (hNV : ∀ vertex : member.member.frame.data.SourceVertex,
      InheritedLimitBranches.vertexMap member.member vertex =
        GlobalResolution.sourceVertexMap member.member.limit (mergeVertex member.member) plM resM
          compatM (N.sourceVertexEquiv vertex))
    (hNE : ∀ edge : member.member.limit.SourceEdge,
      N.sourceEdgeEquiv (InheritedLimitRows.edgeEmbedding member.member edge) =
        ResolutionExpansion.retainedSourceEdge member.member.limit (mergeVertex member.member)
          plM resM compatM edge)
    (transport : ResolutionExpansionFree.TransportFree (ψ'.datum.trans φ.symm)
      (mergeVertex member.member) (mergeVertex w) plM right resM res) :
    member.cls = (starMember (fd := fd) (hRetained := hRetained) (hMerge := hMerge) (hOld := hOld)
      (hEdge := hEdge) hV hR).cls :=
  Quotient.sound ⟨anchoredFrameIso (fd := fd) (hRetained := hRetained) (hMerge := hMerge)
    (hOld := hOld) (hEdge := hEdge) hV hR hD member.member ψ' N hNV hNE transport⟩

end Anchored

end DraismaVargas.Count.StarCensusEngine
