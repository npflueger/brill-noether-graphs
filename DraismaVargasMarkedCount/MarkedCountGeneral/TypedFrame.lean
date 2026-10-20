module

public import DraismaVargasMarkedCount.MarkedCount.MarkedFrame

@[expose] public section

/-!
# The two-point ramified count, module 1: typed marked frames

A **typed marked frame** carries a type `types j : ℕ` at every mark `j`, and satisfies

* **(D4′)**: `r_φ(u_j) ≥ types j` **and** `m(u_j) ≥ types j + 1`
  (`IsTyped`). The second clause is not implied by the first once `types j ≥ 2`: at `g = 2`
  and type `2` there are 456 + 36 full-dimensional frames with `r(u) ≥ 2` and `m(u) = 2` (a
  leaf image with excess change elsewhere, or a divalent image with no excess) that realise
  generic requests but are restrictions of nothing, so it is a field, not a theorem.
  For `types j = 0` both clauses are empty, and the mark is an **unramified mark kept in the
  core**.

The multiplicity is `Mult = D det A / 2^{l*(T)}`, where `l*(T)` is the
number of leaves of the target that are **not** images of marks of positive type
(`leafCountStar`). It is *not* `∏ r(u)^a · D det A / 2^{l(T)}` (false for `a ≥ 2`: a type-`2`
fold has `r(u) = 3` and local factor `2`), and *not* the toric multiplicity of the marked cone
(false for `a ≥ 2`: on computed instances over a genus-four core, its sum over the type-`2`
members is `4`, not `N(4; 2, 0) = 3`); neither reading is used anywhere in this folder.

The dimension count `saturated` is that of the ramification-one marked count, corrected by the
type excess `Σⱼ (types j - 1)`: with `p = 3g - 3 + k` core slots and `d = (g + Σ types + 2)/2`,
`2g + 2d - 5 = p + Σⱼ (types j - 1)` (`TypedFullDim`, `typeExcess`). For all types `1` it is
`MarkedFullDim.saturated` of the ramification-one count verbatim (module `Agreement`).

Everything else is the marked frame of the ramification-one count: the marked rows, the marked
labelling and the marked core identification (`MarkedCoreIdentification`, reused as is), the
isomorphisms over the identity of the marked core, the classes, the fibre at a request, and the
count `typedCount`.

## Contents

The coordinates (`coordsAt`, `mulVec_coordsAt`, `coordsAt_eq_of_mulVec`), the
multiplicity and its two forms (`typedSignedMult_eq`), and the isomorphism invariance of the
coordinates (`TypedFrameIso.exists_column`), of openness and of the multiplicity
(`TypedFrameIso.typedAbsMult_eq`), by the same reindexing as for the ramification-one marked frames
(`markedMatrix_map`, `absMult_eq_of_submatrix`), plus the invariance of the ramified leaf images.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  Local degree and (D4′) -/

/-- **`m(A)`**, the local degree (index) of the source vertex `A`: the size of its block. -/
def markIndex (data : GluingDatum target degree) (vertex : data.SourceVertex) : ℕ :=
  (data.vertexPartition vertex.1.1).blockCard vertex.1.2

/-- **(D4′)**: ramification at least `a` and local degree at least
`a + 1`. -/
def IsTyped (data : GluingDatum target degree) (vertex : data.SourceVertex) (a : ℕ) : Prop :=
  (a : ℤ) ≤ markRamification data vertex ∧ a + 1 ≤ markIndex data vertex

/-- The type excess `Σⱼ (types j - 1)`, the correction to the dimension count. -/
def typeExcess {k : ℕ} (types : Fin k → ℕ) : ℤ := ∑ j, ((types j : ℤ) - 1)

/-! ## 2.  Typed full-dimensionality -/

/-- **Typed full-dimensionality**: the ramification-one `MarkedFullDim` with the dimension count
corrected by `excess` (`|E(T)| + excess = 2 g(G) + 2d - 5`). With `excess = typeExcess types` it is
the saturation of the marked members of type `types` (condition (D3)): `|E(T)| = p` by the
labelling, and `2g + 2d - 5 = p + Σ (types j - 1)` at the headline degree. -/
structure TypedFullDim (data : GluingDatum target degree) (marks : Finset data.SourceVertex)
    (coordinate : Type*) [Fintype coordinate] [DecidableEq coordinate] (excess : ℤ) where
  /-- The datum is a valid gluing datum (connected source, Riemann--Hurwitz). -/
  valid : data.Valid
  /-- Part I's standing hypothesis on the target. -/
  targetConnected : graph_connected target
  /-- Part I's standing hypothesis on the target. -/
  targetGenus : genus target = 0
  /-- The dimension count, corrected by the type excess (a normalization of the degree). -/
  saturated : (target.edges.card : ℤ) + excess = 2 * genus data.sourceGraph + 2 * degree - 5
  /-- The marked labelling. -/
  labelling : MarkedLabelling data marks coordinate
  /-- (D3): the marked edge-length matrix is nonsingular. -/
  det_ne_zero : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0
  /-- No source vertex has four or more surviving occurrences. -/
  trivalent : ∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≤ 3
  /-- (D1): the marks have surviving valency two. -/
  markValency : ∀ vertex ∈ marks, nonDanglingValency data vertex = 2
  /-- No marked row is a cycle. -/
  pathEnds : HasMarkedPathEnds data marks

variable {n p k : ℕ}

/-! ## 3.  Typed frames -/

/-- **A typed marked frame** over the marked core (a marked member of type `types`
without the lengths): a target tree, a gluing datum, the source vertices of the marks, typed
full-dimensionality, the ramification-one marked label (marks to marks), and (D4′) at every mark. -/
structure TypedFrame (core : Core n p) (mark : Fin k → Fin n) (types : Fin k → ℕ)
    (degree : ℕ) where
  /-- The target tree. -/
  target : CFGraph.{0}
  /-- The gluing datum. -/
  data : GluingDatum target degree
  /-- The source vertices of the marks. -/
  markSource : Fin k → data.SourceVertex
  /-- Typed full-dimensionality. -/
  fullDim : TypedFullDim data (markSet markSource) (Fin p) (typeExcess types)
  /-- The marked label (the ramification-one `MarkedCoreIdentification`). -/
  ident : MarkedCoreIdentification core mark data markSource
  /-- (D4′) at every mark. -/
  typed : ∀ j, IsTyped data (markSource j) (types j)

namespace TypedFrame

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

/-- The marked edge-length matrix `A_{ψ;u,v}`. -/
noncomputable def matrix (κ : TypedFrame core mark types degree) : Matrix (Fin p) (Fin p) ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix κ.fullDim.labelling.presentation

theorem det_ne_zero (κ : TypedFrame core mark types degree) : κ.matrix.det ≠ 0 :=
  κ.fullDim.det_ne_zero

/-- The permutation reading a matrix row as a core slot. -/
def slot (κ : TypedFrame core mark types degree) : Fin p ≃ Fin p :=
  κ.fullDim.labelling.row.symm.trans κ.ident.row

/-- **The coordinates at the request `y`**: `z = A⁻¹ y`. -/
noncomputable def coordsAt (κ : TypedFrame core mark types degree) (y : Fin p → ℚ) :
    Fin p → ℚ :=
  κ.matrix⁻¹.mulVec fun row ↦ y (κ.slot row)

theorem mulVec_coordsAt (κ : TypedFrame core mark types degree) (y : Fin p → ℚ) :
    κ.matrix.mulVec (κ.coordsAt y) = fun row ↦ y (κ.slot row) := by
  rw [coordsAt, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr κ.det_ne_zero), Matrix.one_mulVec]

/-- The coordinates are the unique solution of `A z = y ∘ slot`. -/
theorem coordsAt_eq_of_mulVec (κ : TypedFrame core mark types degree) (y : Fin p → ℚ)
    (z : Fin p → ℚ) (h : κ.matrix.mulVec z = fun row ↦ y (κ.slot row)) : κ.coordsAt y = z := by
  rw [coordsAt, ← h, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr κ.det_ne_zero), Matrix.one_mulVec]

/-- **A typed marked member at `y`** is a typed frame open at `y` (coordinates `z > 0`). -/
def OpenAt (κ : TypedFrame core mark types degree) (y : Fin p → ℚ) : Prop :=
  ∀ col, 0 < κ.coordsAt y col

/-- **The images of the ramified marks that are leaves**: the target vertices excluded from
`l*(T)`. A mark is ramified when its type is positive. -/
noncomputable def ramifiedLeafImages (κ : TypedFrame core mark types degree) :
    Finset κ.target.V := by
  classical
  exact ((Finset.univ.filter fun j ↦ 0 < types j).image fun j ↦ (κ.markSource j).1.1).filter
    fun x ↦ Count.IsLeafVertex κ.target x

theorem ramifiedLeafImages_subset (κ : TypedFrame core mark types degree) :
    κ.ramifiedLeafImages ⊆ Count.leafVertices κ.target := by
  classical
  intro x hx
  unfold ramifiedLeafImages at hx
  rw [Count.mem_leafVertices]
  exact (Finset.mem_filter.mp hx).2

/-- **`l*(T)`**: the leaves of the target other than the images of the
ramified marks. -/
noncomputable def leafCountStar (κ : TypedFrame core mark types degree) : ℕ :=
  Count.leafCount κ.target - κ.ramifiedLeafImages.card

/-- **The signed typed multiplicity**: `Mult(ψ; marks) = D_ψ det A_ψ / 2^{l*(T)}`,
Part II's formula on the marked matrix with the images of the ramified marks not counted as
leaves. -/
noncomputable def typedSignedMult (κ : TypedFrame core mark types degree) : ℚ :=
  (Count.denominatorProduct κ.fullDim.labelling.presentation : ℚ) / 2 ^ κ.leafCountStar *
    κ.matrix.det

/-- **The typed multiplicity** `|Mult(ψ; marks)|`. -/
noncomputable def typedAbsMult (κ : TypedFrame core mark types degree) : ℚ := |κ.typedSignedMult|

/-- **The two forms of the multiplicity**: `D det A / 2^{l*} = 2^{#ramified leaf images} · D det A / 2^{l}`
(`2^{[fold]}` times Part II's formula verbatim on the marked matrix). -/
theorem typedSignedMult_eq (κ : TypedFrame core mark types degree) :
    κ.typedSignedMult =
      (2 : ℚ) ^ κ.ramifiedLeafImages.card *
        Count.signedMult κ.fullDim.labelling.presentation := by
  have hle : κ.ramifiedLeafImages.card ≤ Count.leafCount κ.target :=
    Finset.card_le_card κ.ramifiedLeafImages_subset
  unfold typedSignedMult Count.signedMult leafCountStar
  rw [show Count.leafCount κ.target =
    Count.leafCount κ.target - κ.ramifiedLeafImages.card + κ.ramifiedLeafImages.card by omega]
  rw [Nat.add_sub_cancel, pow_add]
  change _ = _ * (_ / (2 ^ (Count.leafCount κ.target - κ.ramifiedLeafImages.card) *
    2 ^ κ.ramifiedLeafImages.card) * κ.matrix.det)
  field_simp

theorem typedSignedMult_ne_zero (κ : TypedFrame core mark types degree) :
    κ.typedSignedMult ≠ 0 := by
  have hDen : ((Count.denominatorProduct κ.fullDim.labelling.presentation : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Count.denominatorProduct_pos κ.fullDim.labelling.presentation).ne'
  exact mul_ne_zero (div_ne_zero hDen (by positivity)) κ.det_ne_zero

end TypedFrame

/-! ## 4.  Isomorphism over the identity of the marked core -/

/-- **An isomorphism of typed frames over the identity of the marked core**: the
ramification-one `MarkedFrameIso`, field for field. -/
structure TypedFrameIso {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
    (first second : TypedFrame core mark types degree) where
  /-- The isomorphism of data. -/
  datum : GeometricDatumIso first.data second.data
  /-- Marks go to marks. -/
  mark : ∀ j, datum.sourceVertexEquiv (first.markSource j) = second.markSource j
  /-- Over the identity of the core, on marked vertices. -/
  overCore_vertex : ∀ (vertex : MarkedBranchVertex first.data (markSet first.markSource))
    (hImage : 3 ≤ nonDanglingValency second.data (datum.sourceVertexEquiv vertex.1) ∨
      datum.sourceVertexEquiv vertex.1 ∈ markSet second.markSource),
    second.ident.vertex ⟨datum.sourceVertexEquiv vertex.1, hImage⟩ = first.ident.vertex vertex
  /-- Over the identity of the core, on marked rows. -/
  overCore_row : ∀ edge : NonDanglingEdge first.data,
    second.ident.row (markedRow (markSet second.markSource)
        (datum.nonDanglingEdgeEquiv first.fullDim.valid.1 edge)) =
      first.ident.row (markedRow (markSet first.markSource) edge)

namespace TypedFrameIso

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {first second : TypedFrame core mark types degree}

theorem mem_markSet_map (iso : TypedFrameIso first second) (vertex : first.data.SourceVertex) :
    iso.datum.sourceVertexEquiv vertex ∈ markSet second.markSource ↔
      vertex ∈ markSet first.markSource := by
  simp only [markSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, iso.datum.sourceVertexEquiv.injective ((iso.mark j).trans hj)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, (iso.mark j).symm⟩

/-- The induced dictionary of marked rows. -/
noncomputable def rowEquiv (iso : TypedFrameIso first second) :
    MarkedStablePath first.data (markSet first.markSource) ≃
      MarkedStablePath second.data (markSet second.markSource) :=
  markedStablePathEquiv iso.datum first.fullDim.valid.1 iso.mem_markSet_map

theorem ident_row_rowEquiv (iso : TypedFrameIso first second)
    (path : MarkedStablePath first.data (markSet first.markSource)) :
    second.ident.row (iso.rowEquiv path) = first.ident.row path := by
  induction path using Quot.ind with
  | mk edge => exact iso.overCore_row edge

/-- The matrix row of `first` matched with matrix row `r` of `second`. -/
noncomputable def rowPerm (iso : TypedFrameIso first second) : Fin p ≃ Fin p :=
  second.fullDim.labelling.row.symm.trans (iso.rowEquiv.symm.trans first.fullDim.labelling.row)

/-- The column of `first` matched with column `c` of `second`. -/
noncomputable def columnPerm (iso : TypedFrameIso first second) : Fin p ≃ Fin p :=
  second.fullDim.labelling.targetEdge.trans
    (iso.datum.targetEdge.symm.trans first.fullDim.labelling.targetEdge.symm)

/-- The marked matrix of `second` is that of `first`, reindexed. -/
theorem matrix_eq_submatrix (iso : TypedFrameIso first second) :
    second.matrix = first.matrix.submatrix iso.rowPerm iso.columnPerm := by
  funext row column
  have h : markedMatrix second.data (markSet second.markSource)
      (iso.rowEquiv (iso.rowEquiv.symm (second.fullDim.labelling.row.symm row)))
      (iso.datum.targetEdge (iso.datum.targetEdge.symm
        (second.fullDim.labelling.targetEdge column))) =
      markedMatrix first.data (markSet first.markSource)
        (iso.rowEquiv.symm (second.fullDim.labelling.row.symm row))
        (iso.datum.targetEdge.symm (second.fullDim.labelling.targetEdge column)) :=
    markedMatrix_map iso.datum first.fullDim.valid.1 iso.mem_markSet_map _ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [Matrix.submatrix_apply, TypedFrame.matrix, TypedFrame.matrix, MarkedLabelling.matrix_eq,
    MarkedLabelling.matrix_eq, h]
  simp [rowPerm, columnPerm]

theorem slot_rowPerm (iso : TypedFrameIso first second) (row : Fin p) :
    first.slot (iso.rowPerm row) = second.slot row := by
  simp only [TypedFrame.slot, rowPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [← iso.ident_row_rowEquiv, Equiv.apply_symm_apply]

/-- **An isomorphism permutes the coordinates.** -/
theorem exists_column (iso : TypedFrameIso first second) :
    ∃ σ : Fin p ≃ Fin p, ∀ (y : Fin p → ℚ) (col : Fin p),
      second.coordsAt y (σ col) = first.coordsAt y col := by
  refine ⟨iso.columnPerm.symm, fun y col ↦ ?_⟩
  have hSolve : second.coordsAt y = fun c ↦ first.coordsAt y (iso.columnPerm c) := by
    refine second.coordsAt_eq_of_mulVec y _ ?_
    funext row
    rw [iso.matrix_eq_submatrix, ← iso.slot_rowPerm]
    refine Eq.trans ?_ (congrFun (first.mulVec_coordsAt y) (iso.rowPerm row))
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    exact Fintype.sum_equiv iso.columnPerm _ _ fun _ ↦ rfl
  rw [hSolve]
  simp

/-- An isomorphism preserves openness. -/
theorem openAt_iff (iso : TypedFrameIso first second) (y : Fin p → ℚ) :
    first.OpenAt y ↔ second.OpenAt y := by
  obtain ⟨σ, hσ⟩ := iso.exists_column
  constructor
  · intro h col
    rw [← σ.apply_symm_apply col, hσ]
    exact h _
  · intro h col
    rw [← hσ]
    exact h _

/-- An isomorphism carries the ramified leaf images onto the ramified leaf images. -/
theorem card_ramifiedLeafImages (iso : TypedFrameIso first second) :
    second.ramifiedLeafImages.card = first.ramifiedLeafImages.card := by
  classical
  refine (Finset.card_bij (fun x _ ↦ iso.datum.targetVertex x) ?_ ?_ ?_).symm
  · intro x hx
    unfold TypedFrame.ramifiedLeafImages at hx ⊢
    obtain ⟨hImg, hLeaf⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hImg
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, hj, ?_⟩,
      (iso.datum.isLeafVertex_map _).mpr hLeaf⟩
    rw [← iso.mark j]
    rfl
  · exact fun _ _ _ _ h ↦ iso.datum.targetVertex.injective h
  · intro x hx
    unfold TypedFrame.ramifiedLeafImages at hx
    obtain ⟨hImg, hLeaf⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hImg
    refine ⟨(first.markSource j).1.1, ?_, ?_⟩
    · unfold TypedFrame.ramifiedLeafImages
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
      rw [← iso.datum.isLeafVertex_map]
      rw [← iso.mark j] at hLeaf
      exact hLeaf
    · rw [← iso.mark j]
      rfl

/-- **An isomorphism preserves the typed multiplicity.** -/
theorem typedAbsMult_eq (iso : TypedFrameIso first second) :
    first.typedAbsMult = second.typedAbsMult := by
  have hAbs : Count.absMult second.fullDim.labelling.presentation =
      Count.absMult first.fullDim.labelling.presentation :=
    absMult_eq_of_submatrix _ _ iso.rowPerm iso.columnPerm iso.matrix_eq_submatrix
      iso.datum.leafCount_map
  unfold TypedFrame.typedAbsMult
  rw [first.typedSignedMult_eq, second.typedSignedMult_eq, abs_mul, abs_mul,
    iso.card_ramifiedLeafImages]
  exact congrArg _ hAbs.symm

end TypedFrameIso

/-! ## 5.  Classes, the typed fibre and the typed count -/

/-- **Typed frames up to isomorphism over the marked core.** -/
def TypedFrameClass (core : Core n p) (mark : Fin k → Fin n) (types : Fin k → ℕ)
    (degree : ℕ) : Type 1 :=
  Quot fun first second : TypedFrame core mark types degree ↦
    Nonempty (TypedFrameIso first second)

namespace TypedFrameClass

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

/-- The class of a typed frame. -/
def mk (κ : TypedFrame core mark types degree) : TypedFrameClass core mark types degree :=
  Quot.mk _ κ

theorem mk_surjective :
    Function.Surjective (mk (core := core) (mark := mark) (types := types) (degree := degree)) :=
  Quot.mk_surjective

theorem mk_eq_mk_of_iso {κ κ' : TypedFrame core mark types degree}
    (h : Nonempty (TypedFrameIso κ κ')) : mk κ = mk κ' :=
  Quot.sound h

/-- Openness of a class at a request. -/
def OpenAt (x : TypedFrameClass core mark types degree) (y : Fin p → ℚ) : Prop :=
  Quot.lift (fun κ : TypedFrame core mark types degree ↦ κ.OpenAt y)
    (fun _ _ h ↦ h.elim fun iso ↦ propext (iso.openAt_iff y)) x

/-- The typed multiplicity of a class. -/
noncomputable def typedAbsMult (x : TypedFrameClass core mark types degree) : ℚ :=
  Quot.lift TypedFrame.typedAbsMult (fun _ _ h ↦ h.elim fun iso ↦ iso.typedAbsMult_eq) x

@[simp] theorem openAt_mk (κ : TypedFrame core mark types degree) (y : Fin p → ℚ) :
    (mk κ).OpenAt y ↔ κ.OpenAt y := Iff.rfl

@[simp] theorem typedAbsMult_mk (κ : TypedFrame core mark types degree) :
    (mk κ).typedAbsMult = κ.typedAbsMult := rfl

end TypedFrameClass

/-- **The typed fibre** at `y`: the classes of typed frames open at `y`, i.e. the marked
members of type `types`. -/
def TypedFibre (core : Core n p) (mark : Fin k → Fin n) (types : Fin k → ℕ) (y : Fin p → ℚ)
    (degree : ℕ) : Type 1 :=
  {x : TypedFrameClass core mark types degree // x.OpenAt y}

/-- **The typed count** `N_{types}`: `Σ_{ψ} |Mult(ψ; marks)|` over the typed fibre (the left
side of `typedCount_twiceMarked`). A rational number a priori; it is a `finsum`, which is honest
because the fibre is finite (`Correspondence.finite_typedFibre`). -/
noncomputable def typedCount (core : Core n p) (mark : Fin k → Fin n) (types : Fin k → ℕ)
    (y : Fin p → ℚ) (degree : ℕ) : ℚ :=
  ∑ᶠ x : TypedFibre core mark types y degree, x.1.typedAbsMult

end DraismaVargas.Count.MarkedCountGeneral
