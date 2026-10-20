module

public import DraismaVargasMarkedCount.MarkedCount.Core
public import DraismaVargasMarkedCount.MarkedCount.MarkedPath
public import DraismaVargasMarkedCount.MarkedCount.MarkedTransport
public import DraismaVargasCount.Fibre
public import DraismaVargasCount.GeometricStableTransport

@[expose] public section

/-!
# Marked frames, their multiplicity, the marked fibre and the marked count

The intrinsic object of the marked count: marked discrete tropical morphisms, their
multiplicity and their fibre, in the request-free frame form of
`DraismaVargasCount.SegmentWalls.Frame` and `CrossCoreTransport.FrameClass`. For a morphism
`φ : G → T` with marks `u_G, v_G, …` over a marked core, the conditions are labelled:

* **(D1)** the marks are non-dangling, of surviving valency two;
* **(D2)** the *marked stable graph* (vertices: surviving valency at least three, or a mark;
  edges: the maximal paths whose interior vertices have surviving valency two and are not
  marks) is identified with the marked core, the marks going to the marks;
* **(D3)** the marked edge-length matrix `A_{φ;u,v}` is square and nonsingular;
* **(D4)** `r_φ(u_G) ≥ a` at a mark of type `a`; here every mark has type `a = 1`.

A *marked member* at the request `y` satisfies (D1)--(D4) and has coordinates
`z = A_{φ;u,v}⁻¹ y > 0`; a *marked frame* is the same without the lengths. This module defines:

* `markRamification data A = r_φ(A)`, the local ramification (`GluingDatum.localRamification`)
  at the block of a source vertex.
* `MarkedFullDim data marks coordinate excess`: the marked twin of
  `FullDimensionalSourcePresentation`, with the marked labelling (module `MarkedPath`), the marks
  of surviving valency two ((D1)), the marked path ends, and the dimension count
  `|E(T)| + excess = 2 g(G) + 2d - 5`.  With every mark ramified the excess is `0`, the unmarked
  form, because `|E(T)| = p = 3g - 3 + k` and `d = (g + k)/2 + 1`; marks of other types correct
  it (module `MarkedCountGeneral.TypedFrame`).
* `MarkedCoreIdentification core mark data markSource`: the marked twin of
  `CoreIdentification`, sending the marks to the marks ((D2)).
* `MarkedFrameBase core mark excess degree`: a target tree, a gluing datum, the marks, marked
  full-dimensionality and the marked label, with no condition at the marks yet. It carries the
  coordinates `coordsAt` and openness `OpenAt`, and its isomorphisms `MarkedFrameBase.Iso` over
  the identity of the marked core, phrased pointwise on the source so that no induced dictionary
  is needed to state them.
* `MarkedFrame core mark degree`: a marked frame, extending `MarkedFrameBase` at excess `0` by
  the field `ramified : 1 ≤ r_φ(u_G)` at every mark ((D4) with `a = 1`; unramified marks are
  never in the core).
* `markedSignedMult = (∏ⱼ r_φ(markⱼ)) · D_φ det A_{φ;u,v} / 2^{l(T)}` and `markedAbsMult`, its
  absolute value (equivalently, `absMult` times `∏ⱼ r_φ(markⱼ)`).
* `MarkedFrameIso`: the isomorphisms of the underlying `MarkedFrameBase`.
* `MarkedFrameClass`, `MarkedFibre core mark y degree` (the classes open at `y`: the marked fibre
  `M(Γ, u, v; a, b)` consists of the members, which have `z > 0`) and **`markedCount`**, the sum of
  `markedAbsMult` over the marked fibre.

## Isomorphisms

* `MarkedFrameBase.Iso.exists_column`: an isomorphism permutes the coordinate vector;
* `MarkedFrameIso.markedAbsMult_eq`: an isomorphism preserves the marked multiplicity.

Both are the marked twins of facts proved for `GeometricMemberIso` (`coords_column`,
`absMult_eq`, in `DraismaVargasCount.GeometricMultiplicity`), and are proved the same way: the
induced dictionary of marked rows `MarkedFrameBase.Iso.rowEquiv` preserves the natural marked
matrix (`markedMatrix_map`, module `MarkedTransport`), so the matrix of `second` is that of
`first` reindexed (`MarkedFrameBase.Iso.matrix_eq_submatrix`, hence `Iso.absMult_eq`); and `r_φ`
is a relabelling invariant (`localRamification_map`).

## Proved here

`markRamification_nonneg` (Riemann--Hurwitz), `ramificationFactor_pos`,
`markedSignedMult_ne_zero`, `mulVec_coordsAt`, `coordsAt_eq_of_mulVec`, the two statements
on isomorphisms, and `MarkedFrameBase.Iso.openAt_iff` from `exists_column`.
-/

namespace DraismaVargas.Count.MarkedCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  Ramification at a source vertex -/

/-- **`r_φ(A)`**, the Riemann--Hurwitz residual `(val A - 2) - m(A)(val φ(A) - 2)` at the block of
the source vertex `A`. -/
def markRamification (data : GluingDatum target degree) (vertex : data.SourceVertex) : ℤ :=
  data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩

/-- Riemann--Hurwitz: `r_φ ≥ 0` on a valid datum. -/
theorem markRamification_nonneg {data : GluingDatum target degree} (hValid : data.Valid)
    (vertex : data.SourceVertex) : 0 ≤ markRamification data vertex := by
  have hRH := hValid.2 vertex.1.1 vertex.1.2
  unfold markRamification GluingDatum.localRamification
  linarith

/-! ## 2.  Marked full-dimensionality -/

/-- The set of marks of a marked datum. -/
def markSet {data : GluingDatum target degree} {k : ℕ} (markSource : Fin k → data.SourceVertex) :
    Finset data.SourceVertex :=
  Finset.univ.image markSource

theorem mem_markSet {data : GluingDatum target degree} {k : ℕ}
    (markSource : Fin k → data.SourceVertex) (j : Fin k) : markSource j ∈ markSet markSource :=
  Finset.mem_image_of_mem _ (Finset.mem_univ j)

/-- **Marked full-dimensionality** ((D1), (D3)) with dimension excess `excess`: the marked
twin of `FullDimensionalSourcePresentation`. The rows of the length matrix are the marked rows,
the marks have surviving valency two, no marked row is a cycle, and the dimension count is
`|E(T)| + excess = 2 g(G) + 2d - 5`. At excess `0` it is the unmarked dimension count, which
holds verbatim when every mark is ramified. -/
structure MarkedFullDim (data : GluingDatum target degree) (marks : Finset data.SourceVertex)
    (coordinate : Type*) [Fintype coordinate] [DecidableEq coordinate] (excess : ℤ) where
  /-- The datum is a valid gluing datum (connected source, Riemann--Hurwitz). -/
  valid : data.Valid
  /-- Part I's standing hypothesis on the target. -/
  targetConnected : graph_connected target
  /-- Part I's standing hypothesis on the target. -/
  targetGenus : genus target = 0
  /-- The dimension count, corrected by the excess (a normalization of the degree). -/
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

/-- Marked full-dimensionality at an equal excess. -/
def MarkedFullDim.castExcess {data : GluingDatum target degree}
    {marks : Finset data.SourceVertex} {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] {excess excess' : ℤ} (h : excess = excess')
    (fd : MarkedFullDim data marks coordinate excess) :
    MarkedFullDim data marks coordinate excess' :=
  { fd with saturated := h ▸ fd.saturated }

variable {n p k : ℕ}

/-- **The marked label** ((D2)): the marked stable graph is identified with the marked core,
with the marks going to the marks. The marked twin of `CoreIdentification`. -/
structure MarkedCoreIdentification (core : Core n p) (mark : Fin k → Fin n)
    {target : CFGraph.{0}} {degree : ℕ} (data : GluingDatum target degree)
    (markSource : Fin k → data.SourceVertex) where
  /-- Marked vertices are core vertices. -/
  vertex : MarkedBranchVertex data (markSet markSource) ≃ Fin n
  /-- Marked rows are core slots. -/
  row : MarkedStablePath data (markSet markSource) ≃ Fin p
  /-- Every incidence multiplicity is matched. -/
  incidence : ∀ (branch : MarkedBranchVertex data (markSet markSource)) (slot : Fin p),
    markedIncidenceCount data (markSet markSource) branch.1 (row.symm slot) =
      coreIncidence core (vertex branch) slot
  /-- `ι(u_G) = u`. -/
  vertex_mark : ∀ j, vertex ⟨markSource j, Or.inr (mem_markSet markSource j)⟩ = mark j

/-- Over a marked cubic core, the marks of a marked label are distinct source vertices. -/
theorem MarkedCoreIdentification.markSource_injective {core : Core n p} {mark : Fin k → Fin n}
    {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
    {markSource : Fin k → data.SourceVertex}
    (ident : MarkedCoreIdentification core mark data markSource) (hc : IsMarkedCubic core mark) :
    Function.Injective markSource := by
  intro i j h
  apply hc.injective
  rw [← ident.vertex_mark i, ← ident.vertex_mark j]
  congr 1
  exact Subtype.ext h

/-! ## 3.  Marked frames -/

/-- **The frame of a marked member, without a condition at the marks**, over the marked core and
with dimension excess `excess`: a target tree, a gluing datum, the source vertices of the marks,
marked full-dimensionality and the marked label. -/
structure MarkedFrameBase (core : Core n p) (mark : Fin k → Fin n) (excess : ℤ)
    (degree : ℕ) where
  /-- The target tree. -/
  target : CFGraph.{0}
  /-- The gluing datum. -/
  data : GluingDatum target degree
  /-- The source vertices `u_G, v_G` of the marks. -/
  markSource : Fin k → data.SourceVertex
  /-- Marked full-dimensionality. -/
  fullDim : MarkedFullDim data (markSet markSource) (Fin p) excess
  /-- The marked label. -/
  ident : MarkedCoreIdentification core mark data markSource

namespace MarkedFrameBase

variable {core : Core n p} {mark : Fin k → Fin n} {excess : ℤ}

/-- The marked edge-length matrix `A_{φ;u,v}`. -/
noncomputable def matrix (κ : MarkedFrameBase core mark excess degree) :
    Matrix (Fin p) (Fin p) ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix κ.fullDim.labelling.presentation

theorem det_ne_zero (κ : MarkedFrameBase core mark excess degree) : κ.matrix.det ≠ 0 :=
  κ.fullDim.det_ne_zero

/-- The permutation reading a matrix row as a core slot. -/
def slot (κ : MarkedFrameBase core mark excess degree) : Fin p ≃ Fin p :=
  κ.fullDim.labelling.row.symm.trans κ.ident.row

/-- **The coordinates of a marked frame at the request `y`**: `z = A⁻¹ y`. -/
noncomputable def coordsAt (κ : MarkedFrameBase core mark excess degree) (y : Fin p → ℚ) :
    Fin p → ℚ :=
  κ.matrix⁻¹.mulVec fun row ↦ y (κ.slot row)

theorem mulVec_coordsAt (κ : MarkedFrameBase core mark excess degree) (y : Fin p → ℚ) :
    κ.matrix.mulVec (κ.coordsAt y) = fun row ↦ y (κ.slot row) := by
  rw [coordsAt, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr κ.det_ne_zero), Matrix.one_mulVec]

/-- **The coordinates are the unique solution** of `A z = y ∘ slot`. -/
theorem coordsAt_eq_of_mulVec (κ : MarkedFrameBase core mark excess degree) (y : Fin p → ℚ)
    (z : Fin p → ℚ) (h : κ.matrix.mulVec z = fun row ↦ y (κ.slot row)) : κ.coordsAt y = z := by
  rw [coordsAt, ← h, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr κ.det_ne_zero), Matrix.one_mulVec]

/-- **A marked member at `y`** is a marked frame open at `y` (`z > 0`). -/
def OpenAt (κ : MarkedFrameBase core mark excess degree) (y : Fin p → ℚ) : Prop :=
  ∀ col, 0 < κ.coordsAt y col

end MarkedFrameBase

/-- **A marked frame** over the marked core: a target
tree, a gluing datum, the source vertices of the marks, marked full-dimensionality, the marked
label, and ramification at every mark, `r_φ(u_G) ≥ 1` ((D4) with `a = 1`). -/
structure MarkedFrame (core : Core n p) (mark : Fin k → Fin n) (degree : ℕ) extends
    MarkedFrameBase core mark 0 degree where
  /-- (D4): every mark is ramified. -/
  ramified : ∀ j, 1 ≤ markRamification data (markSource j)

namespace MarkedFrame

variable {core : Core n p} {mark : Fin k → Fin n}

/-- `∏ⱼ r_φ(markⱼ)`. -/
def ramificationFactor (κ : MarkedFrame core mark degree) : ℤ :=
  ∏ j, markRamification κ.data (κ.markSource j)

theorem ramificationFactor_pos (κ : MarkedFrame core mark degree) : 0 < κ.ramificationFactor :=
  Finset.prod_pos fun j _ ↦ lt_of_lt_of_le zero_lt_one (κ.ramified j)

/-- **The signed marked multiplicity** (every mark of type `a = 1`):
`Mult(φ; marks) = (∏ⱼ r_φ(markⱼ)) · D_φ · det A_{φ;u,v} / 2^{l(T)}`. The last three factors are
Part II's `signedMult` applied verbatim to the marked presentation. -/
noncomputable def markedSignedMult (κ : MarkedFrame core mark degree) : ℚ :=
  (κ.ramificationFactor : ℚ) * Count.signedMult κ.fullDim.labelling.presentation

/-- **The marked multiplicity** `|Mult(φ; marks)|`. -/
noncomputable def markedAbsMult (κ : MarkedFrame core mark degree) : ℚ := |κ.markedSignedMult|

theorem markedSignedMult_ne_zero (κ : MarkedFrame core mark degree) :
    κ.markedSignedMult ≠ 0 := by
  have hDen : ((Count.denominatorProduct κ.fullDim.labelling.presentation : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Count.denominatorProduct_pos κ.fullDim.labelling.presentation).ne'
  refine mul_ne_zero (by exact_mod_cast κ.ramificationFactor_pos.ne') ?_
  exact mul_ne_zero (div_ne_zero hDen (by positivity)) κ.det_ne_zero

end MarkedFrame

/-! ## 4.  Isomorphism over the identity of the marked core -/

/-- **An isomorphism of marked frames over the identity of the marked core**:
an isomorphism of gluing data (`GeometricDatumIso`, per-vertex and per-edge sheet permutations
compatible along incidences) carrying marks to marks and inducing the identity on the marked
core, on vertices and on rows. The conditions are stated pointwise on the source, so that
stating them needs no induced dictionary of marked rows. -/
structure MarkedFrameBase.Iso {core : Core n p} {mark : Fin k → Fin n} {excess : ℤ}
    (first second : MarkedFrameBase core mark excess degree) where
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

namespace MarkedFrameBase.Iso

variable {core : Core n p} {mark : Fin k → Fin n} {excess : ℤ}
  {first second : MarkedFrameBase core mark excess degree}

/-- **Marks correspond**: `iso` carries the mark set of `first` onto that of `second`. -/
theorem mem_markSet_map (iso : Iso first second) (vertex : first.data.SourceVertex) :
    iso.datum.sourceVertexEquiv vertex ∈ markSet second.markSource ↔
      vertex ∈ markSet first.markSource := by
  simp only [markSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, iso.datum.sourceVertexEquiv.injective ((iso.mark j).trans hj)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, (iso.mark j).symm⟩

/-- **The induced dictionary of marked rows** (`markedStablePathEquiv`). -/
noncomputable def rowEquiv (iso : Iso first second) :
    MarkedStablePath first.data (markSet first.markSource) ≃
      MarkedStablePath second.data (markSet second.markSource) :=
  markedStablePathEquiv iso.datum first.fullDim.valid.1 iso.mem_markSet_map

/-- The dictionary of marked rows is over the identity of the core: `overCore_row`, descended
to marked rows. -/
theorem ident_row_rowEquiv (iso : Iso first second)
    (path : MarkedStablePath first.data (markSet first.markSource)) :
    second.ident.row (iso.rowEquiv path) = first.ident.row path := by
  induction path using Quot.ind with
  | mk edge => exact iso.overCore_row edge

/-- The matrix row of `first` matched with matrix row `r` of `second`. -/
noncomputable def rowPerm (iso : Iso first second) : Fin p ≃ Fin p :=
  second.fullDim.labelling.row.symm.trans (iso.rowEquiv.symm.trans first.fullDim.labelling.row)

/-- The column of `first` matched with column `c` of `second`, through the target relabelling. -/
noncomputable def columnPerm (iso : Iso first second) : Fin p ≃ Fin p :=
  second.fullDim.labelling.targetEdge.trans
    (iso.datum.targetEdge.symm.trans first.fullDim.labelling.targetEdge.symm)

/-- **The marked matrix of `second` is that of `first`, reindexed** (`markedMatrix_map`). -/
theorem matrix_eq_submatrix (iso : Iso first second) :
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
  rw [Matrix.submatrix_apply, MarkedFrameBase.matrix, MarkedFrameBase.matrix,
    MarkedLabelling.matrix_eq, MarkedLabelling.matrix_eq, h]
  simp [rowPerm, columnPerm]

/-- An isomorphism preserves Part II's `D_φ |det A_{φ;u,v}| / 2^{l(T)}`, by the reindexing
`matrix_eq_submatrix` and `leafCount_map` (`absMult_eq_of_submatrix`). -/
theorem absMult_eq (iso : Iso first second) :
    Count.absMult second.fullDim.labelling.presentation =
      Count.absMult first.fullDim.labelling.presentation :=
  absMult_eq_of_submatrix _ _ iso.rowPerm iso.columnPerm iso.matrix_eq_submatrix
    iso.datum.leafCount_map

/-- The request is read through matched slots. -/
theorem slot_rowPerm (iso : Iso first second) (row : Fin p) :
    first.slot (iso.rowPerm row) = second.slot row := by
  simp only [MarkedFrameBase.slot, rowPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [← iso.ident_row_rowEquiv, Equiv.apply_symm_apply]

/-- **An isomorphism permutes the coordinates**: the marked twin of
`GeometricMemberIso.coords_column`. The matrix of `second` is that of `first` reindexed by
`rowPerm` and `columnPerm` (`matrix_eq_submatrix`), and the slots are matched by `rowPerm`
(`slot_rowPerm`), so `z ∘ columnPerm` solves the equations of `second`
(`coordsAt_eq_of_mulVec`). -/
theorem exists_column (iso : Iso first second) :
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

/-- An isomorphism preserves openness, from `exists_column`. -/
theorem openAt_iff (iso : Iso first second) (y : Fin p → ℚ) :
    first.OpenAt y ↔ second.OpenAt y := by
  obtain ⟨σ, hσ⟩ := iso.exists_column
  constructor
  · intro h col
    rw [← σ.apply_symm_apply col, hσ]
    exact h _
  · intro h col
    rw [← hσ]
    exact h _

end MarkedFrameBase.Iso

/-- **An isomorphism of marked frames over the identity of the marked core**: an isomorphism of
the underlying `MarkedFrameBase`. -/
abbrev MarkedFrameIso {core : Core n p} {mark : Fin k → Fin n}
    (first second : MarkedFrame core mark degree) :=
  MarkedFrameBase.Iso first.toMarkedFrameBase second.toMarkedFrameBase

namespace MarkedFrameIso

variable {core : Core n p} {mark : Fin k → Fin n} {first second : MarkedFrame core mark degree}

/-- `r_φ` at corresponding source vertices agrees (`localRamification_map`). -/
theorem markRamification_map (iso : MarkedFrameIso first second)
    (vertex : first.data.SourceVertex) :
    markRamification second.data (iso.datum.sourceVertexEquiv vertex) =
      markRamification first.data vertex :=
  localRamification_map iso.datum vertex.1.1 ⟨vertex.1.2, vertex.2⟩
    (iso.datum.sourceVertexEquiv vertex).2

/-- **An isomorphism preserves the marked multiplicity.** The ramification factor agrees mark by
mark (`markRamification_map` and `mark`); `D_φ |det A_{φ;u,v}| / 2^{l(T)}` agrees by
`MarkedFrameBase.Iso.absMult_eq`. -/
theorem markedAbsMult_eq (iso : MarkedFrameIso first second) :
    first.markedAbsMult = second.markedAbsMult := by
  have hFactor : second.ramificationFactor = first.ramificationFactor := by
    unfold MarkedFrame.ramificationFactor
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← iso.mark j, iso.markRamification_map]
  unfold MarkedFrame.markedAbsMult MarkedFrame.markedSignedMult
  rw [abs_mul, abs_mul, hFactor]
  exact congrArg _ iso.absMult_eq.symm

end MarkedFrameIso

/-! ## 5.  The marked fibre and the marked count -/

/-- **Marked frames up to isomorphism over the marked core**, the request-free model of the
marked fibre. A `Quot` by the isomorphism relation: no equivalence-relation proof is needed to
form it, and lifting only needs invariance under one isomorphism. -/
def MarkedFrameClass (core : Core n p) (mark : Fin k → Fin n) (degree : ℕ) : Type 1 :=
  Quot fun first second : MarkedFrame core mark degree ↦ Nonempty (MarkedFrameIso first second)

namespace MarkedFrameClass

variable {core : Core n p} {mark : Fin k → Fin n}

/-- The class of a marked frame. -/
def mk (κ : MarkedFrame core mark degree) : MarkedFrameClass core mark degree := Quot.mk _ κ

theorem mk_surjective : Function.Surjective (mk (core := core) (mark := mark) (degree := degree)) :=
  Quot.mk_surjective

theorem mk_eq_mk_of_iso {κ κ' : MarkedFrame core mark degree} (h : Nonempty (MarkedFrameIso κ κ')) :
    mk κ = mk κ' :=
  Quot.sound h

/-- Openness of a class at a request. -/
def OpenAt (x : MarkedFrameClass core mark degree) (y : Fin p → ℚ) : Prop :=
  Quot.lift (fun κ : MarkedFrame core mark degree ↦ κ.OpenAt y)
    (fun _ _ h ↦ h.elim fun iso ↦ propext (iso.openAt_iff y)) x

/-- The marked multiplicity of a class. -/
noncomputable def markedAbsMult (x : MarkedFrameClass core mark degree) : ℚ :=
  Quot.lift MarkedFrame.markedAbsMult (fun _ _ h ↦ h.elim fun iso ↦ iso.markedAbsMult_eq) x

@[simp] theorem openAt_mk (κ : MarkedFrame core mark degree) (y : Fin p → ℚ) :
    (mk κ).OpenAt y ↔ κ.OpenAt y := Iff.rfl

@[simp] theorem markedAbsMult_mk (κ : MarkedFrame core mark degree) :
    (mk κ).markedAbsMult = κ.markedAbsMult := rfl

end MarkedFrameClass

/-- **The marked fibre** `M(Γ, marks)` at the request `y`: the classes of
marked frames open at `y`, i.e. the marked members with `z > 0`. -/
def MarkedFibre (core : Core n p) (mark : Fin k → Fin n) (y : Fin p → ℚ) (degree : ℕ) : Type 1 :=
  {x : MarkedFrameClass core mark degree // x.OpenAt y}

/-- **The marked count**: `Σ_{ψ ∈ M(Γ, marks)} |Mult(ψ; marks)|`, a rational
number a priori (integrality is a corollary of the lollipop lemma). -/
noncomputable def markedCount (core : Core n p) (mark : Fin k → Fin n) (y : Fin p → ℚ)
    (degree : ℕ) : ℚ :=
  ∑ᶠ x : MarkedFibre core mark y degree, x.1.markedAbsMult

end DraismaVargas.Count.MarkedCount
