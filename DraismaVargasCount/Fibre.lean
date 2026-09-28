import DraismaVargasCount.Multiplicity
import DraismaVargasCount.Transport
import DraismaVargas.LocalCases.StableGraphIncidence
import Utilities.Subdivision.SubdivisionGraph

/-!
# The labelled fibre over a metric graph, its quotient, and the odd count

**Two quotients.**  The member and core structures defined here are shared by the whole
library.  The quotient `Fibre` and the counts `oddCount`, `openOddCount` of this file use
`MemberIso`, which preserves the stored endpoint order of the target edges; they serve the
finite normal-form cover and regression checks.  The count of the genus-six assembly is
taken on the geometric quotient instead (`GeometricFibre`, `GeometricCount`), whose segment
and star consumers are `GeometricSegmentWalls` and `GeometricStar`.  Cardinality and parity
of the strict quotient here must not be substituted for the geometric counts.  The rest of
this docstring describes the strict interface.

**Source.**  Vargas, Part II (arXiv:2609.09109), the space of full-rank tropical morphisms
`TM(d,g)` (`definition-TMSpace`) and the count of the section on invariance of the count
(`sec-deformation-invariance`).

## Two design decisions

* The fibre is **labelled**: the identification of the stable graph of the
  gluing datum with the *requested core* is a field of a member
  (`FibreMember.ident`), not something quotiented away.  This is what removes
  `lemma-count-realizations` and `Aut(H)`-triviality from the route, and it is
  what `OuterWalk.TrackedState` already does.
* The quotient is **only** by isomorphisms of the datum **over the identity of
  the core** (`MemberIso`): the induced dictionary of the stable graph has to
  carry `ident` to `ident` on the nose.  Nothing is quotiented by
  `Aut(spec.core)`.

## What is proved

* `coreIncidence`, `CoreIdentification` -- the labelling of the stable graph by
  the request: branch vertices to core vertices, stable paths to core slots,
  with every incidence multiplicity matched (a stable loop counts twice at its
  branch, exactly as `coreIncidence` counts a core loop twice).
* `FibreMember core y degree` -- target tree, gluing datum, Part I's
  `FullDimensionalSourcePresentation` over the coordinate type `Fin p`, the
  core identification, the coordinate vector `z`, and the realization equation
  `A_φ z = y ∘ ident`.  `FibreMember.Open` (`0 < z`) and `FibreMember.Closed`
  (`0 ≤ z`).
* `coords_injective`, `coords_unique` -- `z` is *determined* by the datum and
  the request: the length matrix of a full-dimensional presentation is
  nonsingular, so a member carries no coordinate freedom.
* `MemberIso`, `IsoOverCore`, `memberSetoid`, `Fibre` -- an isomorphism of the
  two gluing data (`Count.Transport.DatumIso`: a relabelling of the target
  compatible with both endpoint maps, together with per-vertex and per-edge
  sheet permutations carrying one partition assignment to the other *and*
  compatible at both endpoints of every occurrence) which is *over the identity
  of the core*, its `refl`, `symm`, `trans`, and the quotient.  The dictionary
  of the stable graph is not a field: `MemberIso.stableVertex`,
  `MemberIso.stableRow` and `MemberIso.incidence` are constructed from the
  isomorphism of data, and `Transport.DatumIso.branchVertexEquiv_refl` and its
  five companions are the functoriality those three need.
* `Open`/`Closed` are invariant (`MemberIso.open_iff`, `closed_iff`), because
  an isomorphism matches the coordinate vectors along the induced permutation
  `MemberIso.column` of the target edges.
* `IsOddClass`, `oddCount` -- the number of classes of odd multiplicity, with
  oddness phrased existentially, `∃ k : ℕ, Odd k ∧ absMult = k`
  (`FibreMember.HasOddMult`).  **`oddCount` does not depend on the request** --
  see the note at its own docstring -- so `openOddCount`, the count restricted
  to the *open* classes, is the count that matters.
* `openOddCount`, `openOddCount_pos_of_open_hasOddMult` -- the count over the
  fibre *proper*: classes that are open **and** of odd multiplicity.
  `Count.SegmentWalls.openOddCount_eq_of_no_wall` supplies the constancy
  between wall parameters.
* `Finite (GluingDatum target degree)` -- over a *fixed* target, gluing data are
  finite (`gluingDatum_ext` plus finiteness of `SheetPartition`); and
  `finite_fibre_of_meets`, the reduction of `Fintype (Fibre …)` to a finite
  family of members meeting every class.

## What is not proved here

* **Integrality of the multiplicity** is not proved *in this file*, so oddness is phrased
  existentially rather than through a natural-number multiplicity: everything here says
  `∃ k : ℕ, Odd k ∧ absMult φ = k`.  Integrality is proved, unconditionally, in
  `Count/Integrality.lean`: `Count.isIntegralMultiplicity` holds for
  every full-dimensional presentation, and the oddness bridge
  `Count.hasOddMult_iff_odd_oddMult` proves `HasOddMult` equivalent to
  `Odd member.oddMult` (with `oddMult := fdAbsMultNat member.fullDim` and
  `absMult = oddMult` by `FibreMember.absMult_eq_oddMult`), so every statement
  below can be restated through `oddMult` with no change of content.
  The definition stays existential here only because `Count.Integrality`
  imports this file, not the other way round.
* **`absMult` is not shown to descend in this file.**  `MemberIso` deliberately carries no
  length-matrix-correspondence field: supplying one would assume the descent.  The descent
  is the named proposition `AbsMultDescends`, an explicit argument of `isOddClass_cls_iff`
  and of `Fibre.absMult`, and it is never assumed by a definition here.  It is
  **proved**, with no hypothesis, one file later:
  `Count.TransportMultiplicity.absMultDescends` derives it from the `datum`
  field, and `isOddClass_cls_iff'` and `Fibre.absMult'` are the hypothesis-free
  forms of the two statements below.
* **`Fintype (Fibre …)` is supplied elsewhere, unconditionally.**  A `FibreMember` carries
  its own target `CFGraph.{0}`, so the type of members is not small; the needed step is a
  normal form for the target together with the transport of a gluing datum along it
  (`Count.TargetNormalForm`, `Count.TransportMultiplicity`).
  `Count.FibreNormalForm.instFiniteFibre` gives `Finite (Fibre …)` with no
  hypothesis on the core, the request or the degree, and no descent statement
  assumed; `Count.FibreNormalForm.instFintypeFibre` is the same fact as a
  `Fintype`, built from `Finite` by `Fintype.ofFinite`, hence **noncomputable
  and enumerating nothing** -- `Finite` is the natural form, and the one in which Part II
  states the finiteness of the fibre (at the end of the subsection on symmetries of
  `TM(d,g)`), and the `Fintype` exists only so that
  `oddCount_eq_card_filter` below, which is stated with a `Fintype` instance
  argument, can be applied.  What this file delivers directly is only the
  fixed-target half (`GluingDatum.instFinite`) and the reduction
  `finite_fibre_of_meets`; all cardinality facts below go through explicit
  maps, never through decidable counting.
* Nothing here claims the fibre is nonempty in general.  Non-vacuity is
  `DraismaVargas.Count.FibreCaterpillar`, which inhabits `FibreMember` over the
  caterpillar-of-loops core for every even genus and every positive request.
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ}

/-! ## 1.  The request, and the identification of the stable graph with it -/

/-- How often the core slot `slot` meets the core vertex `vertex`.  A core loop
meets its vertex twice, which is exactly how `incidenceCount` counts a stable
loop at its branch vertex. -/
def coreIncidence (core : Core n p) (vertex : Fin n) (slot : Fin p) : ℕ :=
  (if core.tail slot = vertex then 1 else 0) +
    (if core.head slot = vertex then 1 else 0)

theorem coreIncidence_le_two (core : Core n p) (vertex : Fin n) (slot : Fin p) :
    coreIncidence core vertex slot ≤ 2 := by
  unfold coreIncidence; split_ifs <;> omega

/-- **The label.**  An identification of the stable graph of `data` with the
requested core: branch vertices with core vertices, stable paths with core
slots, matching every incidence multiplicity.  This is the datum the labelled
fibre keeps and never quotients away. -/
structure CoreIdentification (core : Core n p) {target : CFGraph.{0}} {degree : ℕ}
    (data : GluingDatum target degree) where
  /-- Branch vertices of the stable graph are the core's vertices. -/
  vertex : BranchVertex data ≃ Fin n
  /-- Stable paths are the core's edge slots. -/
  row : StablePath data ≃ Fin p
  /-- Every incidence multiplicity is matched. -/
  incidence : ∀ (branch : BranchVertex data) (slot : Fin p),
    incidenceCount data branch.1 (row.symm slot) = coreIncidence core (vertex branch) slot

/-! ## 2.  Members of the fibre -/

/-- **A labelled member of the fibre over the metric graph `(core, y)`.**
A target tree, a gluing datum on it, a full-dimensional
presentation whose coordinate type is the request's slot type, the
identification of the stable graph with the request, a coordinate vector `z` on
the target edges, and the realization equation saying that the length matrix
carries `z` to the requested lengths. -/
structure FibreMember (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) where
  /-- The target tree. -/
  target : CFGraph.{0}
  /-- The gluing datum over it. -/
  data : GluingDatum target degree
  /-- Its full-dimensional presentation, on the request's slot type. -/
  fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p)
  /-- The identification of the stable graph with the requested core. -/
  ident : CoreIdentification core data
  /-- The coordinate vector `z`, indexed through `fullDim.labelling.targetEdge`. -/
  coords : Fin p → ℚ
  /-- `A_φ z = y ∘ ident`. -/
  realizes : (GluingDatum.LengthMatrixPresentation.matrix
      fullDim.labelling.presentation).mulVec coords =
    fun row ↦ y (ident.row (fullDim.labelling.row.symm row))

namespace FibreMember

variable {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}

/-- The length matrix of a member. -/
noncomputable def matrix (member : FibreMember core y degree) :
    Matrix (Fin p) (Fin p) ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix member.fullDim.labelling.presentation

theorem det_matrix_ne_zero (member : FibreMember core y degree) :
    member.matrix.det ≠ 0 := member.fullDim.det_ne_zero

/-- The fibre proper: all coordinates positive. -/
def Open (member : FibreMember core y degree) : Prop := ∀ slot, 0 < member.coords slot

/-- The closed cone: all coordinates nonnegative.  This is what
`ClosedBoundaryMember` delivers at every non-negative request. -/
def Closed (member : FibreMember core y degree) : Prop := ∀ slot, 0 ≤ member.coords slot

theorem Closed.of_open {member : FibreMember core y degree} (hOpen : member.Open) :
    member.Closed := fun slot ↦ (hOpen slot).le

/-- The multiplicity of a member, in the sense of `Count.Multiplicity`. -/
noncomputable def absMult (member : FibreMember core y degree) : ℚ :=
  fdAbsMult member.fullDim

theorem absMult_nonneg (member : FibreMember core y degree) : 0 ≤ member.absMult :=
  abs_nonneg _

theorem absMult_ne_zero (member : FibreMember core y degree) : member.absMult ≠ 0 :=
  abs_ne_zero.mpr (fdSignedMult_ne_zero member.fullDim)

/-- **Oddness, phrased existentially.**  Integrality of the multiplicity is
proved downstream of this file (`Count.Integrality` imports it), so this says
"the multiplicity is an odd natural number" without producing that natural number
from a proof of integrality.  `Count.hasOddMult_iff_odd_oddMult` in
`Count/Integrality.lean` shows this is
exactly `Odd member.oddMult`, where `oddMult := fdAbsMultNat member.fullDim`
and `absMult = oddMult` (`FibreMember.absMult_eq_oddMult`). -/
def HasOddMult (member : FibreMember core y degree) : Prop :=
  ∃ k : ℕ, Odd k ∧ member.absMult = k

/-- A member of multiplicity one has odd multiplicity. -/
theorem hasOddMult_of_absMult_eq_one {member : FibreMember core y degree}
    (h : member.absMult = 1) : member.HasOddMult :=
  ⟨1, odd_one, by rw [h]; norm_num⟩

/-! ### The coordinates are determined -/

theorem coords_injective (member : FibreMember core y degree)
    {first second : Fin p → ℚ}
    (h : member.matrix.mulVec first = member.matrix.mulVec second) : first = second := by
  have hUnit : IsUnit member.matrix.det := isUnit_iff_ne_zero.mpr member.det_matrix_ne_zero
  have hInv : IsUnit member.matrix := (Matrix.isUnit_iff_isUnit_det _).mpr hUnit
  obtain ⟨inverse, hinv⟩ := hInv.exists_left_inv
  have hStep := congrArg (fun vector ↦ inverse.mulVec vector) h
  simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at hStep
  exact hStep

/-- A member carries no coordinate freedom: `z` is the unique solution of the
realization equation for its own datum. -/
theorem coords_unique (member : FibreMember core y degree) (candidate : Fin p → ℚ)
    (h : member.matrix.mulVec candidate =
      fun row ↦ y (member.ident.row (member.fullDim.labelling.row.symm row))) :
    candidate = member.coords :=
  member.coords_injective (h.trans member.realizes.symm)

end FibreMember

/-! ## 3.  Isomorphism of data over the identity of the core -/

open DraismaVargas.Count.Transport (DatumIso)

/-- **An isomorphism of two members over the identity of the core.**

The first field is an isomorphism of the two gluing data
(`Count.Transport.DatumIso`): a relabelling of the target (vertices and edge
occurrences, respecting both stored endpoints) together with per-vertex and
per-edge sheet permutations that carry one partition assignment to the other
**and are compatible with each other at both endpoints of every occurrence**.
That compatibility is not a decoration.  Carrying one partition assignment to
the other does *not* by itself make the sheet permutations a map of the quotient
sources: with a discrete occurrence partition, an endpoint vertex partition of
two blocks of size two, the identity occurrence permutation and a vertex
permutation moving a sheet out of its block, both partition conditions hold
while the induced source-vertex and source-edge maps disagree at that endpoint.
It is exactly the condition of `GluingDatum.SheetRelabeling`.

The remaining three fields say that the isomorphism is *over the identity of the
core*: the dictionary of the stable graph that `datum` induces
(`Transport.DatumIso.branchVertexEquiv`, `Transport.DatumIso.stablePathEquiv`)
carries each member's `ident` to the other's on the nose, and the coordinate
vectors agree along the induced permutation `column` of the request's slots.

The stable dictionary is **not** carried as data any more: `stableVertex`,
`stableRow` and `incidence` below are *constructed* from `datum`.  The
coordinate field is not an extra restriction in substance -- `coords_unique`
says `z` is determined by the datum and the request -- but it is what makes this
a quotient of members rather than of bare data.

Deliberately **not** a field: any correspondence of the two length matrices.
That is the descent of `absMult`, proved unconditionally in
`Count.TransportMultiplicity` (`absMultDescends`) from `datum` alone. -/
structure MemberIso {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
    (first second : FibreMember core y degree) where
  /-- The isomorphism of the two gluing data, compatibility included. -/
  datum : DatumIso first.data second.data
  /-- Over the identity of the core, on vertices. -/
  overCore_vertex : ∀ branch : BranchVertex first.data,
    second.ident.vertex (datum.branchVertexEquiv first.fullDim.valid.1 branch) =
      first.ident.vertex branch
  /-- Over the identity of the core, on slots. -/
  overCore_row : ∀ path : StablePath first.data,
    second.ident.row (datum.stablePathEquiv first.fullDim.valid.1 path) =
      first.ident.row path
  /-- The coordinate vectors agree along the induced permutation of the
  columns. -/
  coords : ∀ column : Fin p,
    second.coords (second.fullDim.labelling.targetEdge.symm
        (datum.targetEdge (first.fullDim.labelling.targetEdge column))) =
      first.coords column

namespace MemberIso

variable {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
variable {first second third : FibreMember core y degree}

/-- **The induced dictionary on branch vertices**, constructed from the
isomorphism of gluing data rather than supplied. -/
noncomputable def stableVertex (iso : MemberIso first second) :
    BranchVertex first.data ≃ BranchVertex second.data :=
  iso.datum.branchVertexEquiv first.fullDim.valid.1

/-- **The induced dictionary on stable paths**, likewise constructed. -/
noncomputable def stableRow (iso : MemberIso first second) :
    StablePath first.data ≃ StablePath second.data :=
  iso.datum.stablePathEquiv first.fullDim.valid.1

/-- **Every incidence multiplicity is preserved**, counted with flags, so a
stable loop keeps its two incidences at one branch vertex. -/
theorem incidence (iso : MemberIso first second) (branch : BranchVertex first.data)
    (path : StablePath first.data) :
    incidenceCount first.data branch.1 path =
      incidenceCount second.data (iso.stableVertex branch).1 (iso.stableRow path) :=
  iso.datum.incidenceCount_map first.fullDim.valid.1 branch.1 path

/-- The permutation of the request's slots induced on the *columns* -- the
target edge occurrences -- by an isomorphism. -/
def column (iso : MemberIso first second) : Fin p ≃ Fin p :=
  first.fullDim.labelling.targetEdge.trans
    (iso.datum.targetEdge.trans second.fullDim.labelling.targetEdge.symm)

@[simp] theorem column_apply (iso : MemberIso first second) (slot : Fin p) :
    iso.column slot = second.fullDim.labelling.targetEdge.symm
      (iso.datum.targetEdge (first.fullDim.labelling.targetEdge slot)) := rfl

theorem coords_column (iso : MemberIso first second) (slot : Fin p) :
    second.coords (iso.column slot) = first.coords slot := iso.coords slot

/-- The identity isomorphism. -/
def refl (member : FibreMember core y degree) : MemberIso member member where
  datum := DatumIso.refl member.data
  overCore_vertex branch := by
    rw [Transport.DatumIso.branchVertexEquiv_refl, Equiv.refl_apply]
  overCore_row path := by
    rw [Transport.DatumIso.stablePathEquiv_refl, Equiv.refl_apply]
  coords column := by
    show member.coords (member.fullDim.labelling.targetEdge.symm
      (member.fullDim.labelling.targetEdge column)) = member.coords column
    simp

/-- Relabelling by the inverse isomorphism of data inverts an isomorphism. -/
def symm (iso : MemberIso first second) : MemberIso second first where
  datum := iso.datum.symm
  overCore_vertex branch := by
    rw [Transport.DatumIso.branchVertexEquiv_symm iso.datum first.fullDim.valid.1
      second.fullDim.valid.1]
    have hBack := iso.overCore_vertex
      ((iso.datum.branchVertexEquiv first.fullDim.valid.1).symm branch)
    rw [Equiv.apply_symm_apply] at hBack
    exact hBack.symm
  overCore_row path := by
    rw [Transport.DatumIso.stablePathEquiv_symm iso.datum first.fullDim.valid.1
      second.fullDim.valid.1]
    have hBack := iso.overCore_row
      ((iso.datum.stablePathEquiv first.fullDim.valid.1).symm path)
    rw [Equiv.apply_symm_apply] at hBack
    exact hBack.symm
  coords slot := by
    show first.coords (first.fullDim.labelling.targetEdge.symm
        (iso.datum.targetEdge.symm (second.fullDim.labelling.targetEdge slot))) =
      second.coords slot
    have hForward := iso.coords (iso.column.symm slot)
    rw [show iso.column.symm slot = first.fullDim.labelling.targetEdge.symm
        (iso.datum.targetEdge.symm (second.fullDim.labelling.targetEdge slot)) from rfl]
      at hForward
    simpa using hForward.symm

/-- Isomorphisms compose. -/
def trans (left : MemberIso first second) (right : MemberIso second third) :
    MemberIso first third where
  datum := left.datum.trans right.datum
  overCore_vertex branch := by
    rw [Transport.DatumIso.branchVertexEquiv_trans left.datum right.datum
      first.fullDim.valid.1 second.fullDim.valid.1, Equiv.trans_apply,
      right.overCore_vertex, left.overCore_vertex]
  overCore_row path := by
    rw [Transport.DatumIso.stablePathEquiv_trans left.datum right.datum
      first.fullDim.valid.1 second.fullDim.valid.1, Equiv.trans_apply,
      right.overCore_row, left.overCore_row]
  coords slot := by
    have hRight := right.coords (left.column slot)
    have hLeft := left.coords slot
    rw [column_apply, Equiv.apply_symm_apply] at hRight
    exact hRight.trans hLeft

/-- `Open` is invariant. -/
theorem open_iff (iso : MemberIso first second) : first.Open ↔ second.Open := by
  constructor
  · intro hOpen slot
    have := iso.coords_column (iso.column.symm slot)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact hOpen _
  · intro hOpen slot
    rw [← iso.coords_column slot]
    exact hOpen _

/-- `Closed` is invariant. -/
theorem closed_iff (iso : MemberIso first second) : first.Closed ↔ second.Closed := by
  constructor
  · intro hClosed slot
    have := iso.coords_column (iso.column.symm slot)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact hClosed _
  · intro hClosed slot
    rw [← iso.coords_column slot]
    exact hClosed _

end MemberIso

/-! ## 4.  The quotient -/

variable {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}

/-- Two members are identified exactly when their data are isomorphic over the
identity of the core. -/
def IsoOverCore (first second : FibreMember core y degree) : Prop :=
  Nonempty (MemberIso first second)

theorem isoOverCore_refl (member : FibreMember core y degree) :
    IsoOverCore member member := ⟨MemberIso.refl member⟩

theorem IsoOverCore.symm {first second : FibreMember core y degree}
    (h : IsoOverCore first second) : IsoOverCore second first :=
  h.elim fun iso ↦ ⟨iso.symm⟩

theorem IsoOverCore.trans {first second third : FibreMember core y degree}
    (left : IsoOverCore first second) (right : IsoOverCore second third) :
    IsoOverCore first third :=
  left.elim fun l ↦ right.elim fun r ↦ ⟨l.trans r⟩

/-- The setoid of the labelled fibre. -/
def memberSetoid (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Setoid (FibreMember core y degree) where
  r := IsoOverCore
  iseqv := ⟨isoOverCore_refl, IsoOverCore.symm, IsoOverCore.trans⟩

/-- **The labelled fibre over the metric graph `(core, y)`**: members modulo
isomorphism of the datum over the identity of the core. -/
def Fibre (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Type 1 :=
  Quotient (memberSetoid core y degree)

/-- The class of a member. -/
def FibreMember.cls (member : FibreMember core y degree) : Fibre core y degree :=
  Quotient.mk (memberSetoid core y degree) member

theorem FibreMember.cls_eq_cls_iff {first second : FibreMember core y degree} :
    first.cls = second.cls ↔ IsoOverCore first second :=
  Quotient.eq (r := memberSetoid core y degree)

theorem FibreMember.cls_surjective :
    Function.Surjective (FibreMember.cls (core := core) (y := y) (degree := degree)) :=
  Quotient.mk_surjective

/-- `Open` descends to the fibre. -/
def Fibre.Open (cls : Fibre core y degree) : Prop :=
  Quotient.liftOn cls FibreMember.Open fun _ _ h ↦
    h.elim fun iso ↦ propext iso.open_iff

/-- `Closed` descends to the fibre. -/
def Fibre.Closed (cls : Fibre core y degree) : Prop :=
  Quotient.liftOn cls FibreMember.Closed fun _ _ h ↦
    h.elim fun iso ↦ propext iso.closed_iff

@[simp] theorem Fibre.open_cls (member : FibreMember core y degree) :
    Fibre.Open member.cls ↔ member.Open := Iff.rfl

@[simp] theorem Fibre.closed_cls (member : FibreMember core y degree) :
    Fibre.Closed member.cls ↔ member.Closed := Iff.rfl

/-! ## 5.  Finiteness: what is assembled, and what is reduced -/

/-- Sheet partitions of a fixed degree are finite: a partition is its
idempotent representative map. -/
instance SheetPartition.instFinite (degree : ℕ) : Finite (SheetPartition degree) :=
  Finite.of_injective (fun partition ↦ partition.repr)
    fun first second hEq ↦ SheetPartition.ext_repr first second hEq

/-- Over a **fixed** target, gluing data of a fixed degree are finite: a datum
is two partition assignments (`gluingDatum_ext`), and `SheetPartition degree` is
finite. -/
instance GluingDatum.instFinite (target : CFGraph.{0}) (degree : ℕ) :
    Finite (GluingDatum target degree) := by
  classical
  have hInjective : Function.Injective
      (fun data : GluingDatum target degree ↦
        (data.vertexPartition, data.edgePartition)) := by
    intro first second hEq
    exact gluingDatum_ext (congrArg Prod.fst hEq) (congrArg Prod.snd hEq)
  exact Finite.of_injective _ hInjective

/-- **The reduction of the `Fintype`.**  A finite family of members meeting
every isomorphism class makes the fibre finite.  This is used with such a
family supplied by the normal form for the target tree, `Count.TargetNormalForm`
(every connected genus-zero `CFGraph` with `p` edge occurrences is isomorphic,
**with an orientation bit per tree edge**, to a `TargetNormalForm.orientedTree`
-- *not* to a bare `TreeFamily.rootedTree`; `TargetNormalForm.inPath` is a
connected genus-zero graph with no normal form of all-`false` orientation
bits, so the bit is not a decoration) together with the transport of a gluing
datum along a target isomorphism, `TargetNormalForm.NormalForm.datumIso`.
`Count.FibreNormalForm.instFiniteFibre` assembles both into the unconditional
`Finite (Fibre …)` this lemma only reduces to. -/
theorem finite_fibre_of_meets {index : Type} [Finite index]
    (family : index → FibreMember core y degree)
    (hMeets : ∀ member : FibreMember core y degree,
      ∃ label, IsoOverCore (family label) member) :
    Finite (Fibre core y degree) := by
  refine Finite.of_surjective (fun label ↦ (family label).cls) ?_
  intro cls
  obtain ⟨member, rfl⟩ := FibreMember.cls_surjective cls
  obtain ⟨label, hLabel⟩ := hMeets member
  exact ⟨label, FibreMember.cls_eq_cls_iff.mpr hLabel⟩

/-! ## 6.  The odd count -/

/-- **The descent of `absMult`, as an explicit hypothesis.**  `absMult` is invariant
under isomorphism of gluing data over the identity of the core, hence descends
to the fibre.  It is *not* proved here, and no definition below assumes it; it is
proved in `Count.TransportMultiplicity` (`absMultDescends`). -/
def AbsMultDescends (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ first second : FibreMember core y degree, IsoOverCore first second →
    first.absMult = second.absMult

/-- A class of odd multiplicity: some representative has odd multiplicity.
Stated through representatives so that the *definition* needs no descent. -/
def IsOddClass (cls : Fibre core y degree) : Prop :=
  ∃ member : FibreMember core y degree, member.cls = cls ∧ member.HasOddMult

theorem isOddClass_cls_of_hasOddMult {member : FibreMember core y degree}
    (h : member.HasOddMult) : IsOddClass member.cls := ⟨member, rfl, h⟩

/-- **Well definedness on the quotient, under `AbsMultDescends`.**  Once `absMult`
descends, a class is odd exactly when *every* representative is. -/
theorem isOddClass_cls_iff (hDescends : AbsMultDescends core y degree)
    (member : FibreMember core y degree) :
    IsOddClass member.cls ↔ member.HasOddMult := by
  constructor
  · rintro ⟨witness, hClass, k, hOdd, hMult⟩
    refine ⟨k, hOdd, ?_⟩
    rw [← hMult]
    exact (hDescends witness member
      (FibreMember.cls_eq_cls_iff.mp hClass)).symm ▸ rfl
  · exact isOddClass_cls_of_hasOddMult

/-- Under `AbsMultDescends`, the multiplicity itself descends to the fibre. -/
noncomputable def Fibre.absMult (hDescends : AbsMultDescends core y degree)
    (cls : Fibre core y degree) : ℚ :=
  Quotient.liftOn cls FibreMember.absMult fun first second h ↦ hDescends first second h

@[simp] theorem Fibre.absMult_cls (hDescends : AbsMultDescends core y degree)
    (member : FibreMember core y degree) :
    Fibre.absMult hDescends member.cls = member.absMult := rfl

/-- **`oddCount`: the number of classes of odd multiplicity.**
`Nat.card`, so that the definition is unconditional; with `Finite (Fibre …)` it
is the honest cardinality (`oddCount_pos_of_hasOddMult`).

**This does not depend on the request `y` at all**
(`Count.SegmentWalls.oddCount_eq_oddCount`).  It counts *every* class of odd
multiplicity with no positivity condition, and both the classes and their
multiplicities are functions of the frame alone (target, datum,
full-dimensionality receipt, core identification), never of `y`.  So `oddCount`
is *not* Part II's count; the count the genus-six route needs runs over the
**open** classes only -- see `openOddCount` below. -/
noncomputable def oddCount (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : ℕ :=
  Nat.card {cls : Fibre core y degree // IsOddClass cls}

/-- One odd member makes the count positive, as soon as the fibre is finite. -/
theorem oddCount_pos_of_hasOddMult [Finite (Fibre core y degree)]
    {member : FibreMember core y degree} (h : member.HasOddMult) :
    0 < oddCount core y degree := by
  have : Nonempty {cls : Fibre core y degree // IsOddClass cls} :=
    ⟨⟨member.cls, isOddClass_cls_of_hasOddMult h⟩⟩
  exact Nat.card_pos

/-- The count as a cardinality, once the fibre is a `Fintype`: the
cardinality of the finset of odd classes.  Proved through
`Fintype.card_subtype`, an explicit bijection, not by evaluating a decision
procedure. -/
theorem oddCount_eq_card_filter [Fintype (Fibre core y degree)]
    [DecidablePred (IsOddClass (core := core) (y := y) (degree := degree))] :
    oddCount core y degree =
      (Finset.univ.filter
        (IsOddClass (core := core) (y := y) (degree := degree))).card := by
  rw [oddCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Conversely a positive count produces an odd member, with no finiteness
hypothesis at all. -/
theorem exists_hasOddMult_of_oddCount_pos (h : 0 < oddCount core y degree) :
    ∃ member : FibreMember core y degree, member.HasOddMult := by
  have hNonempty : Nonempty {cls : Fibre core y degree // IsOddClass cls} := by
    by_contra hEmpty
    rw [not_nonempty_iff] at hEmpty
    rw [oddCount, Nat.card_of_isEmpty] at h
    exact Nat.lt_irrefl 0 h
  obtain ⟨cls, member, _, hOdd⟩ := hNonempty
  exact ⟨member, hOdd⟩

/-- **The count over the fibre *proper*: classes that are open *and* of odd
multiplicity.**  This, not `oddCount`, is the analogue of Part II's count (read mod 2) on
this quotient; the genus-six assembly counts on `GeometricFibre` instead
(`GeometricFibre.openOddCount`). -/
noncomputable def openOddCount (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : ℕ :=
  Nat.card {cls : Fibre core y degree // cls.Open ∧ IsOddClass cls}

/-- One open member of odd multiplicity makes the open count positive, as soon
as the fibre is finite. -/
theorem openOddCount_pos_of_open_hasOddMult [Finite (Fibre core y degree)]
    {member : FibreMember core y degree} (hOpen : member.Open)
    (hOdd : member.HasOddMult) : 0 < openOddCount core y degree := by
  have hne : Nonempty {cls : Fibre core y degree // cls.Open ∧ IsOddClass cls} :=
    ⟨⟨member.cls, hOpen, isOddClass_cls_of_hasOddMult hOdd⟩⟩
  have : Finite {cls : Fibre core y degree // cls.Open ∧ IsOddClass cls} :=
    Subtype.finite
  exact Nat.card_pos

/-! ## 7.  The request as a subdivision specification -/

/-- The endgame's request is a `SubdivisionGraph.Spec`: a core with **positive
integral** lengths.  Its fibre is the fibre over `(spec.core, spec.length)`.

Note that `Spec` is strictly less general than `(core, y)`: `Spec.core_loopless`
forbids core loops, and the paper's own caterpillar-of-loops seed *has* core
loops (its stable graph is a chain of self-loops), so `FibreMember` is indexed
by a bare `Core` and a rational length vector.  See the module docstring of
`DraismaVargas.Count.FibreCaterpillar`. -/
abbrev SpecFibreMember (spec : Utilities.Certificate.SubdivisionGraph.Spec n p)
    (degree : ℕ) : Type 1 :=
  FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree

/-- The fibre over a subdivision specification. -/
abbrev SpecFibre (spec : Utilities.Certificate.SubdivisionGraph.Spec n p)
    (degree : ℕ) : Type 1 :=
  Fibre spec.core (fun slot ↦ (spec.length slot : ℚ)) degree

/-- The odd count over a subdivision specification. -/
noncomputable abbrev specOddCount
    (spec : Utilities.Certificate.SubdivisionGraph.Spec n p) (degree : ℕ) : ℕ :=
  oddCount spec.core (fun slot ↦ (spec.length slot : ℚ)) degree

end DraismaVargas.Count
