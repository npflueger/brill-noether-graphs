import DraismaVargasCount.Transport
import DraismaVargasCount.FibreCaterpillar
import DraismaVargasCount.Integrality

/-!
# The multiplicity under a transport, and the descent to the fibre quotient

**Source.**  Vargas, Part II, the multiplicities of `def-multiplicity` and the space
`TM_{g,d}` of full-rank tropical morphisms (`definition-TMSpace`), whose points are
isomorphism classes.  This file proves that `absMult` is invariant under an isomorphism
of gluing data, hence descends to the labelled fibre.  Since `MemberIso` (in
`DraismaVargasCount.Fibre`) carries an isomorphism of gluing data, that descent is
**unconditional**.

## What is proved

* `absMult_of_submatrix` -- **`absMult` is unchanged by a row relabelling and an
  unrelated column relabelling taken together.**  `DraismaVargasCount.Multiplicity` has the
  simultaneous relabelling (`absMult_reindex`) and the row permutation
  (`absMult_reindexRows`); a change of stable labelling moves rows and columns
  by unrelated permutations, so both are needed at once.
* `matrix_labelling_submatrix` -- **two labellings of one datum differ by a row
  and a column permutation**, at the level of the matrix itself (not only its
  determinant).  `absMult_labelling_indep` follows from it, and
  `coords_eq_of_datumIso_member` below and
  `Count.SegmentWalls.Frame.coordsAt_column` both use the matrix identity itself.
* `absMult_labelling_indep` -- **the multiplicity does not depend on the chosen
  `StableLengthMatrixLabelling`.**  Two honest labellings of one datum on one
  coordinate type differ exactly by such a pair of permutations.
* `Transport.DatumIso.isLeafVertex_map`, `leafCount_map` -- leaves of the target
  correspond, so the normalisation `2^{l(T)}` is the same on both sides.
* `transportLabelling`, `matrix_transportLabelling` -- **the transported stable
  labelling has the *same* length matrix**, entry by entry: both presentations
  use the same coordinate type, the rows follow the induced stable dictionary
  and the columns the target relabelling.
* `denominatorProduct_transportLabelling`, `absMult_transportLabelling`,
  **`absMult_eq_of_datumIso`** -- the multiplicity of *any* two honest
  labellings of isomorphic gluing data agrees.  No full-dimensionality, no
  integrality and no relation between the two labellings is assumed.
* `transportFullDim`, `fdAbsMult_transportFullDim`,
  **`fdAbsMult_eq_of_datumIso`** -- the same on
  `FullDimensionalSourcePresentation`, whose nine fields all transport.
* `fdAbsMultNat_eq_of_datumIso`, `oddMult_eq_of_compatible`,
  `hasOddMult_iff_of_compatible` -- the same statements in the natural-number
  form of `Count.Integrality` (the multiplicity as a natural number, by integrality
  of the cleared matrix), so oddness itself transfers.
* `transportIdent`, `FibreMember.transport`, `FibreMember.transport_absMult` --
  a labelled fibre member transported along an isomorphism of its datum.  Its
  coordinates are *literally* the original ones, because the length matrix and
  the row dictionary into the request are both unchanged.
* **`absMult_eq_of_datumIso_member`** and `oddMult_eq_of_datumIso_member` -- the
  **unconditional** invariance of the multiplicity: two labelled members whose gluing data are
  isomorphic have the same multiplicity, whatever labellings, identifications
  and coordinates they carry.
* `MemberIso.toDatumIso`, `MemberIso.ofDatumIso`, `memberIsoTransport`,
  `memberIsoTransport_compatible`, `cls_transport` -- the bridge to the fibre of
  `DraismaVargasCount.Fibre`, in both directions: an isomorphism of gluing data over
  the core induces an isomorphism of members, and an isomorphism of members hands
  back its `datum`.  `MemberIso.Compatible.symm` and `.trans` make the compatible
  isomorphisms a subgroupoid -- vacuously, since every one of them is
  compatible.
* `coords_eq_of_datumIso_member`, **`MemberIso.ofDatumIso'`** -- **the
  coordinate-free variant of `MemberIso.ofDatumIso`.**  Once `overCore_row`
  (`hRow`) is known, the `coords` field is *derivable*, not independent data:
  `coords_eq_of_datumIso_member` proves it from `iso` and `hRow` alone, by the
  same argument as `Count.SegmentWalls.Frame.coordsAt_column` (uniqueness of a
  member's coordinate vector, `FibreMember.coords_unique`, plus
  `matrix_labelling_submatrix` comparing `second`'s own labelling with the one
  `first`'s transports to it).  `ofDatumIso` takes the `coords` field as an
  argument.
* `MemberIso.compatible`, `memberIsoCompatible` -- **every isomorphism over the
  core is compatible**: `MemberIso` carries a `Count.Transport.DatumIso`, whose
  `compatible_fst`/`compatible_snd` are exactly what `MemberIso.Compatible` asks
  for.
* **`absMultDescends`, `isOddClass_cls_iff'`, `Fibre.absMult'`** -- the three
  unconditional statements: `absMult` descends to the labelled fibre, a class is
  odd exactly when its representatives are, and the multiplicity is a function
  on the quotient.  No hypothesis, no receipt.  `Fibre.absMult_eq_absMult'`
  records that the hypothesis-carrying `Count.Fibre.absMult` is literally the
  same function.
* `absMult_eq_of_compatible`, `absMult_eq_of_memberIso`,
  `absMultDescends_of_memberIsoCompatible`,
  `isOddClass_cls_iff_of_memberIsoCompatible`, `Fibre.absMultOfCompatible` --
  the invariance and its two corollaries with compatibility as a hypothesis;
  each hypothesis is discharged by `memberIsoCompatible`.

## What is NOT proved

* Nothing here counts members.  The finiteness of the fibre, `Finite (Fibre …)`
  and its `Fintype`, is proved downstream, unconditionally, by
  `Count.FibreNormalForm.instFiniteFibre` / `instFintypeFibre`, which
  transports a gluing datum along the target normal form of
  `Count.TargetNormalForm` using this file's `FibreMember.transport` and
  `cls_transport`.
* Nothing here says any particular multiplicity is odd, and nothing here claims
  the fibre is nonempty beyond the caterpillar witness below.

## Non-vacuity (`TransportWitness`)

The caterpillar of loops of every even genus `g = 2m + 2`, transported along the
**non-identity** isomorphism `Count.Transport.Witness.catSheetIso m`:
`swappedFullDim` with `fdAbsMult = 1`, `swappedMember` with a datum that is
*different* from the caterpillar datum (`swappedMember_data_ne`), the induced
`swappedIso : MemberIso …` with its stable dictionary constructed from the
`datum` field, its compatibility, and `swappedMember_cls`, which puts the two
members in one class of the labelled fibre.

## Consumers

The odd count on the quotient (oddness of a class is well defined), the star of a
codimension-one limit, and the finiteness of the fibre (`FibreNormalForm`).
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.Transport

variable {target₁ target₂ : CFGraph} {degree : ℕ}

/-! ## 1.  `absMult` does not see the choice of labelling -/

section Submatrix

variable {data : GluingDatum target₁ degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Row and column relabellings, taken independently, leave `absMult`
unchanged.**  `DraismaVargasCount.Multiplicity` has this for a simultaneous relabelling and
for a row permutation; the labelling of a presentation moves rows and columns
by unrelated permutations, so both are needed at once. -/
theorem absMult_of_submatrix (presentation other : data.LengthMatrixPresentation coordinate)
    (rowPerm columnPerm : Equiv.Perm coordinate)
    (hMatrix : matrix presentation = (matrix other).submatrix rowPerm columnPerm) :
    absMult presentation = absMult other := by
  classical
  have hRow : ∀ sourceRow : coordinate,
      rowDenominator presentation sourceRow = rowDenominator other (rowPerm sourceRow) := by
    intro sourceRow
    unfold rowDenominator commonDenominator
    have hFun : (fun column ↦ (matrix presentation sourceRow column).den) =
        (fun column ↦ (matrix other (rowPerm sourceRow) column).den) ∘ columnPerm := by
      funext column
      rw [hMatrix]
      rfl
    rw [hFun, ← Finset.lcm_image, Finset.image_univ_equiv]
  have hProduct : denominatorProduct presentation = denominatorProduct other := by
    unfold denominatorProduct
    rw [show (fun sourceRow ↦ rowDenominator presentation sourceRow) =
        fun sourceRow ↦ rowDenominator other (rowPerm sourceRow) from funext hRow]
    exact Fintype.prod_equiv rowPerm _ _ fun _ ↦ rfl
  have hDet : |(matrix presentation).det| = |(matrix other).det| := by
    rw [hMatrix]
    exact Matrix.abs_det_submatrix_equiv_equiv rowPerm columnPerm (matrix other)
  unfold absMult signedMult
  rw [abs_mul, abs_mul, hProduct, hDet]

end Submatrix

/-! ## 2.  The natural stable-source matrix and two labellings -/

section Labelling

variable {data : GluingDatum target₁ degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Two labellings of one datum differ by a row and a column permutation.**
Stated for the matrix itself, not only for its determinant, because the
coordinate vectors of a full-dimensional presentation have to be compared under
a change of labelling --
`Count.SegmentWalls.Frame.coordsAt_column` and the coordinate-free variant of
`MemberIso.ofDatumIso` below both need the matrix identity itself, not just
its consequence for `absMult`. -/
theorem matrix_labelling_submatrix
    (labelling other : StableLengthMatrixLabelling data coordinate) :
    matrix labelling.presentation =
      (matrix other.presentation).submatrix
        (labelling.row.symm.trans other.row) (labelling.targetEdge.trans other.targetEdge.symm) := by
  funext sourceRow column
  rw [Matrix.submatrix_apply, StableSourceMatrix.labelling_matrix_eq,
    StableSourceMatrix.labelling_matrix_eq]
  congr 1
  · simp
  · simp

/-- **The multiplicity does not depend on the chosen stable labelling.**  Two
honest labellings of the same datum on the same coordinate type differ by a row
permutation and an unrelated column permutation, and `absMult` sees neither. -/
theorem absMult_labelling_indep
    (labelling other : StableLengthMatrixLabelling data coordinate) :
    absMult labelling.presentation = absMult other.presentation := by
  classical
  exact absMult_of_submatrix _ _ (labelling.row.symm.trans other.row)
    (labelling.targetEdge.trans other.targetEdge.symm)
    (matrix_labelling_submatrix labelling other)

end Labelling

/-! ## 3.  Leaves of the target -/

namespace Transport.DatumIso

variable {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

theorem isLeafVertex_map (iso : DatumIso first second) (vertex : target₁.V) :
    IsLeafVertex target₂ (iso.targetVertex vertex) ↔ IsLeafVertex target₁ vertex := by
  unfold IsLeafVertex
  rw [iso.incidentEdges_card_map]

/-- The number of leaves of the target is preserved, so the normalisation
`2^{l(T)}` of the multiplicity is the same on both sides. -/
theorem leafCount_map (iso : DatumIso first second) : leafCount target₂ = leafCount target₁ := by
  classical
  unfold leafCount leafVertices
  refine (Finset.card_bij (fun vertex _ ↦ iso.targetVertex vertex) ?_ ?_ ?_).symm
  · intro vertex hVertex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hVertex ⊢
    exact (iso.isLeafVertex_map vertex).mpr hVertex
  · exact fun _ _ _ _ h ↦ iso.targetVertex.injective h
  · intro vertex hVertex
    refine ⟨iso.targetVertex.symm vertex, ?_, iso.targetVertex.apply_symm_apply vertex⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hVertex ⊢
    refine (iso.isLeafVertex_map _).mp ?_
    rwa [Equiv.apply_symm_apply]

end Transport.DatumIso

/-! ## 4.  The transported presentation -/

section Presentation

variable {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The transported stable labelling**: the rows follow the induced
dictionary of stable paths, the columns the target relabelling. -/
noncomputable def transportLabelling (iso : DatumIso first second)
    (hConnected : first.Connected)
    (labelling : StableLengthMatrixLabelling first coordinate) :
    StableLengthMatrixLabelling second coordinate where
  targetEdge := labelling.targetEdge.trans iso.targetEdge
  row := (iso.stablePathEquiv hConnected).symm.trans labelling.row

/-- **The length matrix is literally unchanged.**  Both presentations use the
same coordinate type, and the transported labelling matches row `i` with row
`i` and column `t` with column `t`. -/
theorem matrix_transportLabelling (iso : DatumIso first second)
    (hConnected : first.Connected)
    (labelling : StableLengthMatrixLabelling first coordinate) :
    matrix (transportLabelling iso hConnected labelling).presentation =
      matrix labelling.presentation := by
  funext sourceRow column
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq]
  exact iso.matrix_map hConnected _ _

theorem denominatorProduct_transportLabelling (iso : DatumIso first second)
    (hConnected : first.Connected)
    (labelling : StableLengthMatrixLabelling first coordinate) :
    denominatorProduct (transportLabelling iso hConnected labelling).presentation =
      denominatorProduct labelling.presentation := by
  unfold denominatorProduct rowDenominator
  rw [matrix_transportLabelling]

/-- **The multiplicity is preserved by the transport.** -/
theorem absMult_transportLabelling (iso : DatumIso first second)
    (hConnected : first.Connected)
    (labelling : StableLengthMatrixLabelling first coordinate) :
    absMult (transportLabelling iso hConnected labelling).presentation =
      absMult labelling.presentation := by
  unfold absMult signedMult
  rw [matrix_transportLabelling, denominatorProduct_transportLabelling,
    iso.leafCount_map]

/-- **Invariance of the multiplicity, at the level of gluing data.**  Any two honest stable
labellings of isomorphic gluing data, on one coordinate type, give the same
multiplicity.  No full-dimensionality, no integrality, and no relation between
the two labellings is required. -/
theorem absMult_eq_of_datumIso (iso : DatumIso first second)
    (hConnected : first.Connected)
    (source : StableLengthMatrixLabelling first coordinate)
    (image : StableLengthMatrixLabelling second coordinate) :
    absMult image.presentation = absMult source.presentation :=
  (absMult_labelling_indep image (transportLabelling iso hConnected source)).trans
    (absMult_transportLabelling iso hConnected source)

/-- **The transported full-dimensional presentation.** -/
noncomputable def transportFullDim (iso : DatumIso first second)
    (fd : FullDimensionalSourcePresentation first coordinate) :
    FullDimensionalSourcePresentation second coordinate where
  valid := iso.valid_map fd.valid
  targetConnected := iso.targetConnected_map fd.targetConnected
  targetGenus := by rw [iso.targetGenus_map]; exact fd.targetGenus
  saturated := by
    rw [iso.targetEdgeCard_map, iso.sourceGenus_map]
    exact fd.saturated
  labelling := transportLabelling iso fd.valid.1 fd.labelling
  det_ne_zero := by
    rw [matrix_transportLabelling]
    exact fd.det_ne_zero
  trivalent := iso.trivalent_map fd.valid.1 fd.trivalent
  pathEnds := iso.hasPathEnds_map fd.valid.1 fd.pathEnds

@[simp] theorem transportFullDim_labelling (iso : DatumIso first second)
    (fd : FullDimensionalSourcePresentation first coordinate) :
    (transportFullDim iso fd).labelling = transportLabelling iso fd.valid.1 fd.labelling := rfl

theorem fdAbsMult_transportFullDim (iso : DatumIso first second)
    (fd : FullDimensionalSourcePresentation first coordinate) :
    fdAbsMult (transportFullDim iso fd) = fdAbsMult fd :=
  absMult_transportLabelling iso fd.valid.1 fd.labelling

/-- **Invariance of the multiplicity on full-dimensional presentations.**  Isomorphic gluing
data have equal multiplicity, whatever presentations they carry. -/
theorem fdAbsMult_eq_of_datumIso (iso : DatumIso first second)
    (source : FullDimensionalSourcePresentation first coordinate)
    (image : FullDimensionalSourcePresentation second coordinate) :
    fdAbsMult image = fdAbsMult source :=
  absMult_eq_of_datumIso iso source.valid.1 source.labelling image.labelling

end Presentation

/-! ## 5.  Transport of a labelled fibre member -/

section Member

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}

/-- **The transported core identification.**  The label of the stable graph
travels along the induced dictionaries, so the transported datum carries the
same request. -/
noncomputable def transportIdent {target₁ target₂ : CFGraph.{0}}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    (iso : DatumIso first second) (hConnected : first.Connected)
    (ident : CoreIdentification core first) : CoreIdentification core second where
  vertex := (iso.branchVertexEquiv hConnected).symm.trans ident.vertex
  row := (iso.stablePathEquiv hConnected).symm.trans ident.row
  incidence branch slot := by
    have hBase := ident.incidence ((iso.branchVertexEquiv hConnected).symm branch)
      slot
    have hMap := iso.incidenceCount_map hConnected
      (((iso.branchVertexEquiv hConnected).symm branch) : BranchVertex first).1
      (ident.row.symm slot)
    have hVertex : iso.sourceVertexEquiv
        (((iso.branchVertexEquiv hConnected).symm branch) : BranchVertex first).1 =
        branch.1 := congrArg Subtype.val
          ((iso.branchVertexEquiv hConnected).apply_symm_apply branch)
    rw [hVertex] at hMap
    rw [show ((iso.stablePathEquiv hConnected).symm.trans ident.row).symm slot =
        iso.stablePathEquiv hConnected (ident.row.symm slot) from rfl, ← hMap]
    exact hBase

/-- **The transported member.**  Its coordinates are literally those of the
original: the length matrix is unchanged and the requested lengths are read
through the same row dictionary. -/
noncomputable def FibreMember.transport (member : FibreMember core y degree)
    {target₂ : CFGraph.{0}} {second : GluingDatum target₂ degree}
    (iso : DatumIso member.data second) : FibreMember core y degree where
  target := target₂
  data := second
  fullDim := transportFullDim iso member.fullDim
  ident := transportIdent iso member.fullDim.valid.1 member.ident
  coords := member.coords
  realizes := by
    have hMatrix := matrix_transportLabelling iso member.fullDim.valid.1
      member.fullDim.labelling
    show (GluingDatum.LengthMatrixPresentation.matrix
      (transportFullDim iso member.fullDim).labelling.presentation).mulVec
      member.coords = _
    rw [transportFullDim_labelling, hMatrix]
    refine member.realizes.trans ?_
    funext row
    simp [transportIdent, transportLabelling]

@[simp] theorem FibreMember.transport_absMult (member : FibreMember core y degree)
    {target₂ : CFGraph.{0}} {second : GluingDatum target₂ degree}
    (iso : DatumIso member.data second) :
    (member.transport iso).absMult = member.absMult :=
  fdAbsMult_transportFullDim iso member.fullDim

end Member

/-! ## 6.  Isomorphisms over the core, and the descent -/

section Core

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}

/-- **Compatibility of an isomorphism over the core**: the relative permutation
`vertexPerm⁻¹ ∘ edgePerm` stays inside every block of the endpoint's vertex
partition -- exactly the compatibility of
`GluingDatum.SheetRelabeling`.  Carrying one partition assignment to the other
does not imply it, and without it the sheet permutations are not a map of
quotient-source graphs.

Since `MemberIso` carries an isomorphism of gluing data,
`datum : DatumIso first.data second.data`, this is **automatic**
(`MemberIso.compatible`); the `…_of_memberIsoCompatible` statements below, which
take it as a hypothesis, are discharged by `memberIsoCompatible`. -/
structure MemberIso.Compatible {first second : FibreMember core y degree}
    (iso : MemberIso first second) : Prop where
  /-- Compatibility at the first endpoint of an occurrence. -/
  fst : ∀ (edge : first.target.edges) (sheet : Fin degree),
    (first.data.vertexPartition
        ((edge : first.target.V × first.target.V)).1).Rel
      ((iso.datum.vertexPerm ((edge : first.target.V × first.target.V)).1).symm
        (iso.datum.edgePerm edge sheet)) sheet
  /-- Compatibility at the second endpoint of an occurrence. -/
  snd : ∀ (edge : first.target.edges) (sheet : Fin degree),
    (first.data.vertexPartition
        ((edge : first.target.V × first.target.V)).2).Rel
      ((iso.datum.vertexPerm ((edge : first.target.V × first.target.V)).2).symm
        (iso.datum.edgePerm edge sheet)) sheet

/-- **Every isomorphism over the core is compatible**, because it carries a
`DatumIso`. -/
theorem MemberIso.compatible {first second : FibreMember core y degree}
    (iso : MemberIso first second) : iso.Compatible :=
  ⟨iso.datum.compatible_fst, iso.datum.compatible_snd⟩

/-- A compatible isomorphism over the core is an isomorphism of gluing data --
simply its `datum` field. -/
def MemberIso.toDatumIso {first second : FibreMember core y degree}
    (iso : MemberIso first second) (_hCompatible : iso.Compatible) :
    DatumIso first.data second.data :=
  iso.datum

/-- The identity isomorphism is compatible. -/
theorem MemberIso.refl_compatible (member : FibreMember core y degree) :
    (MemberIso.refl member).Compatible := (MemberIso.refl member).compatible

/-- **Invariance of the multiplicity under a compatible isomorphism** over the
core. -/
theorem absMult_eq_of_compatible {first second : FibreMember core y degree}
    (iso : MemberIso first second) (hCompatible : iso.Compatible) :
    first.absMult = second.absMult :=
  (fdAbsMult_eq_of_datumIso (iso.toDatumIso hCompatible) first.fullDim second.fullDim).symm

/-- **Compatibility of every isomorphism over the core**, as a proposition: the
sheet permutations recorded by any `MemberIso` are compatible.  It holds by
`memberIsoCompatible`, which discharges the statements below that take it as a
hypothesis. -/
def MemberIsoCompatible (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (first second : FibreMember core y degree) (iso : MemberIso first second),
    iso.Compatible

/-- **Every isomorphism over the core is compatible.**  `MemberIso` carries a
`Count.Transport.DatumIso`, whose two compatibility fields are exactly what is
asked for. -/
theorem memberIsoCompatible (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    MemberIsoCompatible core y degree :=
  fun _ _ iso ↦ ⟨iso.datum.compatible_fst, iso.datum.compatible_snd⟩

/-- **The multiplicity descends to the fibre, given compatibility.** -/
theorem absMultDescends_of_memberIsoCompatible
    (hCompatible : MemberIsoCompatible core y degree) :
    AbsMultDescends core y degree := by
  intro first second hIso
  exact hIso.elim fun iso ↦ absMult_eq_of_compatible iso (hCompatible first second iso)

/-- Well-definedness of oddness on the quotient, given compatibility. -/
theorem isOddClass_cls_iff_of_memberIsoCompatible
    (hCompatible : MemberIsoCompatible core y degree)
    (member : FibreMember core y degree) :
    IsOddClass member.cls ↔ member.HasOddMult :=
  isOddClass_cls_iff (absMultDescends_of_memberIsoCompatible hCompatible) member

/-- The multiplicity on the quotient, given compatibility. -/
noncomputable def Fibre.absMultOfCompatible
    (hCompatible : MemberIsoCompatible core y degree) (cls : Fibre core y degree) : ℚ :=
  Fibre.absMult (absMultDescends_of_memberIsoCompatible hCompatible) cls

@[simp] theorem Fibre.absMultOfCompatible_cls
    (hCompatible : MemberIsoCompatible core y degree)
    (member : FibreMember core y degree) :
    Fibre.absMultOfCompatible hCompatible member.cls = member.absMult := rfl

/-! ### The three unconditional statements -/

/-- **The multiplicity descends, with no hypothesis at all.**  `absMult` is invariant under
isomorphism of gluing data over the identity of the core, so it descends to the
labelled fibre.  Nothing is assumed about the members, their labellings, their
identifications or their coordinates. -/
theorem absMultDescends (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    AbsMultDescends core y degree :=
  absMultDescends_of_memberIsoCompatible (memberIsoCompatible core y degree)

/-- **Oddness is well defined on the quotient, with no hypothesis**: a
class is odd exactly when every -- equivalently, some -- representative is.  The
hypothesis-carrying `Count.isOddClass_cls_iff` is this statement with
`absMultDescends` supplied. -/
theorem isOddClass_cls_iff' (member : FibreMember core y degree) :
    IsOddClass member.cls ↔ member.HasOddMult :=
  isOddClass_cls_iff (absMultDescends core y degree) member

/-- **The multiplicity of a class of the labelled fibre, with no hypothesis.** -/
noncomputable def Fibre.absMult' (cls : Fibre core y degree) : ℚ :=
  Fibre.absMult (absMultDescends core y degree) cls

@[simp] theorem Fibre.absMult'_cls (member : FibreMember core y degree) :
    Fibre.absMult' member.cls = member.absMult := rfl

/-- The hypothesis-carrying `Count.Fibre.absMult` is *literally* this function:
`AbsMultDescends` is a `Prop`, so the two differ only by proof irrelevance.  A
statement about `Fibre.absMult h` may therefore drop `h`. -/
theorem Fibre.absMult_eq_absMult' (hDescends : AbsMultDescends core y degree)
    (cls : Fibre core y degree) :
    Fibre.absMult hDescends cls = Fibre.absMult' cls := rfl

/-- The unconditional invariance, stated directly on an isomorphism over the
core. -/
theorem absMult_eq_of_memberIso {first second : FibreMember core y degree}
    (iso : MemberIso first second) : first.absMult = second.absMult :=
  absMult_eq_of_compatible iso iso.compatible

/-! ### Constructing the dictionary that `MemberIso` carries as data -/

/-- **The isomorphism over the core induced by an isomorphism of gluing data.**
Its stable dictionary is not supplied: `stableVertex`, `stableRow` and
`incidence` are the induced branch-vertex equivalence, the induced stable-path
equivalence and the transported incidence census. -/
noncomputable def memberIsoTransport (member : FibreMember core y degree)
    {target₂ : CFGraph.{0}} {second : GluingDatum target₂ degree}
    (iso : DatumIso member.data second) :
    MemberIso member (member.transport iso) where
  datum := iso
  overCore_vertex branch := by
    show (transportIdent iso member.fullDim.valid.1 member.ident).vertex
      (iso.branchVertexEquiv member.fullDim.valid.1 branch) = _
    simp [transportIdent]
  overCore_row path := by
    show (transportIdent iso member.fullDim.valid.1 member.ident).row
      (iso.stablePathEquiv member.fullDim.valid.1 path) = _
    simp [transportIdent]
  coords column := by
    show member.coords ((transportLabelling iso member.fullDim.valid.1
      member.fullDim.labelling).targetEdge.symm
        (iso.targetEdge (member.fullDim.labelling.targetEdge column))) = _
    simp [transportLabelling]

/-- It is compatible, by construction. -/
theorem memberIsoTransport_compatible (member : FibreMember core y degree)
    {target₂ : CFGraph.{0}} {second : GluingDatum target₂ degree}
    (iso : DatumIso member.data second) :
    (memberIsoTransport member iso).Compatible :=
  (memberIsoTransport member iso).compatible

/-- A member and its transport lie in the same class of the labelled fibre. -/
theorem cls_transport (member : FibreMember core y degree)
    {target₂ : CFGraph.{0}} {second : GluingDatum target₂ degree}
    (iso : DatumIso member.data second) :
    (member.transport iso).cls = member.cls :=
  FibreMember.cls_eq_cls_iff.mpr ⟨(memberIsoTransport member iso).symm⟩

end Core

/-! ### The same invariance in natural-number form -/

section Integral

open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}

variable {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The natural-number multiplicity of `Count.Integrality` is invariant under an
isomorphism of gluing data. -/
theorem fdAbsMultNat_eq_of_datumIso (iso : DatumIso first second)
    (source : FullDimensionalSourcePresentation first coordinate)
    (image : FullDimensionalSourcePresentation second coordinate) :
    fdAbsMultNat image = fdAbsMultNat source := by
  have hRat : ((fdAbsMultNat image : ℚ)) = ((fdAbsMultNat source : ℚ)) := by
    rw [← fdAbsMult_eq_fdAbsMultNat, ← fdAbsMult_eq_fdAbsMultNat]
    exact fdAbsMult_eq_of_datumIso iso source image
  exact_mod_cast hRat

/-- Hence the integral multiplicity of a member descends along a compatible
isomorphism over the core. -/
theorem oddMult_eq_of_compatible {memberFirst memberSecond : FibreMember core y degree}
    (iso : MemberIso memberFirst memberSecond) (hCompatible : iso.Compatible) :
    memberFirst.oddMult = memberSecond.oddMult :=
  (fdAbsMultNat_eq_of_datumIso (iso.toDatumIso hCompatible)
    memberFirst.fullDim memberSecond.fullDim).symm

/-- And oddness itself transfers. -/
theorem hasOddMult_iff_of_compatible {memberFirst memberSecond : FibreMember core y degree}
    (iso : MemberIso memberFirst memberSecond) (hCompatible : iso.Compatible) :
    memberFirst.HasOddMult ↔ memberSecond.HasOddMult := by
  rw [hasOddMult_iff_odd_oddMult, hasOddMult_iff_odd_oddMult,
    oddMult_eq_of_compatible iso hCompatible]

end Integral

/-! ### The general bridge, and the unconditional form of the descent -/

section Bridge

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
variable {first second : FibreMember core y degree}

/-- **Invariance of the multiplicity, unconditionally.**  Two labelled members whose
gluing data are isomorphic have the same multiplicity -- whatever labellings,
identifications and coordinates they carry.  `AbsMultDescends` is this statement
with `Nonempty (MemberIso first second)` in place of
`DatumIso first.data second.data`, and the two differ only by
`MemberIso.Compatible`. -/
theorem absMult_eq_of_datumIso_member (iso : DatumIso first.data second.data) :
    first.absMult = second.absMult :=
  (fdAbsMult_eq_of_datumIso iso first.fullDim second.fullDim).symm

/-- The same for the integral multiplicity of `Count.Integrality`. -/
theorem oddMult_eq_of_datumIso_member (iso : DatumIso first.data second.data) :
    first.oddMult = second.oddMult :=
  (fdAbsMultNat_eq_of_datumIso iso first.fullDim second.fullDim).symm

/-- **The general dictionary constructor.**  Given an isomorphism of the two
members' gluing data, together with the three conditions that make it an
isomorphism *over the core*, the stable dictionary of `MemberIso` is
constructed, not supplied. -/
noncomputable def MemberIso.ofDatumIso (iso : DatumIso first.data second.data)
    (hVertex : ∀ branch : BranchVertex first.data,
      second.ident.vertex (iso.branchVertexEquiv first.fullDim.valid.1 branch) =
        first.ident.vertex branch)
    (hRow : ∀ path : StablePath first.data,
      second.ident.row (iso.stablePathEquiv first.fullDim.valid.1 path) =
        first.ident.row path)
    (hCoords : ∀ column : Fin p,
      second.coords (second.fullDim.labelling.targetEdge.symm
          (iso.targetEdge (first.fullDim.labelling.targetEdge column))) =
        first.coords column) :
    MemberIso first second where
  datum := iso
  overCore_vertex := hVertex
  overCore_row := hRow
  coords := hCoords

/-- **The `coords` field of `MemberIso.ofDatumIso` is derivable from `iso` and
`hRow` alone -- it is not independent data.**  `FibreMember.coords_unique` pins
`second.coords` down as the *unique* solution of `second`'s own realization
equation; checking that `first`'s coordinates, read through the induced column
permutation, solve it is exactly the two-labellings-of-one-datum computation of
`matrix_labelling_submatrix` (applied to `second.data`, comparing `second`'s own
labelling with the one `first`'s transports to it) together with
`matrix_transportLabelling`.  Same argument as
`Count.SegmentWalls.Frame.coordsAt_column`, phrased directly on members instead
of frames so it can live here, ahead of `SegmentWalls` in the import order. -/
theorem coords_eq_of_datumIso_member (iso : DatumIso first.data second.data)
    (hRow : ∀ path : StablePath first.data,
      second.ident.row (iso.stablePathEquiv first.fullDim.valid.1 path) =
        first.ident.row path)
    (column : Fin p) :
    second.coords (second.fullDim.labelling.targetEdge.symm
        (iso.targetEdge (first.fullDim.labelling.targetEdge column))) =
      first.coords column := by
  classical
  set transported := transportLabelling iso first.fullDim.valid.1 first.fullDim.labelling
    with htrans
  set ρ : Fin p ≃ Fin p := second.fullDim.labelling.row.symm.trans transported.row with hρ
  set γ : Fin p ≃ Fin p :=
    second.fullDim.labelling.targetEdge.trans transported.targetEdge.symm with hγ
  have hsub : second.matrix = first.matrix.submatrix ρ γ := by
    show matrix second.fullDim.labelling.presentation =
      (matrix first.fullDim.labelling.presentation).submatrix ρ γ
    rw [matrix_labelling_submatrix second.fullDim.labelling transported, hρ, hγ,
      matrix_transportLabelling iso first.fullDim.valid.1 first.fullDim.labelling]
  have hslot : ∀ r : Fin p,
      second.ident.row (second.fullDim.labelling.row.symm r) =
        first.ident.row (first.fullDim.labelling.row.symm (ρ r)) := by
    intro r
    have h := hRow ((iso.stablePathEquiv first.fullDim.valid.1).symm
      (second.fullDim.labelling.row.symm r))
    rw [Equiv.apply_symm_apply] at h
    have hrowsym : first.fullDim.labelling.row.symm (ρ r) =
        (iso.stablePathEquiv first.fullDim.valid.1).symm
          (second.fullDim.labelling.row.symm r) := by
      rw [hρ, htrans]
      simp [transportLabelling]
    rw [hrowsym]
    exact h
  have hrow : ∀ r : Fin p, second.matrix.mulVec (fun c ↦ first.coords (γ c)) r =
      first.matrix.mulVec first.coords (ρ r) := by
    intro r
    rw [hsub]
    show ∑ c, first.matrix (ρ r) (γ c) * first.coords (γ c) =
      ∑ c, first.matrix (ρ r) c * first.coords c
    exact Fintype.sum_equiv γ _ _ fun c ↦ by simp
  have hsolve : second.matrix.mulVec (fun c ↦ first.coords (γ c)) =
      fun row ↦ y (second.ident.row (second.fullDim.labelling.row.symm row)) := by
    funext r
    rw [hslot r, hrow r]
    exact congrFun first.realizes (ρ r)
  have huniq : (fun c ↦ first.coords (γ c)) = second.coords := second.coords_unique _ hsolve
  have hgamma : γ (second.fullDim.labelling.targetEdge.symm
      (iso.targetEdge (first.fullDim.labelling.targetEdge column))) = column := by
    rw [hγ, htrans]
    simp [transportLabelling]
  rw [← huniq]
  show first.coords (γ (second.fullDim.labelling.targetEdge.symm
    (iso.targetEdge (first.fullDim.labelling.targetEdge column)))) = first.coords column
  rw [hgamma]

/-- **The coordinate-free variant of `MemberIso.ofDatumIso`.**  Once `overCore_row`
is known, `coords_eq_of_datumIso_member` supplies the `coords` field on its own,
so this constructor does not ask for it (`ofDatumIso` takes it as an
argument). -/
noncomputable def MemberIso.ofDatumIso' (iso : DatumIso first.data second.data)
    (hVertex : ∀ branch : BranchVertex first.data,
      second.ident.vertex (iso.branchVertexEquiv first.fullDim.valid.1 branch) =
        first.ident.vertex branch)
    (hRow : ∀ path : StablePath first.data,
      second.ident.row (iso.stablePathEquiv first.fullDim.valid.1 path) =
        first.ident.row path) :
    MemberIso first second :=
  MemberIso.ofDatumIso iso hVertex hRow (coords_eq_of_datumIso_member iso hRow)

theorem MemberIso.ofDatumIso_compatible (iso : DatumIso first.data second.data)
    (hVertex : ∀ branch : BranchVertex first.data,
      second.ident.vertex (iso.branchVertexEquiv first.fullDim.valid.1 branch) =
        first.ident.vertex branch)
    (hRow : ∀ path : StablePath first.data,
      second.ident.row (iso.stablePathEquiv first.fullDim.valid.1 path) =
        first.ident.row path)
    (hCoords : ∀ column : Fin p,
      second.coords (second.fullDim.labelling.targetEdge.symm
          (iso.targetEdge (first.fullDim.labelling.targetEdge column))) =
        first.coords column) :
    (MemberIso.ofDatumIso iso hVertex hRow hCoords).Compatible :=
  (MemberIso.ofDatumIso iso hVertex hRow hCoords).compatible

/-- Compatible isomorphisms over the core are closed under inversion. -/
theorem MemberIso.Compatible.symm {iso : MemberIso first second}
    (_hCompatible : iso.Compatible) : iso.symm.Compatible :=
  iso.symm.compatible

/-- And under composition. -/
theorem MemberIso.Compatible.trans {third : FibreMember core y degree}
    {left : MemberIso first second} {right : MemberIso second third}
    (_hLeft : left.Compatible) (_hRight : right.Compatible) :
    (left.trans right).Compatible :=
  (left.trans right).compatible

end Bridge

/-! ## 7.  Non-vacuity: the caterpillar of loops with a non-identity sheet swap -/

namespace TransportWitness

open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.Count.FibreCaterpillar

/-- The transported full-dimensional presentation of the caterpillar of loops,
along the transposition of sheets `0` and `1`. -/
noncomputable def swappedFullDim (m : ℕ) :
    FullDimensionalSourcePresentation
      (Transport.DatumIso.globalRelabelDatum (caterpillarDatum m)
        (Equiv.swap (0 : Fin (m + 2)) 1)) (Fin (6 * m + 3)) :=
  transportFullDim (Transport.Witness.catSheetIso m) (CaterpillarRows.fullDim m)

/-- **The transport preserves the caterpillar's multiplicity `1`**, uniformly in
the genus. -/
theorem fdAbsMult_swappedFullDim (m : ℕ) : fdAbsMult (swappedFullDim m) = 1 :=
  (fdAbsMult_transportFullDim (Transport.Witness.catSheetIso m)
    (CaterpillarRows.fullDim m)).trans (Caterpillar.fdAbsMult_caterpillar m)

/-- The caterpillar member of genus `2m + 2`, transported along the same
non-identity isomorphism. -/
noncomputable def swappedMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    FibreMember (catCore m) request (m + 2) :=
  (caterpillarMember m request).transport (Transport.Witness.catSheetIso m)

/-- **It really is a different member**: its gluing datum is not the
caterpillar datum. -/
theorem swappedMember_data_ne (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (swappedMember m request).data ≠ (caterpillarMember m request).data :=
  Transport.Witness.catSheetIso_ne m

/-- Its multiplicity is the caterpillar's. -/
theorem swappedMember_absMult (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (swappedMember m request).absMult = 1 :=
  ((caterpillarMember m request).transport_absMult
    (Transport.Witness.catSheetIso m)).trans (caterpillarMember_absMult m request)

theorem swappedMember_hasOddMult (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (swappedMember m request).HasOddMult :=
  FibreMember.hasOddMult_of_absMult_eq_one (swappedMember_absMult m request)

/-- **The induced isomorphism over the core**, with its stable dictionary
constructed rather than supplied. -/
noncomputable def swappedIso (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    MemberIso (caterpillarMember m request) (swappedMember m request) :=
  memberIsoTransport (caterpillarMember m request) (Transport.Witness.catSheetIso m)

/-- It is compatible. -/
theorem swappedIso_compatible (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (swappedIso m request).Compatible :=
  memberIsoTransport_compatible _ _

/-- **And it is not the identity**: its sheet permutation is a transposition. -/
theorem swappedIso_vertexPerm_ne (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (vertex : (catTree m).V) :
    (swappedIso m request).datum.vertexPerm vertex ≠ Equiv.refl (Fin (m + 2)) :=
  Transport.Witness.catSheetIso_vertexPerm_ne m vertex

/-- The two members are one class of the labelled fibre. -/
theorem swappedMember_cls (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (swappedMember m request).cls = (caterpillarMember m request).cls :=
  cls_transport (caterpillarMember m request) (Transport.Witness.catSheetIso m)

/-- The descent holds for this pair, with no hypothesis: `absMult` agrees. -/
theorem swappedMember_absMult_eq (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).absMult = (swappedMember m request).absMult :=
  absMult_eq_of_compatible (swappedIso m request) (swappedIso_compatible m request)

end TransportWitness

end DraismaVargas.Count
