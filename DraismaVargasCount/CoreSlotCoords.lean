import DraismaVargasCount.GeometricCountFamily

/-!
# The coordinate vector read on core slots, and the separation it gives

**Source.**  Vargas, Part II (arXiv:2609.09109), part (2) of `prop-caterpillar-ballot`
("the slope sequence determines the morphism").  This module supplies the separation
criterion that the injective half of the ballot classification needs -- members with
different slope sequences are not isomorphic over the core -- in a form strictly stronger than
the multiset criterion of `DraismaVargasCount.GeometricCountFamily`.

## Why the coordinate *multiset* is not enough

`GeometricFibre.cls_injective_of_coordsMultiset_injective` reduces injectivity
of `i ↦ cls (f i)` to injectivity of `i ↦ (f i).coordsMultiset`.  The multiset
appears there, rather than the coordinate *function*, for a structural reason:
`FibreMember.coords` is indexed by the member's own coordinate type -- the
target edges, through `fullDim.labelling.targetEdge` -- while the *core slot* of
a stable row is read through `ident.row ∘ fullDim.labelling.row.symm`.
`StableLengthMatrixLabelling` carries `targetEdge` and `row` as unrelated
fields, so the two dictionaries differ by an unknown permutation and only the
multiset survives.

For the ballot family that is a real loss, not a technicality.  At
`m = 2` the slope sequences `[2,1,2,3,2]` and `[2,3,2,1,2]` are distinct
elements of `Slopes 6` with the *same multiset of slopes*; over an all-ones
request their coordinate multisets therefore coincide, and no multiset argument
can separate them.  Separating them that way would need Part II's genericity
hypothesis (pairwise distinct edge lengths) as an extra assumption.

## What is proved

* `FibreMember.slotMap` -- the dictionary `Fin p ≃ Fin p` carrying a member's
  coordinate index to the core slot its row is labelled by, i.e.
  `ident.row ∘ fullDim.labelling.row.symm`.  `FibreMember.realizes_slotMap`
  restates the realization equation through it.
* `FibreMember.pos_of_open` -- **an open member forces its own request strictly
  positive**, from non-negativity of the length matrix and nonsingularity alone.
  The frame-level twin is `Count.OpenAtPositivity.pos_of_openAt`; this copy sits
  here so that the rigidity layer can drop redundant positivity binders without
  importing that module.
* `FibreMember.Diagonal` -- the length matrix of the member is diagonal.
  `Diagonal.of_diagonalPattern` gets it from a
  `SeedDeterminant.DiagonalPattern`, and `Diagonal.matrix_diag_ne_zero` derives
  nonvanishing of the diagonal from `det_matrix_ne_zero` alone: **no positivity
  is assumed anywhere below**.
* `FibreMember.coreCoords`, `FibreMember.coreDiag` -- the coordinate vector and
  the diagonal of the length matrix, both **read on core slots**, with
  `Diagonal.coreDiag_mul_coreCoords : coreDiag t * coreCoords t = y t`.
* `slotMap_column` -- **the rigidity lemma, and the point of the module.**  For
  an isomorphism over the core between two *diagonal* members,
  `second.slotMap (iso.column c) = first.slotMap c`.  The two permutations that
  appear in `GeometricMultiplicity.coords_eq_of_datumIso_member` -- `ρ` from the
  row dictionaries and `γ` from the target-edge dictionaries -- are forced to
  agree, because `second.matrix = first.matrix.submatrix ρ γ` and a nonzero
  diagonal entry of `second` has to come from a nonzero entry of `first`, which
  for a diagonal `first` means `ρ r = γ r`.
* `coreCoords_eq_of_geometricIso`, `coreDiag_eq_of_geometricIso` -- consequently
  the coordinate vector read on core slots is a **class invariant as a
  function**, not merely as a multiset; and so is the diagonal, over a request
  that vanishes nowhere.
* `GeometricFibre.cls_ne_cls_of_coreCoords_ne`,
  `GeometricFibre.cls_injective_of_coreCoords_injective`,
  `GeometricFibre.cls_injective_of_coreDiag_injective` -- the separation criteria
  in the shape the `BallotFamily.member_injective` field takes.
* `coreCoords_of_slotMap_id`, `coreDiag_of_slotMap_id`, `Diagonal.of_matrix_eq`
  -- the consumption interface: a member that labels its rows by the core's own
  slots reads `coreCoords`/`coreDiag` as its plain coordinate vector and plain
  diagonal, and diagonality transfers along an equality of length matrices.
* `coordsMultiset_eq_map_coreCoords` -- the multiset invariant is the multiset of the
  core-slot one, so the strengthening is literal.
* `slotMap_caterpillarMember`, `coreCoords_caterpillarMember`,
  `coreDiag_caterpillarMember`, `diagonal_caterpillarMember` -- **non-vacuity**:
  the zig-zag caterpillar member is diagonal, its `slotMap` is the identity, and
  its `coreCoords` and `coreDiag` are `catCoords` and `catDiag`.

## What is not proved here

* **Nothing is separated.**  Every statement below takes the family, its
  diagonality, and the injectivity of its `coreCoords` (or `coreDiag`) as
  hypotheses; that any particular family satisfies them is not addressed here.
* **`Diagonal` is a genuine hypothesis.**  The rigidity lemma fails as
  stated without it: for members whose length matrices are not diagonal the row
  and column dictionaries need not agree, and only the multiset invariant of
  `DraismaVargasCount.GeometricCountFamily` is available.  Both members must be diagonal;
  diagonality of one does not suffice for the argument given.
* **No member is constructed.**  The members over the caterpillar core are built
  elsewhere: `FibreCaterpillar.caterpillarMember` at the zig-zag, and
  `BallotCoreIdentification.ballotFamilyMember` at every slope sequence.
* `coreDiag_eq_of_geometricIso` and `cls_injective_of_coreDiag_injective` carry
  `∀ slot, y slot ≠ 0`.  That hypothesis is only used to divide; the
  `coreCoords` forms carry no hypothesis on the request at all.
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  The core-slot dictionary of a member -/

namespace FibreMember

/-- **The core slot of a coordinate index.**  A member's coordinates are indexed
through `fullDim.labelling.targetEdge`, while its rows are labelled by core
slots through `ident.row`; this is the composite dictionary relating the two
indexings, and it is exactly the permutation appearing on the right-hand side of
the realization equation. -/
noncomputable def slotMap (member : FibreMember core y degree) : Fin p ≃ Fin p :=
  member.fullDim.labelling.row.symm.trans member.ident.row

theorem slotMap_apply (member : FibreMember core y degree) (r : Fin p) :
    member.slotMap r = member.ident.row (member.fullDim.labelling.row.symm r) := rfl

/-- The realization equation, with the right-hand side read through
`slotMap`. -/
theorem realizes_slotMap (member : FibreMember core y degree) (r : Fin p) :
    member.matrix.mulVec member.coords r = y (member.slotMap r) :=
  congrFun member.realizes r

/-- **An open member only sits over a strictly positive request.**  The
requested length of the slot `s` is the `slotMap.symm s` row of the length
matrix applied to the member's coordinate vector; the entries of a length
matrix are non-negative genuine path sums (`SeedDeterminant.row_nonneg`), the
coordinates are strictly positive by `Open`, and the row is not identically zero
because the matrix is nonsingular.  So the sum is strictly positive.

This is the member-level twin of `Count.OpenAtPositivity.pos_of_openAt`, which
says the same thing about a `SegmentWalls.Frame`.  It is proved here, low in the
stack, so that the rigidity layer can drop its redundant positivity binders
without importing `Count.OpenAtPositivity`; that module keeps its own
frame-level statement, from which its `FrameClass` and `GeometricFibre`
corollaries are read. -/
theorem pos_of_open (member : FibreMember core y degree) (h : member.Open) (s : Fin p) :
    0 < y s := by
  have hnonneg : ∀ r c : Fin p, 0 ≤ member.matrix r c := fun _ c ↦
    SeedDeterminant.row_nonneg member.fullDim.labelling.presentation _ c
  obtain ⟨c, hc⟩ : ∃ c, member.matrix (member.slotMap.symm s) c ≠ 0 := by
    by_contra hrow
    push Not at hrow
    exact member.det_matrix_ne_zero
      (Matrix.det_eq_zero_of_row_eq_zero (member.slotMap.symm s) hrow)
  have hy : member.matrix.mulVec member.coords (member.slotMap.symm s) = y s := by
    rw [member.realizes_slotMap, Equiv.apply_symm_apply]
  rw [← hy]
  show 0 < ∑ j, member.matrix (member.slotMap.symm s) j * member.coords j
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (hnonneg _ j) (h j).le)
    ⟨c, Finset.mem_univ c, mul_pos ((hnonneg _ c).lt_of_ne (Ne.symm hc)) (h c)⟩

/-! ## 2.  Diagonal members -/

/-- **A member whose length matrix is diagonal.**  Every member produced by the
row calculus has this property (`SeedDeterminant.DiagonalPattern`), and it is
the hypothesis under which the row and column dictionaries of an isomorphism
over the core are forced to agree. -/
def Diagonal (member : FibreMember core y degree) : Prop :=
  ∀ row column : Fin p, column ≠ row → member.matrix row column = 0

/-- A `DiagonalPattern` on the member's own presentation gives `Diagonal`. -/
theorem Diagonal.of_diagonalPattern {member : FibreMember core y degree}
    (pattern : SeedDeterminant.DiagonalPattern member.fullDim.labelling.presentation) :
    member.Diagonal :=
  fun _ _ hne ↦ pattern.matrix_apply_eq_zero hne

theorem Diagonal.matrix_eq_diagonal {member : FibreMember core y degree}
    (h : member.Diagonal) :
    member.matrix = Matrix.diagonal fun r ↦ member.matrix r r := by
  funext r c
  by_cases hrc : c = r
  · subst hrc
    rw [Matrix.diagonal_apply_eq]
  · rw [h r c hrc, Matrix.diagonal_apply_ne _ (Ne.symm hrc)]

/-- **The diagonal of a diagonal member never vanishes.**  This uses only
nonsingularity of the length matrix, which is a field of the member; no
positivity of the diagonal is assumed. -/
theorem Diagonal.matrix_diag_ne_zero {member : FibreMember core y degree}
    (h : member.Diagonal) (r : Fin p) : member.matrix r r ≠ 0 := by
  intro hzero
  refine member.det_matrix_ne_zero ?_
  rw [h.matrix_eq_diagonal, Matrix.det_diagonal]
  exact Finset.prod_eq_zero (Finset.mem_univ r) hzero

/-! ## 3.  The coordinate vector and the diagonal, read on core slots -/

/-- **The coordinate at a core slot.**  This is the datum Part II's uniqueness
statement is about: the length the member assigns to the requested slot. -/
noncomputable def coreCoords (member : FibreMember core y degree) (slot : Fin p) : ℚ :=
  member.coords (member.slotMap.symm slot)

/-- **The diagonal entry of the length matrix at a core slot**: for a diagonal
member this is the local expansion factor of the row over that slot, and for the
ballot family it is the slope. -/
noncomputable def coreDiag (member : FibreMember core y degree) (slot : Fin p) : ℚ :=
  member.matrix (member.slotMap.symm slot) (member.slotMap.symm slot)

theorem coreDiag_ne_zero {member : FibreMember core y degree} (h : member.Diagonal)
    (slot : Fin p) : member.coreDiag slot ≠ 0 :=
  h.matrix_diag_ne_zero _

/-- **The realization equation at a core slot.**  For a diagonal member the
solve is entry by entry, and this is that solve with both sides read on the
requested slots. -/
theorem Diagonal.coreDiag_mul_coreCoords {member : FibreMember core y degree}
    (h : member.Diagonal) (slot : Fin p) :
    member.coreDiag slot * member.coreCoords slot = y slot := by
  have hmul := member.realizes_slotMap (member.slotMap.symm slot)
  rw [Equiv.apply_symm_apply] at hmul
  rw [← hmul, h.matrix_eq_diagonal, Matrix.mulVec_diagonal]
  rfl

theorem Diagonal.coreCoords_eq_div {member : FibreMember core y degree}
    (h : member.Diagonal) (slot : Fin p) :
    member.coreCoords slot = y slot / member.coreDiag slot := by
  rw [← h.coreDiag_mul_coreCoords slot,
    mul_div_cancel_left₀ _ (coreDiag_ne_zero h slot)]

theorem Diagonal.coreCoords_ne_zero {member : FibreMember core y degree}
    (h : member.Diagonal) {slot : Fin p} (hy : y slot ≠ 0) :
    member.coreCoords slot ≠ 0 := by
  intro hzero
  exact hy (by rw [← h.coreDiag_mul_coreCoords slot, hzero, mul_zero])

theorem Diagonal.coreDiag_eq_div {member : FibreMember core y degree}
    (h : member.Diagonal) {slot : Fin p} (hy : y slot ≠ 0) :
    member.coreDiag slot = y slot / member.coreCoords slot := by
  rw [← h.coreDiag_mul_coreCoords slot,
    mul_div_cancel_right₀ _ (h.coreCoords_ne_zero hy)]

/-- When a member labels its rows by the core slots in the obvious way -- its
`slotMap` is the identity -- the core-slot readings are the plain coordinate
vector and the plain diagonal.  This is the shape in which a member built from a
row labelling over the core's own slot type is consumed. -/
theorem coreCoords_of_slotMap_id {member : FibreMember core y degree}
    (hid : ∀ r, member.slotMap r = r) (slot : Fin p) :
    member.coreCoords slot = member.coords slot := by
  have hrefl : member.slotMap = Equiv.refl (Fin p) := Equiv.ext hid
  show member.coords (member.slotMap.symm slot) = _
  rw [hrefl]
  rfl

theorem coreDiag_of_slotMap_id {member : FibreMember core y degree}
    (hid : ∀ r, member.slotMap r = r) (slot : Fin p) :
    member.coreDiag slot = member.matrix slot slot := by
  have hrefl : member.slotMap = Equiv.refl (Fin p) := Equiv.ext hid
  show member.matrix (member.slotMap.symm slot) (member.slotMap.symm slot) = _
  rw [hrefl]
  rfl

/-- Diagonality is a property of the length matrix alone, so it transfers along
an equality of matrices. -/
theorem Diagonal.of_matrix_eq {member : FibreMember core y degree}
    {M : Matrix (Fin p) (Fin p) ℚ} (hM : member.matrix = M)
    (h : ∀ row column : Fin p, column ≠ row → M row column = 0) : member.Diagonal := by
  intro row column hne
  rw [hM]
  exact h row column hne

/-- The coordinate-multiset class invariant is the multiset of the core-slot one. -/
theorem coordsMultiset_eq_map_coreCoords (member : FibreMember core y degree) :
    member.coordsMultiset =
      (Finset.univ : Finset (Fin p)).val.map member.coreCoords := by
  have hperm : Multiset.map (⇑member.slotMap.symm) (Finset.univ : Finset (Fin p)).val =
      (Finset.univ : Finset (Fin p)).val := by simp
  calc member.coordsMultiset
      = Multiset.map member.coords
          (Multiset.map (⇑member.slotMap.symm) (Finset.univ : Finset (Fin p)).val) := by
        rw [hperm, coordsMultiset_def]
    _ = (Finset.univ : Finset (Fin p)).val.map member.coreCoords :=
        Multiset.map_map _ _ _

end FibreMember

/-! ## 4.  Rigidity: over a diagonal member the two dictionaries agree -/

section Rigidity

variable {first second : FibreMember core y degree}

/-- **The rigidity lemma.**  An isomorphism over the core induces a permutation
`iso.column` of the coordinate indices through the *target-edge* dictionaries
and a permutation of the rows through the *row* dictionaries, and in general
these are unrelated -- which is why only the coordinate multiset was known to be
a class invariant.  When both length matrices are diagonal they are forced to
agree: `second.matrix = first.matrix.submatrix ρ γ`, a nonzero diagonal entry of
`second` needs a nonzero entry of `first` at `(ρ r, γ r)`, and for a diagonal
`first` that means `ρ r = γ r`.  The conclusion is that `iso.column` carries
core slots to core slots on the nose. -/
theorem slotMap_column (h₁ : first.Diagonal) (h₂ : second.Diagonal)
    (iso : GeometricMemberIso first second) (c : Fin p) :
    second.slotMap (iso.column c) = first.slotMap c := by
  classical
  set transported := GeometricMultiplicity.transportLabelling iso.datum
    first.fullDim.valid.1 first.fullDim.labelling with htrans
  set ρ : Fin p ≃ Fin p := second.fullDim.labelling.row.symm.trans transported.row with hρ
  set γ : Fin p ≃ Fin p :=
    second.fullDim.labelling.targetEdge.trans transported.targetEdge.symm with hγ
  have hsub : second.matrix = first.matrix.submatrix ρ γ := by
    show GluingDatum.LengthMatrixPresentation.matrix second.fullDim.labelling.presentation =
      (GluingDatum.LengthMatrixPresentation.matrix
        first.fullDim.labelling.presentation).submatrix ρ γ
    rw [matrix_labelling_submatrix second.fullDim.labelling transported, hρ, hγ,
      GeometricMultiplicity.matrix_transportLabelling iso.datum first.fullDim.valid.1
        first.fullDim.labelling]
  have hργ : ∀ r : Fin p, ρ r = γ r := by
    intro r
    by_contra hne
    refine h₂.matrix_diag_ne_zero r ?_
    rw [hsub, Matrix.submatrix_apply]
    exact h₁ (ρ r) (γ r) (Ne.symm hne)
  have hslot : ∀ r : Fin p, second.slotMap r = first.slotMap (ρ r) := by
    intro r
    have h := iso.overCore_row ((iso.datum.stablePathEquiv first.fullDim.valid.1).symm
      (second.fullDim.labelling.row.symm r))
    rw [Equiv.apply_symm_apply] at h
    have hrowsym : first.fullDim.labelling.row.symm (ρ r) =
        (iso.datum.stablePathEquiv first.fullDim.valid.1).symm
          (second.fullDim.labelling.row.symm r) := by
      rw [hρ, htrans]
      simp [GeometricMultiplicity.transportLabelling]
    show second.ident.row (second.fullDim.labelling.row.symm r) =
      first.ident.row (first.fullDim.labelling.row.symm (ρ r))
    rw [hrowsym]
    exact h
  have hgamma : γ (iso.column c) = c := by
    rw [hγ, htrans]
    simp [GeometricMultiplicity.transportLabelling, GeometricMemberIso.column]
  have hrho : ρ (iso.column c) = c := by rw [hργ]; exact hgamma
  rw [hslot (iso.column c), hrho]

/-- **The coordinate vector read on core slots is a class invariant.**  This is
the statement `cls_injective_of_coordsMultiset_injective` is the multiset shadow
of. -/
theorem coreCoords_eq_of_geometricIso (h₁ : first.Diagonal) (h₂ : second.Diagonal)
    (iso : GeometricMemberIso first second) : first.coreCoords = second.coreCoords := by
  funext slot
  have hcol : iso.column (first.slotMap.symm slot) = second.slotMap.symm slot := by
    apply second.slotMap.injective
    rw [Equiv.apply_symm_apply, slotMap_column h₁ h₂ iso, Equiv.apply_symm_apply]
  show first.coords (first.slotMap.symm slot) = second.coords (second.slotMap.symm slot)
  rw [← hcol]
  exact (iso.coords_column (first.slotMap.symm slot)).symm

/-- **The diagonal read on core slots is a class invariant**, over a request
that vanishes nowhere. -/
theorem coreDiag_eq_of_geometricIso (h₁ : first.Diagonal) (h₂ : second.Diagonal)
    (hy : ∀ slot, y slot ≠ 0) (iso : GeometricMemberIso first second) :
    first.coreDiag = second.coreDiag := by
  funext slot
  rw [h₁.coreDiag_eq_div (hy slot), h₂.coreDiag_eq_div (hy slot),
    congrFun (coreCoords_eq_of_geometricIso h₁ h₂ iso) slot]

end Rigidity

/-! ## 5.  The separation criteria -/

namespace GeometricFibre

variable {first second : FibreMember core y degree}

/-- **Separation by core coordinates.**  Two diagonal members whose coordinate
vectors differ *at some core slot* are not isomorphic over the core.  Unlike
`cls_ne_cls_of_coordsMultiset_ne`, no reordering is permitted. -/
theorem cls_ne_cls_of_coreCoords_ne (h₁ : first.Diagonal) (h₂ : second.Diagonal)
    (h : first.coreCoords ≠ second.coreCoords) : cls first ≠ cls second := by
  intro hEq
  exact (cls_eq_cls_iff.mp hEq).elim fun iso ↦
    h (coreCoords_eq_of_geometricIso h₁ h₂ iso)

/-- **The injectivity criterion, in the shape of `BallotFamily.member_injective`.** -/
theorem cls_injective_of_coreCoords_injective {ι : Type*}
    (f : ι → FibreMember core y degree) (hdiag : ∀ i, (f i).Diagonal)
    (hinj : Function.Injective fun i ↦ (f i).coreCoords) :
    Function.Injective fun i ↦ cls (f i) := by
  intro a b hab
  refine hinj ?_
  exact (cls_eq_cls_iff.mp hab).elim fun iso ↦
    coreCoords_eq_of_geometricIso (hdiag a) (hdiag b) iso

/-- The same criterion read on the diagonal of the length matrix, which is where
a family parametrized by expansion factors -- the ballot caterpillars -- actually
differs. -/
theorem cls_injective_of_coreDiag_injective {ι : Type*}
    (f : ι → FibreMember core y degree) (hdiag : ∀ i, (f i).Diagonal)
    (hy : ∀ slot, y slot ≠ 0)
    (hinj : Function.Injective fun i ↦ (f i).coreDiag) :
    Function.Injective fun i ↦ cls (f i) := by
  refine cls_injective_of_coreCoords_injective f hdiag ?_
  intro a b hab
  refine hinj ?_
  funext slot
  show (f a).coreDiag slot = (f b).coreDiag slot
  rw [(hdiag a).coreDiag_eq_div (hy slot), (hdiag b).coreDiag_eq_div (hy slot),
    show (f a).coreCoords slot = (f b).coreCoords slot from congrFun hab slot]

end GeometricFibre

/-! ## 6.  Non-vacuity: the zig-zag caterpillar member -/

namespace FibreCaterpillar

open DraismaVargas.LocalCases.CaterpillarRows

/-- The caterpillar member's row labelling and its core identification are the
same `rowEquiv`, so its core-slot dictionary is the identity. -/
@[simp] theorem slotMap_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (r : Fin (6 * m + 3)) : (caterpillarMember m request).slotMap r = r :=
  Equiv.apply_symm_apply (CaterpillarRows.rowEquiv m) r

@[simp] theorem slotMap_symm_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (slot : Fin (6 * m + 3)) : (caterpillarMember m request).slotMap.symm slot = slot := by
  apply (caterpillarMember m request).slotMap.injective
  rw [Equiv.apply_symm_apply, slotMap_caterpillarMember]

/-- **The caterpillar member is diagonal** -- `CaterpillarRows.diagonalPattern`. -/
theorem diagonal_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).Diagonal :=
  FibreMember.Diagonal.of_diagonalPattern (CaterpillarRows.diagonalPattern m)

/-- Its coordinates read on core slots are the diagonal solve `catCoords`. -/
theorem coreCoords_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).coreCoords = catCoords m request := by
  funext slot
  show (caterpillarMember m request).coords
    ((caterpillarMember m request).slotMap.symm slot) = _
  rw [slotMap_symm_caterpillarMember, caterpillarMember_coords]

/-- Its diagonal read on core slots is `catDiag`: `2` on a leaf row,
`1/2` on a pair edge, `1` on a slope-one spine edge. -/
theorem coreDiag_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).coreDiag = catDiag m := by
  funext slot
  show (caterpillarMember m request).matrix
    ((caterpillarMember m request).slotMap.symm slot)
      ((caterpillarMember m request).slotMap.symm slot) = _
  rw [slotMap_symm_caterpillarMember]
  rfl

end FibreCaterpillar

end DraismaVargas.Count
