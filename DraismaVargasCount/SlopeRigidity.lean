import DraismaVargasCount.CoreRelabelInvariance
import DraismaVargasCount.CoreSlotCoords

/-!
# What rigidity of the core diagonal asks for, and why genericity does not help

**Source.**  Vargas, Part II (arXiv:2609.09109), part (2) of `prop-caterpillar-ballot`:
every admissible slope sequence uniquely determines a tropical morphism.  In this library the
uniqueness is the statement `CoreDiagRigid` below: two open members of odd multiplicity
with the same core diagonal lie in the same class.  (The `rigid` field of
`Count.BallotSlopes.DiagonalClassification` is the same statement restricted to diagonal
members, `SlopeRigidity.DiagonalRigid`.)  The other half of the uniqueness, that
different slope sequences give different classes, is in `Count/CoreSlotCoords.lean`.

This module does not prove `CoreDiagRigid`.  It isolates a *necessary* condition for
it, which is concrete, checkable, and independent of every genericity
assumption on the request.

## The mechanism, in one paragraph

A `FibreMember c y degree` mentions the core in exactly two places: the
identification `ident` of the stable graph with the core, and the realization
equation `A z = y (ident.row ...)`.  `Count.CoreRelabel.relabelMember` exploits the
first: re-reading the label along an incidence-preserving
permutation pair moves no geometry.  It has to assume `y (d.slot e) = y e`,
because it carries the coordinate vector across unchanged.

**For a diagonal member that assumption is unnecessary**: the realization
equation can simply be *re-solved*, entry by entry, after the label moves.  The
resulting member `twistMember d m h` has the same target, the same gluing datum,
the same full-dimensional presentation -- hence the same multiplicity -- and its
core diagonal is `m.coreDiag` composed with `d.slot.symm`.  So whenever `d`
stabilises the core diagonal, `twistMember d m h` is *another open member of odd
multiplicity with exactly the same core diagonal*, and `CoreDiagRigid` forces it into
the class of `m`.  That happens if and only if `m`'s own gluing datum admits a
self-isomorphism inducing `d` on the core (`Realizes`).

The point is that `twistMember` never touches `y`.  **Genericity of the request
-- the pairwise distinct edge lengths of Part II's `prop-divisors-on-chain` -- does not
remove the obligation**, and `realizes_of_coreDiagRigid_of_injective` says so with the
hypothesis in the type.  What does control the obligation is the stabiliser of the
*diagonal*, a slope-level condition, in the automorphism group of the core.

## What is proved

* `mulVec_of_diagonal`, `mulVec_diag` -- a diagonal length matrix solves entry
  by entry.
* `twistMember` -- **the construction**: a diagonal member, relabelled along a
  `CoreRelabel.Relabel` and re-solved.  `twistMember_coreDiag`,
  `twistMember_coreCoords`, `twistMember_matrix`, `twistMember_diagonal`,
  `twistMember_hasOddMult`, `twistMember_absMult` compute its invariants, and
  `twistMember_open` shows it is open whenever `m` is and `d` stabilises the
  diagonal.  None of these assumes anything about `y`.
* `twistMember_coords_eq_of_request` -- when `d` *does* preserve the request,
  `twistMember` agrees with `Count.CoreRelabel.relabelMember`, so the construction is a
  strict generalisation of that one.
* `Realizes` -- the gluing datum of `m` admits a self-isomorphism inducing the
  core symmetry `d`.  `cls_twistMember_eq_iff` : `m` and its twist are in the
  same geometric class **iff** `Realizes d m`.
* `CoreDiagRigid` -- rigidity of the core diagonal, as a standalone proposition.
* `realizes_of_coreDiagRigid` -- **the headline.**  `CoreDiagRigid` implies that every
  incidence-preserving core symmetry stabilising an open odd diagonal member's
  core diagonal is realised by a self-isomorphism of that member's gluing datum.
* `realizes_of_coreDiagRigid_of_injective`,
  `not_coreDiagRigid_of_not_realizes` -- the same statement with genericity
  assumed (it buys nothing), and the contrapositive.
* `defect` -- **the core-symmetry defect** of an arbitrary `GeometricDatumIso`
  between two members' data: an incidence-preserving permutation pair of the
  core, trivial exactly when the isomorphism is over the core
  (`cls_eq_iff_exists_trivial_defect`).
* `coreDiag_eq_defect` -- **the core diagonal transports along *any* datum
  isomorphism**, moved by the defect.  This is
  `Count.coreDiag_eq_of_geometricIso` with both `overCore` hypotheses dropped,
  and with its `∀ slot, y slot ≠ 0` dropped too: the proof goes through the length
  matrix, not through the coordinates.  `defect_stabilises_coreDiag` is the
  consequence used below, and `coreDiag_eq_of_geometricIso_of_diagonal` is that lemma
  itself with that hypothesis removed.
* `cls_eq_of_realizes_defect` -- a datum isomorphism whose defect is realised by
  the source's own automorphisms can be corrected to one over the core.
* `DatumIsoSupply`, `SymmetryRealized`, **`coreDiagRigid_iff`** -- **the
  reduction, as an equivalence.**  Over a fibre whose open odd members are all
  diagonal, `CoreDiagRigid` *is* the conjunction of two statements: (A) equal core
  diagonals supply an abstract isomorphism of gluing data, and (B) every core
  symmetry stabilising a member's diagonal is realised by an automorphism of its
  datum.  Nothing is lost in either direction.

## What is not proved here

* **`CoreDiagRigid` is neither proved nor refuted here.**  Everything below is a
  *necessary* condition for it.
* **No `Realizes` is established or refuted here for any member.**  Discharging
  `realizes_of_coreDiagRigid`'s conclusion at the caterpillar member means
  exhibiting a self-`GeometricDatumIso` of `CaterpillarDatum.caterpillarDatum`;
  refuting it means showing there is none.  Neither is attempted here.
* **`Diagonal` is a genuine hypothesis of `twistMember`**, and it is not
  optional: re-solving the realization equation entry by entry is what a
  non-diagonal length matrix does not permit.  Not every open odd member is diagonal
  (`ColumnTwist.not_forall_diagonal_of_openOdd`), though individual diagonal members
  exist, which is all `twistMember` needs; `BallotSlopes.DiagonalClassification.diagonal`
  (`Count/DiagonalClassification.lean`) asks only for a diagonal representative per
  class, not per member.
* **`DatumIsoSupply` is not established here for any core or request.**  It is the
  other half of `CoreDiagRigid` -- the classification of combinatorial types by the
  slope data -- and nothing here bears on it.  `coreDiagRigid_iff` takes both
  halves as hypotheses; it inhabits neither.
* `coreDiagRigid_iff` assumes `hdiag`, that every open odd member is diagonal.  That
  fails over every fibre with an open odd member
  (`ColumnTwist.not_forall_diagonal_of_openOdd`), so `coreDiagRigid_iff` applies to no
  such fibre; `SlopeRigidity.diagonalRigid_iff` is the same reduction for
  diagonal members, with no such hypothesis.
* Nothing here is about the count, the ballot family, or parity.
-/

namespace DraismaVargas.Count.SlopeRigidity

open DraismaVargas.Count
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {c c' : Core n p} {y y' : Fin p → ℚ}

/-! ## 1.  A diagonal length matrix solves entry by entry -/

/-- A matrix with no off-diagonal entries acts on a vector coordinatewise. -/
theorem mulVec_of_diagonal {M : Matrix (Fin p) (Fin p) ℚ}
    (h : ∀ row column : Fin p, column ≠ row → M row column = 0) (z : Fin p → ℚ) (r : Fin p) :
    M.mulVec z r = M r r * z r := by
  have hM : M = Matrix.diagonal fun t ↦ M t t := by
    funext row column
    by_cases hrc : column = row
    · subst hrc
      rw [Matrix.diagonal_apply_eq]
    · rw [h row column hrc, Matrix.diagonal_apply_ne _ (Ne.symm hrc)]
  conv_lhs => rw [hM]
  rw [Matrix.mulVec_diagonal]

/-- The realization equation of a diagonal member, one row at a time. -/
theorem mulVec_diag {m : FibreMember c y degree} (h : m.Diagonal)
    (z : Fin p → ℚ) (r : Fin p) : m.matrix.mulVec z r = m.matrix r r * z r :=
  mulVec_of_diagonal h z r

/-! ## 2.  The twist: a diagonal member relabelled and re-solved -/

/-- **The twist of a diagonal member along a core relabelling.**

Target, gluing datum and full-dimensionality receipt are untouched -- so the
multiplicity is untouched -- and the identification with the core is composed
with `d`, exactly as in `Count.CoreRelabel.relabelMember`.  Unlike that
construction the coordinate vector is *re-solved* rather than carried across,
which is possible because the length matrix is diagonal, and which is why no
hypothesis relating `y` to `d` is needed. -/
noncomputable def twistMember (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) : FibreMember c' y' degree where
  target := m.target
  data := m.data
  fullDim := m.fullDim
  ident := relabelIdent d m.ident
  coords := fun r ↦ y' (d.slot (m.slotMap r)) / m.matrix r r
  realizes := by
    funext r
    have hne : m.matrix r r ≠ 0 := h.matrix_diag_ne_zero r
    show m.matrix.mulVec _ r = y' (d.slot (m.slotMap r))
    rw [mulVec_diag h, mul_comm, div_mul_cancel₀ _ hne]

@[simp] theorem twistMember_target (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) : (twistMember (y' := y') d m h).target = m.target := rfl

@[simp] theorem twistMember_data (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) : (twistMember (y' := y') d m h).data = m.data := rfl

@[simp] theorem twistMember_fullDim (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) : (twistMember (y' := y') d m h).fullDim = m.fullDim := rfl

@[simp] theorem twistMember_matrix (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) : (twistMember (y' := y') d m h).matrix = m.matrix := rfl

theorem twistMember_slotMap (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) (r : Fin p) :
    (twistMember (y' := y') d m h).slotMap r = d.slot (m.slotMap r) := rfl

theorem twistMember_slotMap_symm (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) (slot : Fin p) :
    (twistMember (y' := y') d m h).slotMap.symm slot = m.slotMap.symm (d.slot.symm slot) := by
  apply (twistMember (y' := y') d m h).slotMap.injective
  rw [Equiv.apply_symm_apply, twistMember_slotMap, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- **The twist moves the core diagonal by the relabelling, and by nothing
else.** -/
theorem twistMember_coreDiag (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) (slot : Fin p) :
    (twistMember (y' := y') d m h).coreDiag slot = m.coreDiag (d.slot.symm slot) := by
  show (twistMember (y' := y') d m h).matrix _ _ = _
  rw [twistMember_slotMap_symm]
  rfl

/-- The twist is diagonal, its matrix being the old one. -/
theorem twistMember_diagonal (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) : (twistMember (y' := y') d m h).Diagonal := h

/-- The coordinate vector of the twist, read on core slots: the request at the
slot, divided by the *moved* diagonal. -/
theorem twistMember_coreCoords (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) (slot : Fin p) :
    (twistMember (y' := y') d m h).coreCoords slot = y' slot / m.coreDiag (d.slot.symm slot) := by
  show (twistMember (y' := y') d m h).coords _ = _
  rw [twistMember_slotMap_symm]
  show y' (d.slot (m.slotMap (m.slotMap.symm (d.slot.symm slot)))) / _ = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- **The multiplicity is untouched**: it is read off the full-dimensional
presentation, which the twist keeps on the nose. -/
theorem twistMember_absMult (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) : (twistMember (y' := y') d m h).absMult = m.absMult := rfl

theorem twistMember_hasOddMult (d : Relabel c c') (m : FibreMember c y degree)
    (h : m.Diagonal) : (twistMember (y' := y') d m h).HasOddMult ↔ m.HasOddMult := Iff.rfl

/-- **The twist of an open member is open**, provided the relabelling stabilises
the core diagonal.  No hypothesis on the request is used. -/
theorem twistMember_open (d : Relabel c c) (m : FibreMember c y degree) (h : m.Diagonal)
    (hstab : ∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot) (hOpen : m.Open) :
    (twistMember (y' := y) d m h).Open := by
  intro r
  show 0 < y (d.slot (m.slotMap r)) / m.matrix r r
  set t : Fin p := m.slotMap r with ht
  have hr : m.slotMap.symm t = r := by rw [ht, Equiv.symm_apply_apply]
  have hmat : m.matrix r r = m.coreDiag t := by rw [FibreMember.coreDiag, hr]
  have hdiag : m.coreDiag (d.slot t) = m.coreDiag t := by
    have hx := hstab (d.slot t)
    rw [Equiv.symm_apply_apply] at hx
    exact hx.symm
  have hsolve := m.realizes_slotMap (m.slotMap.symm (d.slot t))
  rw [mulVec_diag h, Equiv.apply_symm_apply] at hsolve
  have hcoord : m.matrix (m.slotMap.symm (d.slot t)) (m.slotMap.symm (d.slot t)) =
      m.coreDiag t := by rw [← hdiag]; rfl
  rw [hcoord] at hsolve
  rw [hmat, ← hsolve, mul_div_cancel_left₀ _ (FibreMember.coreDiag_ne_zero h t)]
  exact hOpen _

/-- **The twist generalises `Count.CoreRelabel.relabelMember`.**  When the
relabelling preserves the request, the re-solved coordinate vector is the old
one, so the two constructions agree on every field. -/
theorem twistMember_coords_eq_of_request (d : Relabel c c')
    (hy : ∀ e, y' (d.slot e) = y e) (m : FibreMember c y degree) (h : m.Diagonal) :
    (twistMember (y' := y') d m h).coords = (relabelMember d hy m).coords := by
  funext r
  show y' (d.slot (m.slotMap r)) / m.matrix r r = m.coords r
  rw [hy]
  have hsolve := m.realizes_slotMap r
  rw [mulVec_diag h] at hsolve
  rw [← hsolve, mul_div_cancel_left₀ _ (h.matrix_diag_ne_zero r)]

/-! ## 3.  When is a member isomorphic to its own twist? -/

/-- **The core symmetry `d` is realised by the member's own gluing datum**: a
self-isomorphism of `m.data` whose induced bijections of branch vertices and of
stable rows are the ones `d` names, read through `m`'s identification with the
core.

This is exactly the condition under which `m` and any twist of `m` along `d`
lie in the same geometric class -- see `cls_twistMember_eq_iff`.  Nothing weaker
will do: the two `overCore` fields of a `GeometricMemberIso` are precisely these
two equations. -/
def Realizes (d : Relabel c c) (m : FibreMember c y degree) : Prop :=
  ∃ a : GeometricDatumIso m.data m.data,
    (∀ b : BranchVertex m.data,
        d.vtx (m.ident.vertex (a.branchVertexEquiv m.fullDim.valid.1 b)) = m.ident.vertex b) ∧
    (∀ path : StablePath m.data,
        d.slot (m.ident.row (a.stablePathEquiv m.fullDim.valid.1 path)) = m.ident.row path)

/-- A relabelling that is the identity on both components is realised by every
member, through the identity isomorphism. -/
theorem realizes_of_trivial {d : Relabel c c} (hslot : ∀ e, d.slot e = e)
    (hvtx : ∀ v, d.vtx v = v) (m : FibreMember c y degree) : Realizes d m := by
  refine ⟨GeometricDatumIso.refl m.data, fun b ↦ ?_, fun path ↦ ?_⟩
  · rw [GeometricDatumIso.branchVertexEquiv_refl, Equiv.refl_apply, hvtx]
  · rw [GeometricDatumIso.stablePathEquiv_refl, Equiv.refl_apply, hslot]

/-- **The criterion.**  A member and its twist along `d` are in the same
geometric class exactly when `d` is realised by the member's gluing datum. -/
theorem cls_twistMember_eq_iff (d : Relabel c c) (m : FibreMember c y degree)
    (h : m.Diagonal) :
    GeometricFibre.cls m = GeometricFibre.cls (twistMember (y' := y) d m h) ↔ Realizes d m := by
  constructor
  · intro hcls
    obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp hcls
    exact ⟨iso.datum, iso.overCore_vertex, iso.overCore_row⟩
  · rintro ⟨a, hv, hr⟩
    refine GeometricFibre.cls_eq_cls_iff.mpr ⟨?_⟩
    exact { datum := a, overCore_vertex := hv, overCore_row := hr }

/-! ## 4.  What `rigid` forces -/

/-- **Rigidity of the core diagonal, as a standalone proposition**, over an arbitrary
core and request: two open members of odd multiplicity with the same core diagonal lie in
the same geometric class. -/
def CoreDiagRigid (c : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ first second : FibreMember c y degree,
    first.Open → first.HasOddMult → second.Open → second.HasOddMult →
      first.coreDiag = second.coreDiag →
        GeometricFibre.cls first = GeometricFibre.cls second

/-- **The headline.**  Suppose `CoreDiagRigid` holds over `(c, y)`.  Then for every open
diagonal member of odd multiplicity and every incidence-preserving core symmetry
that stabilises its core diagonal, the member's *gluing datum* admits a
self-isomorphism inducing that symmetry.

This is a necessary condition for `CoreDiagRigid`, and it is about the automorphism
group of the source, not about the request: the twist that produces it re-solves
the realization equation instead of carrying the coordinates across. -/
theorem realizes_of_coreDiagRigid (hrigid : CoreDiagRigid c y degree)
    (m : FibreMember c y degree) (hOpen : m.Open) (hOdd : m.HasOddMult) (h : m.Diagonal)
    (d : Relabel c c) (hstab : ∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot) :
    Realizes d m := by
  refine (cls_twistMember_eq_iff d m h).mp ?_
  refine hrigid m (twistMember (y' := y) d m h) hOpen hOdd
    (twistMember_open d m h hstab hOpen) ((twistMember_hasOddMult d m h).mpr hOdd) ?_
  funext slot
  rw [twistMember_coreDiag, hstab]

/-- **Genericity buys nothing.**  The same conclusion, with the pairwise-distinct edge
lengths of Part II's `prop-divisors-on-chain` assumed as `Function.Injective y`: the
hypothesis
is simply never used, because `twistMember` does not transport the coordinate
vector.  So no strengthening of the request removes the obligation. -/
theorem realizes_of_coreDiagRigid_of_injective (_hinj : Function.Injective y)
    (hrigid : CoreDiagRigid c y degree)
    (m : FibreMember c y degree) (hOpen : m.Open) (hOdd : m.HasOddMult) (h : m.Diagonal)
    (d : Relabel c c) (hstab : ∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot) :
    Realizes d m :=
  realizes_of_coreDiagRigid hrigid m hOpen hOdd h d hstab

/-- **The contrapositive.**  An open odd diagonal
member, a core symmetry stabilising its diagonal, and *no* self-isomorphism of
its gluing datum inducing that symmetry. -/
theorem not_coreDiagRigid_of_not_realizes
    (m : FibreMember c y degree) (hOpen : m.Open) (hOdd : m.HasOddMult) (h : m.Diagonal)
    (d : Relabel c c) (hstab : ∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot)
    (hno : ¬ Realizes d m) : ¬ CoreDiagRigid c y degree :=
  fun hrigid ↦ hno (realizes_of_coreDiagRigid hrigid m hOpen hOdd h d hstab)

/-! ## 5.  The core-symmetry defect of an arbitrary datum isomorphism -/

section Defect

variable {first second : FibreMember c y degree}

/-- **The defect.**  A `GeometricDatumIso` between the data of two members need
not be *over the core*: composing its induced bijections of branch vertices and
of stable rows with the two core identifications leaves a permutation pair of
the core, and that pair preserves every incidence multiplicity.  The two
`overCore` fields of a `GeometricMemberIso` say exactly that the defect is
trivial. -/
noncomputable def defect (i : GeometricDatumIso first.data second.data) : Relabel c c where
  slot :=
    first.ident.row.symm.trans ((i.stablePathEquiv first.fullDim.valid.1).trans second.ident.row)
  vtx :=
    first.ident.vertex.symm.trans
      ((i.branchVertexEquiv first.fullDim.valid.1).trans second.ident.vertex)
  incidence := by
    intro v e
    have hfirst := first.ident.incidence (first.ident.vertex.symm v) e
    rw [Equiv.apply_symm_apply] at hfirst
    have hsecond := second.ident.incidence
      (i.branchVertexEquiv first.fullDim.valid.1 (first.ident.vertex.symm v))
      (second.ident.row (i.stablePathEquiv first.fullDim.valid.1 (first.ident.row.symm e)))
    have hdv : (first.ident.vertex.symm.trans
        ((i.branchVertexEquiv first.fullDim.valid.1).trans second.ident.vertex)) v
        = second.ident.vertex (i.branchVertexEquiv first.fullDim.valid.1
          (first.ident.vertex.symm v)) := rfl
    have hds : (first.ident.row.symm.trans
        ((i.stablePathEquiv first.fullDim.valid.1).trans second.ident.row)) e
        = second.ident.row
          (i.stablePathEquiv first.fullDim.valid.1 (first.ident.row.symm e)) := rfl
    rw [← hfirst, hdv, hds, ← hsecond, Equiv.symm_apply_apply]
    exact (GeometricDatumIso.incidenceCount_map i first.fullDim.valid.1
      (first.ident.vertex.symm v).1 (first.ident.row.symm e)).symm

theorem defect_slot_apply (i : GeometricDatumIso first.data second.data) (e : Fin p) :
    (defect i).slot e =
      second.ident.row (i.stablePathEquiv first.fullDim.valid.1 (first.ident.row.symm e)) := rfl

theorem defect_vtx_apply (i : GeometricDatumIso first.data second.data) (v : Fin n) :
    (defect i).vtx v =
      second.ident.vertex
        (i.branchVertexEquiv first.fullDim.valid.1 (first.ident.vertex.symm v)) := rfl

theorem defect_slot_row (i : GeometricDatumIso first.data second.data)
    (path : StablePath first.data) :
    (defect i).slot (first.ident.row path) =
      second.ident.row (i.stablePathEquiv first.fullDim.valid.1 path) := by
  rw [defect_slot_apply, Equiv.symm_apply_apply]

theorem defect_vtx_branch (i : GeometricDatumIso first.data second.data)
    (b : BranchVertex first.data) :
    (defect i).vtx (first.ident.vertex b) =
      second.ident.vertex (i.branchVertexEquiv first.fullDim.valid.1 b) := by
  rw [defect_vtx_apply, Equiv.symm_apply_apply]

/-- A member isomorphism is a datum isomorphism whose defect is trivial. -/
theorem defect_slot_eq_self (iso : GeometricMemberIso first second) (e : Fin p) :
    (defect iso.datum).slot e = e := by
  rw [defect_slot_apply, iso.overCore_row, Equiv.apply_symm_apply]

theorem defect_vtx_eq_self (iso : GeometricMemberIso first second) (v : Fin n) :
    (defect iso.datum).vtx v = v := by
  rw [defect_vtx_apply, iso.overCore_vertex, Equiv.apply_symm_apply]

/-- ... and conversely. -/
def memberIso_of_defect_trivial (i : GeometricDatumIso first.data second.data)
    (hs : ∀ e, (defect i).slot e = e) (hv : ∀ v, (defect i).vtx v = v) :
    GeometricMemberIso first second where
  datum := i
  overCore_vertex b := by rw [← defect_vtx_branch i b, hv]
  overCore_row path := by rw [← defect_slot_row i path, hs]

/-- **Equality of classes, with the defect made visible.** -/
theorem cls_eq_iff_exists_trivial_defect :
    GeometricFibre.cls first = GeometricFibre.cls second ↔
      ∃ i : GeometricDatumIso first.data second.data,
        (∀ e, (defect i).slot e = e) ∧ (∀ v, (defect i).vtx v = v) := by
  constructor
  · intro h
    obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp h
    exact ⟨iso.datum, defect_slot_eq_self iso, defect_vtx_eq_self iso⟩
  · rintro ⟨i, hs, hv⟩
    exact GeometricFibre.cls_eq_cls_iff.mpr ⟨memberIso_of_defect_trivial i hs hv⟩

/-- **The core diagonal transports along an arbitrary datum isomorphism, moved
by the defect.**

This is `Count.coreDiag_eq_of_geometricIso` with the two `overCore`
hypotheses removed -- what they buy is exactly that the defect is trivial -- and
it needs **no hypothesis on the request**, because it goes through the length
matrix rather than through the coordinates.  Both members must be diagonal: it
is diagonality that forces the row and column dictionaries of the transported
labelling to agree. -/
theorem coreDiag_eq_defect (h₁ : first.Diagonal) (h₂ : second.Diagonal)
    (i : GeometricDatumIso first.data second.data) (slot : Fin p) :
    second.coreDiag slot = first.coreDiag ((defect i).slot.symm slot) := by
  classical
  set transported := GeometricMultiplicity.transportLabelling i
    first.fullDim.valid.1 first.fullDim.labelling with htrans
  set ρ : Fin p ≃ Fin p := second.fullDim.labelling.row.symm.trans transported.row with hρ
  set γ : Fin p ≃ Fin p :=
    second.fullDim.labelling.targetEdge.trans transported.targetEdge.symm with hγ
  have hsub : second.matrix = first.matrix.submatrix ρ γ := by
    show GluingDatum.LengthMatrixPresentation.matrix second.fullDim.labelling.presentation =
      (GluingDatum.LengthMatrixPresentation.matrix
        first.fullDim.labelling.presentation).submatrix ρ γ
    rw [matrix_labelling_submatrix second.fullDim.labelling transported, hρ, hγ,
      GeometricMultiplicity.matrix_transportLabelling i first.fullDim.valid.1
        first.fullDim.labelling]
  have hργ : ∀ r : Fin p, ρ r = γ r := by
    intro r
    by_contra hne
    refine h₂.matrix_diag_ne_zero r ?_
    rw [hsub, Matrix.submatrix_apply]
    exact h₁ (ρ r) (γ r) (Ne.symm hne)
  have hrowsym : ∀ r : Fin p, first.fullDim.labelling.row.symm (ρ r) =
      (i.stablePathEquiv first.fullDim.valid.1).symm
        (second.fullDim.labelling.row.symm r) := by
    intro r
    rw [hρ, htrans]
    simp [GeometricMultiplicity.transportLabelling]
  have hslot : ∀ r : Fin p, (defect i).slot (first.slotMap (ρ r)) = second.slotMap r := by
    intro r
    show (defect i).slot (first.ident.row (first.fullDim.labelling.row.symm (ρ r))) = _
    rw [defect_slot_row, hrowsym r, Equiv.apply_symm_apply]
    rfl
  set r : Fin p := second.slotMap.symm slot with hr
  have hkey : first.slotMap (ρ r) = (defect i).slot.symm slot := by
    have hx : (defect i).slot (first.slotMap (ρ r)) = slot := by
      rw [hslot r, hr, Equiv.apply_symm_apply]
    rw [← hx, Equiv.symm_apply_apply]
  show second.matrix (second.slotMap.symm slot) (second.slotMap.symm slot) = _
  rw [← hr, hsub, Matrix.submatrix_apply, ← hργ r, ← hkey]
  show first.matrix (ρ r) (ρ r) =
    first.matrix (first.slotMap.symm (first.slotMap (ρ r)))
      (first.slotMap.symm (first.slotMap (ρ r)))
  rw [Equiv.symm_apply_apply]

/-- **`Count.coreDiag_eq_of_geometricIso`, with its hypothesis on the
request removed.**  That lemma carries `∀ slot, y slot ≠ 0` because it recovers
the diagonal from the coordinates by division; going through the length matrix
instead, the hypothesis is unnecessary. -/
theorem coreDiag_eq_of_geometricIso_of_diagonal (h₁ : first.Diagonal) (h₂ : second.Diagonal)
    (iso : GeometricMemberIso first second) : first.coreDiag = second.coreDiag := by
  funext slot
  have hfix : (defect iso.datum).slot.symm slot = slot := by
    apply (defect iso.datum).slot.injective
    rw [Equiv.apply_symm_apply, defect_slot_eq_self iso]
  rw [coreDiag_eq_defect h₁ h₂ iso.datum slot, hfix]

/-- **The defect of any datum isomorphism between two diagonal members with the
same core diagonal stabilises that diagonal.**  So the core symmetries that
`realizes_of_coreDiagRigid` asks about are exactly the ones that can appear. -/
theorem defect_stabilises_coreDiag (h₁ : first.Diagonal) (h₂ : second.Diagonal)
    (i : GeometricDatumIso first.data second.data) (heq : first.coreDiag = second.coreDiag)
    (slot : Fin p) :
    first.coreDiag ((defect i).slot.symm slot) = first.coreDiag slot := by
  rw [← coreDiag_eq_defect h₁ h₂ i slot, heq]

/-- **Correcting a datum isomorphism to be over the core.**  If the first
member's own gluing datum realises the defect, the two members are in the same
class: precompose. -/
theorem cls_eq_of_realizes_defect (i : GeometricDatumIso first.data second.data)
    (hreal : Realizes (defect i) first) :
    GeometricFibre.cls first = GeometricFibre.cls second := by
  obtain ⟨a, hv, hs⟩ := hreal
  refine GeometricFibre.cls_eq_cls_iff.mpr ⟨?_⟩
  refine { datum := a.trans i, overCore_vertex := ?_, overCore_row := ?_ }
  · intro b
    rw [GeometricDatumIso.branchVertexEquiv_trans a i first.fullDim.valid.1
      first.fullDim.valid.1, Equiv.trans_apply]
    have hb := hv b
    rw [defect_vtx_branch] at hb
    exact hb
  · intro path
    rw [GeometricDatumIso.stablePathEquiv_trans a i first.fullDim.valid.1
      first.fullDim.valid.1, Equiv.trans_apply]
    have hp := hs path
    rw [defect_slot_row] at hp
    exact hp

end Defect

/-! ## 6.  The reduction: `CoreDiagRigid` is a supply and a realization, and nothing else -/

/-- **(A) Datum supply.**  Two open odd members with the same core diagonal have
abstractly isomorphic gluing data.  This is the classification of combinatorial
types by the slope data; it is not proved here. -/
def DatumIsoSupply (c : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ first second : FibreMember c y degree,
    first.Open → first.HasOddMult → second.Open → second.HasOddMult →
      first.coreDiag = second.coreDiag → Nonempty (GeometricDatumIso first.data second.data)

/-- **(B) Symmetry realisation.**  Every incidence-preserving core symmetry stabilising an
open odd member's core diagonal is realised by a self-isomorphism of that
member's gluing datum.  This is a statement about the automorphism group of the
source; it is not proved here either. -/
def SymmetryRealized (c : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ m : FibreMember c y degree, m.Open → m.HasOddMult →
    ∀ d : Relabel c c, (∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot) → Realizes d m

/-- **The reduction of `CoreDiagRigid`, as an equivalence.**  Over a fibre whose open
odd members are all diagonal, `CoreDiagRigid` is exactly the conjunction of (A) and (B)
above.  Neither implication loses anything, so this is a complete answer to what the
uniqueness in `prop-caterpillar-ballot`(2) reduces to. -/
theorem coreDiagRigid_iff
    (hdiag : ∀ mem : FibreMember c y degree, mem.Open → mem.HasOddMult → mem.Diagonal) :
    CoreDiagRigid c y degree ↔ DatumIsoSupply c y degree ∧ SymmetryRealized c y degree := by
  constructor
  · intro hrigid
    refine ⟨?_, ?_⟩
    · intro first second hO₁ hM₁ hO₂ hM₂ heq
      obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp (hrigid first second hO₁ hM₁ hO₂ hM₂ heq)
      exact ⟨iso.datum⟩
    · intro m hOpen hOdd d hstab
      exact realizes_of_coreDiagRigid hrigid m hOpen hOdd (hdiag m hOpen hOdd) d hstab
  · rintro ⟨hsupply, hrealize⟩ first second hO₁ hM₁ hO₂ hM₂ heq
    obtain ⟨i⟩ := hsupply first second hO₁ hM₁ hO₂ hM₂ heq
    exact cls_eq_of_realizes_defect i
      (hrealize first hO₁ hM₁ (defect i)
        (defect_stabilises_coreDiag (hdiag first hO₁ hM₁) (hdiag second hO₂ hM₂) i heq))

end DraismaVargas.Count.SlopeRigidity
