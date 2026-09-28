import DraismaVargasCount.GeometricMultiplicity
import DraismaVargasCount.FibreNormalForm

/-!
# The orientation-independent labelled fibre

`GeometricMemberIso` uses the actual geometric source dictionary over the fixed
core. Coordinates and multiplicity are derived, not isomorphism fields.
`GeometricFibre` is finite: the finite strict fibre `Fibre` surjects onto it.
This transfers finiteness, not cardinality or parity. The counting, segment and
labelled-metric star arguments over this fibre are in `GeometricCount`,
`GeometricSegmentWalls` and `GeometricStar`; the strict fibre is kept for its
finite normal-form cover.

`GeometricFibre.openOddCount core y 4` is the number whose parity the genus-six
count controls (`Assembly`).
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- An orientation-independent isomorphism over the fixed labelled core.
No arbitrary stable dictionary, matrix equality or coordinate receipt is stored. -/
structure GeometricMemberIso (first second : FibreMember core y degree) where
  datum : GeometricDatumIso first.data second.data
  overCore_vertex : ∀ branch : BranchVertex first.data,
    second.ident.vertex (datum.branchVertexEquiv first.fullDim.valid.1 branch) =
      first.ident.vertex branch
  overCore_row : ∀ path : StablePath first.data,
    second.ident.row (datum.stablePathEquiv first.fullDim.valid.1 path) =
      first.ident.row path

namespace GeometricMemberIso

variable {first second third : FibreMember core y degree}

def refl (member : FibreMember core y degree) : GeometricMemberIso member member where
  datum := GeometricDatumIso.refl member.data
  overCore_vertex branch := by
    rw [GeometricDatumIso.branchVertexEquiv_refl, Equiv.refl_apply]
  overCore_row path := by
    rw [GeometricDatumIso.stablePathEquiv_refl, Equiv.refl_apply]

def symm (iso : GeometricMemberIso first second) : GeometricMemberIso second first where
  datum := iso.datum.symm
  overCore_vertex branch := by
    rw [GeometricDatumIso.branchVertexEquiv_symm iso.datum first.fullDim.valid.1
      second.fullDim.valid.1]
    have h := iso.overCore_vertex
      ((iso.datum.branchVertexEquiv first.fullDim.valid.1).symm branch)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  overCore_row path := by
    rw [GeometricDatumIso.stablePathEquiv_symm iso.datum first.fullDim.valid.1
      second.fullDim.valid.1]
    have h := iso.overCore_row
      ((iso.datum.stablePathEquiv first.fullDim.valid.1).symm path)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

def trans (left : GeometricMemberIso first second) (right : GeometricMemberIso second third) :
    GeometricMemberIso first third where
  datum := left.datum.trans right.datum
  overCore_vertex branch := by
    rw [GeometricDatumIso.branchVertexEquiv_trans left.datum right.datum
      first.fullDim.valid.1 second.fullDim.valid.1, Equiv.trans_apply,
      right.overCore_vertex, left.overCore_vertex]
  overCore_row path := by
    rw [GeometricDatumIso.stablePathEquiv_trans left.datum right.datum
      first.fullDim.valid.1 second.fullDim.valid.1, Equiv.trans_apply,
      right.overCore_row, left.overCore_row]

/-- Strict isomorphisms embed with precisely their existing core dictionaries. -/
def ofStrict (iso : MemberIso first second) : GeometricMemberIso first second where
  datum := GeometricDatumIso.ofStrict iso.datum
  overCore_vertex := iso.overCore_vertex
  overCore_row := iso.overCore_row

def column (iso : GeometricMemberIso first second) : Fin p ≃ Fin p :=
  first.fullDim.labelling.targetEdge.trans
    (iso.datum.targetEdge.trans second.fullDim.labelling.targetEdge.symm)

/-- Coordinate compatibility follows from the actual realization equations. -/
theorem coords_column (iso : GeometricMemberIso first second) (slot : Fin p) :
    second.coords (iso.column slot) = first.coords slot :=
  GeometricMultiplicity.coords_eq_of_datumIso_member iso.datum iso.overCore_row slot

theorem open_iff (iso : GeometricMemberIso first second) : first.Open ↔ second.Open := by
  constructor
  · intro h slot
    have hCoords := iso.coords_column (iso.column.symm slot)
    rw [Equiv.apply_symm_apply] at hCoords
    rw [hCoords]
    exact h _
  · intro h slot
    rw [← iso.coords_column slot]
    exact h _

theorem closed_iff (iso : GeometricMemberIso first second) : first.Closed ↔ second.Closed := by
  constructor
  · intro h slot
    have hCoords := iso.coords_column (iso.column.symm slot)
    rw [Equiv.apply_symm_apply] at hCoords
    rw [hCoords]
    exact h _
  · intro h slot
    rw [← iso.coords_column slot]
    exact h _

theorem absMult_eq (iso : GeometricMemberIso first second) : first.absMult = second.absMult :=
  (GeometricMultiplicity.fdAbsMult_eq_of_datumIso iso.datum first.fullDim second.fullDim).symm

theorem oddMult_eq (iso : GeometricMemberIso first second) : first.oddMult = second.oddMult := by
  have h := iso.absMult_eq
  rw [FibreMember.absMult_eq_oddMult, FibreMember.absMult_eq_oddMult] at h
  exact_mod_cast h

theorem hasOddMult_iff (iso : GeometricMemberIso first second) :
    first.HasOddMult ↔ second.HasOddMult := by
  simp only [FibreMember.HasOddMult, iso.absMult_eq]

/-- Every actual geometric transport gives an isomorphism over the same core. -/
noncomputable def transport (member : FibreMember core y degree)
    {target : CFGraph.{0}} {data : GluingDatum target degree}
    (iso : GeometricDatumIso member.data data) :
    GeometricMemberIso member (GeometricMultiplicity.transportMember member iso) where
  datum := iso
  overCore_vertex branch := by
    show (GeometricMultiplicity.transportIdent iso member.fullDim.valid.1 member.ident).vertex
      (iso.branchVertexEquiv member.fullDim.valid.1 branch) = _
    simp [GeometricMultiplicity.transportIdent]
  overCore_row path := by
    show (GeometricMultiplicity.transportIdent iso member.fullDim.valid.1 member.ident).row
      (iso.stablePathEquiv member.fullDim.valid.1 path) = _
    simp [GeometricMultiplicity.transportIdent]

end GeometricMemberIso

def geometricMemberSetoid (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Setoid (FibreMember core y degree) where
  r first second := Nonempty (GeometricMemberIso first second)
  iseqv := ⟨fun m ↦ ⟨GeometricMemberIso.refl m⟩,
    fun ⟨iso⟩ ↦ ⟨iso.symm⟩, fun ⟨left⟩ ⟨right⟩ ↦ ⟨left.trans right⟩⟩

/-- The geometric fibre: fibre members up to geometric isomorphism (`GeometricMemberIso`). It is
coarser than the strict fibre `Fibre`, which also distinguishes stored orientations (`ofStrict`). -/
def GeometricFibre (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Type 1 :=
  Quotient (geometricMemberSetoid core y degree)

namespace GeometricFibre

def cls (member : FibreMember core y degree) : GeometricFibre core y degree :=
  Quotient.mk (geometricMemberSetoid core y degree) member

theorem cls_eq_cls_iff {first second : FibreMember core y degree} :
    cls first = cls second ↔ Nonempty (GeometricMemberIso first second) :=
  Quotient.eq (r := geometricMemberSetoid core y degree)

theorem cls_surjective : Function.Surjective (cls (core := core) (y := y) (degree := degree)) :=
  Quotient.mk_surjective

theorem cls_transport (member : FibreMember core y degree)
    {target : CFGraph.{0}} {data : GluingDatum target degree}
    (iso : GeometricDatumIso member.data data) :
    cls (GeometricMultiplicity.transportMember member iso) = cls member :=
  cls_eq_cls_iff.mpr ⟨(GeometricMemberIso.transport member iso).symm⟩

/-- Forget stored orientation distinctions. This need not be injective. -/
def ofStrict (old : Fibre core y degree) : GeometricFibre core y degree :=
  Quotient.liftOn old cls fun _ _ h ↦
    h.elim fun iso ↦ cls_eq_cls_iff.mpr ⟨GeometricMemberIso.ofStrict iso⟩

@[simp] theorem ofStrict_cls (member : FibreMember core y degree) :
    ofStrict member.cls = cls member := rfl

theorem ofStrict_surjective :
    Function.Surjective (ofStrict (core := core) (y := y) (degree := degree)) := by
  intro c
  obtain ⟨member, rfl⟩ := cls_surjective c
  exact ⟨member.cls, rfl⟩

/-- The geometric fibre is a quotient of the finite strict fibre, hence finite. -/
instance instFinite (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Finite (GeometricFibre core y degree) :=
  Finite.of_surjective ofStrict ofStrict_surjective

noncomputable instance instFintype (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Fintype (GeometricFibre core y degree) := Fintype.ofFinite _

theorem card_le_strict :
    Fintype.card (GeometricFibre core y degree) ≤ Fintype.card (Fibre core y degree) :=
  Fintype.card_le_of_surjective ofStrict ofStrict_surjective

def Open (c : GeometricFibre core y degree) : Prop :=
  Quotient.liftOn c FibreMember.Open fun _ _ h ↦ h.elim fun iso ↦ propext iso.open_iff

def Closed (c : GeometricFibre core y degree) : Prop :=
  Quotient.liftOn c FibreMember.Closed fun _ _ h ↦ h.elim fun iso ↦ propext iso.closed_iff

noncomputable def absMult (c : GeometricFibre core y degree) : ℚ :=
  Quotient.liftOn c FibreMember.absMult fun _ _ h ↦ h.elim fun iso ↦ iso.absMult_eq

noncomputable def multNat (c : GeometricFibre core y degree) : ℕ :=
  Quotient.liftOn c FibreMember.oddMult fun _ _ h ↦ h.elim fun iso ↦ iso.oddMult_eq

def IsOdd (c : GeometricFibre core y degree) : Prop := Odd c.multNat

@[simp] theorem open_cls (member : FibreMember core y degree) : Open (cls member) ↔ member.Open :=
  Iff.rfl

@[simp] theorem closed_cls (member : FibreMember core y degree) :
    Closed (cls member) ↔ member.Closed := Iff.rfl

@[simp] theorem absMult_cls (member : FibreMember core y degree) :
    absMult (cls member) = member.absMult := rfl

@[simp] theorem multNat_cls (member : FibreMember core y degree) :
    multNat (cls member) = member.oddMult := rfl

theorem isOdd_cls_iff (member : FibreMember core y degree) :
    IsOdd (cls member) ↔ member.HasOddMult :=
  (hasOddMult_iff_odd_oddMult member).symm

theorem absMult_eq_multNat (c : GeometricFibre core y degree) : c.absMult = c.multNat := by
  obtain ⟨member, rfl⟩ := cls_surjective c
  exact member.absMult_eq_oddMult

/-- The number of classes of odd multiplicity: a finite count, not a parity assertion. -/
noncomputable def oddCount (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : ℕ :=
  Nat.card {c : GeometricFibre core y degree // c.IsOdd}

/-- The number of open classes of odd multiplicity, the quantity of the generic count. No parity
is asserted here. -/
noncomputable def openOddCount (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : ℕ :=
  Nat.card {c : GeometricFibre core y degree // c.Open ∧ c.IsOdd}

end GeometricFibre
end DraismaVargas.Count
