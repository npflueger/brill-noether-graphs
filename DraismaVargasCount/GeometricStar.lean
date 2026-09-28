import DraismaVargasCount.GeometricInheritedBranches
import DraismaVargasCount.InheritedLimitIncidence

/-!
# The geometric star of an inherited labelled metric limit

Specialization retains the actual inherited branch and row labels at a positive
source request. Target metric preservation is a theorem of row-label preservation,
not an additional field. Facets are quotiented by geometric over-core frame
isomorphisms; the resulting star injects into the actual geometric fibre.

The strict, unlabelled star `WallStar.Star` is a different object and is not the
count used here. Nothing identifies its cardinality or parity with this star.
-/

namespace DraismaVargas.Count.GeometricStar

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open W4StableSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open GeometricSegmentWalls (FrameIso)
open InheritedLimitRows (limit_connected)
open InheritedLimitIncidence (coreIdentification)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- Isomorphism of the actual inherited labelled limits. The dictionaries
used here are constructed from contraction, not supplied as arbitrary bijections. -/
structure LimitIso (hy : Nondegenerate y) (first second : Regrowth core y degree) where
  datum : GeometricDatumIso first.limit second.limit
  overCore_vertex : ∀ branch : BranchVertex first.limit,
    (coreIdentification second hy).vertex (datum.branchVertexEquiv (limit_connected first) branch) =
      (coreIdentification first hy).vertex branch
  overCore_row : ∀ row : StablePath first.limit,
    (coreIdentification second hy).row (datum.stablePathEquiv (limit_connected first) row) =
      (coreIdentification first hy).row row

namespace LimitIso

variable {hy : Nondegenerate y} {first second third : Regrowth core y degree}

noncomputable def refl (hy : Nondegenerate y) (first : Regrowth core y degree) :
    LimitIso hy first first where
  datum := GeometricDatumIso.refl _
  overCore_vertex branch := by
    rw [GeometricDatumIso.branchVertexEquiv_refl, Equiv.refl_apply]
  overCore_row row := by
    rw [GeometricDatumIso.stablePathEquiv_refl, Equiv.refl_apply]

noncomputable def symm (iso : LimitIso hy first second) : LimitIso hy second first where
  datum := iso.datum.symm
  overCore_vertex branch := by
    rw [GeometricDatumIso.branchVertexEquiv_symm iso.datum
      (limit_connected first) (limit_connected second)]
    have h := iso.overCore_vertex
      ((iso.datum.branchVertexEquiv (limit_connected first)).symm branch)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  overCore_row row := by
    rw [GeometricDatumIso.stablePathEquiv_symm iso.datum
      (limit_connected first) (limit_connected second)]
    have h := iso.overCore_row
      ((iso.datum.stablePathEquiv (limit_connected first)).symm row)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

noncomputable def trans (left : LimitIso hy first second) (right : LimitIso hy second third) :
    LimitIso hy first third where
  datum := left.datum.trans right.datum
  overCore_vertex branch := by
    rw [GeometricDatumIso.branchVertexEquiv_trans left.datum right.datum
      (limit_connected first) (limit_connected second), Equiv.trans_apply,
      right.overCore_vertex, left.overCore_vertex]
  overCore_row row := by
    rw [GeometricDatumIso.stablePathEquiv_trans left.datum right.datum
      (limit_connected first) (limit_connected second), Equiv.trans_apply,
      right.overCore_row, left.overCore_row]

/-- Label preservation at the fixed request forces preservation of the actual
surviving target lengths. -/
theorem metric (iso : LimitIso hy first second)
    (edge : (first.frame.limitTarget first.column).edges) :
    StarPilot.limitLength second (iso.datum.targetEdge edge) = StarPilot.limitLength first edge :=
  InheritedLimitRows.limitLength_map_of_labelledIso first hy second iso.datum iso.overCore_row edge

noncomputable def toMetric (iso : LimitIso hy first second) :
    GeometricLimitTransport.MetricLimitIso first second := ⟨iso.datum, iso.metric⟩

/-- Actual over-core frame transport preserves both inherited dictionaries. -/
noncomputable def ofFrameIso (hy : Nondegenerate y) (iso : FrameIso first.frame second.frame) :
    LimitIso hy first second :=
  ⟨GeometricLimitTransport.limitIso iso,
    GeometricInheritedBranches.branchLabel_limitIso hy iso,
    GeometricInheritedRows.rowLabel_limitIso hy iso⟩

end LimitIso

def SameLimit (hy : Nondegenerate y) (first second : Regrowth core y degree) : Prop :=
  Nonempty (LimitIso hy first second)

theorem sameLimit_equivalence (hy : Nondegenerate y) : Equivalence (SameLimit (core := core) (degree := degree) hy) where
  refl first := ⟨LimitIso.refl hy first⟩
  symm h := h.elim fun iso ↦ ⟨iso.symm⟩
  trans h h' := h.elim fun left ↦ h'.elim fun right ↦ ⟨left.trans right⟩

structure StarMember (hy : Nondegenerate y) (wall : Regrowth core y degree) where
  member : Regrowth core y degree
  specializes : SameLimit hy member wall

namespace StarMember

variable {hy : Nondegenerate y} {wall : Regrowth core y degree}

def Rel (first second : StarMember hy wall) : Prop :=
  Nonempty (FrameIso first.member.frame second.member.frame)

theorem rel_equivalence : Equivalence (Rel (hy := hy) (wall := wall)) where
  refl _ := ⟨FrameIso.refl _⟩
  symm h := h.elim fun iso ↦ ⟨iso.symm⟩
  trans h h' := h.elim fun left ↦ h'.elim fun right ↦ ⟨left.trans right⟩

/-- Specialization is saturated under the actual geometric over-core relation. -/
noncomputable def ofFrameIso (member : StarMember hy wall) (other : Regrowth core y degree)
    (iso : FrameIso other.frame member.member.frame) : StarMember hy wall :=
  ⟨other, member.specializes.elim fun limit ↦ ⟨(LimitIso.ofFrameIso hy iso).trans limit⟩⟩

end StarMember

def starSetoid (hy : Nondegenerate y) (wall : Regrowth core y degree) :
    Setoid (StarMember hy wall) := ⟨StarMember.Rel, StarMember.rel_equivalence⟩

def Star (hy : Nondegenerate y) (wall : Regrowth core y degree) := Quotient (starSetoid hy wall)

def StarMember.cls {hy : Nondegenerate y} {wall : Regrowth core y degree}
    (member : StarMember hy wall) : Star hy wall := Quotient.mk _ member

namespace Star

variable {hy : Nondegenerate y} {wall : Regrowth core y degree}

noncomputable def toFibre (star : Star hy wall) : GeometricFibre core y degree :=
  Quotient.liftOn star (fun member ↦ GeometricFibre.cls (member.member.frame.member y)) (by
    rintro first second ⟨iso⟩
    exact GeometricFibre.cls_eq_cls_iff.mpr ⟨iso.toMemberIso y⟩)

@[simp] theorem toFibre_cls (member : StarMember hy wall) :
    toFibre member.cls = GeometricFibre.cls (member.member.frame.member y) := rfl

theorem toFibre_injective : Function.Injective (toFibre (hy := hy) (wall := wall)) := by
  intro first second
  refine Quotient.inductionOn₂ first second ?_
  intro a b h
  obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp h
  exact Quotient.sound ⟨FrameIso.ofMemberIso iso⟩

instance instFinite : Finite (Star hy wall) := Finite.of_injective _ toFibre_injective

noncomputable instance instFintype : Fintype (Star hy wall) := Fintype.ofFinite _

def self (hy : Nondegenerate y) (wall : Regrowth core y degree) : StarMember hy wall :=
  ⟨wall, ⟨LimitIso.refl hy wall⟩⟩

instance instNonempty : Nonempty (Star hy wall) := ⟨(self hy wall).cls⟩

theorem closed (star : Star hy wall) : (toFibre star).Closed := by
  refine Quotient.inductionOn star ?_
  exact fun member ↦ member.member.closed

theorem not_open (star : Star hy wall) : ¬ (toFibre star).Open := by
  refine Quotient.inductionOn star ?_
  exact fun member ↦ member.member.not_open

end Star

/-- Membership in the geometric star is actual labelled-metric
specialization, on geometric fibre classes. -/
def IsStarClass (hy : Nondegenerate y) (wall : Regrowth core y degree)
    (cls : GeometricFibre core y degree) : Prop :=
  ∃ member : StarMember hy wall, GeometricFibre.cls (member.member.frame.member y) = cls

noncomputable def Star.equivSubtype (hy : Nondegenerate y) (wall : Regrowth core y degree) :
    Star hy wall ≃ {cls : GeometricFibre core y degree // IsStarClass hy wall cls} :=
  Equiv.ofBijective (fun star ↦ ⟨Star.toFibre star, by
    refine Quotient.inductionOn star ?_
    exact fun member ↦ ⟨member, rfl⟩⟩)
    ⟨fun _ _ h ↦ Star.toFibre_injective (congrArg Subtype.val h), by
      rintro ⟨cls, member, hMember⟩
      exact ⟨member.cls, Subtype.ext hMember⟩⟩

/-- Specialization can be checked on any representative frame of the class. -/
theorem isStarClass_frame_iff (hy : Nondegenerate y) (wall : Regrowth core y degree)
    (frame : SegmentWalls.Frame core degree) :
    IsStarClass hy wall (GeometricFibre.cls (frame.member y)) ↔
      ∃ col, ∃ h : frame.DegenerateAt y col,
        SameLimit hy (⟨frame, col, h⟩ : Regrowth core y degree) wall := by
  constructor
  · rintro ⟨member, hClass⟩
    obtain ⟨memberIso⟩ := GeometricFibre.cls_eq_cls_iff.mp hClass
    let iso : FrameIso member.member.frame frame := FrameIso.ofMemberIso memberIso
    have hDeg := iso.degenerateAt_map member.member.degenerate
    refine ⟨iso.column member.member.column, hDeg, ?_⟩
    exact (member.ofFrameIso ⟨frame, iso.column member.member.column, hDeg⟩ iso.symm).specializes
  · rintro ⟨col, hDeg, hLimit⟩
    exact ⟨⟨⟨frame, col, hDeg⟩, hLimit⟩, rfl⟩

end DraismaVargas.Count.GeometricStar
