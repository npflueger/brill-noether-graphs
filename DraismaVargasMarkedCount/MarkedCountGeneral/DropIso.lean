module

public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame

@[expose] public section

/-!
# The drop lemma: the algebra of typed frame isomorphisms

`TypedFrameClass` is a `Quot` by `Nonempty (TypedFrameIso _ _)`, which is not a priori an
equivalence relation. This module proves that it is one (`TypedFrameIso.refl`, `symm`, `trans`,
built from the public `GeometricDatumIso.refl`, `symm`, `trans`), so that equality of classes is
isomorphism of representatives (`TypedFrameClass.mk_eq_mk_iff`). The drop lemma compares classes
through it.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

/-! ## 1.  Source dictionaries of the inverse and the composite -/

section Dictionaries

variable {target₁ target₂ target₃ : CFGraph} {first : GluingDatum target₁ degree}
  {second : GluingDatum target₂ degree} {third : GluingDatum target₃ degree}

/-- The source-vertex dictionary of the inverse is the inverse dictionary. -/
theorem GeometricDatumIso.sourceVertexEquiv_symm' (iso : GeometricDatumIso first second)
    (vertex : second.SourceVertex) :
    iso.symm.sourceVertexEquiv vertex = iso.sourceVertexEquiv.symm vertex := rfl

/-- The source-edge dictionary of the inverse is the inverse dictionary. -/
theorem GeometricDatumIso.sourceEdgeEquiv_symm' (iso : GeometricDatumIso first second)
    (edge : second.SourceEdge) :
    iso.symm.sourceEdgeEquiv edge = iso.sourceEdgeEquiv.symm edge := rfl

/-- The source-vertex dictionary of a composite is the composite dictionary. -/
theorem GeometricDatumIso.sourceVertexEquiv_trans' (left : GeometricDatumIso first second)
    (right : GeometricDatumIso second third) (vertex : first.SourceVertex) :
    (left.trans right).sourceVertexEquiv vertex =
      right.sourceVertexEquiv (left.sourceVertexEquiv vertex) := rfl

/-- The source-edge dictionary of a composite is the composite dictionary. -/
theorem GeometricDatumIso.sourceEdgeEquiv_trans' (left : GeometricDatumIso first second)
    (right : GeometricDatumIso second third) (edge : first.SourceEdge) :
    (left.trans right).sourceEdgeEquiv edge =
      right.sourceEdgeEquiv (left.sourceEdgeEquiv edge) := rfl

/-- The source-vertex dictionary of the identity is the identity. -/
theorem GeometricDatumIso.sourceVertexEquiv_refl' (data : GluingDatum target₁ degree)
    (vertex : data.SourceVertex) :
    (GeometricDatumIso.refl data).sourceVertexEquiv vertex = vertex := rfl

/-- The source-edge dictionary of the identity is the identity. -/
theorem GeometricDatumIso.sourceEdgeEquiv_refl' (data : GluingDatum target₁ degree)
    (edge : data.SourceEdge) :
    (GeometricDatumIso.refl data).sourceEdgeEquiv edge = edge := rfl

end Dictionaries

/-! ## 2.  Identity, inverse, composite -/

namespace TypedFrameIso

variable {κ₁ κ₂ κ₃ : TypedFrame core mark types degree}

/-- **The identity isomorphism.** -/
noncomputable def refl (κ : TypedFrame core mark types degree) : TypedFrameIso κ κ where
  datum := GeometricDatumIso.refl κ.data
  mark _ := rfl
  overCore_vertex _ _ := rfl
  overCore_row _ := rfl

/-- **The inverse isomorphism.** -/
noncomputable def symm (iso : TypedFrameIso κ₁ κ₂) : TypedFrameIso κ₂ κ₁ where
  datum := iso.datum.symm
  mark j := by
    rw [GeometricDatumIso.sourceVertexEquiv_symm', Equiv.symm_apply_eq]
    exact (iso.mark j).symm
  overCore_vertex vertex hImage := by
    have hBack : iso.datum.sourceVertexEquiv (iso.datum.symm.sourceVertexEquiv vertex.1) =
        vertex.1 := by
      rw [GeometricDatumIso.sourceVertexEquiv_symm', Equiv.apply_symm_apply]
    have h := iso.overCore_vertex ⟨iso.datum.symm.sourceVertexEquiv vertex.1, hImage⟩
      (by rw [hBack]; exact vertex.2)
    have hEq : (⟨iso.datum.sourceVertexEquiv (iso.datum.symm.sourceVertexEquiv vertex.1),
        by rw [hBack]; exact vertex.2⟩ : MarkedBranchVertex κ₂.data (markSet κ₂.markSource)) =
          vertex := Subtype.ext hBack
    rw [hEq] at h
    exact h.symm
  overCore_row edge := by
    have h := iso.overCore_row (iso.datum.symm.nonDanglingEdgeEquiv κ₂.fullDim.valid.1 edge)
    have hBack : iso.datum.nonDanglingEdgeEquiv κ₁.fullDim.valid.1
        (iso.datum.symm.nonDanglingEdgeEquiv κ₂.fullDim.valid.1 edge) = edge := by
      apply Subtype.ext
      rw [GeometricDatumIso.nonDanglingEdgeEquiv_val, GeometricDatumIso.nonDanglingEdgeEquiv_val,
        GeometricDatumIso.sourceEdgeEquiv_symm', Equiv.apply_symm_apply]
    rw [hBack] at h
    exact h.symm

/-- **The composite isomorphism.** -/
noncomputable def trans (left : TypedFrameIso κ₁ κ₂) (right : TypedFrameIso κ₂ κ₃) :
    TypedFrameIso κ₁ κ₃ where
  datum := left.datum.trans right.datum
  mark j := by
    rw [GeometricDatumIso.sourceVertexEquiv_trans', left.mark j, right.mark j]
  overCore_vertex vertex hImage := by
    have hMid : 3 ≤ nonDanglingValency κ₂.data (left.datum.sourceVertexEquiv vertex.1) ∨
        left.datum.sourceVertexEquiv vertex.1 ∈ markSet κ₂.markSource := by
      rcases vertex.2 with h | h
      · left
        rw [GeometricDatumIso.nonDanglingValency_map left.datum κ₁.fullDim.valid.1]
        exact h
      · right
        exact (left.mem_markSet_map vertex.1).mpr h
    have h₁ := left.overCore_vertex vertex hMid
    have h₂ := right.overCore_vertex ⟨left.datum.sourceVertexEquiv vertex.1, hMid⟩ hImage
    exact h₂.trans h₁
  overCore_row edge := by
    have h₁ := left.overCore_row edge
    have h₂ := right.overCore_row (left.datum.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 edge)
    refine Eq.trans ?_ (h₂.trans h₁)
    rfl

end TypedFrameIso

/-! ## 3.  Classes -/

namespace TypedFrameClass

/-- The isomorphism relation is closed under its equivalence closure. -/
theorem nonempty_iso_of_eqvGen {κ₁ κ₂ : TypedFrame core mark types degree}
    (h : Relation.EqvGen (fun first second : TypedFrame core mark types degree ↦
      Nonempty (TypedFrameIso first second)) κ₁ κ₂) : Nonempty (TypedFrameIso κ₁ κ₂) := by
  induction h with
  | rel _ _ h => exact h
  | refl κ => exact ⟨TypedFrameIso.refl κ⟩
  | symm _ _ _ ih => exact ih.elim fun iso ↦ ⟨iso.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.elim fun i₁ ↦ ih₂.elim fun i₂ ↦ ⟨i₁.trans i₂⟩

/-- **Equal classes are isomorphic frames**: the relation is an equivalence. -/
theorem mk_eq_mk_iff {κ₁ κ₂ : TypedFrame core mark types degree} :
    mk κ₁ = mk κ₂ ↔ Nonempty (TypedFrameIso κ₁ κ₂) :=
  ⟨fun h ↦ nonempty_iso_of_eqvGen (Quot.eqvGen_exact h), mk_eq_mk_of_iso⟩

end TypedFrameClass

end DraismaVargas.Count.MarkedCountGeneral
