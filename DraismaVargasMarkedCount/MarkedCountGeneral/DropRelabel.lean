module

public import DraismaVargasMarkedCount.MarkedCountGeneral.NilFrame
public import DraismaVargasCount.CoreRelabelInvariance

@[expose] public section

/-!
# Typed counts are relabelling invariants

The content of `Drop.typedCount_relabel`.

A relabelling `r : Relabel c c'` of the core, a permutation `σ` of the marks with
`r.vtx (mark j) = mark' (σ j)`, and types with `types' (σ j) = types j` carry a typed frame over
`(c, mark, types)` to one over `(c', mark', types')` (`relabelFrame`): the target and the datum are
kept, the marks are reindexed by `σ` (`markSource ∘ σ.symm`, whose mark set has the same members,
so the receipts move by `NilFrame`'s `MarkedFullDim.congrMarks`), and the identification is
composed with `r`. The marked matrix is unchanged, the slots are permuted by `r.slot`
(`relabelFrame_slot`), so the coordinates at `y' = y ∘ r.slot⁻¹` are the old ones at `y`
(`coordsAt_relabelFrame`), and the ramified leaf images do not move. It is the typed twin of
`CoreRelabel.relabelEquiv`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.CoreRelabel (Relabel)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ}

/-- Reindexing the marks by a permutation keeps the members of the mark set. -/
theorem mem_markSet_comp_symm {target : CFGraph} {data : GluingDatum target degree}
    (σ : Fin k ≃ Fin k) (markSource : Fin k → data.SourceVertex) (v : data.SourceVertex) :
    v ∈ markSet markSource ↔ v ∈ markSet (markSource ∘ σ.symm) := by
  simp only [markSet, Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨σ j, by rw [σ.symm_apply_apply]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨σ.symm j, rfl⟩

/-- The type excess is a permutation invariant. -/
theorem typeExcess_perm (σ : Fin k ≃ Fin k) {types types' : Fin k → ℕ}
    (hTypes : ∀ j, types' (σ j) = types j) : typeExcess types = typeExcess types' := by
  unfold typeExcess
  rw [← σ.sum_comp (fun j ↦ ((types' j : ℤ) - 1))]
  simp only [hTypes]

section Relabel

variable {c c' : Core n p} (r : Relabel c c') {mark mark' : Fin k → Fin n} (σ : Fin k ≃ Fin k)
  (hMark : ∀ j, r.vtx (mark j) = mark' (σ j)) {types types' : Fin k → ℕ}
  (hTypes : ∀ j, types' (σ j) = types j)

include hMark hTypes in
/-- **A typed frame, relabelled.** Target and datum are kept; the marks are reindexed by `σ`;
the identification is composed with `r`. -/
def relabelFrame (κ : TypedFrame c mark types degree) : TypedFrame c' mark' types' degree where
  target := κ.target
  data := κ.data
  markSource := κ.markSource ∘ σ.symm
  fullDim := κ.fullDim.congrMarks (mem_markSet_comp_symm σ κ.markSource)
    (typeExcess_perm σ hTypes)
  ident :=
    { vertex := (markedBranchVertexCongr (mem_markSet_comp_symm σ κ.markSource)).symm.trans
        (κ.ident.vertex.trans r.vtx)
      row := (markedStablePathCongr (mem_markSet_comp_symm σ κ.markSource)).symm.trans
        (κ.ident.row.trans r.slot)
      incidence := fun branch slot ↦ by
        simp only [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.trans_apply]
        rw [markedIncidenceCount_congr]
        have h := κ.ident.incidence
          ((markedBranchVertexCongr (mem_markSet_comp_symm σ κ.markSource)).symm branch)
          (r.slot.symm slot)
        have key := r.incidence (κ.ident.vertex
          ((markedBranchVertexCongr (mem_markSet_comp_symm σ κ.markSource)).symm branch))
          (r.slot.symm slot)
        rw [Equiv.apply_symm_apply] at key
        rw [key]
        exact h
      vertex_mark := fun j ↦ by
        change r.vtx (κ.ident.vertex ⟨κ.markSource (σ.symm j),
          Or.inr (mem_markSet κ.markSource (σ.symm j))⟩) = mark' j
        rw [κ.ident.vertex_mark, hMark, σ.apply_symm_apply] }
  typed j := by
    have h := κ.typed (σ.symm j)
    rwa [← hTypes (σ.symm j), σ.apply_symm_apply] at h

variable (κ : TypedFrame c mark types degree)

theorem relabelFrame_matrix : (relabelFrame r σ hMark hTypes κ).matrix = κ.matrix := rfl

theorem relabelFrame_slot (row : Fin p) :
    (relabelFrame r σ hMark hTypes κ).slot row = r.slot (κ.slot row) := by
  simp [MarkedFrameBase.slot, relabelFrame, MarkedFullDim.congrMarks, labellingCongrMarks]

/-- **The coordinates of the relabelled frame at the relabelled request are the old ones.** -/
theorem coordsAt_relabelFrame {y y' : Fin p → ℚ} (hy : ∀ e, y' (r.slot e) = y e) :
    (relabelFrame r σ hMark hTypes κ).coordsAt y' = κ.coordsAt y := by
  unfold MarkedFrameBase.coordsAt
  simp only [relabelFrame_matrix, relabelFrame_slot, hy]

theorem ramifiedLeafImages_relabelFrame :
    (relabelFrame r σ hMark hTypes κ).ramifiedLeafImages = κ.ramifiedLeafImages := by
  classical
  unfold TypedFrame.ramifiedLeafImages
  congr 1
  ext x
  refine Finset.mem_image.trans (Iff.trans ?_ Finset.mem_image.symm)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hx⟩
    refine ⟨σ.symm j, ?_, hx⟩
    rwa [← hTypes (σ.symm j), σ.apply_symm_apply]
  · rintro ⟨j, hj, hx⟩
    refine ⟨σ j, ?_, ?_⟩
    · rwa [hTypes j]
    · change (κ.markSource (σ.symm (σ j))).1.1 = _
      rw [σ.symm_apply_apply, hx]

theorem typedAbsMult_relabelFrame :
    (relabelFrame r σ hMark hTypes κ).typedAbsMult = κ.typedAbsMult := by
  unfold TypedFrame.typedAbsMult TypedFrame.typedSignedMult TypedFrame.leafCountStar
  rw [ramifiedLeafImages_relabelFrame]
  rfl

/-- **Relabelling carries typed isomorphisms to typed isomorphisms**: the same datum isomorphism
serves. -/
def relabelIso {κ κ' : TypedFrame c mark types degree} (iso : TypedFrameIso κ κ') :
    TypedFrameIso (relabelFrame r σ hMark hTypes κ) (relabelFrame r σ hMark hTypes κ') where
  datum := iso.datum
  mark j := iso.mark (σ.symm j)
  overCore_vertex vertex hImage :=
    congrArg r.vtx (iso.overCore_vertex ⟨vertex.1, vertex.2.imp_right
      (mem_markSet_comp_symm σ κ.markSource vertex.1).mpr⟩
      (hImage.imp_right (mem_markSet_comp_symm σ κ'.markSource _).mpr))
  overCore_row edge := congrArg r.slot (iso.overCore_row edge)

end Relabel

section Inverse

variable {c c' : Core n p} (r : Relabel c c') {mark mark' : Fin k → Fin n} (σ : Fin k ≃ Fin k)
  (hMark : ∀ j, r.vtx (mark j) = mark' (σ j)) {types types' : Fin k → ℕ}
  (hTypes : ∀ j, types' (σ j) = types j)

include hMark in
theorem hMark_symm : ∀ j, r.symm.vtx (mark' j) = mark (σ.symm j) := by
  intro j
  have h := hMark (σ.symm j)
  rw [σ.apply_symm_apply] at h
  rw [← h, Relabel.symm_vtx, Equiv.symm_apply_apply]

include hTypes in
theorem hTypes_symm : ∀ j, types (σ.symm j) = types' j := by
  intro j
  rw [← hTypes (σ.symm j), σ.apply_symm_apply]

/-- **The round trip is the identity up to isomorphism**: the datum is literally unchanged, and
the permutations cancel. -/
def relabelRoundTrip (κ : TypedFrame c mark types degree) :
    TypedFrameIso (relabelFrame r.symm σ.symm (hMark_symm r σ hMark) (hTypes_symm σ hTypes)
      (relabelFrame r σ hMark hTypes κ)) κ where
  datum := GeometricDatumIso.refl κ.data
  mark j := by
    change κ.markSource (σ.symm (σ j)) = κ.markSource j
    rw [σ.symm_apply_apply]
  overCore_vertex vertex _ := by
    change κ.ident.vertex ⟨vertex.1, _⟩ = r.vtx.symm (r.vtx (κ.ident.vertex ⟨vertex.1, _⟩))
    rw [Equiv.symm_apply_apply]
  overCore_row edge := by
    change κ.ident.row (markedRow _ edge) = r.slot.symm (r.slot (κ.ident.row (markedRow _ edge)))
    rw [Equiv.symm_apply_apply]

/-- **The relabelling on classes**, an equivalence. -/
noncomputable def relabelClassEquiv :
    TypedFrameClass c mark types degree ≃ TypedFrameClass c' mark' types' degree where
  toFun := Quot.lift (fun κ ↦ TypedFrameClass.mk (relabelFrame r σ hMark hTypes κ)) fun _ _ h ↦
    h.elim fun iso ↦ TypedFrameClass.mk_eq_mk_of_iso ⟨relabelIso r σ hMark hTypes iso⟩
  invFun := Quot.lift (fun κ ↦ TypedFrameClass.mk (relabelFrame r.symm σ.symm
      (hMark_symm r σ hMark) (hTypes_symm σ hTypes) κ)) fun _ _ h ↦
    h.elim fun iso ↦ TypedFrameClass.mk_eq_mk_of_iso ⟨relabelIso r.symm σ.symm
      (hMark_symm r σ hMark) (hTypes_symm σ hTypes) iso⟩
  left_inv x := by
    induction x using Quot.ind with
    | mk κ => exact TypedFrameClass.mk_eq_mk_of_iso ⟨relabelRoundTrip r σ hMark hTypes κ⟩
  right_inv x := by
    induction x using Quot.ind with
    | mk κ =>
      exact TypedFrameClass.mk_eq_mk_of_iso
        ⟨relabelRoundTrip r.symm σ.symm (hMark_symm r σ hMark) (hTypes_symm σ hTypes) κ⟩

include hMark hTypes in
/-- **Typed counts and genericity are relabelling invariants.** -/
theorem typedCount_relabel' {y y' : Fin p → ℚ} (hy : ∀ e, y' (r.slot e) = y e) :
    typedCount c mark types y degree = typedCount c' mark' types' y' degree ∧
      ((∀ (κ : TypedFrame c mark types degree) (col : Fin p), κ.coordsAt y col ≠ 0) →
        ∀ (κ' : TypedFrame c' mark' types' degree) (col : Fin p), κ'.coordsAt y' col ≠ 0) := by
  have hy' : ∀ e, y (r.symm.slot e) = y' e := CoreRelabel.symm_request r hy
  refine ⟨?_, fun hGen κ' col ↦ ?_⟩
  · let e : TypedFibre c mark types y degree ≃ TypedFibre c' mark' types' y' degree :=
      (relabelClassEquiv r σ hMark hTypes).subtypeEquiv fun x ↦ by
        induction x using Quot.ind with
        | mk κ =>
          change κ.OpenAt y ↔ (relabelFrame r σ hMark hTypes κ).OpenAt y'
          unfold MarkedFrameBase.OpenAt
          rw [coordsAt_relabelFrame r σ hMark hTypes κ hy]
    unfold typedCount
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun x ↦ ?_
    obtain ⟨x, hx⟩ := x
    induction x using Quot.ind with
    | mk κ => exact (typedAbsMult_relabelFrame r σ hMark hTypes κ).symm
  · have h := hGen (relabelFrame r.symm σ.symm (hMark_symm r σ hMark) (hTypes_symm σ hTypes) κ')
      col
    rwa [coordsAt_relabelFrame r.symm σ.symm _ _ κ' hy'] at h

end Inverse

end DraismaVargas.Count.MarkedCountGeneral
