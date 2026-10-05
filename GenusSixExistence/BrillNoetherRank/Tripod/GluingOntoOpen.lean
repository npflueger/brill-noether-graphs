module

public import GenusSixExistence.BrillNoetherRank.Tripod.GluingOntoIdent

@[expose] public section

/-!
# The deletion is open at the base request

Infrastructure for `GluingOnto.openAt_of_shape`. Prose:
`Research/genus-six-brill-noether-rank.md`, §5.5 (The bijection, the onto step, "Open": the
coordinates of the deleted datum are sums of coordinates of the glued member, so they are
positive). For a datum `D` with the shape of a gluing of an open member
`φ` (`ShapeLabels`), and any core identification of `D` whose row labels are the merged labels of
the glued pieces, the coordinate of `D` on a target edge `t` is the sum of the coordinates of `φ` on
the pieces of `t` (`coordsAt_eq`). Both sides of the realisation equation are the same sum over the
surviving edges of `refine₃ D π` (`mulVec_pieceCoords`, `baseRequest_eq_sum`):

* the length of a stable path `P` of `D` is the sum over its edges and their pieces;
* the base request of the slot of `P` is the sum of the requested lengths of the G-slots of `Γ̃`
  merging to it, each the length of its glued path (`φ.realizes`), and those glued paths are the
  glued paths through the pieces of the edges of `P`.
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

namespace Onto

/-! ## 1. Generic sums -/

section Sums

open Classical in
/-- **The realisation equation, edge by edge**: row `r` of `A w` is the length of the stable path
of `r`, the sum over its surviving edges of the target coordinate over the index. -/
theorem mulVec_eq_sum {S : CFGraph} {k : ℕ} {E : GluingDatum S k} {m : ℕ}
    (L : StableLengthMatrixLabelling E (Fin m)) (w : Fin m → ℚ) (r : Fin m) :
    (GluingDatum.LengthMatrixPresentation.matrix L.presentation).mulVec w r =
      ∑ x : NonDanglingEdge E, if L.row x.stablePath = r then
        w (L.targetEdge.symm x.1.1.1) / E.sourceEdgeIndex x.1 else 0 := by
  rw [matrix_eq_clsMatrix]
  simp only [Matrix.mulVec, dotProduct, clsMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hr : L.row x.stablePath = r
  · rw [ite_eq_left hr, Finset.sum_eq_single (L.targetEdge.symm x.1.1.1)]
    · rw [ite_eq_left ⟨hr, (Equiv.apply_symm_apply _ _).symm⟩]
      ring
    · intro c _ hc
      rw [ite_eq_right]
      · ring
      rintro ⟨-, h⟩
      exact hc (by rw [h, Equiv.symm_apply_apply])
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hr]
    exact Finset.sum_eq_zero fun c _ ↦ by rw [ite_eq_right fun h ↦ hr h.1, zero_mul]

/-- Summing a fibre over the fibres of a composite. -/
theorem sum_fiber_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq γ]
    (f : α → γ) (g : β → α) (j : γ) (h : β → ℚ) :
    (∑ a, if f a = j then ∑ b, (if g b = a then h b else 0) else 0) =
      ∑ b, if f (g b) = j then h b else 0 := by
  have h1 : ∀ a, (if f a = j then ∑ b, (if g b = a then h b else 0) else 0) =
      ∑ b, if g b = a then (if f a = j then h b else 0) else 0 := by
    intro a
    split_ifs with ha
    · exact Finset.sum_congr rfl fun b _ ↦ by split_ifs <;> rfl
    · exact (Finset.sum_eq_zero fun b _ ↦ by split_ifs <;> rfl).symm
  rw [Finset.sum_congr rfl fun a _ ↦ h1 a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_ite_eq]
  simp

/-- One merge of a request, as a sum over the pieces. -/
theorem mergeRequest_eq_sum {q : ℕ} (e : Fin q) (w : Fin (q + 1) → ℚ) (j : Fin q) :
    mergeRequest e w j = ∑ i : Fin (q + 1), if mergeOne e i = j then w i else 0 := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [mergeOne_castSucc, mergeOne_last, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold mergeRequest
  by_cases h : j = e
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), add_zero]

/-- **The base request of a slot of `G̃`** is the sum of the requested lengths of the G-slots of
`Γ̃` merging to it. -/
theorem baseRequest_eq_sum {p : ℕ} (s : MarkSlots p) (y : Fin (p + 1 + 1 + 1 + 3) → ℚ)
    (j : Fin p) :
    baseRequest s y j = ∑ i : Fin (p + 1 + 1 + 1),
      if mergeOne s.first (mergeOne s.second (mergeOne s.third i)) = j then
        y (Fin.castAdd 3 i) else 0 := by
  classical
  unfold baseRequest
  rw [mergeRequest_eq_sum]
  simp only [mergeRequest_eq_sum]
  rw [sum_fiber_comp (fun i₁ ↦ mergeOne s.first i₁) (fun i₂ ↦ mergeOne s.second i₂) j,
    sum_fiber_comp (fun i₂ ↦ mergeOne s.first (mergeOne s.second i₂))
      (fun i ↦ mergeOne s.third i) j]
  rfl

/-- The G-slots merging to `j`, counted against one slot `r` of `Γ̃`. -/
theorem sum_castAdd_eq {p : ℕ} (s : MarkSlots p) (j : Fin p) (r : Fin (p + 1 + 1 + 1 + 3))
    (c : ℚ) :
    (∑ i : Fin (p + 1 + 1 + 1),
      if mergeOne s.first (mergeOne s.second (mergeOne s.third i)) = j then
        (if r = Fin.castAdd 3 i then c else 0) else 0) =
      if mergeSlot s r = some j then c else 0 := by
  classical
  rcases Dichotomy.isGSlot_or_eq_legSlot r with hr | ⟨k, rfl⟩
  · set i₀ : Fin (p + 1 + 1 + 1) := ⟨r.val, hr⟩
    have hr' : r = Fin.castAdd 3 i₀ := Fin.ext rfl
    rw [Finset.sum_eq_single i₀]
    · rw [hr', mergeSlot_castAdd, ite_eq_left rfl]
      by_cases h : mergeOne s.first (mergeOne s.second (mergeOne s.third i₀)) = j
      · rw [ite_eq_left h, ite_eq_left (by rw [h])]
      · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (Option.some_injective _ h'))]
    · intro i _ hi
      rw [hr']
      split_ifs with h1 h2
      · exact absurd (Fin.castAdd_injective _ _ h2).symm hi
      · rfl
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hnone : mergeSlot s (legSlot p k) = none := by
      unfold mergeSlot
      rw [dite_eq_right (by simp only [legSlot, Fin.val_natAdd]; omega)]
    rw [hnone, ite_eq_right (by simp)]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hne : legSlot p k ≠ Fin.castAdd 3 i := by
      intro h
      have := congrArg Fin.val h
      simp only [legSlot, Fin.val_natAdd, Fin.val_castAdd] at this
      have := i.isLt
      omega
    split_ifs <;> rfl

end Sums

/-! ## 2. The pieces of a target edge of `D` -/

section Pieces

variable {T : CFGraph} {d : ℕ} {D : GluingDatum T d} {π : Placement T d}

/-- The target edge of `D` under a target edge of `T₃`. -/
def parent₃ (π : Placement T d) (ε : π.T₃.edges) : T.edges :=
  parentT π.edge₀ (parentT π.edge₁ (parentT π.edge₂ ε))

/-- The first piece of a target edge of `D`, in `T₃`. -/
def firstT₃ (π : Placement T d) (t : T.edges) : π.T₃.edges :=
  subdivOcc _ π.edge₂ (some (subdivOcc _ π.edge₁ (some (subdivOcc T π.edge₀ (some t)))))

theorem parent₃_firstT₃ (π : Placement T d) (t : T.edges) : parent₃ π (firstT₃ π t) = t := by
  simp [parent₃, firstT₃]

theorem anc_val (hD : D.Connected) (z : NonDanglingEdge (refine₃ D π)) :
    (CutPaths.anc D π hD z).1.1 = (parent₃ π z.1.1.1, z.1.1.2) := rfl

open Classical in
/-- **The surviving pieces of a surviving edge of `D`** are its sheet over the pieces of its target
edge. -/
theorem sum_anc_eq (hD : D.Connected) (x : NonDanglingEdge D) (G : π.T₃.edges → ℚ) :
    (∑ z : NonDanglingEdge (refine₃ D π), if CutPaths.anc D π hD z = x then G z.1.1.1 else 0) =
      ∑ ε : π.T₃.edges, if parent₃ π ε = x.1.1.1 then G ε else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hrepr : ∀ ε : π.T₃.edges, parent₃ π ε = x.1.1.1 →
      ((refine₃ D π).edgePartition ε).repr x.1.1.2 = x.1.1.2 := by
    intro ε hε
    rw [refineDatum_edgePartition, refineDatum_edgePartition, refineDatum_edgePartition]
    change (D.edgePartition (parent₃ π ε)).repr x.1.1.2 = x.1.1.2
    rw [hε]
    exact x.1.2
  refine Finset.sum_bij (fun z _ ↦ z.1.1.1) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have h := congrArg (fun w : NonDanglingEdge D ↦ w.1.1.1) hz
    exact h
  · intro z hz z' hz' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    have h1 := congrArg (fun w : NonDanglingEdge D ↦ w.1.1.2) hz
    have h2 := congrArg (fun w : NonDanglingEdge D ↦ w.1.1.2) hz'
    exact Subtype.ext (Subtype.ext (Prod.ext h (by
      change z.1.1.2 = z'.1.1.2
      rw [show z.1.1.2 = (CutPaths.anc D π hD z).1.1.2 from rfl,
        show z'.1.1.2 = (CutPaths.anc D π hD z').1.1.2 from rfl, h1, h2])))
  · intro ε hε
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hε
    let z₁ : (refine₃ D π).SourceEdge := ⟨(ε, x.1.1.2), hrepr ε hε⟩
    have hpar : parentSE₃ D π z₁ = x.1 := Subtype.ext (Prod.ext hε rfl)
    have hnd : ¬ IsDangling (refine₃ D π) z₁ := by
      rw [isDangling_iff₃ D π hD, hpar]
      exact x.2
    exact ⟨⟨z₁, hnd⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hpar⟩, rfl⟩
  · intro z _
    rfl

end Pieces

/-! ## 3. The coordinates of the deletion -/

section Coords

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph.{0}} {d : ℕ}
  {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D) (hT0 : genus T = 0) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {φ : FibreMember (tripodCore core s) y (d + 1)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ)

/-- The coordinate of `φ` on a target edge of the glued datum. -/
def zG (ε : π.T₆.edges) : ℚ :=
  φ.coords (φ.fullDim.labelling.targetEdge.symm (Ξ.targetEdge ε))

/-- **The length of a glued old path** is the requested length of its slot of `Γ̃`. -/
theorem length_gluedPath (z₀ : NonDanglingEdge (refine₃ D π)) :
    (∑ z : NonDanglingEdge (refine₃ D π),
      if CutPaths.gluedPath D π hD hT hπ z = CutPaths.gluedPath D π hD hT hπ z₀ then
        zG Ξ (π.liftE₃ z.1.1.1) / (refine₃ D π).sourceEdgeIndex z.1 else 0) =
      y (φ.ident.row (Ξ.stablePathEquiv (glueDatum_connected D π hD hT)
        (CutPaths.gluedPath D π hD hT hπ z₀))) := by
  classical
  have hG := glueDatum_connected D π hD hT
  set Qφ := Ξ.stablePathEquiv hG (CutPaths.gluedPath D π hD hT hπ z₀) with hQφ
  -- the realisation equation of `φ` at the row of `Qφ`
  have hreal := congrFun φ.realizes (φ.fullDim.labelling.row Qφ)
  rw [mulVec_eq_sum, Equiv.symm_apply_apply] at hreal
  rw [← hreal, ← (Ξ.nonDanglingEdgeEquiv hG).sum_comp]
  -- transport to the glued datum, then to the old edges
  have hF : ∀ a : NonDanglingEdge (glueDatum D π),
      (if φ.fullDim.labelling.row (Ξ.nonDanglingEdgeEquiv hG a).stablePath =
          φ.fullDim.labelling.row Qφ then
        φ.coords (φ.fullDim.labelling.targetEdge.symm (Ξ.nonDanglingEdgeEquiv hG a).1.1.1) /
          (φ.data.sourceEdgeIndex (Ξ.nonDanglingEdgeEquiv hG a).1 : ℚ) else 0) =
      if a.stablePath = CutPaths.gluedPath D π hD hT hπ z₀ then
        zG Ξ a.1.1.1 / ((glueDatum D π).sourceEdgeIndex a.1 : ℚ) else 0 := by
    intro a
    have hiff : φ.fullDim.labelling.row (Ξ.nonDanglingEdgeEquiv hG a).stablePath =
        φ.fullDim.labelling.row Qφ ↔ a.stablePath = CutPaths.gluedPath D π hD hT hπ z₀ := by
      rw [φ.fullDim.labelling.row.injective.eq_iff, hQφ,
        ← GeometricDatumIso.stablePathEquiv_mk, (Ξ.stablePathEquiv hG).injective.eq_iff]
    by_cases ha : a.stablePath = CutPaths.gluedPath D π hD hT hπ z₀
    · rw [ite_eq_left (hiff.mpr ha), ite_eq_left ha, GeometricDatumIso.nonDanglingEdgeEquiv_val,
        Ξ.sourceEdgeIndex_map]
      rfl
    · rw [ite_eq_right (fun h ↦ ha (hiff.mp h)), ite_eq_right ha]
  rw [Finset.sum_congr rfl fun a _ ↦ hF a, CutPaths.sum_eq_sum_liftND hD hT hπ]
  · refine Finset.sum_congr rfl fun z _ ↦ ?_
    show _ = if CutPaths.gluedPath D π hD hT hπ z = CutPaths.gluedPath D π hD hT hπ z₀ then
      zG Ξ (π.liftE₃ z.1.1.1) / ((glueDatum D π).sourceEdgeIndex (liftSE D π z.1) : ℚ) else 0
    rw [CutPaths.sourceEdgeIndex_liftSE z.1]
  · intro a ha
    rw [ite_eq_right]
    intro h
    exact ha ((CutPaths.isOld_iff_of_stablePath_eq hD hT hπ h).mpr
      (CutPaths.isOld_liftND hD hT hπ z₀))

open Classical in
/-- The coordinate vector of the deletion: the sum of the coordinates of `φ` over the pieces. -/
def pieceCoords (L : StableLengthMatrixLabelling D (Fin p)) (c : Fin p) : ℚ :=
  ∑ ε : π.T₃.edges, if parent₃ π ε = L.targetEdge c then zG Ξ (π.liftE₃ ε) else 0

omit hπ hT0 in
theorem pieceCoords_pos (hφ : φ.Open) (L : StableLengthMatrixLabelling D (Fin p)) (c : Fin p) :
    0 < pieceCoords Ξ L c := by
  classical
  unfold pieceCoords
  have hnn : ∀ ε ∈ (Finset.univ : Finset π.T₃.edges),
      0 ≤ if parent₃ π ε = L.targetEdge c then zG Ξ (π.liftE₃ ε) else 0 := by
    intro ε _
    split_ifs
    · exact (hφ _).le
    · rfl
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn (Finset.mem_univ (firstT₃ π (L.targetEdge c))))
  rw [ite_eq_left (parent₃_firstT₃ π _)]
  exact hφ _

include hS in
/-- **The merged label of a glued old path is the row of its ancestor's path**, for an
identification with the glued row labels. -/
theorem glabel_eq_ident (ident : CoreIdentification core D)
    (hrow : ∀ e : NonDanglingEdge D, ∃ e' : NonDanglingEdge φ.data,
      e'.1 = Ξ.sourceEdgeEquiv (π.oldSourceEdge D e.1) ∧
        mergeSlot s (φ.ident.row e'.stablePath) = some (ident.row e.stablePath))
    (z : NonDanglingEdge (refine₃ D π)) :
    glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ z) =
      some (ident.row (CutPaths.anc D π hD z).stablePath) := by
  have hG := glueDatum_connected D π hD hT
  set e := CutPaths.anc D π hD z with he
  obtain ⟨e', he', hr⟩ := hrow e
  have h1 := dlabel_anc hD hT hπ Ξ hS z
  have h2 := dlabel_anc hD hT hπ Ξ hS (firstND hD e)
  rw [anc_firstND] at h2
  rw [← h1, ← he, h2, ← hr]
  have he'' : e' = Ξ.nonDanglingEdgeEquiv hG (CutPaths.liftND D π hD hT hπ (firstND hD e)) := by
    apply Subtype.ext
    rw [he', GeometricDatumIso.nonDanglingEdgeEquiv_val]
    show _ = Ξ.sourceEdgeEquiv (liftSE D π (firstPiece₃ D π e.1))
    rw [liftSE_firstPiece₃]
  rw [he'']
  rfl

include hD hT hπ hS hT0 in
/-- **The coordinates of the deletion at the base request** are the piece sums
(`FibreMember.coords_unique`): both sides of the realisation equation are the same sum over the
surviving edges of `refine₃ D π`. -/
theorem mulVec_pieceCoords (fd : FullDimensionalSourcePresentation D (Fin p))
    (ident : CoreIdentification core D)
    (hrow : ∀ e : NonDanglingEdge D, ∃ e' : NonDanglingEdge φ.data,
      e'.1 = Ξ.sourceEdgeEquiv (π.oldSourceEdge D e.1) ∧
        mergeSlot s (φ.ident.row e'.stablePath) = some (ident.row e.stablePath))
    (r : Fin p) :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        (pieceCoords Ξ fd.labelling) r =
      baseRequest s y (ident.row (fd.labelling.row.symm r)) := by
  classical
  have hG := glueDatum_connected D π hD hT
  set P := fd.labelling.row.symm r with hP
  set j := ident.row P with hj
  set f : NonDanglingEdge (refine₃ D π) → ℚ := fun z ↦
    zG Ξ (π.liftE₃ z.1.1.1) / (refine₃ D π).sourceEdgeIndex z.1 with hf
  -- the left side: the length of `P`, over the pieces
  have hL : (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      (pieceCoords Ξ fd.labelling) r =
      ∑ z : NonDanglingEdge (refine₃ D π),
        if ident.row (CutPaths.anc D π hD z).stablePath = j then f z else 0 := by
    rw [mulVec_eq_sum]
    have hx : ∀ x : NonDanglingEdge D,
        (if fd.labelling.row x.stablePath = r then
          pieceCoords Ξ fd.labelling (fd.labelling.targetEdge.symm x.1.1.1) /
            (D.sourceEdgeIndex x.1 : ℚ) else 0) =
        if ident.row x.stablePath = j then
          ∑ z : NonDanglingEdge (refine₃ D π),
            (if CutPaths.anc D π hD z = x then f z else 0) else 0 := by
      intro x
      have hiff : fd.labelling.row x.stablePath = r ↔ ident.row x.stablePath = j := by
        rw [hj, hP, ident.row.injective.eq_iff, Equiv.eq_symm_apply]
      by_cases hxr : fd.labelling.row x.stablePath = r
      · rw [ite_eq_left hxr, ite_eq_left (hiff.mp hxr)]
        unfold pieceCoords
        have hanc := sum_anc_eq hD x (fun ε ↦ zG Ξ (π.liftE₃ ε) / (D.sourceEdgeIndex x.1 : ℚ))
        beta_reduce at hanc
        rw [Equiv.apply_symm_apply, Finset.sum_div]
        simp only [ite_div, zero_div]
        rw [← hanc]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        by_cases hz : CutPaths.anc D π hD z = x
        · rw [ite_eq_left hz, ite_eq_left hz, hf]
          beta_reduce
          rw [show (refine₃ D π).sourceEdgeIndex z.1 = D.sourceEdgeIndex x.1 from by
            rw [← hz]; exact CutPaths.idx_eq_anc hD z]
        · rw [ite_eq_right hz, ite_eq_right hz]
      · rw [ite_eq_right hxr, ite_eq_right (fun h ↦ hxr (hiff.mpr h))]
    rw [Finset.sum_congr rfl fun x _ ↦ hx x,
      sum_fiber_comp (fun x : NonDanglingEdge D ↦ ident.row x.stablePath)
        (CutPaths.anc D π hD) j f]
  -- the right side: the requested lengths of the G-slots merging to `j`
  have hR : baseRequest s y j = ∑ z : NonDanglingEdge (refine₃ D π),
      if ident.row (CutPaths.anc D π hD z).stablePath = j then f z else 0 := by
    rw [baseRequest_eq_sum]
    have hi : ∀ i : Fin (p + 1 + 1 + 1), y (Fin.castAdd 3 i) =
        ∑ z : NonDanglingEdge (refine₃ D π),
          if φ.ident.row (Ξ.stablePathEquiv hG (CutPaths.gluedPath D π hD hT hπ z)) =
            Fin.castAdd 3 i then f z else 0 := by
      intro i
      obtain ⟨z₀, hz₀⟩ := exists_gluedPath_eq_gSlot hD hT hπ hT0 Ξ hS i
      have h := length_gluedPath hD hT hπ Ξ z₀
      rw [hz₀, Equiv.apply_symm_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      have hiff : CutPaths.gluedPath D π hD hT hπ z = CutPaths.gluedPath D π hD hT hπ z₀ ↔
          φ.ident.row (Ξ.stablePathEquiv hG (CutPaths.gluedPath D π hD hT hπ z)) =
            Fin.castAdd 3 i := by
        rw [← Equiv.eq_symm_apply, ← hz₀, (Ξ.stablePathEquiv hG).injective.eq_iff]
      by_cases hz : CutPaths.gluedPath D π hD hT hπ z = CutPaths.gluedPath D π hD hT hπ z₀
      · rw [ite_eq_left hz, ite_eq_left (hiff.mp hz)]
      · rw [ite_eq_right hz, ite_eq_right (fun h ↦ hz (hiff.mpr h))]
    simp only [hi]
    have hsum : ∀ i : Fin (p + 1 + 1 + 1),
        (if mergeOne s.first (mergeOne s.second (mergeOne s.third i)) = j then
          ∑ z : NonDanglingEdge (refine₃ D π),
            (if φ.ident.row (Ξ.stablePathEquiv hG (CutPaths.gluedPath D π hD hT hπ z)) =
              Fin.castAdd 3 i then f z else 0) else 0) =
        ∑ z : NonDanglingEdge (refine₃ D π),
          if mergeOne s.first (mergeOne s.second (mergeOne s.third i)) = j then
            (if φ.ident.row (Ξ.stablePathEquiv hG (CutPaths.gluedPath D π hD hT hπ z)) =
              Fin.castAdd 3 i then f z else 0) else 0 := by
      intro i
      split_ifs
      · rfl
      · exact (Finset.sum_eq_zero fun _ _ ↦ rfl).symm
    rw [Finset.sum_congr rfl fun i _ ↦ hsum i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [sum_castAdd_eq s j _ (f z)]
    have hlab := glabel_eq_ident hD hT hπ Ξ hS ident hrow z
    unfold glabel at hlab
    rw [hlab]
    by_cases hz : ident.row (CutPaths.anc D π hD z).stablePath = j
    · rw [ite_eq_left (by rw [hz]), ite_eq_left hz]
    · rw [ite_eq_right (fun h ↦ hz (Option.some_injective _ h)), ite_eq_right hz]
  rw [hL, hR]

end Coords

end Onto

end GenusSixExistence.Tripod.Gluing

end
