module

public import DraismaVargasCount.StarPilot

@[expose] public section

/-!
# Labelled retained columns force equality of limit metrics

Two regrowths have the same labelled metric limit (`StarPilot.SameMetricLimit`)
when there is an isomorphism of the contracted combinatorial data that also
preserves its metric over the labelled source. This module proves that the
second condition is forced once the surviving matrix columns agree in the fixed
core-row labelling.

The contracted target isomorphism canonically identifies the surviving columns;
adding the two collapsed columns extends that identification to a permutation.
Both collapsed coordinates are zero. The remaining common matrix coefficients
then identify the source requests, and the original member's nonsingular square
matrix forces equality of all target coordinates. No rank assertion about an
independently constructed rectangular matrix is needed.

The only additional input in `sameMetricLimit_of_retainedColumnsAgree` is
`RetainedColumnsAgree`. It is a concrete equality of the actual member matrices,
with row matching determined by their core identifications. It is not proved
here for an arbitrary `DatumIso`. This module neither strengthens
`WallStar.Regrowth.SameLimit` nor claims that the strict star `WallStar.Star`
enumerates the fixed labelled metric limits of Vargas, Part II.

The identification `retainedColumns` of the retained coordinates with the
contracted target occurrences is used by `InheritedLimitRows`.
-/

namespace DraismaVargas.Count.StarMetricCompatibility

open DraismaVargas.Infrastructure
open DraismaVargas.Count.SegmentWalls
open DraismaVargas.Count.WallStar
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p}

/-- The retained coordinates are precisely the contracted target occurrences. -/
noncomputable def retainedColumns (k : Frame core degree) (col : Fin p) :
    {c : Fin p // c ≠ col} ≃ (k.limitTarget col).edges :=
  (Equiv.subtypeEquiv k.fullDim.labelling.targetEdge (fun c ↦ by
    change c ≠ col ↔ k.fullDim.labelling.targetEdge c ≠ k.fullDim.labelling.targetEdge col
    exact not_congr k.fullDim.labelling.targetEdge.injective.eq_iff.symm)).trans
    (GluingContraction.foldEdgeEquiv rfl
      (GluingContraction.fst_ne_snd (k.edgeOf col)) (k.numEdges_edgeOf col))

theorem coords_retainedColumns_symm {y : Fin p → ℚ} (w : Regrowth core y degree)
    (e : (w.frame.limitTarget w.column).edges) :
    w.frame.coordsAt y ((retainedColumns w.frame w.column).symm e).1 =
      StarPilot.limitLength w e := rfl

/-- The retained-coordinate bijection induced by a contracted datum isomorphism. -/
noncomputable def limitColumnEquiv {y : Fin p → ℚ} (w w' : Regrowth core y degree)
    (iso : Transport.DatumIso w.limit w'.limit) :
    {c : Fin p // c ≠ w.column} ≃ {c : Fin p // c ≠ w'.column} :=
  (retainedColumns w.frame w.column).trans
    (iso.targetEdge.trans (retainedColumns w'.frame w'.column).symm)

/-- Extend the retained-coordinate map by pairing the two collapsed columns. -/
noncomputable def allColumnEquiv {y : Fin p → ℚ} (w w' : Regrowth core y degree)
    (iso : Transport.DatumIso w.limit w'.limit) : Fin p ≃ Fin p :=
  (Equiv.optionSubtypeNe w.column).symm.trans
    ((Equiv.optionCongr (limitColumnEquiv w w' iso)).trans
      (Equiv.optionSubtypeNe w'.column))

theorem allColumnEquiv_collapsed {y : Fin p → ℚ} (w w' : Regrowth core y degree)
    (iso : Transport.DatumIso w.limit w'.limit) :
    allColumnEquiv w w' iso w.column = w'.column := by
  simp [allColumnEquiv]

theorem allColumnEquiv_retained {y : Fin p → ℚ} (w w' : Regrowth core y degree)
    (iso : Transport.DatumIso w.limit w'.limit) (c : {c : Fin p // c ≠ w.column}) :
    allColumnEquiv w w' iso c.1 = (limitColumnEquiv w w' iso c).1 := by
  simp [allColumnEquiv, Equiv.optionSubtypeNe_symm_of_ne c.2]

/-- A common labelled request determines the target coordinates from just the
retained columns; the vanished coordinate contributes zero to every row. -/
theorem coords_eq_of_retained_columns {k l : Frame core degree}
    {y : Fin p → ℚ} {col : Fin p} (columns : Fin p ≃ Fin p)
    (hl : l.coordsAt y (columns col) = 0)
    (hretained : ∀ r c, c ≠ col →
      l.matrix (l.slot.symm (k.slot r)) (columns c) = k.matrix r c) :
    ∀ c, l.coordsAt y (columns c) = k.coordsAt y c := by
  let z : Fin p → ℚ := fun c ↦ l.coordsAt y (columns c)
  have hmul : k.matrix.mulVec z = k.matrix.mulVec (k.coordsAt y) := by
    funext r
    calc
      k.matrix.mulVec z r = ∑ c,
          l.matrix (l.slot.symm (k.slot r)) (columns c) * l.coordsAt y (columns c) := by
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : c = col
        · subst hc
          simp only [z, hl, mul_zero]
        · rw [hretained r c hc]
      _ = l.matrix.mulVec (l.coordsAt y) (l.slot.symm (k.slot r)) := by
        simpa only [Matrix.mulVec, dotProduct] using
          columns.sum_comp (fun c ↦ l.matrix (l.slot.symm (k.slot r)) c * l.coordsAt y c)
      _ = k.matrix.mulVec (k.coordsAt y) r := by
        rw [k.mulVec_coordsAt, l.mulVec_coordsAt]
        simp only [Equiv.apply_symm_apply]
  have heq : z = k.coordsAt y := by
    have hinv := congrArg (fun v ↦ k.matrix⁻¹.mulVec v) hmul
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ k.isUnit_det,
      Matrix.one_mulVec] using hinv
  exact congrFun heq

/-- The retained-column hypothesis, stated on actual member matrices.
The row permutation is forced by the common labelled core. -/
def RetainedColumnsAgree {y : Fin p → ℚ} (w w' : Regrowth core y degree)
    (iso : Transport.DatumIso w.limit w'.limit) : Prop :=
  ∀ r (c : {c : Fin p // c ≠ w.column}),
    w'.frame.matrix (w'.frame.slot.symm (w.frame.slot r))
      (limitColumnEquiv w w' iso c).1 = w.frame.matrix r c.1

/-- Once the labelled retained columns agree, the contracted datum
isomorphism necessarily preserves all surviving target lengths. -/
theorem sameMetricLimit_of_retainedColumnsAgree {y : Fin p → ℚ}
    (w w' : Regrowth core y degree) (iso : Transport.DatumIso w.limit w'.limit)
    (h : RetainedColumnsAgree w w' iso) : StarPilot.SameMetricLimit w w' := by
  have hcoords := coords_eq_of_retained_columns (allColumnEquiv w w' iso)
    (by rw [allColumnEquiv_collapsed]; exact w'.degenerate.1)
    (fun r c hc ↦ by
      rw [allColumnEquiv_retained w w' iso ⟨c, hc⟩]
      exact h r ⟨c, hc⟩)
  refine ⟨iso, fun e ↦ ?_⟩
  have heq := hcoords ((retainedColumns w.frame w.column).symm e).1
  rw [allColumnEquiv_retained] at heq
  have hc : limitColumnEquiv w w' iso ((retainedColumns w.frame w.column).symm e) =
      (retainedColumns w'.frame w'.column).symm (iso.targetEdge e) := by
    simp [limitColumnEquiv]
  rw [hc, coords_retainedColumns_symm, coords_retainedColumns_symm] at heq
  exact heq

end DraismaVargas.Count.StarMetricCompatibility

