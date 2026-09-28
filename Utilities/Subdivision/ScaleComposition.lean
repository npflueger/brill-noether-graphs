import Utilities.Subdivision.SlotGrid

/-!
# Composing two scalings of a subdivision specification

Scaling a subdivision specification by `u` and then by `v` presents the same
graph as scaling it by `v * u`, but not definitionally.  `Spec.scale` (from
`Utilities.Gonality.GonalityTransport`) is a structure whose `length` field is
`fun edge => k * spec.length edge`, so

    ((spec.scale u).scale v).length e = v * (u * spec.length e)
    (spec.scale (v * u)).length e     = v * u * spec.length e

differ by `Nat.mul_assoc`, and the interior index types `Fin (v * (u * L) - 1)`
and `Fin (v * u * L - 1)` are not syntactically equal.  The two specifications
are therefore **not** definitionally equal and a `Spec.Relabeling`
(from `Utilities.Subdivision.SubdivisionIso`) is needed.

## What is proved

* `scaleScaleRelabeling spec u v hu hv :
    ((spec.scale u hu).scale v hv).Relabeling (spec.scale (v * u) _)` — the
  relabelling, in the shape of `Spec.scaleOneRelabeling`
  (`Utilities.Gonality.GonalityTransport`): identity on core vertices and on
  slots, no slot reversed, lengths matched by `Nat.mul_assoc`.
* `scaleScaleLaplacianEquiv` — its `LaplacianEquiv` via `Spec.laplacianEquiv`
  (`Utilities.Subdivision.SubdivisionIso`), so divisors, degrees and rank
  bounds transport by `LaplacianEquiv.mapDiv` and `rank_mapDiv_ge_iff`
  (`Utilities.Subdivision.LaplacianEquiv`).
* `scaleScale_interiorEquiv_val`, `onGrid_vertexEquiv_iff`,
  `onGrid_symm_of_onGrid` — the relabelling preserves slot offsets, hence the
  `M`-grid of `Utilities.Subdivision.SlotGrid` in both directions.
* `roundData_symm_eq_inl`, `roundDist_symm_eq_zero` — rounding across the
  composition: a vertex of `spec.scale (v * u)` whose offset is divisible by
  `v` is, after the relabelling, `Spec.fineOf` of a vertex of `spec.scale u`,
  so `Spec.roundData` takes the `Sum.inl` branch and `Spec.roundDist` is `0`.
* `segmentScaleScale` and the examples below it — the relabelling instantiated
  at `segmentSpec` with `u = 3`, `v = 2`, where the vertex equivalence and the
  zero rounding distance are computed on a concrete interior vertex.

## What is NOT proved here

Nothing about `Spec.scale` commuting with itself as an equality of
specifications (it does not), and nothing about divisors beyond what
`LaplacianEquiv` already transports.  `scaleScaleRelabeling` fixes the slot
order and orientation; a relabelling that permutes slots is a different
statement.  No hypothesis beyond `0 < u` and `0 < v` remains.

## Consumers

`Utilities.Subdivision.ZeroBudgetRounding`, and through it the Draisma--Vargas
count, where it is used to construct odd-subdivision witnesses.
-/

namespace DraismaVargas.Count.ScaleComposition

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Count.SlotGrid

variable {n p : ℕ}

/-! ## The composition relabelling -/

/-- The composition relabelling: scaling by `u` and then by `v` presents the same graph
as scaling by `v * u`.  Identity on core vertices and slots, no slot reversed; the
lengths are matched by `Nat.mul_assoc`. -/
def scaleScaleRelabeling (spec : Spec n p) (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ((spec.scale u hu).scale v hv).Relabeling (spec.scale (v * u) (Nat.mul_pos hv hu)) where
  coreEquiv := Equiv.refl _
  slotEquiv := Equiv.refl _
  reversed := fun _ => false
  length_eq := by intro e; simp [Nat.mul_assoc]
  tail_eq := by intro e; simp
  head_eq := by intro e; simp

/-- The Laplacian equivalence of the composition relabelling. -/
def scaleScaleLaplacianEquiv (spec : Spec n p) (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v) :
    LaplacianEquiv ((spec.scale u hu).scale v hv).graph
      (spec.scale (v * u) (Nat.mul_pos hv hu)).graph :=
  Spec.laplacianEquiv _ _ (scaleScaleRelabeling spec u v hu hv)

/-- The relabelling preserves slot offsets. -/
theorem scaleScale_interiorEquiv_val (spec : Spec n p) (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v) (e : Fin p)
    (o : Fin (((spec.scale u hu).scale v hv).length e - 1)) :
    ((Spec.interiorEquiv _ _ (scaleScaleRelabeling spec u v hu hv) e) o).val = o.val := by
  unfold Spec.interiorEquiv
  simp only [scaleScaleRelabeling, Bool.false_eq_true, if_false]
  rfl

/-- Its vertex equivalence is the relabelling's. -/
theorem scaleScaleLaplacianEquiv_toEquiv (spec : Spec n p) (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v) :
    (scaleScaleLaplacianEquiv spec u v hu hv).toEquiv =
      Spec.vertexEquiv _ _ (scaleScaleRelabeling spec u v hu hv) := rfl

/-- Hence it preserves the `M`-grid. -/
theorem onGrid_vertexEquiv_iff (spec : Spec n p) (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (M : ℕ) (x : ((spec.scale u hu).scale v hv).Vertex) :
    OnGrid (spec.scale (v * u) (Nat.mul_pos hv hu)) M
        (Spec.vertexEquiv _ _ (scaleScaleRelabeling spec u v hu hv) x) ↔
      OnGrid ((spec.scale u hu).scale v hv) M x := by
  rcases x with w | ⟨e, o⟩
  · exact Iff.rfl
  · show OnGrid _ M (Spec.vertexEquiv _ _ (scaleScaleRelabeling spec u v hu hv)
        (((spec.scale u hu).scale v hv).interiorVertex e o)) ↔ _
    rw [Spec.vertexEquiv_interiorVertex, onGrid_interiorVertex_iff,
      scaleScale_interiorEquiv_val]
    exact Iff.rfl

/-- The grid transports backwards along the relabelling. -/
theorem onGrid_symm_of_onGrid (spec : Spec n p) (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (M : ℕ) {y : (spec.scale (v * u) (Nat.mul_pos hv hu)).Vertex}
    (hy : OnGrid (spec.scale (v * u) (Nat.mul_pos hv hu)) M y) :
    OnGrid ((spec.scale u hu).scale v hv) M
      ((scaleScaleLaplacianEquiv spec u v hu hv).toEquiv.symm y) := by
  rw [← onGrid_vertexEquiv_iff spec u v hu hv M]
  rw [scaleScaleLaplacianEquiv_toEquiv] at *
  rwa [Equiv.apply_symm_apply]

/-- A vertex of `spec.scale (v * u)` at an offset divisible by `v` is, after the
relabelling, the image of a vertex of `spec.scale u`, so `roundData` takes the
`Sum.inl` branch. -/
theorem roundData_symm_eq_inl (spec : Spec n p) (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    {y : (spec.scale (v * u) (Nat.mul_pos hv hu)).Vertex}
    (hy : OnGrid (spec.scale (v * u) (Nat.mul_pos hv hu)) v y) :
    ∃ x : (spec.scale u hu).Vertex,
      (scaleScaleLaplacianEquiv spec u v hu hv).toEquiv.symm y =
          (spec.scale u hu).fineOf v hv x ∧
        (spec.scale u hu).roundData v hv
            ((scaleScaleLaplacianEquiv spec u v hu hv).toEquiv.symm y) = Sum.inl x := by
  obtain ⟨x, hx⟩ :=
    exists_fineOf_of_onGrid (spec.scale u hu) v hv
      (onGrid_symm_of_onGrid spec u v hu hv v hy)
  exact ⟨x, hx, by rw [hx, roundData_fineOf]⟩

/-- Consequently its rounding distance is zero. -/
theorem roundDist_symm_eq_zero (spec : Spec n p) (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    {y : (spec.scale (v * u) (Nat.mul_pos hv hu)).Vertex}
    (hy : OnGrid (spec.scale (v * u) (Nat.mul_pos hv hu)) v y) :
    (spec.scale u hu).roundDist v hv
      ((scaleScaleLaplacianEquiv spec u v hu hv).toEquiv.symm y) = 0 :=
  roundDist_eq_zero_of_onGrid (spec.scale u hu) v hv
    (onGrid_symm_of_onGrid spec u v hu hv v hy)

/-! ## The relabelling at a concrete small specification -/

/-- The composition relabelling for the unit segment scaled first by `3`, then by `2`,
against the same segment scaled by `6`. -/
def segmentScaleScale :
    ((segmentSpec.scale 3 (by norm_num)).scale 2 (by norm_num)).Relabeling
      (segmentSpec.scale (2 * 3) (by norm_num)) :=
  scaleScaleRelabeling segmentSpec 3 2 (by norm_num) (by norm_num)

example : ((segmentSpec.scale 3 (by norm_num)).scale 2 (by norm_num)).length 0
    = (segmentSpec.scale (2 * 3) (by norm_num)).length (segmentScaleScale.slotEquiv 0) :=
  segmentScaleScale.length_eq 0

example :
    Spec.vertexEquiv _ _ segmentScaleScale (Sum.inr ⟨0, ⟨3, by norm_num⟩⟩)
      = Sum.inr ⟨0, ⟨3, by norm_num⟩⟩ := rfl

example :
    (scaleScaleLaplacianEquiv segmentSpec 3 2 (by norm_num) (by norm_num)).toEquiv
        (Sum.inr ⟨0, ⟨3, by norm_num⟩⟩)
      = Sum.inr ⟨0, ⟨3, by norm_num⟩⟩ := rfl

/-- The fine vertex at offset `4` of `σ₆` is a `2`-grid point, so after the relabelling it
rounds onto `σ₃` at distance zero. -/
example :
    (segmentSpec.scale 3 (by norm_num)).roundDist 2 (by norm_num)
        ((scaleScaleLaplacianEquiv segmentSpec 3 2 (by norm_num) (by norm_num)).toEquiv.symm
          (Sum.inr ⟨0, ⟨3, by norm_num⟩⟩)) = 0 :=
  roundDist_symm_eq_zero segmentSpec 3 2 (by norm_num) (by norm_num)
    (by show (2 : ℕ) ∣ 3 + 1; norm_num)

end DraismaVargas.Count.ScaleComposition
