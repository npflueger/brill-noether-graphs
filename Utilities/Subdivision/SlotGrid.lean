module

public import Utilities.Subdivision.OddSubdivisionDescent
public import Utilities.Gonality.GonalityTransport
public import Mathlib.Tactic

@[expose] public section

/-!
# The `M`-grid inside a subdivision specification

This module names the set of vertices a divisor is allowed to sit on after the
interior-firing step (`Utilities.Subdivision.InteriorFiring`), and identifies
it with the image of the coarse graph inside an `M`-fold refinement.  It is
the vocabulary shared by the interior-firing lemma and by the composition of
two scalings (`Utilities.Subdivision.ScaleComposition`).

## What is proved

* `OnGrid T M` — a vertex of `T.graph` is *on the `M`-grid* when it is a core
  vertex, or an interior vertex of a slot whose offset `j + 1` is divisible by
  `M`.  Nothing is assumed about `T` or `M`; in particular `M = 0` is allowed
  (then only the core vertices and no interior vertex are on the grid).
* `exists_fineOf_of_onGrid` — on `S.scale M`, the grid is exactly the image of
  `Spec.fineOf` (from `Utilities.Subdivision.SubdivisionChipDescent`), the
  embedding of the coarse vertices into the refinement.
* `roundData_fineOf` — a vertex in that image lands in the `Sum.inl` branch of
  `Spec.roundData` (from `Utilities.Subdivision.OddSubdivisionDescent`), and
  hence `nearest_fineOf`, `roundDist_fineOf`, `roundDist_eq_zero_of_onGrid`:
  its nearest-rounding distance `Spec.roundDist` is `0`.  This is what makes
  the rounding budget of `Utilities.Subdivision.ZeroBudgetRounding` free.
* `segmentSpec` — the unit segment (two core vertices, one slot of length one)
  with the concrete computations that exercise `fineOf`, `roundData`,
  `roundDist` and `OnGrid` at `S = segmentSpec.scale 3`, `M = 2`.

## What is NOT proved here

Nothing about divisors, firing, rank or Brill--Noether existence.  No relation
between `OnGrid` on `(spec.scale u).scale v` and on `spec.scale (v * u)` —
that is `Utilities.Subdivision.ScaleComposition`, which needs a relabelling.

## Consumers

`Utilities.Subdivision.InteriorFiring` (the conclusion of the firing lemma),
`Utilities.Subdivision.ScaleComposition`, and
`Utilities.Subdivision.ZeroBudgetRounding` (the hypothesis of the rounding
step).
-/

namespace DraismaVargas.Count.SlotGrid

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph

variable {n p : ℕ}

/-- A vertex of `T.graph` is on the `M`-grid when it is a core vertex, or an interior
vertex of a slot whose offset `j + 1` is divisible by `M`. -/
def OnGrid (T : Spec n p) (M : ℕ) : T.Vertex → Prop
  | Sum.inl _ => True
  | Sum.inr c => M ∣ (c.2.val + 1)

/-- Core vertices are always on the grid. -/
theorem onGrid_coreVertex (T : Spec n p) (M : ℕ) (v : Fin n) :
    OnGrid T M (T.coreVertex v) := trivial

/-- On an interior vertex the grid condition is divisibility of the offset. -/
theorem onGrid_interiorVertex_iff (T : Spec n p) (M : ℕ) (e : Fin p)
    (o : Fin (T.length e - 1)) :
    OnGrid T M (T.interiorVertex e o) ↔ M ∣ (o.val + 1) := Iff.rfl

/-- On an `M`-fold refinement the grid is exactly the image of the coarse vertices. -/
theorem exists_fineOf_of_onGrid (S : Spec n p) (M : ℕ) (hM : 0 < M)
    {y : (S.scale M hM).Vertex} (hy : OnGrid (S.scale M hM) M y) :
    ∃ x : S.Vertex, y = S.fineOf M hM x := by
  rcases y with w | ⟨e, j⟩
  · exact ⟨Sum.inl w, rfl⟩
  · obtain ⟨t, ht⟩ : M ∣ (j.val + 1) := hy
    have hjlt : j.val + 1 < M * S.length e := by
      have hj := j.isLt
      simp only [Spec.scale_length] at hj
      have := Nat.mul_pos hM (S.length_pos e)
      omega
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, Nat.mul_zero] at ht; omega
      · exact h
    have htlt : t < S.length e := by
      by_contra hcon
      have : S.length e ≤ t := by omega
      have := Nat.mul_le_mul_left M this
      omega
    refine ⟨S.interiorVertex e ⟨t - 1, by omega⟩, ?_⟩
    simp only [Spec.interiorVertex, Spec.fineOf, Sum.inr.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and]
    apply Fin.ext
    show j.val = M * (t - 1 + 1) - 1
    rw [Nat.sub_add_cancel ht1, ← ht]
    omega

/-- A coarse vertex, seen in the refinement, is classified by `roundData` as a coarse
vertex: the `Sum.inl` branch. -/
theorem roundData_fineOf (S : Spec n p) (M : ℕ) (hM : 0 < M) (x : S.Vertex) :
    S.roundData M hM (S.fineOf M hM x) = Sum.inl x := by
  have hleft : (S.roundData M hM (S.fineOf M hM x)).isLeft = true := by
    rcases x with w | ⟨e, o⟩
    · rfl
    · have hpos : 0 < M * (o.val + 1) := Nat.mul_pos hM (Nat.succ_pos _)
      have hmod : (M * (o.val + 1) - 1 + 1) % M = 0 := by
        have hrw : M * (o.val + 1) - 1 + 1 = M * (o.val + 1) := by omega
        rw [hrw]
        exact Nat.mul_mod_right _ _
      simp only [Spec.fineOf, Spec.roundData, hmod, dite_eq_left, Sum.isLeft]
  obtain ⟨x', hx'⟩ := Sum.isLeft_iff.mp hleft
  rw [hx']
  congr 1
  exact S.fineOf_injective M hM
    (S.eq_fineOf_of_roundData_eq_inl M hM hx').symm

/-- Nearest-rounding fixes the image of a coarse vertex. -/
theorem nearest_fineOf (S : Spec n p) (M : ℕ) (hM : 0 < M) (x : S.Vertex) :
    S.nearest M hM (S.fineOf M hM x) = x := by
  unfold Spec.nearest
  rw [roundData_fineOf]
  rfl

/-- A coarse vertex, seen in the refinement, is at rounding distance zero. -/
theorem roundDist_fineOf (S : Spec n p) (M : ℕ) (hM : 0 < M) (x : S.Vertex) :
    S.roundDist M hM (S.fineOf M hM x) = 0 := by
  unfold Spec.roundDist
  rw [roundData_fineOf]
  rfl

/-- Every grid vertex is at rounding distance zero: the zero rounding budget of
`Utilities.Subdivision.ZeroBudgetRounding`. -/
theorem roundDist_eq_zero_of_onGrid (S : Spec n p) (M : ℕ) (hM : 0 < M)
    {y : (S.scale M hM).Vertex} (hy : OnGrid (S.scale M hM) M y) :
    S.roundDist M hM y = 0 := by
  obtain ⟨x, hx⟩ := exists_fineOf_of_onGrid S M hM hy
  rw [hx, roundDist_fineOf]

/-! ## A concrete small specification -/

/-- Two core vertices joined by one edge slot. -/
def segmentCore : ExplicitPotential.Core 2 1 where
  tail := fun _ => 0
  head := fun _ => 1

/-- The unit segment: two core vertices, one slot of length one. -/
def segmentSpec : Spec 2 1 where
  core := segmentCore
  length := fun _ => 1
  core_nonempty := by norm_num
  core_loopless := by decide
  length_pos := by intro _; norm_num

@[simp] theorem segmentSpec_length (e : Fin 1) : segmentSpec.length e = 1 := rfl

example : (segmentSpec.scale 3 (by norm_num)).length 0 = 3 := by norm_num

example : ((segmentSpec.scale 3 (by norm_num)).scale 2 (by norm_num)).length 0 = 6 := by
  norm_num

example : (segmentSpec.scale (2 * 3) (by norm_num)).length 0 = 6 := by norm_num

/-- The coarse interior vertex at offset `2` of the three-fold segment. -/
def segmentCoarseMid : (segmentSpec.scale 3 (by norm_num)).Vertex :=
  (segmentSpec.scale 3 (by norm_num)).interiorVertex 0 ⟨1, by norm_num⟩

example :
    (segmentSpec.scale 3 (by norm_num)).fineOf 2 (by norm_num) segmentCoarseMid
      = Sum.inr ⟨0, ⟨3, by norm_num⟩⟩ := rfl

example :
    (segmentSpec.scale 3 (by norm_num)).roundData 2 (by norm_num)
        ((segmentSpec.scale 3 (by norm_num)).fineOf 2 (by norm_num) segmentCoarseMid)
      = Sum.inl segmentCoarseMid :=
  roundData_fineOf _ _ _ _

example :
    (segmentSpec.scale 3 (by norm_num)).roundDist 2 (by norm_num)
        ((segmentSpec.scale 3 (by norm_num)).fineOf 2 (by norm_num) segmentCoarseMid) = 0 :=
  roundDist_fineOf _ _ _ _

example :
    OnGrid ((segmentSpec.scale 3 (by norm_num)).scale 2 (by norm_num)) 2
      (Sum.inr ⟨0, ⟨3, by norm_num⟩⟩) := by
  show (2 : ℕ) ∣ 3 + 1
  norm_num

end DraismaVargas.Count.SlotGrid
