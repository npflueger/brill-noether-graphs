module

public import DraismaVargasCount.Star

@[expose] public section

/-!
# Positive requests on a target facet, and metric compatibility of limits

A limit of a frame at a wall collapses one column of the frame: a target facet.  To study the
star of such a limit at a strictly positive request, one needs a frame whose target facet meets
the strictly positive source orthant.  A full-dimensional presentation alone does not give that
condition: the caterpillar presentations are diagonal.

`positiveWall_iff` gives the exact additional finite check. Every stable row must
have a positive coefficient outside the collapsed column (`RetainedRowSupport`). When this holds,
`unitWallRequest` constructs the request by assigning length one to every retained
target occurrence and zero to the collapsed one, and `unitRegrowth` is the resulting regrowth,
whose star is nonempty and finite (`positive_finite_star`). This is a construction on actual
`Frame`s, not on arbitrary matrices.

`pilotCore` is a small concrete example: a labelled trivalent core of genus four, with six
vertices and nine slots.

The last section defines `SameMetricLimit`: two regrowths have the same metric limit when some
isomorphism of their limits preserves the surviving target lengths (`limitLength`).
`Regrowth.SameLimit` forgets both the source labels and the metric lengths, so it still has to be
compared with the fixed labelled metric limit of Part II; `SameMetricLimit` restores the lengths.
It is the notion of "same limit" used by the censuses of the type-change step (step 3 of
`DraismaVargasCount.Assembly`).
-/

namespace DraismaVargas.Count.StarPilot

open DraismaVargas.Infrastructure
open DraismaVargas.Count.SegmentWalls
open DraismaVargas.Count.WallStar
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p}

/-- Positivity of the genuine path sums, specialized to a frame. -/
theorem matrix_nonneg (k : Frame core degree) (r c : Fin p) :
    0 ≤ k.matrix r c :=
  LocalCases.SeedDeterminant.row_nonneg k.fullDim.labelling.presentation _ _

/-- Unit lengths on the retained target occurrences, zero on the collapsed one. -/
def unitWallCoords (col : Fin p) : Fin p → ℚ := fun c ↦ if c = col then 0 else 1

/-- The requested core lengths produced by those target lengths. -/
noncomputable def unitWallRequest (k : Frame core degree) (col : Fin p) : Fin p → ℚ :=
  fun s ↦ k.matrix.mulVec (unitWallCoords col) (k.slot.symm s)

theorem coordsAt_unitWallRequest (k : Frame core degree) (col : Fin p) :
    k.coordsAt (unitWallRequest k col) = unitWallCoords col := by
  have hrequest : (fun r ↦ unitWallRequest k col (k.slot r)) =
      k.matrix.mulVec (unitWallCoords col) := by
    funext r
    simp only [unitWallRequest, Equiv.symm_apply_apply]
  rw [Frame.coordsAt, hrequest, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ k.isUnit_det, Matrix.one_mulVec]

theorem degenerateAt_unitWallRequest (k : Frame core degree) (col : Fin p) :
    k.DegenerateAt (unitWallRequest k col) col := by
  rw [Frame.DegenerateAt, coordsAt_unitWallRequest]
  constructor
  · simp [unitWallCoords]
  · intro c hc
    simp [unitWallCoords, hc]

/-- The finite support test for an interior target facet. -/
def RetainedRowSupport (k : Frame core degree) (col : Fin p) : Prop :=
  ∀ r, ∃ c, c ≠ col ∧ 0 < k.matrix r c

theorem nondegenerate_unitWallRequest (k : Frame core degree) (col : Fin p)
    (hsupport : RetainedRowSupport k col) : Nondegenerate (unitWallRequest k col) := by
  intro s
  obtain ⟨c, hc, hpos⟩ := hsupport (k.slot.symm s)
  change 0 < ∑ j, k.matrix (k.slot.symm s) j * unitWallCoords col j
  apply Finset.sum_pos'
  · intro j _
    apply mul_nonneg (matrix_nonneg k _ j)
    simp only [unitWallCoords]
    split_ifs <;> norm_num
  · exact ⟨c, Finset.mem_univ c, by simpa [unitWallCoords, hc] using hpos⟩

/-- Any positive request on this facet forces each row to retain a nonzero term. -/
theorem retainedRowSupport_of_degenerateAt (k : Frame core degree) (col : Fin p)
    {y : Fin p → ℚ} (hdeg : k.DegenerateAt y col) (hy : Nondegenerate y) :
    RetainedRowSupport k col := by
  intro r
  by_contra h
  push Not at h
  have hzero : k.matrix.mulVec (k.coordsAt y) r = 0 := by
    change (∑ c, k.matrix r c * k.coordsAt y c) = 0
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : c = col
    · subst hc
      rw [hdeg.1, mul_zero]
    · have hz : k.matrix r c = 0 := le_antisymm (h c hc) (matrix_nonneg k r c)
      rw [hz, zero_mul]
  rw [k.mulVec_coordsAt y] at hzero
  exact (ne_of_gt (hy (k.slot r))) hzero

/-- Exact, necessary and sufficient condition for a frame to yield a positive
source request on the chosen target facet. -/
theorem positiveWall_iff (k : Frame core degree) (col : Fin p) :
    (∃ y : Fin p → ℚ, Nondegenerate y ∧ k.DegenerateAt y col) ↔
      RetainedRowSupport k col := by
  constructor
  · rintro ⟨y, hy, hdeg⟩
    exact retainedRowSupport_of_degenerateAt k col hdeg hy
  · intro hs
    exact ⟨unitWallRequest k col, nondegenerate_unitWallRequest k col hs,
      degenerateAt_unitWallRequest k col⟩

/-- An actual regrowth, with no new proof field beyond the existing frame. -/
noncomputable def unitRegrowth (k : Frame core degree) (col : Fin p) :
    Regrowth core (unitWallRequest k col) degree :=
  ⟨k, col, degenerateAt_unitWallRequest k col⟩

/-- Its star is finite and inhabited at a strictly positive source request
precisely when the finite support test passes. This does not enumerate it. -/
theorem positive_finite_star (k : Frame core degree) (col : Fin p)
    (hsupport : RetainedRowSupport k col) :
    Nondegenerate (unitWallRequest k col) ∧
      Nonempty (Star (unitRegrowth k col)) ∧ Finite (Star (unitRegrowth k col)) :=
  ⟨nondegenerate_unitWallRequest k col hsupport, inferInstance, inferInstance⟩

section Concrete

open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.StablePathCount (incidenceCount incidentEdges mem_incidentEdges)

/-- A labelled trivalent core of genus four, with six vertices and nine slots. -/
def pilotCore : Core 6 9 where
  tail := ![0,0,0,1,1,2,3,4,4]
  head := ![1,3,4,2,2,3,5,5,5]

end Concrete

section MetricCompatibility

open GluingContraction

variable {y : Fin p → ℚ}

/-- The surviving target metric of a regrowth, retained by literal contraction. -/
noncomputable def limitLength (w : Regrowth core y degree)
    (e : (w.frame.limitTarget w.column).edges) : ℚ :=
  w.frame.coordsAt y (w.frame.fullDim.labelling.targetEdge.symm
    (unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) e))

theorem limitLength_pos (w : Regrowth core y degree)
    (e : (w.frame.limitTarget w.column).edges) : 0 < limitLength w e := by
  apply w.degenerate.2
  intro h
  have heq := congrArg w.frame.fullDim.labelling.targetEdge h
  rw [Equiv.apply_symm_apply] at heq
  exact unfoldEdge_ne_contracted rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) e heq

/-- The metric compatibility that a witness of `SameLimit` does not store.
Even this condition alone does not express compatibility with the source labels. -/
def SameMetricLimit (w w' : Regrowth core y degree) : Prop :=
  ∃ iso : Transport.DatumIso w.limit w'.limit,
    ∀ e, limitLength w' (iso.targetEdge e) = limitLength w e

theorem SameMetricLimit.sameLimit {w w' : Regrowth core y degree}
    (h : SameMetricLimit w w') : w.SameLimit w' :=
  ⟨h.choose⟩

theorem SameMetricLimit.refl (w : Regrowth core y degree) : SameMetricLimit w w :=
  ⟨Transport.DatumIso.refl w.limit, fun _ ↦ rfl⟩

theorem SameMetricLimit.symm {w w' : Regrowth core y degree}
    (h : SameMetricLimit w w') : SameMetricLimit w' w := by
  obtain ⟨iso, hmetric⟩ := h
  refine ⟨iso.symm, fun e ↦ ?_⟩
  exact (hmetric (iso.targetEdge.symm e)).symm.trans
    (congrArg (limitLength w') (iso.targetEdge.apply_symm_apply e))

theorem SameMetricLimit.trans {w w' w'' : Regrowth core y degree}
    (h : SameMetricLimit w w') (h' : SameMetricLimit w' w'') :
    SameMetricLimit w w'' := by
  obtain ⟨iso, hmetric⟩ := h
  obtain ⟨iso', hmetric'⟩ := h'
  exact ⟨iso.trans iso', fun e ↦ (hmetric' (iso.targetEdge e)).trans (hmetric e)⟩

end MetricCompatibility

end DraismaVargas.Count.StarPilot
