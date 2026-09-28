import Utilities.IntegralGeometry.PositiveOrthantExit
import DraismaVargas.LocalCases.ClassifiedContinuation

/-!
# Attaching a first cone exit to classified local continuation

`PositiveOrthantExit` supplies the first coordinate wall of an incoming cone.
`ClassifiedContinuation` supplies a valid outgoing gluing datum after the
source case, balanced global family, and compatible outgoing velocity systems
have been constructed.  This file joins those two load-bearing arrows.

The geometric wall fields are derived here, not repeated as hypotheses.  The
remaining inputs are exactly the source-dependent classifier and length-system
identities, so this is not a source-exhaustion theorem.
-/

namespace DraismaVargas.LocalCases.MarchContinuation

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.RationalAffineWall
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.ClassifiedContinuation

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- At the first wall of an incoming positive cone, a coordinate-indexed
classifier produces an actual valid opposite-side datum and positive step. -/
theorem exists_valid_positive_exit_at_first_wall
    (hValid : data.Valid) (start finish : coordinate → ℚ)
    (hstart : ∀ i, 0 < start i) (houtside : ∃ i, finish i < 0)
    (hsimple : SimpleNegativeCrossings start finish)
    (caseAt : coordinate → SourceCase)
    (familyAt : ∀ wall, Family (coordinate := coordinate)
      (caseAt wall).arity data)
    (hwallColumn : ∀ wall, (familyAt wall).wallColumn = wall)
    (incomingAt : ∀ wall, Fin (caseAt wall).arity)
    (hincomingNonzero : ∀ wall,
      ((familyAt wall).matrix (incomingAt wall)).det ≠ 0)
    (outgoingVelocity : ∀ wall,
      Fin (caseAt wall).arity → coordinate → ℚ)
    (hSystems : ∀ wall outgoing,
      ((familyAt wall).matrix outgoing).det ≠ 0 →
      ((familyAt wall).matrix (incomingAt wall)).mulVec
          (fun i => finish i - start i) =
        ((familyAt wall).matrix outgoing).mulVec
          (outgoingVelocity wall outgoing)) :
    ∃ wall : coordinate, ∃ time : ℚ,
      0 < time ∧ time < 1 ∧
      RationalAffineWall.segment start finish time wall = 0 ∧
      ∃ outgoing : Fin (caseAt wall).arity,
        ((familyAt wall).candidate outgoing).datum.Valid ∧
        ((familyAt wall).matrix (incomingAt wall)).det *
            ((familyAt wall).matrix outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (RationalAffineWall.segment start finish time +
            t • outgoingVelocity wall outgoing) i) ∧
          ((familyAt wall).matrix outgoing).mulVec
              (RationalAffineWall.segment start finish time +
                t • outgoingVelocity wall outgoing) =
            ((familyAt wall).matrix (incomingAt wall)).mulVec
                (RationalAffineWall.segment start finish time) +
              t • ((familyAt wall).matrix (incomingAt wall)).mulVec
                (fun i => finish i - start i) := by
  obtain ⟨wall, time, htimePos, htimeLt, hzero, hother, _⟩ :=
    exists_first_positiveOrthant_exit start finish hstart houtside hsimple
  have hfinishWall : finish wall < 0 := by
    by_contra hnot
    have hfinishNonneg : 0 ≤ finish wall := le_of_not_gt hnot
    have hstartPart : 0 < (1 - time) * start wall :=
      mul_pos (sub_pos.mpr htimeLt) (hstart wall)
    have hfinishPart : 0 ≤ time * finish wall :=
      mul_nonneg htimePos.le hfinishNonneg
    unfold RationalAffineWall.segment at hzero
    nlinarith
  let event : WallEvent data coordinate :=
    { sourceCase := caseAt wall
      family := familyAt wall
      incoming := incomingAt wall
      incomingNonzero := hincomingNonzero wall
      wallPoint := RationalAffineWall.segment start finish time
      incomingVelocity := fun i => finish i - start i
      outgoingVelocity := outgoingVelocity wall
      wallPoint_zero := by
        rw [hwallColumn wall]
        exact hzero
      wallPoint_positive := by
        intro i hi
        apply hother i
        intro hiWall
        apply hi
        exact hiWall.trans (hwallColumn wall).symm
      systems := hSystems wall
      incomingDirection := by
        rw [hwallColumn wall]
        linarith [hstart wall, hfinishWall] }
  obtain ⟨outgoing, hvalid, hsign, hstep⟩ :=
    event.exists_valid_positive_exit hValid
  exact ⟨wall, time, htimePos, htimeLt, hzero, outgoing, hvalid, hsign, hstep⟩

/-- Presentation-preserving first-wall continuation.  In addition to the
valid positive outgoing step, every sufficiently small step carries the
explicit cleared rank-one pencil of the selected globally assembled
candidate. -/
theorem exists_valid_positive_exit_with_pencil_at_first_wall
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (start finish : coordinate → ℚ)
    (hstart : ∀ i, 0 < start i) (houtside : ∃ i, finish i < 0)
    (hsimple : SimpleNegativeCrossings start finish)
    (targetWallAt : coordinate → target.V)
    (caseAt : coordinate → SourceCase)
    (familyAt : ∀ wall, PresentedFamily (coordinate := coordinate)
      (caseAt wall).arity data (targetWallAt wall))
    (hwallColumn : ∀ wall, (familyAt wall).wallColumn = wall)
    (incomingAt : ∀ wall, Fin (caseAt wall).arity)
    (hincomingNonzero : ∀ wall,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).det ≠ 0)
    (outgoingVelocity : ∀ wall,
      Fin (caseAt wall).arity → coordinate → ℚ)
    (hSystems : ∀ wall outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).mulVec
          (fun i => finish i - start i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall).presentation outgoing)).mulVec
            (outgoingVelocity wall outgoing)) :
    ∃ wall : coordinate, ∃ time : ℚ,
      0 < time ∧ time < 1 ∧
      RationalAffineWall.segment start finish time wall = 0 ∧
      ∃ outgoing : Fin (caseAt wall).arity,
        ((familyAt wall).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation (incomingAt wall))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation outgoing)).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (RationalAffineWall.segment start finish time +
            t • outgoingVelocity wall outgoing) i) ∧
          (GluingDatum.LengthMatrixPresentation.matrix
              ((familyAt wall).presentation outgoing)).mulVec
                (RationalAffineWall.segment start finish time +
                  t • outgoingVelocity wall outgoing) =
            (GluingDatum.LengthMatrixPresentation.matrix
              ((familyAt wall).presentation (incomingAt wall))).mulVec
                (RationalAffineWall.segment start finish time) +
              t • (GluingDatum.LengthMatrixPresentation.matrix
                ((familyAt wall).presentation (incomingAt wall))).mulVec
                  (fun i => finish i - start i) ∧
          Nonempty (Candidate.ClearedPencil
            ((familyAt wall).candidate outgoing)
            ((familyAt wall).presentation outgoing)
            (RationalAffineWall.segment start finish time +
              t • outgoingVelocity wall outgoing)) := by
  obtain ⟨wall, time, htimePos, htimeLt, hzero, hother, _⟩ :=
    exists_first_positiveOrthant_exit start finish hstart houtside hsimple
  have hfinishWall : finish wall < 0 := by
    by_contra hnot
    have hfinishNonneg : 0 ≤ finish wall := le_of_not_gt hnot
    have hstartPart : 0 < (1 - time) * start wall :=
      mul_pos (sub_pos.mpr htimeLt) (hstart wall)
    have hfinishPart : 0 ≤ time * finish wall :=
      mul_nonneg htimePos.le hfinishNonneg
    unfold RationalAffineWall.segment at hzero
    nlinarith
  let event : PresentedWallEvent data (targetWallAt wall) coordinate :=
    { sourceCase := caseAt wall
      family := familyAt wall
      incoming := incomingAt wall
      incomingNonzero := hincomingNonzero wall
      wallPoint := RationalAffineWall.segment start finish time
      incomingVelocity := fun i => finish i - start i
      outgoingVelocity := outgoingVelocity wall
      wallPoint_zero := by
        rw [hwallColumn wall]
        exact hzero
      wallPoint_positive := by
        intro i hi
        apply hother i
        intro hiWall
        apply hi
        exact hiWall.trans (hwallColumn wall).symm
      systems := hSystems wall
      incomingDirection := by
        rw [hwallColumn wall]
        linarith [hstart wall, hfinishWall] }
  obtain ⟨outgoing, hvalid, hsign, hstep⟩ :=
    event.exists_valid_positive_exit_with_pencil hValid hTargetConnected
      hTargetGenus root
  exact ⟨wall, time, htimePos, htimeLt, hzero, outgoing, hvalid, hsign,
    hstep⟩

/-- The first-wall exit can be resumed as a segment in the outgoing cone.
Besides a positive outgoing point, this records two exact transport facts:
the new start represents the original base segment at the advanced parameter,
and the (possibly nonpositive) outgoing endpoint coordinates represent the
original closed endpoint.  Thus a wall transition changes coordinates and
the gluing datum without changing the base deformation being followed. -/
theorem exists_valid_resumed_segment_at_first_wall
    (hValid : data.Valid) (start finish : coordinate → ℚ)
    (hstart : ∀ i, 0 < start i) (houtside : ∃ i, finish i < 0)
    (hsimple : SimpleNegativeCrossings start finish)
    (caseAt : coordinate → SourceCase)
    (familyAt : ∀ wall, Family (coordinate := coordinate)
      (caseAt wall).arity data)
    (hwallColumn : ∀ wall, (familyAt wall).wallColumn = wall)
    (incomingAt : ∀ wall, Fin (caseAt wall).arity)
    (hincomingNonzero : ∀ wall,
      ((familyAt wall).matrix (incomingAt wall)).det ≠ 0)
    (outgoingVelocity : ∀ wall,
      Fin (caseAt wall).arity → coordinate → ℚ)
    (hSystems : ∀ wall outgoing,
      ((familyAt wall).matrix outgoing).det ≠ 0 →
      ((familyAt wall).matrix (incomingAt wall)).mulVec
          (fun i => finish i - start i) =
        ((familyAt wall).matrix outgoing).mulVec
          (outgoingVelocity wall outgoing)) :
    ∃ wall : coordinate, ∃ time : ℚ,
      ∃ outgoing : Fin (caseAt wall).arity, ∃ ε : ℚ,
        0 < time ∧ time < 1 ∧ 0 < ε ∧ ε < 1 - time ∧
        RationalAffineWall.segment start finish time wall = 0 ∧
        ((familyAt wall).candidate outgoing).datum.Valid ∧
        ((familyAt wall).matrix (incomingAt wall)).det *
            ((familyAt wall).matrix outgoing).det < 0 ∧
        (∀ i, 0 < (RationalAffineWall.segment start finish time +
          ε • outgoingVelocity wall outgoing) i) ∧
        ((familyAt wall).matrix outgoing).mulVec
            (RationalAffineWall.segment start finish time +
              ε • outgoingVelocity wall outgoing) =
          ((familyAt wall).matrix (incomingAt wall)).mulVec
            (RationalAffineWall.segment start finish (time + ε)) ∧
        ((familyAt wall).matrix outgoing).mulVec
            (RationalAffineWall.segment start finish time +
              (1 - time) • outgoingVelocity wall outgoing) =
          ((familyAt wall).matrix (incomingAt wall)).mulVec finish := by
  obtain ⟨wall, time, htimePos, htimeLt, hwallZero, outgoing, hvalid, hsign,
      δ, hδ, hstep⟩ :=
    exists_valid_positive_exit_at_first_wall hValid start finish hstart
      houtside hsimple caseAt familyAt hwallColumn incomingAt
      hincomingNonzero outgoingVelocity hSystems
  let ε : ℚ := min δ ((1 - time) / 2)
  have hHalfPos : 0 < (1 - time) / 2 := by linarith
  have hεPos : 0 < ε := lt_min hδ hHalfPos
  have hεLe : ε ≤ δ := min_le_left _ _
  have hεLtRemaining : ε < 1 - time := by
    exact (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨hpositive, hmap⟩ := hstep ε hεPos hεLe
  let incomingMatrix := (familyAt wall).matrix (incomingAt wall)
  let outgoingMatrix := (familyAt wall).matrix outgoing
  let wallPoint := RationalAffineWall.segment start finish time
  let incomingVelocity : coordinate → ℚ := fun i => finish i - start i
  let selectedOutgoingVelocity := outgoingVelocity wall outgoing
  have hSystem : incomingMatrix.mulVec incomingVelocity =
      outgoingMatrix.mulVec selectedOutgoingVelocity :=
    hSystems wall outgoing
      (ClassifiedContinuation.det_ne_zero_of_mul_det_neg hsign)
  have hWallMap : outgoingMatrix.mulVec wallPoint =
      incomingMatrix.mulVec wallPoint := by
    have hExpanded := hmap
    change outgoingMatrix.mulVec
        (wallPoint + ε • selectedOutgoingVelocity) =
      incomingMatrix.mulVec wallPoint +
        ε • incomingMatrix.mulVec incomingVelocity at hExpanded
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hSystem] at hExpanded
    ext i
    have hi := congrFun hExpanded i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    linarith
  have hSegmentStep :
      RationalAffineWall.segment start finish (time + ε) =
        wallPoint + ε • incomingVelocity := by
    ext i
    simp only [RationalAffineWall.segment, wallPoint, incomingVelocity,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hStepMap :
      outgoingMatrix.mulVec (wallPoint + ε • selectedOutgoingVelocity) =
        incomingMatrix.mulVec
          (RationalAffineWall.segment start finish (time + ε)) := by
    calc
      outgoingMatrix.mulVec (wallPoint + ε • selectedOutgoingVelocity) =
          incomingMatrix.mulVec wallPoint +
            ε • incomingMatrix.mulVec incomingVelocity := by
              exact hmap
      _ = incomingMatrix.mulVec
          (RationalAffineWall.segment start finish (time + ε)) := by
            rw [hSegmentStep, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hFinishCoordinates :
      finish = wallPoint + (1 - time) • incomingVelocity := by
    ext i
    simp only [RationalAffineWall.segment, wallPoint, incomingVelocity,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hFinishMap :
      outgoingMatrix.mulVec
          (wallPoint + (1 - time) • selectedOutgoingVelocity) =
        incomingMatrix.mulVec finish := by
    calc
      outgoingMatrix.mulVec
          (wallPoint + (1 - time) • selectedOutgoingVelocity) =
          outgoingMatrix.mulVec wallPoint +
            (1 - time) • outgoingMatrix.mulVec selectedOutgoingVelocity := by
              rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = incomingMatrix.mulVec wallPoint +
          (1 - time) • incomingMatrix.mulVec incomingVelocity := by
            rw [hWallMap, hSystem]
      _ = incomingMatrix.mulVec
          (wallPoint + (1 - time) • incomingVelocity) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = incomingMatrix.mulVec finish := by rw [← hFinishCoordinates]
  exact ⟨wall, time, outgoing, ε, htimePos, htimeLt, hεPos,
    hεLtRemaining, hwallZero, hvalid, hsign, hpositive, hStepMap, hFinishMap⟩

/-- Presentation-preserving form of `exists_valid_resumed_segment_at_first_wall`.
The chosen positive restart retains its exact cleared subdivision pencil while
the two matrix identities rebase the same deformation in the outgoing chart. -/
theorem exists_valid_resumed_segment_with_pencil_at_first_wall
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (start finish : coordinate → ℚ)
    (hstart : ∀ i, 0 < start i) (houtside : ∃ i, finish i < 0)
    (hsimple : SimpleNegativeCrossings start finish)
    (targetWallAt : coordinate → target.V)
    (caseAt : coordinate → SourceCase)
    (familyAt : ∀ wall, PresentedFamily (coordinate := coordinate)
      (caseAt wall).arity data (targetWallAt wall))
    (hwallColumn : ∀ wall, (familyAt wall).wallColumn = wall)
    (incomingAt : ∀ wall, Fin (caseAt wall).arity)
    (hincomingNonzero : ∀ wall,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).det ≠ 0)
    (outgoingVelocity : ∀ wall,
      Fin (caseAt wall).arity → coordinate → ℚ)
    (hSystems : ∀ wall outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).mulVec
          (fun i => finish i - start i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall).presentation outgoing)).mulVec
            (outgoingVelocity wall outgoing)) :
    ∃ wall : coordinate, ∃ time : ℚ,
      ∃ outgoing : Fin (caseAt wall).arity, ∃ ε : ℚ,
        0 < time ∧ time < 1 ∧ 0 < ε ∧ ε < 1 - time ∧
        RationalAffineWall.segment start finish time wall = 0 ∧
        ((familyAt wall).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation (incomingAt wall))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation outgoing)).det < 0 ∧
        (∀ i, 0 < (RationalAffineWall.segment start finish time +
          ε • outgoingVelocity wall outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation outgoing)).mulVec
              (RationalAffineWall.segment start finish time +
                ε • outgoingVelocity wall outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation (incomingAt wall))).mulVec
              (RationalAffineWall.segment start finish (time + ε)) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation outgoing)).mulVec
              (RationalAffineWall.segment start finish time +
                (1 - time) • outgoingVelocity wall outgoing) =
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation (incomingAt wall))).mulVec finish ∧
        Nonempty (Candidate.ClearedPencil
          ((familyAt wall).candidate outgoing)
          ((familyAt wall).presentation outgoing)
          (RationalAffineWall.segment start finish time +
            ε • outgoingVelocity wall outgoing)) := by
  obtain ⟨wall, time, htimePos, htimeLt, hwallZero, outgoing, hvalid, hsign,
      δ, hδ, hstep⟩ :=
    exists_valid_positive_exit_with_pencil_at_first_wall hValid
      hTargetConnected hTargetGenus root start finish hstart houtside hsimple
      targetWallAt caseAt familyAt hwallColumn incomingAt hincomingNonzero
      outgoingVelocity hSystems
  let ε : ℚ := min δ ((1 - time) / 2)
  have hHalfPos : 0 < (1 - time) / 2 := by linarith
  have hεPos : 0 < ε := lt_min hδ hHalfPos
  have hεLe : ε ≤ δ := min_le_left _ _
  have hεLtRemaining : ε < 1 - time := by
    exact (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨hpositive, hmap, hpencil⟩ := hstep ε hεPos hεLe
  let incomingMatrix := GluingDatum.LengthMatrixPresentation.matrix
    ((familyAt wall).presentation (incomingAt wall))
  let outgoingMatrix := GluingDatum.LengthMatrixPresentation.matrix
    ((familyAt wall).presentation outgoing)
  let wallPoint := RationalAffineWall.segment start finish time
  let incomingVelocity : coordinate → ℚ := fun i => finish i - start i
  let selectedOutgoingVelocity := outgoingVelocity wall outgoing
  have hSystem : incomingMatrix.mulVec incomingVelocity =
      outgoingMatrix.mulVec selectedOutgoingVelocity :=
    hSystems wall outgoing
      (ClassifiedContinuation.det_ne_zero_of_mul_det_neg hsign)
  have hWallMap : outgoingMatrix.mulVec wallPoint =
      incomingMatrix.mulVec wallPoint := by
    have hExpanded := hmap
    change outgoingMatrix.mulVec
        (wallPoint + ε • selectedOutgoingVelocity) =
      incomingMatrix.mulVec wallPoint +
        ε • incomingMatrix.mulVec incomingVelocity at hExpanded
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hSystem] at hExpanded
    ext i
    have hi := congrFun hExpanded i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    linarith
  have hSegmentStep :
      RationalAffineWall.segment start finish (time + ε) =
        wallPoint + ε • incomingVelocity := by
    ext i
    simp only [RationalAffineWall.segment, wallPoint, incomingVelocity,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hStepMap :
      outgoingMatrix.mulVec (wallPoint + ε • selectedOutgoingVelocity) =
        incomingMatrix.mulVec
          (RationalAffineWall.segment start finish (time + ε)) := by
    calc
      outgoingMatrix.mulVec (wallPoint + ε • selectedOutgoingVelocity) =
          incomingMatrix.mulVec wallPoint +
            ε • incomingMatrix.mulVec incomingVelocity := hmap
      _ = incomingMatrix.mulVec
          (RationalAffineWall.segment start finish (time + ε)) := by
            rw [hSegmentStep, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hFinishCoordinates :
      finish = wallPoint + (1 - time) • incomingVelocity := by
    ext i
    simp only [RationalAffineWall.segment, wallPoint, incomingVelocity,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hFinishMap :
      outgoingMatrix.mulVec
          (wallPoint + (1 - time) • selectedOutgoingVelocity) =
        incomingMatrix.mulVec finish := by
    calc
      outgoingMatrix.mulVec
          (wallPoint + (1 - time) • selectedOutgoingVelocity) =
          outgoingMatrix.mulVec wallPoint +
            (1 - time) • outgoingMatrix.mulVec selectedOutgoingVelocity := by
              rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = incomingMatrix.mulVec wallPoint +
          (1 - time) • incomingMatrix.mulVec incomingVelocity := by
            rw [hWallMap, hSystem]
      _ = incomingMatrix.mulVec
          (wallPoint + (1 - time) • incomingVelocity) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = incomingMatrix.mulVec finish := by rw [← hFinishCoordinates]
  exact ⟨wall, time, outgoing, ε, htimePos, htimeLt, hεPos,
    hεLtRemaining, hwallZero, hvalid, hsign, hpositive, hStepMap, hFinishMap,
    hpencil⟩

omit [DecidableEq coordinate] in
/-- A square rational length matrix carries an affine coordinate segment to
the affine segment between the two represented stable metrics. -/
theorem mulVec_segment (matrix : Matrix coordinate coordinate ℚ)
    (start finish : coordinate → ℚ) (time : ℚ) :
    matrix.mulVec (RationalAffineWall.segment start finish time) =
      RationalAffineWall.segment (matrix.mulVec start)
        (matrix.mulVec finish) time := by
  have hSegment :
      RationalAffineWall.segment start finish time =
        start + time • (finish - start) := by
    ext i
    simp [RationalAffineWall.segment]
  rw [hSegment, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub]
  ext i
  simp [RationalAffineWall.segment]

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- Restarting a segment at global time `currentTime` and using a local
parameter `localTime` is the original segment at the corresponding affine
global parameter. -/
theorem segment_rebase_right (start finish : coordinate → ℚ)
    (currentTime localTime : ℚ) :
    RationalAffineWall.segment
        (RationalAffineWall.segment start finish currentTime) finish localTime =
      RationalAffineWall.segment start finish
        (currentTime + (1 - currentTime) * localTime) := by
  ext i
  simp only [RationalAffineWall.segment]
  ring

/-- Global-parameter form of the first-wall continuation theorem.

The current chart starts at `currentTime` on one fixed base deformation and
represents its closed endpoint through `currentFinish`.  The theorem chooses a
wall and a positive restart in an outgoing chart, proves that both its wall
time and restart time strictly advance in the original global parameter, and
proves that the outgoing chart still represents the same base endpoint.  This
is the state-transport statement needed to iterate local continuation without
changing the deformation path. -/
theorem exists_valid_resumed_global_segment_at_first_wall
    (hValid : data.Valid)
    (baseStart baseFinish currentStart currentFinish : coordinate → ℚ)
    (currentTime : ℚ) (hcurrentTime : currentTime < 1)
    (hstart : ∀ i, 0 < currentStart i)
    (houtside : ∃ i, currentFinish i < 0)
    (hsimple : SimpleNegativeCrossings currentStart currentFinish)
    (caseAt : coordinate → SourceCase)
    (familyAt : ∀ wall, Family (coordinate := coordinate)
      (caseAt wall).arity data)
    (hwallColumn : ∀ wall, (familyAt wall).wallColumn = wall)
    (incomingAt : ∀ wall, Fin (caseAt wall).arity)
    (hincomingNonzero : ∀ wall,
      ((familyAt wall).matrix (incomingAt wall)).det ≠ 0)
    (currentMatrix : Matrix coordinate coordinate ℚ)
    (hincomingMatrix : ∀ wall,
      (familyAt wall).matrix (incomingAt wall) = currentMatrix)
    (hcurrentStartMap : currentMatrix.mulVec currentStart =
      RationalAffineWall.segment baseStart baseFinish currentTime)
    (hcurrentFinishMap : currentMatrix.mulVec currentFinish = baseFinish)
    (outgoingVelocity : ∀ wall,
      Fin (caseAt wall).arity → coordinate → ℚ)
    (hSystems : ∀ wall outgoing,
      ((familyAt wall).matrix outgoing).det ≠ 0 →
      ((familyAt wall).matrix (incomingAt wall)).mulVec
          (fun i => currentFinish i - currentStart i) =
        ((familyAt wall).matrix outgoing).mulVec
          (outgoingVelocity wall outgoing)) :
    ∃ wall : coordinate, ∃ localTime : ℚ,
      ∃ outgoing : Fin (caseAt wall).arity, ∃ ε : ℚ,
        0 < localTime ∧ localTime < 1 ∧
        0 < ε ∧ ε < 1 - localTime ∧
        RationalAffineWall.segment currentStart currentFinish
          localTime wall = 0 ∧
        currentTime < currentTime + (1 - currentTime) * localTime ∧
        currentTime + (1 - currentTime) * localTime <
          currentTime + (1 - currentTime) * (localTime + ε) ∧
        currentTime + (1 - currentTime) * (localTime + ε) < 1 ∧
        ((familyAt wall).candidate outgoing).datum.Valid ∧
        ((familyAt wall).matrix (incomingAt wall)).det *
            ((familyAt wall).matrix outgoing).det < 0 ∧
        (∀ i, 0 < (RationalAffineWall.segment currentStart currentFinish
          localTime + ε • outgoingVelocity wall outgoing) i) ∧
        ((familyAt wall).matrix outgoing).mulVec
            (RationalAffineWall.segment currentStart currentFinish localTime +
              ε • outgoingVelocity wall outgoing) =
          RationalAffineWall.segment baseStart baseFinish
            (currentTime + (1 - currentTime) * (localTime + ε)) ∧
        ((familyAt wall).matrix outgoing).mulVec
            (RationalAffineWall.segment currentStart currentFinish localTime +
              (1 - localTime) • outgoingVelocity wall outgoing) =
          baseFinish := by
  obtain ⟨wall, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
      hεPos, hεLt, hwallZero, hvalid, hsign, hpositive, hrestartMap,
      hfinishMap⟩ :=
    exists_valid_resumed_segment_at_first_wall hValid currentStart
      currentFinish hstart houtside hsimple caseAt familyAt hwallColumn
      incomingAt hincomingNonzero outgoingVelocity hSystems
  have hremainingPos : 0 < 1 - currentTime := sub_pos.mpr hcurrentTime
  have hlocalRestartLt : localTime + ε < 1 := by linarith
  have hwallAdvance :
      currentTime < currentTime + (1 - currentTime) * localTime := by
    nlinarith [mul_pos hremainingPos hlocalTimePos]
  have hrestartAdvance :
      currentTime + (1 - currentTime) * localTime <
        currentTime + (1 - currentTime) * (localTime + ε) := by
    nlinarith [mul_pos hremainingPos hεPos]
  have hrestartLt :
      currentTime + (1 - currentTime) * (localTime + ε) < 1 := by
    have hlocalRemaining : 0 < 1 - (localTime + ε) :=
      sub_pos.mpr hlocalRestartLt
    nlinarith [mul_pos hremainingPos hlocalRemaining]
  have hcurrentSegmentMap (time : ℚ) :
      ((familyAt wall).matrix (incomingAt wall)).mulVec
          (RationalAffineWall.segment currentStart currentFinish time) =
        RationalAffineWall.segment baseStart baseFinish
          (currentTime + (1 - currentTime) * time) := by
    rw [hincomingMatrix wall, mulVec_segment, hcurrentStartMap,
      hcurrentFinishMap, segment_rebase_right]
  have hglobalRestartMap :
      ((familyAt wall).matrix outgoing).mulVec
          (RationalAffineWall.segment currentStart currentFinish localTime +
            ε • outgoingVelocity wall outgoing) =
        RationalAffineWall.segment baseStart baseFinish
          (currentTime + (1 - currentTime) * (localTime + ε)) := by
    exact hrestartMap.trans (hcurrentSegmentMap (localTime + ε))
  have hglobalFinishMap :
      ((familyAt wall).matrix outgoing).mulVec
          (RationalAffineWall.segment currentStart currentFinish localTime +
            (1 - localTime) • outgoingVelocity wall outgoing) =
        baseFinish := by
    calc
      _ = ((familyAt wall).matrix (incomingAt wall)).mulVec currentFinish :=
        hfinishMap
      _ = currentMatrix.mulVec currentFinish := by rw [hincomingMatrix wall]
      _ = baseFinish := hcurrentFinishMap
  exact ⟨wall, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
    hεPos, hεLt, hwallZero, hwallAdvance, hrestartAdvance, hrestartLt, hvalid,
    hsign, hpositive, hglobalRestartMap, hglobalFinishMap⟩

/-- Global-parameter continuation with semantic presentations retained.
Besides the strict global-time advances and endpoint transport, the selected
outgoing restart carries its explicit cleared rank-one pencil. -/
theorem exists_valid_resumed_global_segment_with_pencil_at_first_wall
    (hValid : data.Valid)
    (hTargetConnected : graph_connected target)
    (hTargetGenus : genus target = 0) (root : target.V)
    (baseStart baseFinish currentStart currentFinish : coordinate → ℚ)
    (currentTime : ℚ) (hcurrentTime : currentTime < 1)
    (hstart : ∀ i, 0 < currentStart i)
    (houtside : ∃ i, currentFinish i < 0)
    (hsimple : SimpleNegativeCrossings currentStart currentFinish)
    (targetWallAt : coordinate → target.V)
    (caseAt : coordinate → SourceCase)
    (familyAt : ∀ wall, PresentedFamily (coordinate := coordinate)
      (caseAt wall).arity data (targetWallAt wall))
    (hwallColumn : ∀ wall, (familyAt wall).wallColumn = wall)
    (incomingAt : ∀ wall, Fin (caseAt wall).arity)
    (hincomingNonzero : ∀ wall,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).det ≠ 0)
    (currentMatrix : Matrix coordinate coordinate ℚ)
    (hincomingMatrix : ∀ wall,
      GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall)) = currentMatrix)
    (hcurrentStartMap : currentMatrix.mulVec currentStart =
      RationalAffineWall.segment baseStart baseFinish currentTime)
    (hcurrentFinishMap : currentMatrix.mulVec currentFinish = baseFinish)
    (outgoingVelocity : ∀ wall,
      Fin (caseAt wall).arity → coordinate → ℚ)
    (hSystems : ∀ wall outgoing,
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation outgoing)).det ≠ 0 →
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).mulVec
          (fun i => currentFinish i - currentStart i) =
        (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall).presentation outgoing)).mulVec
            (outgoingVelocity wall outgoing)) :
    ∃ wall : coordinate, ∃ localTime : ℚ,
      ∃ outgoing : Fin (caseAt wall).arity, ∃ ε : ℚ,
        0 < localTime ∧ localTime < 1 ∧
        0 < ε ∧ ε < 1 - localTime ∧
        RationalAffineWall.segment currentStart currentFinish
          localTime wall = 0 ∧
        currentTime < currentTime + (1 - currentTime) * localTime ∧
        currentTime + (1 - currentTime) * localTime <
          currentTime + (1 - currentTime) * (localTime + ε) ∧
        currentTime + (1 - currentTime) * (localTime + ε) < 1 ∧
        ((familyAt wall).candidate outgoing).datum.Valid ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation (incomingAt wall))).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation outgoing)).det < 0 ∧
        (∀ i, 0 < (RationalAffineWall.segment currentStart currentFinish
          localTime + ε • outgoingVelocity wall outgoing) i) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation outgoing)).mulVec
              (RationalAffineWall.segment currentStart currentFinish localTime +
                ε • outgoingVelocity wall outgoing) =
          RationalAffineWall.segment baseStart baseFinish
            (currentTime + (1 - currentTime) * (localTime + ε)) ∧
        (GluingDatum.LengthMatrixPresentation.matrix
            ((familyAt wall).presentation outgoing)).mulVec
              (RationalAffineWall.segment currentStart currentFinish localTime +
                (1 - localTime) • outgoingVelocity wall outgoing) =
          baseFinish ∧
        Nonempty (Candidate.ClearedPencil
          ((familyAt wall).candidate outgoing)
          ((familyAt wall).presentation outgoing)
          (RationalAffineWall.segment currentStart currentFinish localTime +
            ε • outgoingVelocity wall outgoing)) := by
  obtain ⟨wall, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
      hεPos, hεLt, hwallZero, hvalid, hsign, hpositive, hrestartMap,
      hfinishMap, hpencil⟩ :=
    exists_valid_resumed_segment_with_pencil_at_first_wall hValid
      hTargetConnected hTargetGenus root currentStart currentFinish hstart
      houtside hsimple targetWallAt caseAt familyAt hwallColumn incomingAt
      hincomingNonzero outgoingVelocity hSystems
  have hremainingPos : 0 < 1 - currentTime := sub_pos.mpr hcurrentTime
  have hlocalRestartLt : localTime + ε < 1 := by linarith
  have hwallAdvance :
      currentTime < currentTime + (1 - currentTime) * localTime := by
    nlinarith [mul_pos hremainingPos hlocalTimePos]
  have hrestartAdvance :
      currentTime + (1 - currentTime) * localTime <
        currentTime + (1 - currentTime) * (localTime + ε) := by
    nlinarith [mul_pos hremainingPos hεPos]
  have hrestartLt :
      currentTime + (1 - currentTime) * (localTime + ε) < 1 := by
    have hlocalRemaining : 0 < 1 - (localTime + ε) :=
      sub_pos.mpr hlocalRestartLt
    nlinarith [mul_pos hremainingPos hlocalRemaining]
  have hcurrentSegmentMap (time : ℚ) :
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation (incomingAt wall))).mulVec
          (RationalAffineWall.segment currentStart currentFinish time) =
        RationalAffineWall.segment baseStart baseFinish
          (currentTime + (1 - currentTime) * time) := by
    rw [hincomingMatrix wall, mulVec_segment, hcurrentStartMap,
      hcurrentFinishMap, segment_rebase_right]
  have hglobalRestartMap :
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation outgoing)).mulVec
          (RationalAffineWall.segment currentStart currentFinish localTime +
            ε • outgoingVelocity wall outgoing) =
        RationalAffineWall.segment baseStart baseFinish
          (currentTime + (1 - currentTime) * (localTime + ε)) := by
    exact hrestartMap.trans (hcurrentSegmentMap (localTime + ε))
  have hglobalFinishMap :
      (GluingDatum.LengthMatrixPresentation.matrix
        ((familyAt wall).presentation outgoing)).mulVec
          (RationalAffineWall.segment currentStart currentFinish localTime +
            (1 - localTime) • outgoingVelocity wall outgoing) =
        baseFinish := by
    calc
      _ = (GluingDatum.LengthMatrixPresentation.matrix
          ((familyAt wall).presentation (incomingAt wall))).mulVec
            currentFinish := hfinishMap
      _ = currentMatrix.mulVec currentFinish := by rw [hincomingMatrix wall]
      _ = baseFinish := hcurrentFinishMap
  exact ⟨wall, localTime, outgoing, ε, hlocalTimePos, hlocalTimeLt,
    hεPos, hεLt, hwallZero, hwallAdvance, hrestartAdvance, hrestartLt, hvalid,
    hsign, hpositive, hglobalRestartMap, hglobalFinishMap, hpencil⟩

end DraismaVargas.LocalCases.MarchContinuation
