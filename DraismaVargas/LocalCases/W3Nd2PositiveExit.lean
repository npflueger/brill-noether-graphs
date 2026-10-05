module

public import DraismaVargas.LocalCases.W3Nd2CoarseStableGraph
public import DraismaVargas.LocalCases.W3Nd2FineStableGraph
public import DraismaVargas.LocalCases.W3Nd2CommonBalance
public import DraismaVargas.LocalCases.StableGraphFullDimensional
public import DraismaVargas.LocalCases.FiniteAtlasMarch

@[expose] public section

/-!
# A positive continuation through the actual Figure 31 pair

An identified full-dimensional coarse or fine member determines the common
coordinate order.  Equation (5) chooses an opposite-sign member, the actual
stable-incidence equivalences transport full-dimensional source data, and the
existing chart solver supplies the positive rational exit and cleared pencil.
This does not match an arbitrary incoming cover to the Figure 31 family.
-/

namespace DraismaVargas.LocalCases.W3Nd2PositiveExit

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource ThirdEquation FullDimensionalSource
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)

/-- Each actual Figure 31 member is equivalent to the original stable
incidence graph, with exactly the row map used in the matrix calculation. -/
noncomputable def equivalence (position : Fin 2) :
    StableGraphIncidence.Equivalence data
      (W3Nd2CommonBalance.candidates input profile position).datum :=
  Fin.cases (W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile)
    (Fin.cases (W3Nd2FineStableGraph.fineStableGraphEquivalence input profile)
      (fun i ↦ Fin.elim0 i)) position

theorem equivalence_row (position : Fin 2) :
    (equivalence input profile position).row =
      W3Nd2CommonBalance.rowEquiv input profile position := by
  fin_cases position <;> rfl

/-- Compare any two actual members through the old stable graph. -/
noncomputable def between (first second : Fin 2) :
    StableGraphIncidence.Equivalence
      (W3Nd2CommonBalance.candidates input profile first).datum
      (W3Nd2CommonBalance.candidates input profile second).datum :=
  (equivalence input profile first).symm.trans (equivalence input profile second)

theorem candidates_valid (position : Fin 2) :
    (W3Nd2CommonBalance.candidates input profile position).datum.Valid :=
  (W3Nd2CommonBalance.candidates input profile position).valid_of_old input.valid

theorem candidate_targetConnected (hConnected : graph_connected target)
    (position : Fin 2) :
    graph_connected
      (W3Nd2CommonBalance.candidates input profile position).outgoingTarget := by
  fin_cases position
  · change graph_connected (TargetExpansion.graph target wall _)
    exact TargetExpansion.graph_connected target wall _ hConnected
  · change graph_connected (TargetExpansion.graph target wall _)
    exact TargetExpansion.graph_connected target wall _ hConnected

theorem candidate_targetGenus (hGenus : genus target = 0) (position : Fin 2) :
    genus (W3Nd2CommonBalance.candidates input profile position).outgoingTarget = 0 := by
  fin_cases position
  · change genus (TargetExpansion.graph target wall _) = 0
    simpa using hGenus
  · change genus (TargetExpansion.graph target wall _) = 0
    simpa using hGenus

theorem candidate_targetEdgeCard (position : Fin 2) :
    (W3Nd2CommonBalance.candidates input profile position).outgoingTarget.edges.card =
      target.edges.card + 1 := by
  fin_cases position
  · change (TargetExpansion.graph target wall _).edges.card = _
    simp
  · change (TargetExpansion.graph target wall _).edges.card = _
    simp

theorem candidate_sourceGenus (position : Fin 2) :
    genus (W3Nd2CommonBalance.candidates input profile position).datum.sourceGraph =
      genus data.sourceGraph := by
  fin_cases position
  · exact coarseCandidate_sourceGenus input profile
  · exact fineCandidate_sourceGenus input profile

noncomputable def initialLabelling
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate) :
    StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate where
  row := (between input profile 0 incoming).row.trans incomingFD.labelling.row
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((W3Nd2CommonBalance.columnEquiv input profile incoming).symm.trans
      (W3Nd2CommonBalance.columnEquiv input profile 0))

noncomputable def outgoingLabelling
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate)
    (outgoing : Fin 2) :
    StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile outgoing).datum coordinate :=
  W3Nd2CommonBalance.labelling input profile
    (initialLabelling input profile incoming incomingFD) outgoing

/-- Transport a full-dimensional presentation to a chosen actual member.
Only that member's compatible matrix must be nonsingular. -/
noncomputable def outgoingPresentation
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming outgoing : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate)
    (outgoingDet :
      (GluingDatum.LengthMatrixPresentation.matrix
        (outgoingLabelling input profile incoming incomingFD outgoing).presentation).det ≠ 0) :
    FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile outgoing).datum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD
    (between input profile incoming outgoing)
    (candidates_valid input profile outgoing)
    (candidate_targetConnected input profile hConnected outgoing)
    (candidate_targetGenus input profile hGenus outgoing)
    ((candidate_targetEdgeCard input profile outgoing).trans
      (candidate_targetEdgeCard input profile incoming).symm)
    ((candidate_sourceGenus input profile outgoing).trans
      (candidate_sourceGenus input profile incoming).symm)
    (outgoingLabelling input profile incoming incomingFD outgoing)
    outgoingDet

/-- Transport to the common first member and back cancels both actual row
and target-occurrence equivalences. -/
theorem outgoingLabelling_self
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate) :
    outgoingLabelling input profile incoming incomingFD incoming =
      incomingFD.labelling := by
  cases incomingFD with
  | mk valid targetConnected targetGenus saturated labelling det_ne_zero trivalent pathEnds =>
    cases labelling with
    | mk targetEdge row =>
      simp only [outgoingLabelling, initialLabelling,
        W3Nd2CommonBalance.labelling, W3Nd2CommonBalance.sourceCoordinates,
        W3Nd2CommonBalance.targetCoordinates]
      congr 1
      · ext column
        simp
      · ext path
        have hBetween :
            (between input profile 0 incoming).row =
              (W3Nd2CommonBalance.rowEquiv input profile 0).symm.trans
                (W3Nd2CommonBalance.rowEquiv input profile incoming) := by
          change (equivalence input profile 0).row.symm.trans
              (equivalence input profile incoming).row = _
          rw [equivalence_row input profile 0,
            equivalence_row input profile incoming]
        rw [hBetween]
        simp

theorem incomingDet_ne_zero
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate) :
    (W3Nd2CommonBalance.squareMatrix input profile
      (initialLabelling input profile incoming incomingFD) incoming).det ≠ 0 := by
  change (GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling input profile incoming incomingFD incoming).presentation).det ≠ 0
  rw [outgoingLabelling_self input profile incoming incomingFD]
  exact incomingFD.det_ne_zero

/-- Equation (5) selects a genuinely nonsingular opposite-sign actual member
and stable incidence equips it with a full-dimensional presentation. -/
theorem exists_oppositePresentation
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate) :
    ∃ outgoing : Fin 2,
      ∃ _outgoingFD : FullDimensionalSourcePresentation
          (W3Nd2CommonBalance.candidates input profile outgoing).datum coordinate,
        (GluingDatum.LengthMatrixPresentation.matrix
          (outgoingLabelling input profile incoming incomingFD incoming).presentation).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            (outgoingLabelling input profile incoming incomingFD outgoing).presentation).det < 0 := by
  let initial := initialLabelling input profile incoming incomingFD
  have hIncoming :
      (W3Nd2CommonBalance.squareMatrix input profile initial incoming).det ≠ 0 :=
    incomingDet_ne_zero input profile incoming incomingFD
  obtain ⟨outgoing, _hValid, hSign⟩ :=
    W3Nd2CommonBalance.exists_valid_opposite input profile initial incoming hIncoming
  have hOutgoing :
      (GluingDatum.LengthMatrixPresentation.matrix
        (outgoingLabelling input profile incoming incomingFD outgoing).presentation).det ≠ 0 := by
    apply BalancedGlobal.det_ne_zero_of_mul_det_neg
      (A := W3Nd2CommonBalance.squareMatrix input profile initial incoming)
    simpa [W3Nd2CommonBalance.squareMatrix, outgoingLabelling] using hSign
  refine ⟨outgoing,
    outgoingPresentation input profile hConnected hGenus incoming outgoing incomingFD hOutgoing, ?_⟩
  simpa [W3Nd2CommonBalance.squareMatrix, outgoingLabelling] using hSign

section Exit

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum coordinate)

/-- The matrices are the actual induced-member presentations. -/
noncomputable def memberMatrix (outgoing : Fin 2) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling input profile incoming incomingFD outgoing).presentation

noncomputable def wallColumn : coordinate :=
  W3Nd2CommonBalance.wallColumn input profile
    (initialLabelling input profile incoming incomingFD)

/-- Canonical outgoing chart velocity at a nonsingular selected member. -/
noncomputable def outgoingVelocity (incomingVelocity : coordinate → ℚ)
    (outgoing : Fin 2) : coordinate → ℚ :=
  FiniteAtlasMarch.chartCoordinates
    (memberMatrix input profile incoming incomingFD outgoing)
    ((memberMatrix input profile incoming incomingFD incoming).mulVec incomingVelocity)

theorem outgoingVelocity_system (incomingVelocity : coordinate → ℚ)
    (outgoing : Fin 2)
    (hDet : (memberMatrix input profile incoming incomingFD outgoing).det ≠ 0) :
    (memberMatrix input profile incoming incomingFD incoming).mulVec incomingVelocity =
      (memberMatrix input profile incoming incomingFD outgoing).mulVec
        (outgoingVelocity input profile incoming incomingFD incomingVelocity outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

/-- Positive coordinates, the exact affine metric equation, and an actual
outgoing full-dimensional presentation on the selected Figure 31 member. -/
theorem exists_positive_exit
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn input profile incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input profile incoming incomingFD → 0 < z i)
    (hIncomingDirection : incomingVelocity
      (wallColumn input profile incoming incomingFD) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (W3Nd2CommonBalance.candidates input profile outgoing).datum coordinate,
        outgoingFD.labelling = outgoingLabelling input profile incoming incomingFD outgoing ∧
        (memberMatrix input profile incoming incomingFD incoming).det *
            (memberMatrix input profile incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity input profile incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix input profile incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity input profile incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix input profile incoming incomingFD incoming).mulVec z +
              t • (memberMatrix input profile incoming incomingFD incoming).mulVec
                incomingVelocity := by
  let initial := initialLabelling input profile incoming incomingFD
  let family := W3Nd2CommonBalance.family input profile initial
  have hIncoming : (family.matrix incoming).det ≠ 0 :=
    incomingDet_ne_zero input profile incoming incomingFD
  obtain ⟨outgoing, _hValid, hSign, δ, hδ, hStep⟩ :=
    family.exists_valid_positive_exit input.valid incoming hIncoming z incomingVelocity
      (outgoingVelocity input profile incoming incomingFD incomingVelocity)
      hz hzpos (outgoingVelocity_system input profile incoming incomingFD incomingVelocity)
      hIncomingDirection
  have hOutgoing : (memberMatrix input profile incoming incomingFD outgoing).det ≠ 0 :=
    BalancedGlobal.det_ne_zero_of_mul_det_neg hSign
  exact ⟨outgoing,
    outgoingPresentation input profile hConnected hGenus incoming outgoing incomingFD hOutgoing,
    rfl, hSign, δ, hδ, hStep⟩

/-- Positive coordinates clear at the datum's explicit rational realization
scale to a rank-one pencil on the member's literal source subdivision. -/
theorem exists_clearedPencil
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (outgoing : Fin 2) (coordinates : coordinate → ℚ)
    (hPositive : ∀ i, 0 < coordinates i) :
    ∃ realization :
        (W3Nd2CommonBalance.candidates input profile outgoing).datum.IntegralRealization,
      ∃ scale : ℕ, 0 < scale ∧
        (∀ column,
          (realization.targetLength
            ((outgoingLabelling input profile incoming incomingFD outgoing).targetEdge column) : ℚ) =
              (scale : ℚ) * coordinates column) ∧
        Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  let datum := (W3Nd2CommonBalance.candidates input profile outgoing).datum
  let labelling := outgoingLabelling input profile incoming incomingFD outgoing
  let targetLength := fun edge ↦ coordinates (labelling.targetEdge.symm edge)
  have hTargetPositive : ∀ edge, 0 < targetLength edge := fun edge ↦ hPositive _
  let realization :=
    GluingDatum.IntegralRealization.ofPositiveRational datum targetLength hTargetPositive
  let root : (W3Nd2CommonBalance.candidates input profile outgoing).outgoingTarget.V := by
    refine Fin.cases (TargetExpansion.oldVertex target wall) ?_ outgoing
    refine Fin.cases (TargetExpansion.oldVertex target wall) ?_
    exact fun i ↦ Fin.elim0 i
  refine ⟨realization, datum.rationalRealizationScale targetLength,
    datum.rationalRealizationScale_pos targetLength, ?_, ?_⟩
  · intro column
    change ((GluingDatum.IntegralRealization.ofPositiveRational datum targetLength
      hTargetPositive).targetLength (labelling.targetEdge column) : ℚ) = _
    rw [GluingDatum.IntegralRealization.ofPositiveRational_targetLength_cast]
    simp [targetLength, labelling]
  · exact (realization.bnExists_and_effective_of_connected_genus_zero_target
      (candidates_valid input profile outgoing).1
      (candidate_targetConnected input profile hConnected outgoing)
      (candidate_targetGenus input profile hGenus outgoing) root).1

/-- The conditional Figure 31 continuation packages the full-dimensional
outgoing source, exact affine equation, positivity, and cleared-scale pencil.
Its incoming datum remains an identified member of the actual Fin 2 family. -/
theorem exists_positive_exit_with_pencil
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn input profile incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input profile incoming incomingFD → 0 < z i)
    (hIncomingDirection : incomingVelocity
      (wallColumn input profile incoming incomingFD) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (W3Nd2CommonBalance.candidates input profile outgoing).datum coordinate,
        outgoingFD.labelling = outgoingLabelling input profile incoming incomingFD outgoing ∧
        (memberMatrix input profile incoming incomingFD incoming).det *
            (memberMatrix input profile incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity input profile incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix input profile incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity input profile incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix input profile incoming incomingFD incoming).mulVec z +
              t • (memberMatrix input profile incoming incomingFD incoming).mulVec
                incomingVelocity ∧
          ∃ realization :
              (W3Nd2CommonBalance.candidates input profile outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) *
                    (z + t • outgoingVelocity input profile incoming incomingFD
                      incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, δ, hδ, hStep⟩ :=
    exists_positive_exit input profile incoming incomingFD hConnected hGenus
      z incomingVelocity hz hzpos hIncomingDirection
  refine ⟨outgoing, outgoingFD, hLabelling, hSign, δ, hδ, ?_⟩
  intro t ht htδ
  obtain ⟨hPositive, hMetric⟩ := hStep t ht htδ
  refine ⟨hPositive, hMetric, ?_⟩
  rw [hLabelling]
  exact exists_clearedPencil input profile incoming incomingFD hConnected hGenus
    outgoing _ hPositive

end Exit

end DraismaVargas.LocalCases.W3Nd2PositiveExit
