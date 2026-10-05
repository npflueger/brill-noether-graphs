module

public import DraismaVargas.LocalCases.M11FullDimensional

@[expose] public section

/-!
# An opposite-sign full-dimensional member of the actual M11 family

The compatible common labelling returns the original honest labelling at the
chosen incoming family member.  Equation (6) therefore supplies a genuinely
nonsingular opposite-sign member, and stable-incidence transport equips that
actual member with a full-dimensional presentation.
-/

namespace DraismaVargas.LocalCases.M11CertifiedOpposite

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource W2R1Target SecondEquation
open FullDimensionalSource
open M11SourceCandidates M11RemoteCandidates M11FullDimensional

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- At the incoming index, transport to the initial member and back cancels
both the actual stable-row equivalences and the occurrence-column
equivalences. -/
theorem outgoingLabelling_self
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (candidates input profile hCard incoming).datum coordinate) :
    outgoingLabelling input profile hCard incoming incomingFD incoming =
      incomingFD.labelling := by
  cases incomingFD with
  | mk valid targetConnected targetGenus saturated labelling det_ne_zero trivalent pathEnds =>
    cases labelling with
    | mk targetEdge row =>
      simp only [outgoingLabelling, initialLabelling,
        M11CommonBalance.labelling, M11CommonBalance.sourceCoordinates,
        M11CommonBalance.targetCoordinates]
      congr 1
      · ext column
        simp
      · ext path
        have hBetween :
            (M11StableGraphs.between input profile hCard 0 incoming).row =
              (M11CommonBalance.rowEquiv input profile hCard 0).symm.trans
                (M11CommonBalance.rowEquiv input profile hCard incoming) := by
          change (M11StableGraphs.equivalence input profile hCard 0).row.symm.trans
              (M11StableGraphs.equivalence input profile hCard incoming).row = _
          rw [M11StableGraphs.equivalence_row input profile hCard 0,
            M11StableGraphs.equivalence_row input profile hCard incoming]
        rw [hBetween]
        simp

/-- The common-family matrix at the incoming index is the original honest
incoming matrix, hence remains nonsingular. -/
theorem incomingDet_ne_zero
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (candidates input profile hCard incoming).datum coordinate) :
    (M11CommonBalance.squareMatrix input profile hCard
      (initialLabelling input profile hCard incoming incomingFD) incoming).det ≠ 0 := by
  change (GluingDatum.LengthMatrixPresentation.matrix
    (outgoingLabelling input profile hCard incoming incomingFD incoming).presentation).det ≠ 0
  rw [outgoingLabelling_self input profile hCard incoming incomingFD]
  exact incomingFD.det_ne_zero

/-- Equation (6) selects an actual opposite-sign M11 member, and the stable
incidence equivalence transports the incoming full-dimensional structure to
it.  No full-dimensional structure is imposed on the contracted wall datum,
and no assertion is made about an arbitrary incoming cover outside this
three-member family. -/
theorem exists_oppositePresentation
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (candidates input profile hCard incoming).datum coordinate) :
    ∃ outgoing : Fin 3,
      ∃ _outgoingFD : FullDimensionalSourcePresentation
          (candidates input profile hCard outgoing).datum coordinate,
        (GluingDatum.LengthMatrixPresentation.matrix
          (outgoingLabelling input profile hCard incoming incomingFD incoming).presentation).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            (outgoingLabelling input profile hCard incoming incomingFD outgoing).presentation).det < 0 := by
  let initial := initialLabelling input profile hCard incoming incomingFD
  have hIncoming :
      (M11CommonBalance.squareMatrix input profile hCard initial incoming).det ≠ 0 := by
    exact incomingDet_ne_zero input profile hCard incoming incomingFD
  obtain ⟨outgoing, _hValid, hSign⟩ :=
    M11CommonBalance.exists_valid_opposite input profile hCard initial
      hConnected hGenus incoming hIncoming
  have hOutgoing :
      (GluingDatum.LengthMatrixPresentation.matrix
        (outgoingLabelling input profile hCard incoming incomingFD outgoing).presentation).det ≠ 0 := by
    apply BalancedGlobal.det_ne_zero_of_mul_det_neg
      (A := M11CommonBalance.squareMatrix input profile hCard initial incoming)
    simpa [M11CommonBalance.squareMatrix, outgoingLabelling] using hSign
  refine ⟨outgoing,
    outgoingPresentation input profile hCard hConnected hGenus incoming outgoing incomingFD hOutgoing, ?_⟩
  simpa [M11CommonBalance.squareMatrix, outgoingLabelling] using hSign

end DraismaVargas.LocalCases.M11CertifiedOpposite
