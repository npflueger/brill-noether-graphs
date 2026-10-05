module

public import DraismaVargasCount.W2M1kTransitionSiting

@[expose] public section

/-!
# Signed multiplicity balance on the constructed M-1k family

The M-1k family is the three-member family of case `{w2-r2-nd3-M-1k}` of Draisma--Vargas Part I
(arXiv:1909.12924; Figure 33), and the balance is that paper's Equation (7).

The two nonzero-determinant branches obtain their full-dimensional
presentations from the incoming chart, and occurrence transport and
transition siting are proved on the actual members, in both pin orientations.  Thus the
balance needs no member-side index or denominator receipt.  Its only other
geometric input is the ramification bound on the incoming second row, used to
separate the incoming second and third rows.

The main statement permits arbitrary common coordinates and an incoming chart
at any position.  The canonical-coordinate statement is a specialization.
-/

namespace DraismaVargas.Count.W2M1kCountBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableLocalProperties FullDimensionalSource
open W2R1Target SecondEquation StableSourceMatrix W2M1kSourceCandidates
open W2M1kCommonBalance W2M1kLimitColumns
open TrivalentWeight RowWalk

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Position one controls the incoming second row, including when the actual
member is constructed over the branch-swapped datum. -/
theorem forall_index_dvd_secondRow_of_memberPresentation
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member 1).datum coordinate) :
    ∀ edge ∈ incomingRowEdges data (secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k := by
  classical
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [limitColumns_eq_alignedOrientation input shape hConnected hGenus hAligned,
      alignedOrientation_member_one] at fd
    let pair := (exists_leafPair shape hAligned).some
    exact W2M1kTransitionSiting.forall_index_dvd_secondRow_remote input shape
      pair.second pair.rel_second (remoteDivided input shape pair hConnected hGenus) fd
  · rw [limitColumns_eq_separatedOrientation input shape hConnected hGenus hAligned,
      separatedOrientation_member_one] at fd
    exact W2M1kTransitionSiting.forall_index_dvd_secondRow input shape
      (exists_dividedData shape hAligned).some fd

/-- Position two is the joined member in either orientation, and controls the
incoming third row. -/
theorem forall_index_dvd_thirdRow_of_memberPresentation
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member 2).datum coordinate) :
    ∀ edge ∈ incomingRowEdges data (thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k := by
  classical
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [limitColumns_eq_alignedOrientation input shape hConnected hGenus hAligned,
      alignedOrientation_member_two] at fd
    exact W2M1kTransitionSiting.forall_index_dvd_thirdRow input shape
      ((exists_leafPair shape hAligned).some.geometry shape) fd
  · rw [limitColumns_eq_separatedOrientation input shape hConnected hGenus hAligned,
      separatedOrientation_member_two] at fd
    exact W2M1kTransitionSiting.forall_index_dvd_thirdRow input shape
      ((exists_dividedData shape hAligned).some.geometry shape) fd

/-- Equation (7)'s signed multiplicity balance on the constructed family, with
all member-side receipts discharged.  The incoming chart can be at any family
position and use arbitrary common coordinates.  Only the incoming second-row
ramification bound remains an explicit row-calculus hypothesis. -/
theorem sum_signedMult_eq_zero
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 3)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member incoming).datum coordinate)
    (hTame : RowRamificationAtMostOne data (secondRow profile)) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape hConnected hGenus).labelling initial position).presentation =
        0 := by
  have hRows : secondRow profile ≠ thirdRow profile :=
    RowGeodesic.secondRow_ne_thirdRow_of_genusZero hConnected hGenus
      input.dangling_no_glue hTame
  apply W2M1kMemberBalance.sum_signedMult_eq_zero_of_conditional input _ initial
    (leafCount_member_zero input shape hConnected hGenus)
    (leafCount_member_one input shape hConnected hGenus)
    (leafCount_member_two input shape hConnected hGenus)
  · intro hDet
    exact IncomingSimpleColumn.incomingRowDenominator_secondRow_eq_of_index
      profile input shape hRows
      (forall_index_dvd_secondRow_of_memberPresentation input shape hConnected hGenus
        (W2M1kMemberBalance.memberPresentation input shape hConnected hGenus
          incoming 1 initial incomingFD hDet))
  · intro hDet
    exact IncomingSimpleColumn.incomingRowDenominator_thirdRow_eq_of_index
      profile input shape hRows
      (forall_index_dvd_thirdRow_of_memberPresentation input shape hConnected hGenus
        (W2M1kMemberBalance.memberPresentation input shape hConnected hGenus
          incoming 2 initial incomingFD hDet))

/-- Tameness is only needed when a perturbing member contributes.  This form
allows the ramification bound to be recovered from either nonsingular member;
when both are singular, the determinant balance settles the sum directly. -/
theorem sum_signedMult_eq_zero_of_conditional_tame
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 3)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member incoming).datum coordinate)
    (hTame : (((limitColumns input shape hConnected hGenus).squareMatrix initial 1).det ≠ 0 ∨
        ((limitColumns input shape hConnected hGenus).squareMatrix initial 2).det ≠ 0) →
      RowRamificationAtMostOne data (secondRow profile)) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape hConnected hGenus).labelling initial position).presentation =
        0 := by
  by_cases hFirst :
      ((limitColumns input shape hConnected hGenus).squareMatrix initial 1).det = 0
  · by_cases hSecond :
        ((limitColumns input shape hConnected hGenus).squareMatrix initial 2).det = 0
    · exact W2M1kMemberBalance.sum_signedMult_eq_zero_of_conditional input _ initial
        (leafCount_member_zero input shape hConnected hGenus)
        (leafCount_member_one input shape hConnected hGenus)
        (leafCount_member_two input shape hConnected hGenus)
        (fun hDet ↦ False.elim (hDet hFirst)) (fun hDet ↦ False.elim (hDet hSecond))
    · exact sum_signedMult_eq_zero input shape hConnected hGenus incoming initial
        incomingFD (hTame (Or.inr hSecond))
  · exact sum_signedMult_eq_zero input shape hConnected hGenus incoming initial
      incomingFD (hTame (Or.inl hFirst))

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- The canonical-coordinate balance, requiring the incoming chart in those
same coordinates. -/
theorem sum_signedMult_canonical_eq_zero
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member incoming).datum
        (Option target.edges))
    (hTame : RowRamificationAtMostOne data (secondRow profile)) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape hConnected hGenus).labelling
        ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input)
          position).presentation = 0 :=
  sum_signedMult_eq_zero input shape hConnected hGenus incoming
    ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input)
    incomingFD hTame

end DraismaVargas.Count.W2M1kCountBalance
