import DraismaVargas.LocalCases.W3Nd2CoarseLimitMatrix
import DraismaVargas.LocalCases.W3Nd2FineLimitMatrix
import Utilities.IntegralGeometry.WallColumnDeterminant

/-!
# Figure 31 common cofactors and Equation (5)

The two actual Figure 31 candidates retain every old target column.  Their
new columns split the two selected old contributions and the corresponding
small/large background contributions.  This file derives the old-column
decompositions from the literal occurrence fibres and proves Equation (5)
with a common honest coordinate labelling.
-/

namespace DraismaVargas.LocalCases.W3Nd2CommonBalance

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource ThirdEquation StableSourceMatrix
open W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineRefinement
open W3Nd2FineCandidates W3Nd2Survival W3Nd2StableLift
open W3Nd2RowDescent W3Nd2FineRowDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)

private theorem incident_sheet_rel {block : WallBlock data wall}
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (data.vertexPartition wall).Rel block.1 edge.1.1.2 := by
  have hBlock := ((incident_wallBlock_sourceVertex_iff data block edge.1).mp edge.2).2
  exact block.2.trans (congrArg Subtype.val hBlock).symm

private theorem selected_small_eq (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path (smallTarget input profile))
    (hRel : (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2) :
    edge = profile.small.1 := by
  obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge
      (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
    apply (incident_iff_target_mem_and_rel data edge _).mpr
    refine ⟨hTarget ▸ smallTarget_mem input profile, ?_⟩
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr input.distinguishedBlock.1) edge.1.2
    exact ((data.vertexPartition wall).rel_repr_left input.distinguishedBlock.1).trans hRel
  rcases selected_survivor_eq_small_or_large input profile ⟨edge, hSurvives⟩ hIncident with
      hSmall | hLarge
  · exact hSmall
  · have hLargeTarget := congrArg (fun e : data.SourceEdge ↦ e.1.1) hLarge
    exact (profile.target_ne (hTarget.symm.trans hLargeTarget)).elim

private theorem selected_large_eq (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path (largeTarget input profile))
    (hRel : (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2) :
    edge = profile.large.1 := by
  obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge
      (WallBlock.sourceVertex data wall input.distinguishedBlock) := by
    apply (incident_iff_target_mem_and_rel data edge _).mpr
    refine ⟨hTarget ▸ largeTarget_mem input profile, ?_⟩
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr input.distinguishedBlock.1) edge.1.2
    exact ((data.vertexPartition wall).rel_repr_left input.distinguishedBlock.1).trans hRel
  rcases selected_survivor_eq_small_or_large input profile ⟨edge, hSurvives⟩ hIncident with
      hSmall | hLarge
  · have hSmallTarget := congrArg (fun e : data.SourceEdge ↦ e.1.1) hSmall
    exact (profile.target_ne (hSmallTarget.symm.trans hTarget)).elim
  · exact hLarge

/-- The old small column consists of its unique selected occurrence and all
literal background occurrences. -/
theorem small_matrix_decomposition (path : StablePath data) :
    matrix data path (smallTarget input profile) =
      (if path = NonDanglingEdge.stablePath
          ⟨profile.small.1, profile.small_survives⟩ then
        (1 : ℚ) / data.sourceEdgeIndex profile.small.1 else 0) +
      ∑ edge ∈ W3Nd2CoarseLimitMatrix.oldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  let selected := (occurrences data path (smallTarget input profile)).filter
    (fun edge ↦ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2)
  have hSelected : selected = ({profile.small.1} : Finset data.SourceEdge).filter
      (fun edge ↦ edge ∈ occurrences data path (smallTarget input profile)) := by
    ext edge
    simp only [selected, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      exact ⟨selected_small_eq input profile edge hMem hRel, hMem⟩
    · rintro ⟨rfl, hMem⟩
      exact ⟨hMem, incident_sheet_rel profile.small⟩
  have hMem (edge : NonDanglingEdge data)
      (hTarget : edge.1.1.1 = smallTarget input profile) :
      edge.1 ∈ occurrences data path (smallTarget input profile) ↔
        path = edge.stablePath := by
    rw [mem_occurrences]
    exact ⟨fun h ↦ h.1.choose_spec.symm,
      fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (occurrences data path (smallTarget input profile))
    (fun edge ↦ (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  change (∑ edge ∈ selected, (1 : ℚ) / data.sourceEdgeIndex edge) +
      (∑ edge ∈ W3Nd2CoarseLimitMatrix.oldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge) =
        matrix data path (smallTarget input profile) at hSplit
  rw [hSelected, Finset.sum_filter, Finset.sum_singleton] at hSplit
  simp only [hMem ⟨profile.small.1, profile.small_survives⟩ rfl] at hSplit
  exact hSplit.symm

/-- The old large column consists of its unique selected occurrence and all
literal background occurrences. -/
theorem large_matrix_decomposition (path : StablePath data) :
    matrix data path (largeTarget input profile) =
      (if path = NonDanglingEdge.stablePath
          ⟨profile.large.1, profile.large_survives⟩ then
        (1 : ℚ) / data.sourceEdgeIndex profile.large.1 else 0) +
      ∑ edge ∈ W3Nd2FineLimitMatrix.oldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  let selected := (occurrences data path (largeTarget input profile)).filter
    (fun edge ↦ (data.vertexPartition wall).Rel input.distinguishedBlock.1 edge.1.2)
  have hSelected : selected = ({profile.large.1} : Finset data.SourceEdge).filter
      (fun edge ↦ edge ∈ occurrences data path (largeTarget input profile)) := by
    ext edge
    simp only [selected, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      exact ⟨selected_large_eq input profile edge hMem hRel, hMem⟩
    · rintro ⟨rfl, hMem⟩
      exact ⟨hMem, incident_sheet_rel profile.large⟩
  have hMem (edge : NonDanglingEdge data)
      (hTarget : edge.1.1.1 = largeTarget input profile) :
      edge.1 ∈ occurrences data path (largeTarget input profile) ↔
        path = edge.stablePath := by
    rw [mem_occurrences]
    exact ⟨fun h ↦ h.1.choose_spec.symm,
      fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (occurrences data path (largeTarget input profile))
    (fun edge ↦ (data.vertexPartition wall).Rel
      input.distinguishedBlock.1 edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  change (∑ edge ∈ selected, (1 : ℚ) / data.sourceEdgeIndex edge) +
      (∑ edge ∈ W3Nd2FineLimitMatrix.oldBackgroundOccurrences input profile path,
        (1 : ℚ) / data.sourceEdgeIndex edge) =
        matrix data path (largeTarget input profile) at hSplit
  rw [hSelected, Finset.sum_filter, Finset.sum_singleton] at hSplit
  simp only [hMem ⟨profile.large.1, profile.large_survives⟩ rfl] at hSplit
  exact hSplit.symm

/-- Figure 31 / Equation (5), pointwise on the actual old stable rows. -/
theorem new_columns_add_eq_old (path : StablePath data) :
    matrix (coarseCandidate input profile).datum
        (coarseStablePathEquiv input profile path)
        (occurrenceEquiv target wall (coarseCandidate input profile).right none) +
      matrix (fineCandidate input profile).datum
        (fineStablePathEquiv input profile path)
        (occurrenceEquiv target wall (fineCandidate input profile).right none) =
      matrix data path (smallTarget input profile) +
        matrix data path (largeTarget input profile) := by
  classical
  rw [W3Nd2CoarseLimitMatrix.matrix_new_on_old_row,
    W3Nd2FineLimitMatrix.matrix_new_on_old_row,
    small_matrix_decomposition, large_matrix_decomposition,
    profile.stablePath_eq, profile.large_index]
  ring

/-- The two actual globally assembled Figure 31 candidates. -/
noncomputable def candidates : Fin 2 → BalancedGlobal.CertifiedCandidate data :=
  ![(coarseCandidate input profile).certified,
    (fineCandidate input profile).certified]

/-- The common source rows are transported by the actual coarse and fine
stable-path equivalences. -/
noncomputable def rowEquiv (position : Fin 2) : StablePath data ≃
    StablePath (candidates input profile position).datum :=
  Fin.cases (coarseStablePathEquiv input profile)
    (Fin.cases (fineStablePathEquiv input profile) (fun i ↦ Fin.elim0 i)) position

/-- Retained target occurrences use the canonical expansion labelling and
`none` names the new wall edge. -/
noncomputable def columnEquiv (position : Fin 2) : Option target.edges ≃
    (candidates input profile position).outgoingTarget.edges :=
  Fin.cases (occurrenceEquiv target wall (coarseCandidate input profile).right)
    (Fin.cases (occurrenceEquiv target wall (fineCandidate input profile).right)
      (fun i ↦ Fin.elim0 i)) position

/-- Natural matrices in the common old row and target-occurrence coordinates. -/
noncomputable def commonMatrix (position : Fin 2) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ matrix (candidates input profile position).datum
    (rowEquiv input profile position path) (columnEquiv input profile position place)

theorem commonMatrix_retained (position : Fin 2) (path : StablePath data)
    (place : target.edges) :
    commonMatrix input profile position path (some place) = matrix data path place := by
  fin_cases position
  · exact W3Nd2CoarseLimitMatrix.matrix_retained input profile path place
  · exact W3Nd2FineLimitMatrix.matrix_retained input profile path place

theorem commonMatrix_new_add (path : StablePath data) :
    commonMatrix input profile 0 path none + commonMatrix input profile 1 path none =
      matrix data path (smallTarget input profile) +
        matrix data path (largeTarget input profile) :=
  new_columns_add_eq_old input profile path

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling
    (candidates input profile 0).datum coordinate)

/-- A single honest member labelling supplies only the finite coordinate
order.  The second member is labelled through the geometric equivalences. -/
noncomputable def sourceCoordinates : StablePath data ≃ coordinate :=
  (rowEquiv input profile 0).trans initial.row

noncomputable def targetCoordinates : coordinate ≃ Option target.edges :=
  initial.targetEdge.trans (columnEquiv input profile 0).symm

noncomputable def labelling (position : Fin 2) :
    StableLengthMatrixLabelling (candidates input profile position).datum coordinate where
  row := (rowEquiv input profile position).symm.trans
    (sourceCoordinates input profile initial)
  targetEdge := (targetCoordinates input profile initial).trans
    (columnEquiv input profile position)

noncomputable def squareMatrix (position : Fin 2) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (labelling input profile initial position).presentation

noncomputable def wallColumn : coordinate :=
  (targetCoordinates input profile initial).symm none

theorem squareMatrix_common (position : Fin 2) (row column : coordinate) :
    squareMatrix input profile initial position row column =
      commonMatrix input profile position
        ((sourceCoordinates input profile initial).symm row)
        (targetCoordinates input profile initial column) := by
  exact labelling_matrix_eq (labelling input profile initial position) row column

theorem squareMatrix_retained (position : Fin 2) (row : coordinate)
    (place : target.edges) :
    squareMatrix input profile initial position row
        ((targetCoordinates input profile initial).symm (some place)) =
      matrix data ((sourceCoordinates input profile initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

theorem squareMatrix_new (position : Fin 2) (row : coordinate) :
    squareMatrix input profile initial position row
        (wallColumn input profile initial) =
      commonMatrix input profile position
        ((sourceCoordinates input profile initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

theorem matrices_agree (first second : Fin 2) :
    AgreeOffColumn (squareMatrix input profile initial first)
      (squareMatrix input profile initial second) (wallColumn input profile initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : targetCoordinates input profile initial column with
  | none =>
      exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

theorem common_cofactors (position : Fin 2) (row : coordinate) :
    (squareMatrix input profile initial position).adjugate
        (wallColumn input profile initial) row =
      (squareMatrix input profile initial 0).adjugate
        (wallColumn input profile initial) row :=
  adjugate_wallRow_eq_of_agreeOffColumn
    (matrices_agree input profile initial position 0) row

theorem old_column_annihilation (place : target.edges) :
    columnContribution (squareMatrix input profile initial 0)
      (wallColumn input profile initial)
      ((targetCoordinates input profile initial).symm (some place)) = 0 := by
  apply columnContribution_eq_zero
  intro h
  have hLabels := (targetCoordinates input profile initial).symm.injective h
  cases hLabels

/-- Equation (5), for the two actual Figure 31 covers in their induced
common labellings.  Neither determinant is assumed nonzero. -/
theorem determinant_balance :
    (squareMatrix input profile initial 0).det +
      (squareMatrix input profile initial 1).det = 0 := by
  classical
  let A := squareMatrix input profile initial
  let k := wallColumn input profile initial
  let smallColumn :=
    (targetCoordinates input profile initial).symm (some (smallTarget input profile))
  let largeColumn :=
    (targetCoordinates input profile initial).symm (some (largeTarget input profile))
  have hDet (position : Fin 2) : (A position).det =
      ∑ row, A position row k * (A 0).adjugate k row :=
    det_eq_sum_wallColumn_mul_commonCofactor
      (matrices_agree input profile initial position 0)
  have hColumn (row : coordinate) : A 0 row k + A 1 row k =
      A 0 row smallColumn + A 0 row largeColumn := by
    dsimp only [A, k, smallColumn, largeColumn]
    rw [squareMatrix_new, squareMatrix_new,
      squareMatrix_retained, squareMatrix_retained]
    exact commonMatrix_new_add input profile _
  calc
    (A 0).det + (A 1).det =
        ∑ row, (A 0 row k + A 1 row k) * (A 0).adjugate k row := by
      rw [hDet 0, hDet 1]
      simp only [add_mul, Finset.sum_add_distrib]
    _ = columnContribution (A 0) k smallColumn +
        columnContribution (A 0) k largeColumn := by
      simp_rw [hColumn]
      simp only [columnContribution, add_mul, Finset.sum_add_distrib]
    _ = 0 := by
      rw [old_column_annihilation input profile initial,
        old_column_annihilation input profile initial]
      ring

theorem positiveBalance : BalancingValencyTwo.PositiveBalance ![1, 1]
    (fun position ↦ (squareMatrix input profile initial position).det) := by
  constructor
  · intro position
    fin_cases position <;> norm_num
  · have h := determinant_balance input profile initial
    simpa [Fin.sum_univ_succ] using h

noncomputable def family : BalancedGlobal.Family (coordinate := coordinate) 2 data where
  candidate := candidates input profile
  matrix := squareMatrix input profile initial
  wallColumn := wallColumn input profile initial
  weight := ![1, 1]
  positiveBalance := positiveBalance input profile initial
  agreeOffWall := matrices_agree input profile initial

theorem family_matrix_is_honest (position : Fin 2) :
    (family input profile initial).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (labelling input profile initial position).presentation := rfl

/-- Any nonsingular chosen member has an actual valid opposite-sign member;
no nonsingularity hypothesis is imposed on the other member. -/
theorem exists_valid_opposite (incoming : Fin 2)
    (hIncoming : (squareMatrix input profile initial incoming).det ≠ 0) :
    ∃ outgoing, (candidates input profile outgoing).datum.Valid ∧
      (squareMatrix input profile initial incoming).det *
        (squareMatrix input profile initial outgoing).det < 0 :=
  (family input profile initial).exists_valid_opposite input.valid incoming hIncoming

end Square

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- The existing W3 source census supplies a canonical square coordinate
order; it does not assert any extra geometric row matching. -/
noncomputable def canonicalRowOrder : StablePath data ≃ Option target.edges :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_option, Multiset.card_coe]
    exact input.stablePath_card)

noncomputable def canonicalInitialLabelling : StableLengthMatrixLabelling
    (candidates input profile 0).datum (Option target.edges) where
  row := (rowEquiv input profile 0).symm.trans (canonicalRowOrder input)
  targetEdge := columnEquiv input profile 0

noncomputable def canonicalMatrix (position : Fin 2) :
    Matrix (Option target.edges) (Option target.edges) ℚ :=
  squareMatrix input profile (canonicalInitialLabelling input profile) position

theorem canonical_determinant_balance :
    (canonicalMatrix input profile 0).det +
      (canonicalMatrix input profile 1).det = 0 :=
  determinant_balance input profile (canonicalInitialLabelling input profile)

noncomputable def canonicalFamily :
    BalancedGlobal.Family (coordinate := Option target.edges) 2 data :=
  family input profile (canonicalInitialLabelling input profile)

theorem canonicalFamily_matrix_is_honest (position : Fin 2) :
    (canonicalFamily input profile).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (labelling input profile (canonicalInitialLabelling input profile) position).presentation := rfl

end DraismaVargas.LocalCases.W3Nd2CommonBalance
