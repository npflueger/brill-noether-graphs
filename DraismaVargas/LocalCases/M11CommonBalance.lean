module

public import DraismaVargas.LocalCases.M11RemoteLimitMatrix
public import DraismaVargas.LocalCases.M11JoinedBackgroundMatrix
public import Utilities.IntegralGeometry.WallColumnDeterminant

@[expose] public section

/-!
# Actual M11 common cofactors and Equation (6)

Source: Draisma--Vargas Part I, the compatible labellings and limit matrices
of the subsection on inherited properties (`lemma-limit-matrix-change`), and
Case {w2-r2-nd3-M-11} (abbreviated M11 here): Figure 32 and Equation (6). All
three actual candidates retain the original stable-row coordinates through
their proved occurrence maps.

The old single and double target directions have identical background sums:
same-sheet transport at the unramified divalent background junctions preserves
the actual stable row and index. The distinguished double occurrences are
enumerated by the deleted sheet and its opposite. Their occurrences are
distinct; their stable rows are allowed to coincide.

`weighted_column_balance` proves C1 + C2 + 4 C3 = 2 Cdouble + 2 Csingle
pointwise on the actual old stable rows. In particular, the joined background
is retained until the old-column cofactor cancellation is proved.

One honest square labelling of the first member supplies the finite coordinate
order; `labelling` constructs the other two through the proved geometric row
equivalences. `common_cofactors` and `old_column_annihilation` follow from
the actual off-column equality and the adjugate identity. `determinant_balance`
proves Equation (6) without assuming any member nonsingular. `family` uses
the certified-family interface and retains a possibly singular
joined member; its opposite-sign consumer needs only the chosen incoming
determinant to be nonzero. No prescribed graph endpoint theorem is asserted.

`canonicalInitialLabelling` obtains the initial coordinate order from the
stable-row census of Case {w2}, so `canonicalFamily` and
`canonical_determinant_balance` require no supplied square labelling. The
general initial-labelling APIs remain available for matching incoming data.
-/

namespace DraismaVargas.LocalCases.M11CommonBalance

open DraismaVargas.Infrastructure TargetExpansion
open W4Assembly W4StableSource W2R1Target SecondEquation StableSourceMatrix
open M11SourceCandidates M11JoinedGeometry M11JoinedBackground M11JoinedDescentGeometry
open M11JoinedStableLift
open M11SplitSurvival M11BranchSeparation

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

noncomputable def backgroundOccurrences (path : StablePath data) (label : Fin 2) :
    Finset data.SourceEdge := by
  classical
  exact (occurrences data path (star.edge label)).filter
    (fun edge ↦ ¬ (data.vertexPartition wall).Rel block.1 edge.1.2)

theorem mem_backgroundOccurrences (path : StablePath data) (label : Fin 2) (edge : data.SourceEdge) :
    edge ∈ backgroundOccurrences (star := star) (block := block) path label ↔
      edge ∈ occurrences data path (star.edge label) ∧
        ¬ (data.vertexPartition wall).Rel block.1 edge.1.2 := by
  classical
  simp only [backgroundOccurrences, Finset.mem_filter]

include input profile hCard in
theorem background_transfer_mem (path : StablePath data) (one two : Fin 2)
    (edge : data.SourceEdge) (hMem : edge ∈ backgroundOccurrences (star := star) (block := block) path one) :
    data.sourceEdge (star.edge two) edge.1.2 ∈ backgroundOccurrences (star := star) (block := block) path two := by
  have hData := (mem_backgroundOccurrences path one edge).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hData.1
  have hCanonical := background_sourceEdge_eq input profile one edge.1.2 hData.2 edge hTarget rfl
  have hOld : ¬ IsDangling data (data.sourceEdge (star.edge one) edge.1.2) := by
    rw [hCanonical]
    exact hSurvives
  have hNew : ¬ IsDangling data (data.sourceEdge (star.edge two) edge.1.2) := by
    intro hDangling
    have hj := (background_isDangling_iff input profile hCard two edge.1.2 hData.2).mpr hDangling
    exact hOld ((background_isDangling_iff input profile hCard one edge.1.2 hData.2).mp hj)
  refine (mem_backgroundOccurrences path two _).mpr ⟨(mem_occurrences _ _ _).mpr ⟨⟨hNew, ?_⟩, rfl⟩, ?_⟩
  · have hPaths := background_old_stablePath_eq input profile edge.1.2 hData.2
      (⟨data.sourceEdge (star.edge two) edge.1.2, hNew⟩ : NonDanglingEdge data)
      (⟨edge, hSurvives⟩ : NonDanglingEdge data)
      (incident_sourceEdge_sourceEndpoint data wall _ (star.edge_mem_incidentEdges two) _)
      (by
        have hIncident := incident_sourceEdge_sourceEndpoint data wall _ (star.edge_mem_incidentEdges one) edge.1.2
        rw [hCanonical] at hIncident
        exact hIncident)
    exact hPaths.trans hRow
  · exact fun h ↦ hData.2 (h.trans ((star.edgePartition_refines_wall data two).rel
      ((data.edgePartition (star.edge two)).rel_repr_left edge.1.2)))

include input profile in
theorem background_transfer_inverse (path : StablePath data) (one two : Fin 2)
    (edge : data.SourceEdge) (hMem : edge ∈ backgroundOccurrences (star := star) (block := block) path one) :
    data.sourceEdge (star.edge one) (data.sourceEdge (star.edge two) edge.1.2).1.2 = edge := by
  have hData := (mem_backgroundOccurrences path one edge).mp hMem
  have hRel := (star.edgePartition_refines_wall data two).rel
    ((data.edgePartition (star.edge two)).rel_repr_left edge.1.2)
  exact background_sourceEdge_eq input profile one _ (fun h ↦ hData.2 (h.trans hRel)) edge
    ((mem_occurrences _ _ _).mp hData.1).2 hRel

include input profile hCard in
/-- The two old backgrounds agree term by term along their literal
divalent source junctions, even if several occurrences share one stable row. -/
theorem background_sum_eq (path : StablePath data) (one two : Fin 2) :
    (∑ edge ∈ backgroundOccurrences (star := star) (block := block) path one, (1 : ℚ) / data.sourceEdgeIndex edge) =
      ∑ edge ∈ backgroundOccurrences (star := star) (block := block) path two, (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  apply Finset.sum_nbij' (fun edge ↦ data.sourceEdge (star.edge two) edge.1.2)
    (fun edge ↦ data.sourceEdge (star.edge one) edge.1.2)
    (fun edge h ↦ background_transfer_mem input profile hCard path one two edge h)
    (fun edge h ↦ background_transfer_mem input profile hCard path two one edge h)
    (fun edge h ↦ background_transfer_inverse input profile path one two edge h)
    (fun edge h ↦ background_transfer_inverse input profile path two one edge h)
  intro edge hMem
  have hData := (mem_backgroundOccurrences path one edge).mp hMem
  have hCanonical := background_sourceEdge_eq input profile one edge.1.2 hData.2 edge
    ((mem_occurrences _ _ _).mp hData.1).2 rfl
  rw [← background_index_eq input profile hCard two edge.1.2 hData.2,
    background_index_eq input profile hCard one edge.1.2 hData.2, hCanonical]

theorem selected_sheet_pair : (data.vertexPartition wall).block block.1 =
    {profile.deleted.edge.1.1.2, oppositeSheet profile hCard} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro sheet hSheet
    rcases Finset.mem_insert.mp hSheet with rfl | hSheet
    · exact (SheetPartition.mem_block_iff _ _ _).mpr (sheet_rel_of_incident_block profile.deleted.edge)
    · rw [Finset.mem_singleton] at hSheet
      exact hSheet ▸ (SheetPartition.mem_block_iff _ _ _).mpr (oppositeSheet_rel profile hCard)
  · rw [Finset.card_pair (oppositeSheet_ne profile hCard).symm]
    exact le_of_eq hCard

theorem selected_double_iff (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.doubleLabel) :
    (data.vertexPartition wall).Rel block.1 edge.1.2 ↔
      edge = (M11SplitRowDescent.newOldEdge profile hCard).1 ∨
        edge = (oppositeDouble profile hCard).1 := by
  classical
  constructor
  · intro hRel
    have hMem := (SheetPartition.mem_block_iff _ _ _).mpr hRel
    rw [selected_sheet_pair profile hCard, Finset.mem_insert, Finset.mem_singleton] at hMem
    have hSelf : data.sourceEdge (star.edge profile.doubleLabel) edge.1.2 = edge := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data edge
    rcases hMem with hSheet | hSheet
    · exact Or.inl (hSelf.symm.trans (congrArg (data.sourceEdge (star.edge profile.doubleLabel)) hSheet))
    · exact Or.inr (hSelf.symm.trans (congrArg (data.sourceEdge (star.edge profile.doubleLabel)) hSheet))
  · rintro (rfl | rfl)
    · change (data.vertexPartition wall).Rel block.1
        (data.sourceEdge (star.edge profile.doubleLabel) profile.deleted.edge.1.1.2).1.2
      rw [double_sourceEdge_sheet profile hCard _ (sheet_rel_of_incident_block profile.deleted.edge)]
      exact sheet_rel_of_incident_block profile.deleted.edge
    · change (data.vertexPartition wall).Rel block.1
        (data.sourceEdge (star.edge profile.doubleLabel) (oppositeSheet profile hCard)).1.2
      rw [double_sourceEdge_sheet profile hCard _ (oppositeSheet_rel profile hCard)]
      exact oppositeSheet_rel profile hCard

include hCard in
theorem selected_double_index (edge : data.SourceEdge)
    (hTarget : edge.1.1 = star.edge profile.doubleLabel)
    (hRel : (data.vertexPartition wall).Rel block.1 edge.1.2) : data.sourceEdgeIndex edge = 1 := by
  apply index_eq_one_of_blockCard_eq_two profile hCard ⟨edge, ?_⟩
  apply (incident_iff_target_mem_and_rel _ _ _).mpr
  refine ⟨hTarget ▸ star.edge_mem_incidentEdges profile.doubleLabel, ?_⟩
  change (data.vertexPartition wall).Rel ((data.vertexPartition wall).repr block.1) edge.1.2
  exact ((data.vertexPartition wall).rel_repr_left block.1).trans hRel

theorem double_matrix_decomposition (path : StablePath data) :
    matrix data path (star.edge profile.doubleLabel) =
      (∑ edge ∈ backgroundOccurrences (star := star) (block := block) path profile.doubleLabel,
        (1 : ℚ) / data.sourceEdgeIndex edge) +
      (if path = (M11SplitRowDescent.newOldEdge profile hCard).stablePath then 1 else 0) +
      (if path = (oppositeDouble profile hCard).stablePath then 1 else 0) := by
  classical
  let first := M11SplitRowDescent.newOldEdge profile hCard
  let second := oppositeDouble profile hCard
  let selected := (occurrences data path (star.edge profile.doubleLabel)).filter
    (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2)
  have hFirstSecond : first.1 ≠ second.1 := (oppositeDouble_ne_sameSheet profile hCard).symm
  have hSelected : selected = ({first.1, second.1} : Finset data.SourceEdge).filter
      (fun edge ↦ edge ∈ occurrences data path (star.edge profile.doubleLabel)) := by
    ext edge
    simp only [selected, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      exact ⟨(selected_double_iff profile hCard edge ((mem_occurrences _ _ _).mp hMem).2).mp hRel, hMem⟩
    · rintro ⟨hPair, hMem⟩
      exact ⟨hMem, (selected_double_iff profile hCard edge ((mem_occurrences _ _ _).mp hMem).2).mpr hPair⟩
  have hIndexFirst : data.sourceEdgeIndex first.1 = 1 :=
    selected_double_index profile hCard first.1 rfl ((selected_double_iff profile hCard first.1 rfl).mpr (Or.inl rfl))
  have hIndexSecond : data.sourceEdgeIndex second.1 = 1 :=
    selected_double_index profile hCard second.1 rfl ((selected_double_iff profile hCard second.1 rfl).mpr (Or.inr rfl))
  have hMem (edge : NonDanglingEdge data) (hTarget : edge.1.1.1 = star.edge profile.doubleLabel) :
      edge.1 ∈ occurrences data path (star.edge profile.doubleLabel) ↔ path = edge.stablePath := by
    rw [mem_occurrences]
    exact ⟨fun h ↦ h.1.choose_spec.symm, fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩
  have hSplit := Finset.sum_filter_add_sum_filter_not (occurrences data path (star.edge profile.doubleLabel))
    (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  change (∑ edge ∈ selected, (1 : ℚ) / data.sourceEdgeIndex edge) +
    (∑ edge ∈ backgroundOccurrences (star := star) (block := block) path profile.doubleLabel,
      (1 : ℚ) / data.sourceEdgeIndex edge) = matrix data path (star.edge profile.doubleLabel) at hSplit
  rw [hSelected, Finset.sum_filter, Finset.sum_pair hFirstSecond,
    hIndexFirst, hIndexSecond, Nat.cast_one, div_one] at hSplit
  simp only [hMem first rfl, hMem second rfl] at hSplit
  exact hSplit.symm.trans (by ring)

include hCard in
theorem single_matrix_decomposition (path : StablePath data) :
    matrix data path (star.edge profile.singleLabel) =
      (∑ edge ∈ backgroundOccurrences (star := star) (block := block) path profile.singleLabel,
        (1 : ℚ) / data.sourceEdgeIndex edge) +
      (if path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ then 1 else 0) := by
  have hSet : backgroundOccurrences (star := star) (block := block) path profile.singleLabel =
      M11JoinedBackgroundMatrix.oldBackgroundOccurrences profile path := by
    ext edge
    rw [mem_backgroundOccurrences, M11JoinedBackgroundMatrix.mem_oldBackgroundOccurrences]
  rw [hSet]
  exact (M11JoinedBackgroundMatrix.sum_old_add_third profile hCard path).symm

/-- The common source rows are transported by the three already-proved
literal occurrence maps, including the remote branch swap. -/
noncomputable def rowEquiv (position : Fin 3) : StablePath data ≃
    StablePath (M11RemoteCandidates.candidates input profile hCard position).datum :=
  Fin.cases (M11SplitRowDescent.stablePathEquiv input profile hCard)
    (Fin.cases (M11RemoteLimitMatrix.stablePathEquiv input profile hCard)
      (Fin.cases (M11JoinedRowDescent.stablePathEquiv input profile hCard)
        (fun i ↦ Fin.elim0 i))) position

noncomputable def columnEquiv (position : Fin 3) : Option target.edges ≃
    (M11RemoteCandidates.candidates input profile hCard position).outgoingTarget.edges :=
  Fin.cases (occurrenceEquiv target wall (firstSplitPattern input profile hCard).candidate.right)
    (Fin.cases (occurrenceEquiv target wall (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.right)
      (Fin.cases (occurrenceEquiv target wall (joinedPattern data star block hCard).candidate.right)
        (fun i ↦ Fin.elim0 i))) position

/-- Natural matrices in compatible common coordinates. No displayed matrix
or supplied row correspondence enters this definition. -/
noncomputable def commonMatrix (position : Fin 3) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ matrix (M11RemoteCandidates.candidates input profile hCard position).datum
    (rowEquiv input profile hCard position path) (columnEquiv input profile hCard position place)

theorem commonMatrix_retained (position : Fin 3) (path : StablePath data) (place : target.edges) :
    commonMatrix input profile hCard position path (some place) = matrix data path place := by
  fin_cases position
  · exact M11SplitLimitMatrix.matrix_retained input profile hCard path place
  · exact M11RemoteLimitMatrix.matrix_retained input profile hCard path place
  · exact M11JoinedLimitMatrix.matrix_retained input profile hCard path place

/-- Figure 32's weighted column identity on actual stable rows. Occurrences
are counted individually, so coincident distinguished stable classes are allowed. -/
theorem weighted_column_balance (hConnected : graph_connected target) (hGenus : genus target = 0)
    (path : StablePath data) :
    commonMatrix input profile hCard 0 path none + commonMatrix input profile hCard 1 path none +
        4 * commonMatrix input profile hCard 2 path none =
      2 * matrix data path (star.edge profile.doubleLabel) +
        2 * matrix data path (star.edge profile.singleLabel) := by
  classical
  have hFirst : commonMatrix input profile hCard 0 path none =
      if path = (M11SplitRowDescent.newOldEdge profile hCard).stablePath then 2 else 0 :=
    M11SplitLimitMatrix.matrix_new input profile hCard path
  have hSecond : commonMatrix input profile hCard 1 path none =
      if path = (oppositeDouble profile hCard).stablePath then 2 else 0 :=
    M11RemoteLimitMatrix.matrix_new input profile hCard hConnected hGenus path
  have hThird : commonMatrix input profile hCard 2 path none =
      matrix data path (star.edge profile.singleLabel) -
        (if path = NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩ then (1 / 2 : ℚ) else 0) :=
    M11JoinedBackgroundMatrix.matrix_new_eq_old_sub_half input profile hCard path
  rw [hFirst, hSecond, hThird, double_matrix_decomposition profile hCard,
    single_matrix_decomposition profile hCard,
    background_sum_eq input profile hCard path profile.doubleLabel profile.singleLabel]
  split_ifs <;> ring

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling
    (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)

/-- A single honest member labelling supplies only the finite coordinate
order. All inter-member row correspondences were constructed above. -/
noncomputable def sourceCoordinates : StablePath data ≃ coordinate :=
  (rowEquiv input profile hCard 0).trans initial.row

noncomputable def targetCoordinates : coordinate ≃ Option target.edges :=
  initial.targetEdge.trans (columnEquiv input profile hCard 0).symm

noncomputable def labelling (position : Fin 3) :
    StableLengthMatrixLabelling (M11RemoteCandidates.candidates input profile hCard position).datum coordinate where
  row := (rowEquiv input profile hCard position).symm.trans (sourceCoordinates input profile hCard initial)
  targetEdge := (targetCoordinates input profile hCard initial).trans (columnEquiv input profile hCard position)

noncomputable def squareMatrix (position : Fin 3) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix (labelling input profile hCard initial position).presentation

noncomputable def wallColumn : coordinate := (targetCoordinates input profile hCard initial).symm none

theorem squareMatrix_common (position : Fin 3) (row column : coordinate) :
    squareMatrix input profile hCard initial position row column =
      commonMatrix input profile hCard position
        ((sourceCoordinates input profile hCard initial).symm row)
        (targetCoordinates input profile hCard initial column) := by
  exact labelling_matrix_eq (labelling input profile hCard initial position) row column

theorem squareMatrix_retained (position : Fin 3) (row : coordinate) (place : target.edges) :
    squareMatrix input profile hCard initial position row
        ((targetCoordinates input profile hCard initial).symm (some place)) =
      matrix data ((sourceCoordinates input profile hCard initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

theorem squareMatrix_new (position : Fin 3) (row : coordinate) :
    squareMatrix input profile hCard initial position row (wallColumn input profile hCard initial) =
      commonMatrix input profile hCard position ((sourceCoordinates input profile hCard initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

theorem matrices_agree (first second : Fin 3) :
    AgreeOffColumn (squareMatrix input profile hCard initial first)
      (squareMatrix input profile hCard initial second) (wallColumn input profile hCard initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : targetCoordinates input profile hCard initial column with
  | none =>
    exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

/-- The common cofactor row is derived from the actual limit-column
dictionary; no cofactor correspondence or nonsingularity is supplied. -/
theorem common_cofactors (position : Fin 3) (row : coordinate) :
    (squareMatrix input profile hCard initial position).adjugate (wallColumn input profile hCard initial) row =
      (squareMatrix input profile hCard initial 0).adjugate (wallColumn input profile hCard initial) row :=
  adjugate_wallRow_eq_of_agreeOffColumn (matrices_agree input profile hCard initial position 0) row

/-- Each old-column cancellation follows from the adjugate identity, even
when the chosen reference member is singular. -/
theorem old_column_annihilation (place : target.edges) :
    columnContribution (squareMatrix input profile hCard initial 0) (wallColumn input profile hCard initial)
      ((targetCoordinates input profile hCard initial).symm (some place)) = 0 := by
  apply columnContribution_eq_zero
  intro h
  have hLabels := (targetCoordinates input profile hCard initial).symm.injective h
  cases hLabels

/-- Equation (6), for the three actual M11 covers in their induced common
labellings. No member is assumed nonsingular, including the joined member. -/
theorem determinant_balance (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (squareMatrix input profile hCard initial 0).det +
        (squareMatrix input profile hCard initial 1).det +
        4 * (squareMatrix input profile hCard initial 2).det = 0 := by
  classical
  let A := squareMatrix input profile hCard initial
  let k := wallColumn input profile hCard initial
  let doubleColumn := (targetCoordinates input profile hCard initial).symm (some (star.edge profile.doubleLabel))
  let singleColumn := (targetCoordinates input profile hCard initial).symm (some (star.edge profile.singleLabel))
  have hDet (position : Fin 3) : (A position).det =
      ∑ row, A position row k * (A 0).adjugate k row :=
    det_eq_sum_wallColumn_mul_commonCofactor (matrices_agree input profile hCard initial position 0)
  have hColumn (row : coordinate) : A 0 row k + A 1 row k + 4 * A 2 row k =
      2 * A 0 row doubleColumn + 2 * A 0 row singleColumn := by
    dsimp only [A, k, doubleColumn, singleColumn]
    rw [squareMatrix_new, squareMatrix_new, squareMatrix_new,
      squareMatrix_retained, squareMatrix_retained]
    exact weighted_column_balance input profile hCard hConnected hGenus _
  calc
    (A 0).det + (A 1).det + 4 * (A 2).det =
        ∑ row, (A 0 row k + A 1 row k + 4 * A 2 row k) * (A 0).adjugate k row := by
      rw [hDet 0, hDet 1, hDet 2]
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * columnContribution (A 0) k doubleColumn +
        2 * columnContribution (A 0) k singleColumn := by
      simp_rw [hColumn]
      simp only [columnContribution, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 0 := by
      rw [old_column_annihilation input profile hCard initial,
        old_column_annihilation input profile hCard initial]
      ring

theorem positiveBalance (hConnected : graph_connected target) (hGenus : genus target = 0) :
    BalancingValencyTwo.PositiveBalance ![1, 1, 4]
      (fun position ↦ (squareMatrix input profile hCard initial position).det) := by
  constructor
  · intro position
    fin_cases position <;> norm_num
  · have h := determinant_balance input profile hCard initial hConnected hGenus
    simpa [Fin.sum_univ_succ, add_assoc] using h

/-- Package the proved source family through the certified interface; a
singular joined member is permitted and kept in the family. -/
noncomputable def family (hConnected : graph_connected target) (hGenus : genus target = 0) :
    BalancedGlobal.Family (coordinate := coordinate) 3 data where
  candidate := M11RemoteCandidates.candidates input profile hCard
  matrix := squareMatrix input profile hCard initial
  wallColumn := wallColumn input profile hCard initial
  weight := ![1, 1, 4]
  positiveBalance := positiveBalance input profile hCard initial hConnected hGenus
  agreeOffWall := matrices_agree input profile hCard initial

theorem family_matrix_is_honest (hConnected : graph_connected target) (hGenus : genus target = 0)
    (position : Fin 3) :
    (family input profile hCard initial hConnected hGenus).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix (labelling input profile hCard initial position).presentation := rfl

/-- Any nonsingular chosen member has an actual valid opposite-sign member.
The other two members need not be nonsingular. -/
theorem exists_valid_opposite (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3) (hIncoming : (squareMatrix input profile hCard initial incoming).det ≠ 0) :
    ∃ outgoing, (M11RemoteCandidates.candidates input profile hCard outgoing).datum.Valid ∧
      (squareMatrix input profile hCard initial incoming).det *
        (squareMatrix input profile hCard initial outgoing).det < 0 :=
  (family input profile hCard initial hConnected hGenus).exists_valid_opposite input.valid incoming hIncoming

end Square

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- Choose only a finite coordinate order from the source census of Case {w2}.
This choice is not an inter-member geometric row correspondence. -/
noncomputable def canonicalRowOrder (input : W2SourceInput data star) : StablePath data ≃ Option target.edges :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_option, Multiset.card_coe]
    exact input.stablePath_card)

/-- The first member's honest square labelling exists from the source census
and the actual row and target occurrence equivalences. -/
noncomputable def canonicalInitialLabelling : StableLengthMatrixLabelling
    (M11RemoteCandidates.candidates input profile hCard 0).datum (Option target.edges) where
  row := (rowEquiv input profile hCard 0).symm.trans (canonicalRowOrder input)
  targetEdge := columnEquiv input profile hCard 0

noncomputable def canonicalMatrix (position : Fin 3) :
    Matrix (Option target.edges) (Option target.edges) ℚ :=
  squareMatrix input profile hCard (canonicalInitialLabelling input profile hCard) position

/-- Equation (6) with no supplied square labelling: the source census of Case
{w2} provides it. Nonsingularity is not required of any member. -/
theorem canonical_determinant_balance (hConnected : graph_connected target) (hGenus : genus target = 0) :
    (canonicalMatrix input profile hCard 0).det + (canonicalMatrix input profile hCard 1).det +
      4 * (canonicalMatrix input profile hCard 2).det = 0 :=
  determinant_balance input profile hCard (canonicalInitialLabelling input profile hCard) hConnected hGenus

/-- A source-certified balanced family needing no external coordinate
labelling. All sibling row maps remain the proved geometric ones. -/
noncomputable def canonicalFamily (hConnected : graph_connected target) (hGenus : genus target = 0) :
    BalancedGlobal.Family (coordinate := Option target.edges) 3 data :=
  family input profile hCard (canonicalInitialLabelling input profile hCard) hConnected hGenus

theorem canonicalFamily_matrix_is_honest (hConnected : graph_connected target) (hGenus : genus target = 0)
    (position : Fin 3) :
    (canonicalFamily input profile hCard hConnected hGenus).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (labelling input profile hCard (canonicalInitialLabelling input profile hCard) position).presentation := rfl

end DraismaVargas.LocalCases.M11CommonBalance
