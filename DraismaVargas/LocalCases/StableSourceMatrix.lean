import DraismaVargas.LocalCases.StableLocalProperties

/-!
# The literal stable-source matrix, including rectangular wall matrices

The paper's matrix at a codimension-one limit has one fewer target column
than stable-source rows. `StableLengthMatrixLabelling` deliberately labels a
square matrix and cannot label that wall. Here we record the same occurrence
sum directly on its natural row and column types, without changing the
presentation interface. The square case is proved to agree with the honest
labelling.

This definition does not assert inherited rank or identify stable rows across
contraction; those require actual occurrence-level source transport.
-/

namespace DraismaVargas.LocalCases.StableSourceMatrix

open DraismaVargas.Infrastructure
open W4StableSource StableLocalProperties

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- The literal surviving occurrences of one stable row over one target edge. -/
noncomputable def occurrences (data : GluingDatum target degree)
    (path : StablePath data) (targetEdge : target.edges) : Finset data.SourceEdge := by
  classical
  exact Finset.univ.filter fun edge ↦
    (∃ hSurvives : ¬ IsDangling data edge,
      NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path) ∧
        edge.1.1 = targetEdge

theorem mem_occurrences (path : StablePath data) (targetEdge : target.edges)
    (edge : data.SourceEdge) :
    edge ∈ occurrences data path targetEdge ↔
      (∃ hSurvives : ¬ IsDangling data edge,
        NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path) ∧
          edge.1.1 = targetEdge := by
  classical
  simp [occurrences]

/-- Draisma--Vargas's natural, possibly rectangular matrix: no square
labelling, arbitrary path list, or added topology receipt is involved. -/
noncomputable def matrix (data : GluingDatum target degree) :
    Matrix (StablePath data) target.edges ℚ :=
  fun path targetEdge ↦ ∑ edge ∈ occurrences data path targetEdge,
    (1 : ℚ) / data.sourceEdgeIndex edge

/-- For an honest square labelling, the presentation is precisely
the natural stable-source matrix with its rows and columns relabelled. -/
theorem labelling_matrix_eq {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (labelling : StableLengthMatrixLabelling data coordinate)
    (row column : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row column =
      matrix data (labelling.row.symm row) (labelling.targetEdge column) := by
  classical
  have hNodup : (labelling.path row).Nodup := by
    unfold StableLengthMatrixLabelling.path
    exact List.Nodup.filter _ (Finset.univ.nodup_toList)
  have hToFinset : (labelling.path row).toFinset =
      (Finset.univ : Finset data.SourceEdge).filter
        (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
          labelling.row (NonDanglingEdge.stablePath
            (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) := by
    ext edge
    simp [List.mem_toFinset, labelling.mem_path_iff]
  have hCoeff (edge : data.SourceEdge) :
      GluingDatum.LengthMatrixPresentation.coefficient labelling.presentation edge column =
        if edge.1.1 = labelling.targetEdge column then
          (1 : ℚ) / data.sourceEdgeIndex edge else 0 := by
    unfold GluingDatum.LengthMatrixPresentation.coefficient
    have hIff : column = labelling.targetEdge.symm edge.1.1 ↔
        edge.1.1 = labelling.targetEdge column := by
      rw [Equiv.eq_symm_apply]
      exact eq_comm
    change (if column = labelling.targetEdge.symm edge.1.1 then _ else _) = _
    simp only [hIff]
  calc
    _ = ∑ edge ∈ (labelling.path row).toFinset,
        GluingDatum.LengthMatrixPresentation.coefficient labelling.presentation edge column :=
      (List.sum_toFinset _ hNodup).symm
    _ = ∑ edge ∈ ((labelling.path row).toFinset).filter
        (fun edge ↦ edge.1.1 = labelling.targetEdge column),
        (1 : ℚ) / data.sourceEdgeIndex edge := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun edge _ ↦ hCoeff edge
    _ = _ := by
      unfold matrix occurrences
      rw [hToFinset, Finset.filter_filter]
      congr 1
      ext edge
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        ← Equiv.eq_symm_apply]

/-- An actual wholly dangling target fibre gives a zero column, whether
or not the stable-source matrix is square. -/
theorem column_eq_zero_of_dangling (targetEdge : target.edges)
    (hDangling : ∀ edge : data.SourceEdge, edge.1.1 = targetEdge → IsDangling data edge)
    (path : StablePath data) : matrix data path targetEdge = 0 := by
  have hEmpty : occurrences data path targetEdge = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge hEdge
    obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences path targetEdge edge).mp hEdge
    exact hSurvives (hDangling edge hTarget)
  simp only [matrix, hEmpty, Finset.sum_empty]

/-- The source's equal-column argument, localized to one actual stable row.
Only blocks met by this row need to be unramified: contributions from other
rows can be discarded separately, for example when their cofactors vanish. -/
theorem column_eq_of_divalent_of_path_localRamification_zero
    (vertex : target.V) (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (path : StablePath data)
    (hSurvivingBlocks : ∀ (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge),
      NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path →
      edge.1.1 ∈ GluingDatum.incidentEdges vertex →
      data.localRamification vertex ((data.vertexPartition vertex).toBlock edge.1.2) = 0)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex) :
    matrix data path first = matrix data path second := by
  classical
  have hTransfer : ∀ (one two : target.edges),
      one ∈ GluingDatum.incidentEdges vertex →
      two ∈ GluingDatum.incidentEdges vertex → one ≠ two →
      ∀ edge ∈ occurrences data path one,
        data.sourceEdge two edge.1.2 ∈ occurrences data path two := by
    intro one two hOne hTwo hOneTwo edge hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences path one edge).mp hEdge
    have hSelf : data.sourceEdge one edge.1.2 = edge := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data edge
    have hZero : data.localRamification vertex
        ((data.vertexPartition vertex).toBlock edge.1.2) = 0 :=
      hSurvivingBlocks edge hSurvives hRow (by rw [hTarget]; exact hOne)
    have hOneSurvives : ¬ IsDangling data (data.sourceEdge one edge.1.2) := by
      rw [hSelf]
      exact hSurvives
    have hTwoSurvives : ¬ IsDangling data (data.sourceEdge two edge.1.2) :=
      fun hDangling ↦ hOneSurvives
        ((isDangling_sourceEdge_iff_of_divalent_localRamification_zero data
          vertex hDivalent edge.1.2 hZero hOneTwo hOne hTwo).2 hDangling)
    have hPathEq := stablePath_sourceEdge_eq_of_divalent_localRamification_zero
      data vertex hDivalent edge.1.2 hZero hOneTwo hOne hTwo hOneSurvives hTwoSurvives
    apply (mem_occurrences path two _).mpr
    refine ⟨⟨hTwoSurvives, ?_⟩, rfl⟩
    rw [← hPathEq,
      show (⟨data.sourceEdge one edge.1.2, hOneSurvives⟩ : NonDanglingEdge data) =
        ⟨edge, hSurvives⟩ from Subtype.ext hSelf]
    exact hRow
  unfold matrix
  refine Finset.sum_nbij' (fun edge ↦ data.sourceEdge second edge.1.2)
    (fun edge ↦ data.sourceEdge first edge.1.2)
    (hTransfer first second hFirst hSecond hNe)
    (hTransfer second first hSecond hFirst hNe.symm) ?_ ?_ ?_
  · intro edge hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences path first edge).mp hEdge
    exact sourceEdge_transport_left_inverse_of_divalent_localRamification_zero
      data vertex hDivalent first second hFirst hSecond edge hTarget
      (hSurvivingBlocks edge hSurvives hRow (by rw [hTarget]; exact hFirst))
  · intro edge hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences path second edge).mp hEdge
    exact sourceEdge_transport_left_inverse_of_divalent_localRamification_zero
      data vertex hDivalent second first hSecond hFirst edge hTarget
      (hSurvivingBlocks edge hSurvives hRow (by rw [hTarget]; exact hSecond))
  · intro edge hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences path first edge).mp hEdge
    have hZero : data.localRamification vertex
        ((data.vertexPartition vertex).toBlock edge.1.2) = 0 :=
      hSurvivingBlocks edge hSurvives hRow (by rw [hTarget]; exact hFirst)
    have hSelf : data.sourceEdge first edge.1.2 = edge := by
      rw [← hTarget]
      exact GluingDatum.sourceEdge_self data edge
    have hFirstIndex := sourceEdgeIndex_eq_of_divalent_localRamification_zero
      data vertex hDivalent edge.1.2 hZero first hFirst
    rw [hSelf] at hFirstIndex
    have hSecondIndex := sourceEdgeIndex_eq_of_divalent_localRamification_zero
      data vertex hDivalent edge.1.2 hZero second hSecond
    rw [hFirstIndex, hSecondIndex]

/-- The source's equal-column argument at an unramified divalent vertex,
on the natural rectangular matrix as well as on a square presentation.
Blocks invisible to the surviving source need not have ramification zero. -/
theorem column_eq_of_divalent_of_surviving_localRamification_zero
    (vertex : target.V) (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (hSurvivingBlocks : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 ∈ GluingDatum.incidentEdges vertex →
      data.localRamification vertex ((data.vertexPartition vertex).toBlock edge.1.2) = 0)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex)
    (path : StablePath data) : matrix data path first = matrix data path second :=
  column_eq_of_divalent_of_path_localRamification_zero vertex hDivalent path
    (fun edge hSurvives _ ↦ hSurvivingBlocks edge hSurvives) hNe hFirst hSecond

end DraismaVargas.LocalCases.StableSourceMatrix
