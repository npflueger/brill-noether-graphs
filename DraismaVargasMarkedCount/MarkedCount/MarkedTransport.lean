module

public import DraismaVargasMarkedCount.MarkedCount.MarkedPath
public import DraismaVargasCount.GeometricMultiplicity

@[expose] public section

/-!
# The marked matrix and its transport along an isomorphism of data

Helper module of `DraismaVargasMarkedCount.MarkedCount.MarkedFrame`. It is the
marked twin of three public pieces:

* `StableSourceMatrix.matrix` and `labelling_matrix_eq`: the natural marked matrix
  `markedMatrix data marks`, indexed by marked rows and target edges, and
  `MarkedLabelling.matrix_eq`, saying that a marked labelling only relabels its rows and columns;
  `absMult_eq_of_submatrix`, the cross-datum form of `Count.absMult_of_submatrix`;
* `GeometricDatumIso.consecutive_map_iff`, `stablePathEquiv`, `occurrences_map`, `matrix_map`:
  an isomorphism of data carrying marks to marks (`hMarks`) induces a dictionary of marked rows
  (`markedStablePathEquiv`, a `Quot.congr` of the occurrence bijection) that preserves every
  entry of the natural marked matrix (`markedMatrix_map`);
* the local ramification `r_φ` is invariant under the relabelling (`localRamification_map`).

Nothing here is specific to frames; `MarkedFrame` assembles its two statements on isomorphisms from
it.
-/

namespace DraismaVargas.Count.MarkedCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource

/-! ## 1.  The natural marked matrix -/

section NaturalMatrix

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {marks : Finset data.SourceVertex}

/-- The surviving occurrences of one marked row over one target edge. -/
noncomputable def markedOccurrences (data : GluingDatum target degree)
    (marks : Finset data.SourceVertex) (path : MarkedStablePath data marks)
    (place : target.edges) : Finset data.SourceEdge := by
  classical
  exact Finset.univ.filter fun edge ↦
    (∃ hSurvives : ¬ IsDangling data edge,
      markedRow marks (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path) ∧ edge.1.1 = place

theorem mem_markedOccurrences (path : MarkedStablePath data marks) (place : target.edges)
    (edge : data.SourceEdge) :
    edge ∈ markedOccurrences data marks path place ↔
      (∃ hSurvives : ¬ IsDangling data edge,
        markedRow marks (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path) ∧
          edge.1.1 = place := by
  classical
  simp [markedOccurrences]

/-- **The natural marked matrix** `A_{φ;u,v}`, on its own row and column types: the entry at a
marked row and a target edge is `∑ 1/m(e)` over the occurrences of the row above the edge. -/
noncomputable def markedMatrix (data : GluingDatum target degree)
    (marks : Finset data.SourceVertex) : Matrix (MarkedStablePath data marks) target.edges ℚ :=
  fun path place ↦ ∑ edge ∈ markedOccurrences data marks path place,
    (1 : ℚ) / data.sourceEdgeIndex edge

namespace MarkedLabelling

variable {coordinate : Type*}

theorem mem_path_iff (labelling : MarkedLabelling data marks coordinate) (row : coordinate)
    (edge : data.SourceEdge) :
    edge ∈ labelling.path row ↔
      ∃ hSurvives : ¬ IsDangling data edge,
        labelling.row (markedRow marks (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row := by
  classical
  simp [path]

variable [DecidableEq coordinate]

/-- **A marked labelling only relabels the natural marked matrix**, the marked twin of
`StableSourceMatrix.labelling_matrix_eq`, with the same proof. -/
theorem matrix_eq (labelling : MarkedLabelling data marks coordinate) (row column : coordinate) :
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row column =
      markedMatrix data marks (labelling.row.symm row) (labelling.targetEdge column) := by
  classical
  have hNodup : (labelling.path row).Nodup := by
    unfold path
    exact List.Nodup.filter _ (Finset.univ.nodup_toList)
  have hToFinset : (labelling.path row).toFinset =
      (Finset.univ : Finset data.SourceEdge).filter
        (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
          labelling.row (markedRow marks (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) := by
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
      unfold markedMatrix markedOccurrences
      rw [hToFinset, Finset.filter_filter]
      congr 1
      ext edge
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← Equiv.eq_symm_apply]

end MarkedLabelling

end NaturalMatrix

/-! ## 2.  `absMult` across data, from a reindexing of the matrix -/

section Reindex

open GluingDatum.LengthMatrixPresentation in
/-- **Row and column permutations leave `absMult` unchanged, across two data** whose targets have
as many leaves: the cross-datum form of `Count.absMult_of_submatrix`, with the same proof. -/
theorem absMult_eq_of_submatrix {target₁ target₂ : CFGraph} {degree : ℕ}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (presentation : second.LengthMatrixPresentation coordinate)
    (other : first.LengthMatrixPresentation coordinate)
    (rowPerm columnPerm : Equiv.Perm coordinate)
    (hMatrix : matrix presentation = (matrix other).submatrix rowPerm columnPerm)
    (hLeaf : leafCount target₂ = leafCount target₁) :
    absMult presentation = absMult other := by
  classical
  have hRow : ∀ sourceRow : coordinate,
      rowDenominator presentation sourceRow = rowDenominator other (rowPerm sourceRow) := by
    intro sourceRow
    unfold rowDenominator commonDenominator
    have hFun : (fun column ↦ (matrix presentation sourceRow column).den) =
        (fun column ↦ (matrix other (rowPerm sourceRow) column).den) ∘ columnPerm := by
      funext column
      rw [hMatrix]
      rfl
    rw [hFun, ← Finset.lcm_image, Finset.image_univ_equiv]
  have hProduct : denominatorProduct presentation = denominatorProduct other := by
    unfold denominatorProduct
    rw [show (fun sourceRow ↦ rowDenominator presentation sourceRow) =
        fun sourceRow ↦ rowDenominator other (rowPerm sourceRow) from funext hRow]
    exact Fintype.prod_equiv rowPerm _ _ fun _ ↦ rfl
  have hDet : |(matrix presentation).det| = |(matrix other).det| := by
    rw [hMatrix]
    exact Matrix.abs_det_submatrix_equiv_equiv rowPerm columnPerm (matrix other)
  unfold absMult signedMult
  rw [abs_mul, abs_mul, hProduct, hDet, hLeaf]

end Reindex

/-! ## 3.  Transport of marked rows along an isomorphism of data carrying marks to marks -/

section Transport

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  {marks₁ : Finset first.SourceVertex} {marks₂ : Finset second.SourceVertex}

/-- **Marked consecutiveness is transported**: the unmarked `consecutive_map_iff`, plus marks
going to marks. -/
theorem markedConsecutive_map_iff (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (hMarks : ∀ vertex, iso.sourceVertexEquiv vertex ∈ marks₂ ↔ vertex ∈ marks₁)
    (left right : NonDanglingEdge first) :
    MarkedConsecutive second marks₂ (iso.nonDanglingEdgeEquiv hConnected left)
        (iso.nonDanglingEdgeEquiv hConnected right) ↔
      MarkedConsecutive first marks₁ left right := by
  constructor
  · rintro ⟨hNe, vertex, hLeft, hRight, hValency, hMark⟩
    obtain ⟨vertex, rfl⟩ := iso.sourceVertexEquiv.surjective vertex
    refine ⟨fun h ↦ hNe (congrArg (iso.nonDanglingEdgeEquiv hConnected) h),
      vertex, ?_, ?_, ?_, ?_⟩
    · exact (iso.incident_map_iff left.1 vertex).mp hLeft
    · exact (iso.incident_map_iff right.1 vertex).mp hRight
    · rwa [iso.nonDanglingValency_map hConnected] at hValency
    · rwa [hMarks] at hMark
  · rintro ⟨hNe, vertex, hLeft, hRight, hValency, hMark⟩
    refine ⟨(iso.nonDanglingEdgeEquiv hConnected).injective.ne hNe,
      iso.sourceVertexEquiv vertex, ?_, ?_, ?_, ?_⟩
    · exact (iso.incident_map_iff left.1 vertex).mpr hLeft
    · exact (iso.incident_map_iff right.1 vertex).mpr hRight
    · rwa [iso.nonDanglingValency_map hConnected]
    · rwa [hMarks]

/-- **The induced dictionary of marked rows**, descended from the occurrence bijection. -/
noncomputable def markedStablePathEquiv (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (hMarks : ∀ vertex, iso.sourceVertexEquiv vertex ∈ marks₂ ↔ vertex ∈ marks₁) :
    MarkedStablePath first marks₁ ≃ MarkedStablePath second marks₂ :=
  Quot.congr (iso.nonDanglingEdgeEquiv hConnected)
    fun left right ↦ (markedConsecutive_map_iff iso hConnected hMarks left right).symm

theorem markedStablePathEquiv_markedRow (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (hMarks : ∀ vertex, iso.sourceVertexEquiv vertex ∈ marks₂ ↔ vertex ∈ marks₁)
    (edge : NonDanglingEdge first) :
    markedStablePathEquiv iso hConnected hMarks (markedRow marks₁ edge) =
      markedRow marks₂ (iso.nonDanglingEdgeEquiv hConnected edge) := rfl

/-- Marked-row-filtered occurrence sets correspond. -/
theorem markedOccurrences_map (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (hMarks : ∀ vertex, iso.sourceVertexEquiv vertex ∈ marks₂ ↔ vertex ∈ marks₁)
    (path : MarkedStablePath first marks₁) (place : target₁.edges) :
    markedOccurrences second marks₂ (markedStablePathEquiv iso hConnected hMarks path)
        (iso.targetEdge place) =
      (markedOccurrences first marks₁ path place).image iso.sourceEdgeEquiv := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := iso.sourceEdgeEquiv.surjective edge
  rw [mem_markedOccurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    have hOld : ¬ IsDangling first edge := fun h ↦ hSurvives
      ((iso.isDangling_map_iff hConnected edge).mpr h)
    have hOldTarget : edge.1.1 = place := iso.targetEdge.injective hTarget
    apply Finset.mem_image.mpr
    refine ⟨edge, (mem_markedOccurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, hOldTarget⟩, rfl⟩
    apply (markedStablePathEquiv iso hConnected hMarks).injective
    exact (markedStablePathEquiv_markedRow iso hConnected hMarks ⟨edge, hOld⟩).trans hRow
  · intro hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    have hEq : old = edge := iso.sourceEdgeEquiv.injective hEqual
    subst hEq
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_markedOccurrences _ _ _).mp hOld
    have hNew : ¬ IsDangling second (iso.sourceEdgeEquiv old) := fun h ↦
      hSurvives ((iso.isDangling_map_iff hConnected old).mp h)
    refine ⟨⟨hNew, ?_⟩, congrArg iso.targetEdge hTarget⟩
    exact (markedStablePathEquiv_markedRow iso hConnected hMarks ⟨old, hSurvives⟩).symm.trans
      (congrArg (markedStablePathEquiv iso hConnected hMarks) hRow)

/-- **Every entry of the natural marked matrix is preserved**, the marked twin of
`GeometricDatumIso.matrix_map`. -/
theorem markedMatrix_map (iso : GeometricDatumIso first second) (hConnected : first.Connected)
    (hMarks : ∀ vertex, iso.sourceVertexEquiv vertex ∈ marks₂ ↔ vertex ∈ marks₁)
    (path : MarkedStablePath first marks₁) (place : target₁.edges) :
    markedMatrix second marks₂ (markedStablePathEquiv iso hConnected hMarks path)
        (iso.targetEdge place) =
      markedMatrix first marks₁ path place := by
  classical
  unfold markedMatrix
  rw [markedOccurrences_map iso hConnected hMarks, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by rw [iso.sourceEdgeIndex_map]
  · exact fun _ _ _ _ h ↦ iso.sourceEdgeEquiv.injective h

/-! ## 4.  Local ramification under relabelling -/

/-- **`r_φ` is invariant under an isomorphism of data**: the incident target edges correspond,
their refinement counts at corresponding sheets agree (`blockCountWithin_map`), and so do the
block sizes and the target valency. -/
theorem localRamification_map (iso : GeometricDatumIso first second) (vertex : target₁.V)
    (sheet : (first.vertexPartition vertex).Blocks)
    (hSheet : (second.vertexPartition (iso.targetVertex vertex)).repr
      (iso.vertexPerm vertex sheet.1) = iso.vertexPerm vertex sheet.1) :
    second.localRamification (iso.targetVertex vertex) ⟨iso.vertexPerm vertex sheet.1, hSheet⟩ =
      first.localRamification vertex sheet := by
  classical
  unfold GluingDatum.localRamification
  have hSum : (∑ edge ∈ GluingDatum.incidentEdges (iso.targetVertex vertex),
      ((second.edgePartition edge).blockCountWithin
        (second.vertexPartition (iso.targetVertex vertex)) (iso.vertexPerm vertex sheet.1) : ℤ)) =
      ∑ edge ∈ GluingDatum.incidentEdges vertex,
        ((first.edgePartition edge).blockCountWithin (first.vertexPartition vertex) sheet.1 :
          ℤ) := by
    refine (Finset.sum_bij (fun edge _ ↦ iso.targetEdge edge) ?_ ?_ ?_ ?_).symm
    · exact fun edge hEdge ↦ (iso.mem_incidentEdges_map vertex edge).mpr hEdge
    · exact fun _ _ _ _ h ↦ iso.targetEdge.injective h
    · intro edge hEdge
      refine ⟨iso.targetEdge.symm edge, ?_, iso.targetEdge.apply_symm_apply edge⟩
      refine (iso.mem_incidentEdges_map vertex _).mp ?_
      rwa [Equiv.apply_symm_apply]
    · intro edge hEdge
      exact_mod_cast (iso.blockCountWithin_map vertex edge hEdge sheet.1).symm
  have hCard : (second.vertexPartition (iso.targetVertex vertex)).blockCard
      (iso.vertexPerm vertex sheet.1) = (first.vertexPartition vertex).blockCard sheet.1 := by
    rw [iso.vertexPartition vertex]
    exact (first.vertexPartition vertex).relabel_blockCard (iso.vertexPerm vertex) sheet.1
  rw [hSum, iso.incidentEdges_card_map vertex, hCard]


end Transport

end DraismaVargas.Count.MarkedCount
