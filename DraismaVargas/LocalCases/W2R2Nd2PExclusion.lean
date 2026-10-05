module

public import DraismaVargas.LocalCases.W2R2Nd2PLeaf

@[expose] public section

/-!
# Excluding all concentrated nd2 profiles via the Figure 36 cofactor argument

Source: Draisma--Vargas Part I, case `{w2-r2-nd2-P}` and Figure 36. The same
argument excludes all nd2 profiles, including the same-direction unit-index
return. Off the distinguished row the two wall columns agree by actual r0
transport; inherited rank makes their difference nonzero. Thus their annihilator
vanishes on that row, irrespective of the index profile. Base I has already been
excluded by the leaf column. In Base II compare the contracted column with the
other column at one divalent endpoint. For a row with nonzero cofactor, every
incident constituent must have ramification zero: a ramified constituent maps
into the distinguished fibre, whose cofactor vanishes. Canonical r0 occurrence
transport therefore equates the two entries of that row. Rows with zero cofactor
contribute nothing. The determinant expansion equals the off-diagonal adjugate
product, hence zero: a contradiction.

Thus the paper's common background contribution `s` is established on the
actual incoming occurrences. No displayed-matrix identity, background receipt,
or classification of a chosen outgoing resolution is assumed.
The file name refers to the P case; `nonDanglingValency_eq_three_of_contraction`
is the stronger statement.
-/

namespace DraismaVargas.LocalCases.W2R2Nd2PExclusion

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open WallDegeneration FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum data hc hab hOne) star)
  (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
  (hR : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 2)
  (profile : W2R2Nd2SourceProfile.SourceProfile (contractDatum data hc hab hOne) block)

include fullDim hCompat hForest input hR

include profile in
/-- **Every concentrated r2-nd2 case is impossible.** The Figure 36 cofactor
argument extends to both index profiles and the same-direction return by
using inherited rank to make the one-row column difference nonzero. -/
theorem false_of_nd2 : False := by
  classical
  obtain ⟨hLeft, _, _, _⟩ := W2R2Nd2PLeaf.endpoints_divalent data hc hab hOne
    fullDim hCompat hForest input block hR profile
  obtain ⟨retained, hRetained, hNe⟩ :=
    Finset.exists_mem_ne (show 1 < (GluingDatum.incidentEdges a).card by omega) contracted
  let A := GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation
  let column := fullDim.labelling.targetEdge.symm contracted
  let otherColumn := fullDim.labelling.targetEdge.symm retained
  have hColumnNe : otherColumn ≠ column :=
    fun h ↦ hNe (fullDim.labelling.targetEdge.symm.injective h)
  have hEntry (row : coordinate) (hCofactor : A.adjugate column row ≠ 0) :
      A row column = A row otherColumn := by
    have hZero : ∀ (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge),
        NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) =
          fullDim.labelling.row.symm row →
        edge.1.1 ∈ GluingDatum.incidentEdges a →
        data.localRamification a ((data.vertexPartition a).toBlock edge.1.2) = 0 := by
      intro edge hSurvives hPath hAt
      by_contra hNotZero
      have hNonneg := data.localRamification_nonneg a (fullDim.valid.2 a)
        ((data.vertexPartition a).toBlock edge.1.2)
      have hPositive : 0 < data.localRamification a
          ((data.vertexPartition a).toBlock edge.1.2) := by omega
      have hMap := W2RankObstructions.sourceVertexMap_eq_of_positive_ramification data hc hab hOne
        fullDim.valid hForest input block hR (data.sourceEndpoint a edge.1.2) (Or.inl rfl) hPositive
      have hIncident : Incident data edge (data.sourceEndpoint a edge.1.2) := by
        have h := incident_sourceEdge_sourceEndpoint data a edge.1.1 hAt edge.1.2
        rw [GluingDatum.sourceEdge_self] at h
        exact h
      have hVanishing := W2R2Nd2PCofactor.cofactor_eq_zero_of_incident_fibre data hc hab hOne
        fullDim hCompat hForest input block hR profile ⟨edge, hSurvives⟩
        (data.sourceEndpoint a edge.1.2) hIncident hMap
      rw [hPath, fullDim.labelling.row.apply_symm_apply] at hVanishing
      exact hCofactor hVanishing
    have hNatural := StableSourceMatrix.column_eq_of_divalent_of_path_localRamification_zero
      a hLeft (fullDim.labelling.row.symm row) hZero hNe.symm
      (contracted_mem_incidentEdges_left hc) hRetained
    simpa only [A, column, otherColumn, StableSourceMatrix.labelling_matrix_eq,
      fullDim.labelling.targetEdge.apply_symm_apply] using hNatural
  apply fullDim.det_ne_zero
  change A.det = 0
  rw [Matrix.det_eq_sum_mul_adjugate_col A column]
  calc
    _ = columnContribution A column otherColumn := by
      unfold columnContribution
      apply Finset.sum_congr rfl
      intro row _
      by_cases hCofactor : A.adjugate column row = 0
      · rw [hCofactor, mul_zero, mul_zero]
      · rw [hEntry row hCofactor]
    _ = 0 := columnContribution_eq_zero A hColumnNe

/-- Figure 36's P case, retained as the source-facing specialization of the
stronger obstruction. No index inequality is needed by the stronger proof. -/
theorem false_of_indices_ne
    (_hIndices : (contractDatum data hc hab hOne).sourceEdgeIndex profile.small.1 ≠
      (contractDatum data hc hab hOne).sourceEdgeIndex profile.large.1) : False :=
  false_of_nd2 data hc hab hOne fullDim hCompat hForest input block hR profile

/-- The concentrated r2 block of any actual full-dimensional W2 contraction
is trivalent in the pruned source. Both nd0 and every nd2 profile are excluded;
no pass-once, direction-injectivity or matrix-entry bound is assumed. -/
theorem nonDanglingValency_eq_three_of_contraction :
    nonDanglingValency (contractDatum data hc hab hOne)
      (WallBlock.sourceVertex _ _ block) = 3 := by
  rcases W2RankObstructions.nonDanglingValency_eq_two_or_three_of_contraction
    data hc hab hOne fullDim hCompat hForest input block hR with hTwo | hThree
  · obtain ⟨actualProfile⟩ := W2R2Nd2SourceProfile.exists_sourceProfile input block hR hTwo
    exact (false_of_nd2 data hc hab hOne fullDim hCompat hForest input block hR actualProfile).elim
  · exact hThree

end DraismaVargas.LocalCases.W2R2Nd2PExclusion
