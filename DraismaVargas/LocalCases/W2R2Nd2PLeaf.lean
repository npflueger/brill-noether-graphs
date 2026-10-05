module

public import DraismaVargas.LocalCases.W2R2Nd2PCofactor
public import DraismaVargas.LocalCases.MonovalentWall

@[expose] public section

/-!
# Excluding concentrated nd2 at a leaf-endpoint contraction (Base I)

Source: Draisma--Vargas Part I, case `{w2-r2-nd2-P}` and Figure 36: the
unequal-index P pair precludes Base I. The argument here applies to every nd2
index profile, using inherited
rank to prove the distinguished cofactor is zero. We use that equation to avoid a
second explicit enumeration of the leaf fibre. A change-minimal leaf has
exactly two surviving occurrences on one stable row, meeting one r2 vertex.
Forest ramification additivity places that vertex inside the distinguished
wall r2 fibre. Every incidence there has zero cofactor.
The entire contracted leaf column is supported in that row, so its cofactor
expansion is zero, contradicting full-dimensionality.

Both leaf orientations are covered. No leaf/trivalent source diagram or
new-column formula is assumed. The divalent--divalent r0 background is handled
separately in `W2R2Nd2PExclusion`.
-/

namespace DraismaVargas.LocalCases.W2R2Nd2PLeaf

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open WallDegeneration FullDimensionalSource MonovalentWall

variable {target : CFGraph} {degree : ℕ}

/-- **A concentrated nd2 profile cannot arise in Base I.** The actual leaf column's
cofactor expansion vanishes, contradicting the incoming nonsingular matrix. -/
theorem false_of_leaf_endpoint
    (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
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
    (leaf : target.V) (hAt : leaf = a ∨ leaf = b)
    (hLeaf : (GluingDatum.incidentEdges leaf).card = 1) : False := by
  classical
  have hContracted : contracted ∈ GluingDatum.incidentEdges leaf := by
    rcases hAt with hAt | hAt
    · rw [hAt]; exact contracted_mem_incidentEdges_left hc
    · rw [hAt]; exact contracted_mem_incidentEdges_right hc
  have hLeafSet : GluingDatum.incidentEdges leaf = {contracted} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hContracted, fun other hOther ↦
      Finset.card_le_one.mp (by omega) other hOther contracted hContracted⟩
  obtain ⟨fibre⟩ := exists_leafFibre data fullDim leaf contracted hLeafSet
  have hPositive : 0 < data.localRamification leaf fibre.block := by rw [fibre.ramification]; norm_num
  have hMap := W2RankObstructions.sourceVertexMap_eq_of_positive_ramification data hc hab hOne
    fullDim.valid hForest input block hR (blockVertex data leaf fibre.block) hAt hPositive
  have hCofactor := W2R2Nd2PCofactor.cofactor_eq_zero_of_incident_fibre data hc hab hOne
    fullDim hCompat hForest input block hR profile fibre.first
    (blockVertex data leaf fibre.block) fibre.first_incident hMap
  apply fullDim.det_ne_zero
  rw [Matrix.det_eq_sum_mul_adjugate_col _ (fullDim.labelling.targetEdge.symm contracted)]
  apply Finset.sum_eq_zero
  intro row _
  by_cases hRow : row = fullDim.labelling.row fibre.first.stablePath
  · rw [hRow, hCofactor, mul_zero]
  · rw [matrix_column_eq_zero_of_single_stablePath fullDim.labelling contracted
      fibre.first.stablePath fibre.stablePath_eq_of_target row hRow, zero_mul]

/-- Every hypothetical incoming concentrated nd2 profile is therefore in Base II: both target
endpoints are divalent and carry one unit of change. This consumes the
exhaustive three-way endpoint split, not an extra target-shape hypothesis. -/
theorem endpoints_divalent
    (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
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
    (profile : W2R2Nd2SourceProfile.SourceProfile (contractDatum data hc hab hOne) block) :
    (GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
      data.targetChange a = 1 ∧ data.targetChange b = 1 := by
  rcases valencySplit_of_twoStar data hc hab hOne fullDim.valid fullDim.changeMinimal star with
    hBoth | hLeft | hRight
  · exact hBoth
  · exact (false_of_leaf_endpoint data hc hab hOne fullDim hCompat hForest input block hR
      profile a (Or.inl rfl) hLeft.1).elim
  · exact (false_of_leaf_endpoint data hc hab hOne fullDim hCompat hForest input block hR
      profile b (Or.inr rfl) hRight.2.1).elim

end DraismaVargas.LocalCases.W2R2Nd2PLeaf
