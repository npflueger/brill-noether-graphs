module

public import DraismaVargas.LocalCases.W2RankObstructions
public import DraismaVargas.LocalCases.W2R2Nd2PColumns
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# The distinguished nd2 cofactor vanishes in the actual incoming matrix

Figure 36's two limit-column equations imply `c_h = 0`. We read that
cofactor from the honest full-dimensional incoming matrix, using the proved
canonical row pushforward. The adjugate row at the contracted target column
annihilates every retained incoming column, hence every pushed-forward wall
column. The wall columns agree off the distinguished row, and inherited rank
ensures their difference is nonzero. Thus the value on the lifted distinguished
row vanishes for every nd2 profile, not only the unequal-index P pair.

The downstream `W2R2Nd2PExclusion` completes the nd2 exclusion by transporting
the actual r0 background and proving the new column's expansion vanishes.
-/

namespace DraismaVargas.LocalCases.W2R2Nd2PCofactor

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource W2R1Target SecondEquation
open WallDegeneration FullDimensionalSource WallInheritedRank PrunedFibreStablePath

variable {target : CFGraph} {degree : ℕ}

/-- The cofactor at the actual lifted distinguished row is zero. No row
equivalence, cofactor identity, or incoming matrix-entry formula is assumed. -/
theorem cofactor_liftedPath_eq_zero
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
    (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).adjugate
      (fullDim.labelling.targetEdge.symm contracted)
      (fullDim.labelling.row
        (stablePathLift data hc hab hOne fullDim.valid.1 hCompat hForest
          (W2R2Nd2PColumns.distinguishedPath profile))) = 0 := by
  classical
  let A := GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation
  let column := fullDim.labelling.targetEdge.symm contracted
  let cofactor : (coordinate → ℚ) →ₗ[ℚ] ℚ :=
    (LinearMap.proj column).comp A.adjugate.mulVecLin
  let push := rowPushforward data hc hab hOne fullDim.valid.1 hCompat hForest fullDim.labelling
  let functional := cofactor.comp push
  have hAnnihilates : ∀ edge : (contract target hab hOne).edges,
      functional ((StableSourceMatrix.matrix (contractDatum data hc hab hOne)).col edge) = 0 := by
    intro edge
    change cofactor (push ((StableSourceMatrix.matrix (contractDatum data hc hab hOne)).col edge)) = 0
    apply Eq.trans (congrArg cofactor
      (rowPushforward_column data hc hab hOne fullDim.valid.1 hCompat hForest fullDim.labelling edge))
    have hNe : fullDim.labelling.targetEdge.symm (unfoldEdge hc hab hOne edge) ≠ column := by
      intro hEq
      exact unfoldEdge_ne_contracted hc hab hOne edge
        (fullDim.labelling.targetEdge.symm.injective hEq)
    change Matrix.mulVec A.adjugate
      (A.col (fullDim.labelling.targetEdge.symm (unfoldEdge hc hab hOne edge))) column = 0
    simpa only [Matrix.mulVec, dotProduct, Matrix.col_apply, columnContribution, mul_comm] using
      columnContribution_eq_zero A hNe
  have hZero := W2R2Nd2PColumns.annihilator_single_eq_zero_of_rank star
    profile (W2RankObstructions.other_localRamification_eq_zero input block hR)
    (WallInheritedRank.columns_independent data hc hab hOne fullDim hCompat hForest)
    functional hAnnihilates
  change cofactor (rowPushforward data hc hab hOne fullDim.valid.1 hCompat hForest
    fullDim.labelling (Pi.single (W2R2Nd2PColumns.distinguishedPath profile) (1 : ℚ))) = 0 at hZero
  have hSingle := congrArg cofactor (rowPushforward_single data hc hab hOne
    fullDim.valid.1 hCompat hForest fullDim.labelling (W2R2Nd2PColumns.distinguishedPath profile))
  have hValue := hSingle.symm.trans hZero
  simpa only [cofactor, LinearMap.comp_apply, LinearMap.proj_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply, A, column] using hValue

/-- Every incoming surviving incidence touching the distinguished nd2 fibre
has the same vanishing cofactor. This uses the physical divalent-fibre lift
and works for both Base I and Base II, without classifying their internal
edge sets or indices. -/
theorem cofactor_eq_zero_of_incident_fibre
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
    (edge : NonDanglingEdge data) (point : data.SourceVertex)
    (hIncident : Incident data edge.1 point)
    (hMap : sourceVertexMap data hc hab hOne point = WallBlock.sourceVertex _ _ block) :
    (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).adjugate
      (fullDim.labelling.targetEdge.symm contracted) (fullDim.labelling.row edge.stablePath) = 0 := by
  let vertex := WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ block
  let small : NonDanglingEdge data := nonDanglingEmbedding data hCompat.1
    ⟨profile.small.1, profile.small_survives⟩
  obtain ⟨smallPoint, hSmallInc, hSmallMap⟩ := exists_incident_sourceEdgeEmbedding
    data hc hab hOne profile.small.1 vertex profile.small.2
  have hPath : edge.stablePath = stablePathLift data hc hab hOne fullDim.valid.1 hCompat hForest
      (W2R2Nd2PColumns.distinguishedPath profile) :=
    stablePath_eq_of_divalent_fibre data hc hab hOne vertex
      (PrunedFibreTree.nonDanglingValency_eq_two_of_sourceVertexMap_eq
        data hc hab hOne fullDim.valid.1 hCompat hForest vertex profile.valency)
      edge small point smallPoint hIncident hSmallInc hMap hSmallMap
  rw [hPath]
  exact cofactor_liftedPath_eq_zero data hc hab hOne fullDim hCompat hForest input block hR profile

end DraismaVargas.LocalCases.W2R2Nd2PCofactor
