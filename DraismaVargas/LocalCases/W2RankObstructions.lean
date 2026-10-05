module

public import DraismaVargas.LocalCases.WallInheritedRank
public import DraismaVargas.LocalCases.StablePathContraction

@[expose] public section

/-!
# Rank exclusions for actual divalent walls

The source's W2 case analysis uses inherited full column rank, not merely
the five fields of `SecondEquation.W2SourceInput`. Here the rank theorem is
consumed on the literal natural matrix. A ramification-two block cannot be
entirely pruned: otherwise every surviving block is unramified and the two
target columns coincide. For an nd2 block, equal survivor indices likewise
force coincident columns unless the two survivors have the same target.

The latter degree-two, unit-index exception is deliberately retained by the
wall-rank-only statements here. Downstream `W2R2Nd2PExclusion` excludes it and
the unequal-index P branch by extending Figure 36's incoming cofactor
argument (Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd2-P}`).
Part I instead invokes global
pass-once for the return at `lemma-limit-no-return`. No theorem below alone
claims those incoming-resolution exclusions.
-/

namespace DraismaVargas.LocalCases.W2RankObstructions

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ClassInjectivity WallDegeneration FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

/-- A block using both units of wall ramification leaves every other block
unramified. This follows from the actual total change and nonnegativity. -/
theorem other_localRamification_eq_zero (input : W2SourceInput data star)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 2)
    (other : WallBlock data wall) (hNe : other ≠ block) :
    data.localRamification wall other = 0 := by
  classical
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun item : WallBlock data wall ↦ data.localRamification wall item)
    (Finset.subset_univ ({other, block} : Finset (WallBlock data wall)))
    (fun item _ _ ↦ input.localRamification_nonneg item)
  rw [Finset.sum_pair hNe, input.sum_localRamification, hR] at hLe
  have hNonneg := input.localRamification_nonneg other
  omega

/-- An entirely pruned exceptional block is invisible in the natural
matrix. All visible blocks are r0, making the two distinct target columns
equal and contradicting full column rank. -/
theorem nonDanglingValency_ne_zero (input : W2SourceInput data star)
    (hRank : LinearIndependent ℚ (StableSourceMatrix.matrix data).col)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 2) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) ≠ 0 := by
  intro hZero
  have hOthers : ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
      edge.1.1 ∈ GluingDatum.incidentEdges wall →
      data.localRamification wall ((data.vertexPartition wall).toBlock edge.1.2) = 0 := by
    intro edge hSurvives hIncident
    apply other_localRamification_eq_zero input block hR
      (WallBlock.ofSheet data wall edge.1.2)
    intro hBlock
    exact nonDanglingValency_ne_zero_of_incident data hSurvives
      ((incident_wallBlock_sourceVertex_iff data block edge).mpr ⟨hIncident, hBlock⟩) hZero
  have hNe : star.edge 0 ≠ star.edge 1 := fun h ↦ by
    have hBad := star.edge_injective h
    exact (by decide : (0 : Fin 2) ≠ 1) hBad
  exact hNe (hRank.injective (funext
    (StableSourceMatrix.column_eq_of_divalent_of_surviving_localRamification_zero
      wall star.card_incidentEdges hOthers hNe
      (star.edge_mem_incidentEdges 0) (star.edge_mem_incidentEdges 1))))

/-- The concentrated block of a full-rank W2 input has nd2 or nd3, not nd0. -/
theorem nonDanglingValency_eq_two_or_three (input : W2SourceInput data star)
    (hRank : LinearIndependent ℚ (StableSourceMatrix.matrix data).col)
    (block : WallBlock data wall) (hR : data.localRamification wall block = 2) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 ∨
      nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3 := by
  exact (input.nonDangling_valency block).resolve_left
    (nonDanglingValency_ne_zero input hRank block hR)

section Contraction

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum data hc hab hOne) star)

include fullDim hCompat hForest input

/-- Source-facing contraction endpoint: no separate inherited-rank receipt
is required to exclude the entirely pruned concentrated block. -/
theorem nonDanglingValency_eq_two_or_three_of_contraction
    (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hR : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 2) :
    nonDanglingValency (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex _ _ block) = 2 ∨
      nonDanglingValency (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex _ _ block) = 3 :=
  nonDanglingValency_eq_two_or_three input
    (WallInheritedRank.columns_independent data hc hab hOne fullDim hCompat hForest) block hR

end Contraction

/-- Every incoming ramified constituent over an endpoint maps to the unique
concentrated r2 wall block. Otherwise forest ramification additivity would
force its ramification to vanish. This is actual source-vertex transport. -/
theorem sourceVertexMap_eq_of_positive_ramification
    (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hValid : data.Valid) (hForest : ContractionForest data a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum data hc hab hOne) star)
    (block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hR : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ block = 2)
    (point : data.SourceVertex) (hAt : point.1.1 = a ∨ point.1.1 = b)
    (hPositive : 0 < data.localRamification point.1.1 ⟨point.1.2, point.2⟩) :
    sourceVertexMap data hc hab hOne point = WallBlock.sourceVertex _ _ block := by
  let other := WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ point.1.2
  have hOther : other = block := by
    by_contra hNe
    have hZero := other_localRamification_eq_zero input block hR other hNe
    have hAtZero : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ point.1.2 = 0 :=
      (localRamificationAt_congr (contractDatum data hc hab hOne) ⟨a, hab⟩
        (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_right point.1.2)).trans
          ((localRamificationAt_block _ _ other).trans hZero)
    have hEnds := StablePathContraction.endpoint_localRamification_eq_zero data hc hab hOne
      hValid hForest point.1.2 hAtZero
    have hPointZero : data.localRamification point.1.1
        ((data.vertexPartition point.1.1).toBlock point.1.2) = 0 := by
      rcases hAt with hAt | hAt
      · rw [hAt]; exact hEnds.1
      · rw [hAt]; exact hEnds.2
    have hBlockEq : (data.vertexPartition point.1.1).toBlock point.1.2 =
        (⟨point.1.2, point.2⟩ : (data.vertexPartition point.1.1).Blocks) := Subtype.ext point.2
    rw [hBlockEq] at hPointZero
    omega
  rw [← hOther]
  unfold sourceVertexMap
  rw [ContractionFibre.fold_eq_of_eq_or hab hAt]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr_idem point.1.2).symm

end DraismaVargas.LocalCases.W2RankObstructions
