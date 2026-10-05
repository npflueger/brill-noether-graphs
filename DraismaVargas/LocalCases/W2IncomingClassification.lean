module

public import DraismaVargas.LocalCases.W2R2Nd2PExclusion

@[expose] public section

/-!
# Exhaustive actual incoming W2 occurrence profiles

In Case `{w2}` of Draisma--Vargas Part I the ramification either splits as
`1+1` or concentrates as `2`.  The inherited-rank and cofactor obstructions
force a concentrated block to have surviving valency three.  Consequently the
r1 profiles (Figures 37--38 of Part I) and the r2-nd3 M/P profiles
(Figures 32--35) exhaust the actual ramified blocks of an incoming
full-dimensional forest contraction.
The constructors also record that every other wall block is r0.

This is an exhaustive *source-profile* classification, not an outgoing
continuation theorem. No candidate-family census, stable-row identification,
determinant balance or progress witness is claimed by this file.
-/

namespace DraismaVargas.LocalCases.W2IncomingClassification

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource W2R1Target SecondEquation
open WallDegeneration FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- Actual source occurrences and exact ramification support. Each r1
profile contains its nd2/nd3 alternatives; the concentrated profile contains
the r2-nd3 M/P alternatives. Nothing is a freely chosen numerical diagram. -/
inductive Classification (data : GluingDatum target degree) (star : TwoStar target wall) where
  | split (first second : WallBlock data wall) (distinct : first ≠ second)
      (firstProfile : W2R1SourceProfile.SourceProfile data star first)
      (secondProfile : W2R1SourceProfile.SourceProfile data star second)
      (background : ∀ other : WallBlock data wall, other ≠ first → other ≠ second →
        data.localRamification wall other = 0)
  | concentrated (block : WallBlock data wall)
      (profile : W2R2SourceProfile.SourceProfile data star block)
      (background : ∀ other : WallBlock data wall, other ≠ block →
        data.localRamification wall other = 0)

/-- The split case's two units of ramification exhaust the total change. -/
theorem other_localRamification_eq_zero_of_split
    {data : GluingDatum target degree} {star : TwoStar target wall}
    (input : W2SourceInput data star) (first second : WallBlock data wall)
    (hNe : first ≠ second) (hFirst : data.localRamification wall first = 1)
    (hSecond : data.localRamification wall second = 1)
    (other : WallBlock data wall) (hOtherFirst : other ≠ first) (hOtherSecond : other ≠ second) :
    data.localRamification wall other = 0 := by
  classical
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun item : WallBlock data wall ↦ data.localRamification wall item)
    (Finset.subset_univ ({other, first, second} : Finset (WallBlock data wall)))
    (fun item _ _ ↦ input.localRamification_nonneg item)
  have hNotMem : other ∉ ({first, second} : Finset (WallBlock data wall)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hOtherFirst, hOtherSecond⟩
  rw [Finset.sum_insert hNotMem,
    Finset.sum_pair hNe, hFirst, hSecond, input.sum_localRamification] at hLe
  have hNonneg := input.localRamification_nonneg other
  omega

/-- Every actual full-dimensional incoming W2 contraction has one of the
listed occurrence profiles. The concentrated nd3 condition is proved, not
supplied; no no-return or pass-once hypothesis is added. -/
theorem exists_classification
    (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
    (input : W2SourceInput (contractDatum data hc hab hOne) star) :
    Nonempty (Classification (contractDatum data hc hab hOne) star) := by
  rcases input.ramification_split_or_concentrated with
    ⟨first, second, hNe, hFirst, hSecond⟩ | ⟨block, hR⟩
  · obtain ⟨firstProfile⟩ := W2R1SourceProfile.exists_sourceProfile input first hFirst
    obtain ⟨secondProfile⟩ := W2R1SourceProfile.exists_sourceProfile input second hSecond
    exact ⟨.split first second hNe firstProfile secondProfile
      (other_localRamification_eq_zero_of_split input first second hNe hFirst hSecond)⟩
  · have hNd := W2R2Nd2PExclusion.nonDanglingValency_eq_three_of_contraction
      data hc hab hOne fullDim hCompat hForest input block hR
    obtain ⟨profile⟩ := W2R2SourceProfile.exists_sourceProfile input block hR hNd
    exact ⟨.concentrated block profile
      (W2RankObstructions.other_localRamification_eq_zero input block hR)⟩

end DraismaVargas.LocalCases.W2IncomingClassification
