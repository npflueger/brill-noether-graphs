module

public import DraismaVargas.LocalCases.SourceFibreForest
public import DraismaVargas.LocalCases.W2IncomingClassification
public import DraismaVargas.LocalCases.W3IncomingClassification

@[expose] public section

/-!
# Exhaustive incoming source-case selection

This module is the source-profile router for a genuine codimension-one wall
contraction.  The incoming datum is an honest full-dimensional presentation;
the contracted occurrence has zero coordinate in a nonnegative metric whose
stable row lengths remain nonzero.  Hence its source fibre is a forest and the
merged target valency is two, three, or four.

At valency two, `W2IncomingClassification` supplies the actual ramified wall
blocks and occurrence profiles.  The M alternative is split into M-11, M-1k,
and M-kk from the positive indices of its literal two doubled-direction
occurrences; the P and two-r1-block alternatives are retained verbatim.  At
valency three, `W3IncomingClassification` supplies the cases of Figures 28--31
of Draisma--Vargas Part I.  At valency four,
`AuxR0SourceInput.activeProfile` and `.blockPicture` are the canonical actual
W4 occurrence profiles.  The equation numbers (6)--(10) below are those of
Part I, Section 6.

The output is deliberately only a `ClassifiedContinuation.SourceCase` tag
together with the source profile and arithmetic premises selecting it.  It
does not construct any outgoing family, stable presentation, determinant
balance, incoming-member equality, or the per-case continuation across the
wall.
-/

namespace DraismaVargas.LocalCases.IncomingSourceCases

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open W4Assembly W4StableSource WallDegeneration FullDimensionalSource
open W2R1Target SecondEquation ThirdEquation

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}

/-! ## Refining the actual W2 classification into Equations (6)--(10) -/

namespace W2

/-- Equations (6)--(10), with the actual incoming profiles which select them.
The background fields record that the displayed ramified blocks exhaust the
wall's two units of change. -/
inductive Classification (data : GluingDatum target degree)
    (star : TwoStar target wall) (input : W2SourceInput data star) where
  /-- Equation (6): M with both doubled-direction indices equal to one. -/
  | m11 (block : WallBlock data wall)
      (source : W2R2SourceProfile.SourceProfile data star block)
      (deleted_target : source.deleted.edge.1.1.1 = star.edge source.singleLabel)
      (pair_card : data.sourceEdgeIndex source.first.1 +
          data.sourceEdgeIndex source.second.1 =
        (data.vertexPartition wall).blockCard block.1)
      (single_succ_card : data.sourceEdgeIndex source.third.1 + 1 =
        (data.vertexPartition wall).blockCard block.1)
      (background : ∀ other : WallBlock data wall, other ≠ block →
        data.localRamification wall other = 0)
      (first_one : data.sourceEdgeIndex source.first.1 = 1)
      (second_one : data.sourceEdgeIndex source.second.1 = 1)
      (third_one : data.sourceEdgeIndex source.third.1 = 1)
      (block_card_two : (data.vertexPartition wall).blockCard block.1 = 2) :
      Classification data star input
  /-- Equation (7): M with exactly one unit doubled-direction index and the
  other at least two.  The disjunction retains which literal occurrence is
  the unit one, without silently reordering the source profile. -/
  | m1k (block : WallBlock data wall)
      (source : W2R2SourceProfile.SourceProfile data star block)
      (deleted_target : source.deleted.edge.1.1.1 = star.edge source.singleLabel)
      (pair_card : data.sourceEdgeIndex source.first.1 +
          data.sourceEdgeIndex source.second.1 =
        (data.vertexPartition wall).blockCard block.1)
      (single_succ_card : data.sourceEdgeIndex source.third.1 + 1 =
        (data.vertexPartition wall).blockCard block.1)
      (background : ∀ other : WallBlock data wall, other ≠ block →
        data.localRamification wall other = 0)
      (unit_large :
        (data.sourceEdgeIndex source.first.1 = 1 ∧
          2 ≤ data.sourceEdgeIndex source.second.1) ∨
        (data.sourceEdgeIndex source.second.1 = 1 ∧
          2 ≤ data.sourceEdgeIndex source.first.1)) :
      Classification data star input
  /-- Equation (8): M with both doubled-direction indices at least two. -/
  | mkk (block : WallBlock data wall)
      (source : W2R2SourceProfile.SourceProfile data star block)
      (deleted_target : source.deleted.edge.1.1.1 = star.edge source.singleLabel)
      (pair_card : data.sourceEdgeIndex source.first.1 +
          data.sourceEdgeIndex source.second.1 =
        (data.vertexPartition wall).blockCard block.1)
      (single_succ_card : data.sourceEdgeIndex source.third.1 + 1 =
        (data.vertexPartition wall).blockCard block.1)
      (background : ∀ other : WallBlock data wall, other ≠ block →
        data.localRamification wall other = 0)
      (first_two_le : 2 ≤ data.sourceEdgeIndex source.first.1)
      (second_two_le : 2 ≤ data.sourceEdgeIndex source.second.1) :
      Classification data star input
  /-- Equation (9): the P half of the concentrated r2-nd3 profile. -/
  | p (block : WallBlock data wall)
      (source : W2R2SourceProfile.SourceProfile data star block)
      (deleted_target : source.deleted.edge.1.1.1 = star.edge source.doubleLabel)
      (pair_succ_card : data.sourceEdgeIndex source.first.1 +
          data.sourceEdgeIndex source.second.1 + 1 =
        (data.vertexPartition wall).blockCard block.1)
      (single_card : data.sourceEdgeIndex source.third.1 =
        (data.vertexPartition wall).blockCard block.1)
      (background : ∀ other : WallBlock data wall, other ≠ block →
        data.localRamification wall other = 0) :
      Classification data star input
  /-- Equation (10): the two distinct ramification-one blocks, each with its
  actual nd2/nd3 occurrence profile. -/
  | r1 (first second : WallBlock data wall) (distinct : first ≠ second)
      (firstProfile : W2R1SourceProfile.SourceProfile data star first)
      (secondProfile : W2R1SourceProfile.SourceProfile data star second)
      (background : ∀ other : WallBlock data wall,
        other ≠ first → other ≠ second →
          data.localRamification wall other = 0) :
      Classification data star input

namespace Classification

/-- The exact finite source-case tag selected by a W2 classification. -/
def sourceCase {data : GluingDatum target degree} {star : TwoStar target wall}
    {input : W2SourceInput data star} :
    Classification data star input → ClassifiedContinuation.SourceCase
  | .m11 .. => .w2M11
  | .m1k .. => .w2M1k
  | .mkk .. => .w2Mkk
  | .p .. => .w2P
  | .r1 .. => .w2R1

end Classification

/-- Refine the already-proved exhaustive incoming W2 classification into the
five equation tags.  The only new split is M-11/M-1k/M-kk, obtained from
positivity of the two actual source-edge indices. -/
theorem ofIncoming {data : GluingDatum target degree}
    {star : TwoStar target wall} (input : W2SourceInput data star)
    (incoming : W2IncomingClassification.Classification data star) :
    Nonempty (Classification data star input) := by
  cases incoming with
  | split first second distinct firstProfile secondProfile background =>
      exact ⟨.r1 first second distinct firstProfile secondProfile background⟩
  | concentrated block source background =>
      rcases source.cases with hM | hP
      · by_cases hFirst : data.sourceEdgeIndex source.first.1 = 1
        · by_cases hSecond : data.sourceEdgeIndex source.second.1 = 1
          · have hThird : data.sourceEdgeIndex source.third.1 = 1 := by
              omega
            have hCard : (data.vertexPartition wall).blockCard block.1 = 2 := by
              omega
            exact ⟨.m11 block source hM.1 hM.2.1 hM.2.2 background hFirst
              hSecond hThird hCard⟩
          · have hSecondPos := data.sourceEdgeIndex_pos source.second.1
            exact ⟨.m1k block source hM.1 hM.2.1 hM.2.2 background
              (Or.inl ⟨hFirst, by omega⟩)⟩
        · have hFirstPos := data.sourceEdgeIndex_pos source.first.1
          by_cases hSecond : data.sourceEdgeIndex source.second.1 = 1
          · exact ⟨.m1k block source hM.1 hM.2.1 hM.2.2 background
              (Or.inr ⟨hSecond, by omega⟩)⟩
          · have hSecondPos := data.sourceEdgeIndex_pos source.second.1
            exact ⟨.mkk block source hM.1 hM.2.1 hM.2.2 background
              (by omega) (by omega)⟩
      · exact ⟨.p block source hP.1 hP.2.1 hP.2.2 background⟩

end W2

/-! ## The ten-way wall router -/

/-- Source-derived classification of an actual contracted wall datum.  The W4
constructor retains an `AuxR0SourceInput`; its canonical literal profiles are
`input.activeProfile` and `input.blockPicture`. -/
inductive Classification (wallData : GluingDatum target degree)
    (wall : target.V) where
  | w4 (star : W4TargetPairings.FourStar target wall)
      (input : AuxR0SourceInput wallData star) : Classification wallData wall
  | w3 (star : ThreeStar target wall) (input : W3SourceInput wallData star)
      (profile : W3IncomingClassification.Classification wallData star input) :
      Classification wallData wall
  | w2 (star : TwoStar target wall) (input : W2SourceInput wallData star)
      (profile : W2.Classification wallData star input) :
      Classification wallData wall

namespace Classification

/-- Forget the genuine source profile to the exact ten-element endpoint used
by the continuation layer. -/
def sourceCase {wallData : GluingDatum target degree} {wall : target.V} :
    Classification wallData wall → ClassifiedContinuation.SourceCase
  | .w4 .. => .w4
  | .w3 _ _ profile => profile.sourceCase
  | .w2 _ _ profile => profile.sourceCase

end Classification

/-- Every admissible full-dimensional nonnegative wall contraction selects
one of the ten source cases with its actual occurrence profile.

The forest premise is derived from the nonnegative wall metric.  The supplied
stable-path, dangling-compatibility, and trivalence fields are the
wall-degeneration/source-model receipts used by all three source-input bridges;
no incoming rank receipt or no-return hypothesis is needed. -/
theorem exists_classification {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ)
    (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec coordinates row ≠ 0)
    (hZero : coordinates (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hStable : Nonempty
      (StablePath (contractDatum data hc hab hOne) ≃ StablePath data))
    (hCompatible : DanglingCompatible data hc hab hOne)
    (hTrivalent : ∀ sourceBlock : WallBlock
        (contractDatum data hc hab hOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩
            sourceBlock) ≤ 3) :
    Nonempty (Classification (contractDatum data hc hab hOne) ⟨a, hab⟩) := by
  let hForest := SourceFibreForest.contractionForest_of_fullDimensional
      (data := data) (coordinate := coordinate) fullDim coordinates
      hNonnegative hRows hc hZero
  rcases SourceFibreForest.wall_valencies_of_nonnegative_metric
      (data := data) (coordinate := coordinate) fullDim coordinates
      hNonnegative hRows hc hab hOne hZero with hTwo | hThree | hFour
  · let star : TwoStar (contract target hab hOne) ⟨a, hab⟩ := TwoStar.of_card hTwo
    let input : W2SourceInput (contractDatum data hc hab hOne) star :=
      w2SourceInput_of_contraction data hc hab hOne fullDim hForest hStable
        hCompatible.2 hTrivalent
    obtain ⟨incoming⟩ := W2IncomingClassification.exists_classification data hc hab
      hOne fullDim hCompatible hForest input
    obtain ⟨profile⟩ := W2.ofIncoming input incoming
    exact ⟨.w2 star input profile⟩
  · let star : ThreeStar (contract target hab hOne) ⟨a, hab⟩ :=
      ThreeStar.of_card hThree
    let input : W3SourceInput (contractDatum data hc hab hOne) star :=
      w3SourceInput_of_contraction data hc hab hOne fullDim hForest hStable
        hCompatible.2 hTrivalent
    obtain ⟨profile⟩ := W3IncomingClassification.exists_classification input
    exact ⟨.w3 star input profile⟩
  · let star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩ :=
      W4TargetPairings.FourStar.of_card hFour
    let input : AuxR0SourceInput (contractDatum data hc hab hOne) star :=
      W4Bridge.auxR0SourceInput_of_contraction data hc hab hOne fullDim hForest
        hStable hCompatible.2 hTrivalent
    exact ⟨.w4 star input⟩

end DraismaVargas.LocalCases.IncomingSourceCases
