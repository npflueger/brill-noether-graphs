module

public import DraismaVargas.LocalCases.ClassifiedContinuation
public import DraismaVargas.LocalCases.W3R1SourceProfile

@[expose] public section

/-!
# Exhaustive incoming source cases at a trivalent wall

The unique ramified block of a `ThirdEquation.W3SourceInput` has either the
actual nd2 profile of Figure 31, or one of the three actual nd3 profiles of
Figures 28--30.  This file records the exact routing to Equations (2)--(5),
including the occurrence-level profile and the arithmetic premise which
selects the equation.

This is classification only.  In particular it constructs no outgoing
resolution, stable-row dictionary, determinant balance, or continuation.
-/

namespace DraismaVargas.LocalCases.W3IncomingClassification

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource ThirdEquation W3R1SourceProfile

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- The four source-derived alternatives at a trivalent wall.  Every
constructor retains literal surviving source occurrences through its profile.
The displayed arithmetic fields are consequences of that profile, rather
than caller-supplied numerical diagrams. -/
inductive Classification (data : GluingDatum target degree)
    (star : ThreeStar target wall) (input : W3SourceInput data star) where
  /-- Figure 28 and Equation (2): three distinct target directions and the
  largest index equal to the local degree. -/
  | four (profile : Nd3Profile data (W3SourceInput.distinguishedBlock input))
      (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
      (largest_index : data.sourceEdgeIndex profile.largest.1 =
        (data.vertexPartition wall).blockCard
          (W3SourceInput.distinguishedBlock input).1)
      (pair_index : data.sourceEdgeIndex profile.first.1 +
          data.sourceEdgeIndex profile.second.1 =
        (data.vertexPartition wall).blockCard
          (W3SourceInput.distinguishedBlock input).1) :
      Classification data star input
  /-- Figure 29 and Equation (3): three distinct target directions and all
  three indices at least two because the largest is below the local degree. -/
  | shift (profile : Nd3Profile data (W3SourceInput.distinguishedBlock input))
      (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
      (largest_lt : data.sourceEdgeIndex profile.largest.1 <
        (data.vertexPartition wall).blockCard
          (W3SourceInput.distinguishedBlock input).1)
      (indices_two_le : 2 ≤ data.sourceEdgeIndex profile.first.1 ∧
        2 ≤ data.sourceEdgeIndex profile.second.1 ∧
        2 ≤ data.sourceEdgeIndex profile.largest.1) :
      Classification data star input
  /-- Figure 30 and Equation (4): two survivors share one target direction;
  their indices sum to the local degree, as does the largest index alone. -/
  | nd3CoarseFine
      (profile : Nd3Profile data (W3SourceInput.distinguishedBlock input))
      (same_direction : profile.first.1.1.1 = profile.second.1.1.1)
      (pair_index : data.sourceEdgeIndex profile.first.1 +
          data.sourceEdgeIndex profile.second.1 =
        (data.vertexPartition wall).blockCard
          (W3SourceInput.distinguishedBlock input).1)
      (largest_index : data.sourceEdgeIndex profile.largest.1 =
        (data.vertexPartition wall).blockCard
          (W3SourceInput.distinguishedBlock input).1) :
      Classification data star input
  /-- Figure 31 and Equation (5): the two actual survivors have distinct
  target directions and indices `|A|-1, |A|`; these facts are fields of the
  retained nd2 profile. -/
  | nd2CoarseFine
      (profile : Nd2Profile data (W3SourceInput.distinguishedBlock input)) :
      Classification data star input

namespace Classification

/-- The exact `ClassifiedContinuation.SourceCase` selected by a trivalent
incoming classification. -/
def sourceCase {data : GluingDatum target degree}
    {star : ThreeStar target wall} {input : W3SourceInput data star} :
    Classification data star input → ClassifiedContinuation.SourceCase
  | .four .. => .w3Four
  | .shift .. => .w3Shift
  | .nd3CoarseFine .. => .w3Nd3CoarseFine
  | .nd2CoarseFine .. => .w3Nd2CoarseFine

end Classification

/-- Every actual trivalent-wall source input selects one of the four
W3 tags, with its occurrence profile and its equation-selecting arithmetic
derived from the source input. -/
theorem exists_classification {data : GluingDatum target degree}
    {star : ThreeStar target wall} (input : W3SourceInput data star) :
    Nonempty (Classification data star input) := by
  rcases distinguished_sourceProfiles input with hNd2 | hNd3
  · obtain ⟨profile⟩ := hNd2
    exact ⟨.nd2CoarseFine profile⟩
  · obtain ⟨profile⟩ := hNd3
    rcases profile.cases with
      ⟨hSame, hLargest⟩ | ⟨hDistinct, hLargest⟩ | ⟨hDistinct, hLt⟩
    · obtain ⟨hPair, hLargest'⟩ := profile.doubled_direction hSame
      exact ⟨.nd3CoarseFine profile hSame hPair hLargest'⟩
    · exact ⟨.four profile hDistinct hLargest
        (profile.indices_of_largest_eq hLargest)⟩
    · exact ⟨.shift profile hDistinct hLt
        (profile.indices_two_le_of_largest_lt hLt)⟩

end DraismaVargas.LocalCases.W3IncomingClassification
