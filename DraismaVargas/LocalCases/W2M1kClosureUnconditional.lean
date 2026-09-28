import DraismaVargas.LocalCases.W2M1kLeafBackground
import DraismaVargas.LocalCases.W2M1kSelectedCensus

/-!
# The case split and the `background` field at an M-1k wall

Source: Draisma--Vargas Part I, Case {w2-r2-nd3-M-1k} (abbreviated M-1k or
M1k here), Figure 33 and Equation (7).

The M-1k closure at an incoming wall needs, besides the standing bundle -- the
incoming datum and its full-dimensional presentation, the contraction forest,
the wall input, its `w2-r2-nd3` profile and that profile's M-1k `Shape` -- the
source-side witness that names the orientation (`LeafPair` or `DividedData`),
the restored target valencies where they are needed, and the positivity data of
the exit.  The census hypotheses `W2M1kIncomingMatching.SelectedCensus` and
`W2M1kIncomingMatching.LeafBackgroundCensus` are proved in
`W2M1kSelectedCensus` and `W2M1kLeafBackground`.  This module supplies the two
remaining pieces of the case analysis.

* `wall_background`: the `background` field of
  `IncomingSourceCases.W2.Classification.m1k` is *not* an input: at a `w2-r2`
  wall a ramification-two block leaves nothing for the others
  (`W2RankObstructions.other_localRamification_eq_zero`), so it is derived from
  `wallInput` and `wallProfile.ramification`.
* `headline_cases`: three configurations exhaust the case.  A separated wall
  datum is never `T_∅` (`W2M1kSelectedCensus.not_dividedData_of_leaf`), so the
  surviving (source witness, target type) pairs are exactly aligned/`T_∅`,
  aligned/`T_2` and separated/`T_2`.

## The three configurations

**The leaf configuration produces its leaf pair.**  Figure 33's `M⁽¹⁾` retains
the pair `{x, s}` where `x` is the (common) pinned sheet and `s` is whatever
sheet the incoming leaf endpoint keeps with it.  `s` is *read off the cover*,
not chosen, so the census cannot hold for an arbitrary `LeafPair` -- the pair
is an output.  The alignment field of that pair is a theorem
(`W2M1kSelectedCensus.aligned_of_leaf`), not an assumption.

**The separated configuration needs no census choice.**  The census at a
separated `T_2` wall is a genuine dichotomy (Part I, Case {w2-r2}: `ndG(A₀)`
has one edge `e'` or two edges `e'`, `e''`), both branches occur, and either
one leads to the same exit, with the Figure 33 position inside
`separatedOrientation … divided`.

**The aligned `T_2` configuration** has the census of `M⁽³⁾`, and at an aligned
wall Base II.2.2 is impossible
(`W2M1kSelectedCensus.not_detaching_of_aligned`).
-/

namespace DraismaVargas.LocalCases.W2M1kClosureUnconditional

open DraismaVargas.Infrastructure
open TargetExpansion
open GraphContraction GluingContraction ContractionRamification WallDegeneration
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource
open W2M1kSourceCandidates
open W2M1kIncomingCensus W2M1kIncomingMatching

variable {degree : ℕ}
  {incomingTarget : CFGraph} {a b : incomingTarget.V} {contracted : incomingTarget.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (incoming : GluingDatum incomingTarget degree)
  (hc : (contracted : incomingTarget.V × incomingTarget.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges incomingTarget a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  {wallStar : TwoStar (contract incomingTarget hab hOne) ⟨a, hab⟩}
  (wallInput : W2SourceInput (contractDatum incoming hc hab hOne) wallStar)
  {wallBlock : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
  (wallProfile : W2R2SourceProfile.SourceProfile (contractDatum incoming hc hab hOne)
    wallStar wallBlock)
  (wallShape : Shape wallProfile)

include wallInput wallProfile

/-- **The classifier's `background` field, derived.**  At a `w2-r2` wall the two
units of change are spent on the ramification-two block, so every other wall
block carries none. -/
theorem wall_background (other : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hNe : other ≠ wallBlock) :
    (contractDatum incoming hc hab hOne).localRamification ⟨a, hab⟩ other = 0 :=
  W2RankObstructions.other_localRamification_eq_zero wallInput wallBlock
    wallProfile.ramification other hNe

include fullDim hForest

omit wallInput hForest in
/-- **Three configurations exhaust the case.**  On the source side
exactly one of `LeafPair`, `DividedData` is available over the wall datum
(`W2M1kSourceCandidates.exists_leafPair_or_dividedData`,
`not_leafPair_and_dividedData`), and on the target side
`W2M1kIncomingCensus.member_trichotomy` decides `T_2` against `T_∅`.  A separated
datum is never `T_∅` (`W2M1kSelectedCensus.not_dividedData_of_leaf`), so the
surviving pairs are exactly three: aligned `T_∅` (leaf), aligned `T_2`
(joined), separated `T_2`. -/
theorem headline_cases (shape : Shape wallProfile) :
    (Nonempty (LeafPair wallProfile) ∧
        ((GluingDatum.incidentEdges a).card = 1 ∨
          (GluingDatum.incidentEdges b).card = 1)) ∨
      (Nonempty (LeafPair wallProfile) ∧ (GluingDatum.incidentEdges a).card = 2 ∧
        (GluingDatum.incidentEdges b).card = 2) ∨
      (Nonempty (DividedData wallProfile) ∧ (GluingDatum.incidentEdges a).card = 2 ∧
        (GluingDatum.incidentEdges b).card = 2) := by
  rcases exists_leafPair_or_dividedData shape with hPair | hDivided
  · rcases member_trichotomy incoming hc hab hOne wallStar fullDim with
      ⟨hLeft, hRight, _, _⟩ | ⟨hLeft, _, _, _⟩ | ⟨_, hRight, _, _⟩
    · exact Or.inr (Or.inl ⟨hPair, hLeft, hRight⟩)
    · exact Or.inl ⟨hPair, Or.inl hLeft⟩
    · exact Or.inl ⟨hPair, Or.inr hRight⟩
  · rcases member_trichotomy incoming hc hab hOne wallStar fullDim with
      ⟨hLeft, hRight, _, _⟩ | ⟨hLeft, _, _, _⟩ | ⟨_, hRight, _, _⟩
    · exact Or.inr (Or.inr ⟨hDivided, hLeft, hRight⟩)
    · exact absurd (W2M1kSelectedCensus.not_dividedData_of_leaf incoming hc hab hOne fullDim
        wallProfile shape (Or.inl hLeft) hDivided.some) not_false
    · exact absurd (W2M1kSelectedCensus.not_dividedData_of_leaf incoming hc hab hOne fullDim
        wallProfile shape (Or.inr hRight) hDivided.some) not_false

end DraismaVargas.LocalCases.W2M1kClosureUnconditional
