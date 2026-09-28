import DraismaVargasCount.UnitWeightBalance
import DraismaVargas.LocalCases.W3Nd2CommonBalance

/-!
# `prop-signed-mult`(1) for Equation (5): the case `{w3-r1-nd2}`

**Source.**  Vargas, Part II (arXiv:2609.09109), Proposition `prop-signed-mult` (1) and its
proof; Draisma--Vargas Part I (arXiv:1909.12924), case `{w3-r1-nd2}`, Figure 31 and
**Equation (5)**, formalized as
`DraismaVargas.LocalCases.W3Nd2CommonBalance.determinant_balance` and
`canonical_determinant_balance`.

Equation (5) has **two** members and the unit weight vector `![1, 1]`
(`W3Nd2CommonBalance.positiveBalance`), so `Count.UnitWeightBalance` applies
verbatim: the column identity `new⁽¹⁾ + new⁽²⁾ = t_small + t_large`
(`W3Nd2CommonBalance.commonMatrix_new_add`) forces the two denominator
products to agree, with no incoming row denominator evaluated.

For the record, the two members' regrown columns really are the old ones
perturbed in a single shared row: with `k = blockCard` of the distinguished
block, `Nd2Profile.small_index` and `large_index` give
`|e_small| = k - 1` and `|e_large| = k`, and `profile.stablePath_eq` puts both
selected occurrences on the same stable row `h`; so the coarse regrown column
is the old small column plus `1/k - 1/(k-1)` at `h`, the fine one is the old
large column plus `1/(k-1) - 1/k` at `h`, and the two corrections are
negatives of each other.  The proof below does not need to name any of that:
`UnitWeightBalance.lcm_den_eq_of_add_eq_add` extracts exactly this
cancellation from the column identity alone.

## What is proved, on the family Part I actually constructs

Stated for `W3Nd2CommonBalance.labelling input profile initial position`, the
two honest square labellings of `W3Nd2SourceCandidates.coarseCandidate` and
`W3Nd2FineCandidates.fineCandidate`.  No abstract family, no new structure.

* `leafCount_coarse`, `leafCount_fine` -- **unconditional**:
  `l(T⁽¹⁾) = l(T⁽²⁾) = l(T₀)`; both members split the trivalent wall `1 + 2`.
* `denominatorProduct_eq_prod`, `denominatorProduct_eq` -- **unconditional**:
  `D⁽ᵠ⁾ = ∏_h lcm(den(new⁽ᵠ⁾(h)), d₀(h))` and `D⁽¹⁾ = D⁽²⁾`.  It is **not**
  claimed that either equals `D₀`.
* `sum_signedMult_eq_zero`, `sum_signedMult_canonical_eq_zero` --
  `Σ_q Mult φ_q = 0`, in the second case with no supplied labelling.

## What is NOT proved

No value of any incoming row denominator: **no sharp incoming-row denominator is used**.  The
remaining hypotheses are exactly Equation (5)'s: a
`ThirdEquation.W3SourceInput` and a `W3R1SourceProfile.Nd2Profile` on its
distinguished block.  Nothing about integrality, the genus, the degree, or
nonsingularity of either member enters.

## Consumers

`W3Nd2StarCensusProof` and `RegrowthWallInput.exists_w3Nd2_balance` (Equation (5) at every
regrowth tagged `w3Nd2CoarseFine`), part of the multiplicity input of the star parity in
step 2 (trivalent walls) of `DraismaVargasCount/Assembly.lean`.
-/

namespace DraismaVargas.Count.W3Nd2UnitBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.Count.TrivalentWeight
open DraismaVargas.Count.UnitWeightBalance
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.W3Nd2SourceCandidates
open DraismaVargas.LocalCases.W3Nd2FineRefinement
open DraismaVargas.LocalCases.W3Nd2FineCandidates
open DraismaVargas.LocalCases.W3Nd2CommonBalance
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableSourceMatrix
open DraismaVargas.Infrastructure.TargetExpansion

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)

/-! ## 1.  The two expanded targets have the leaf count of `T₀` -/

/-- `M⁽¹⁾` keeps the small direction on the retained copy of the wall. -/
theorem leafCount_coarse :
    leafCount (graph target wall (coarseCandidate input profile).right) =
      leafCount target := by
  refine leafCount_graph_candidate wall (coarseCandidate input profile) ?_ ?_
  · have h : wallEdgesAssigned target wall
        (coarseCandidate input profile).right false = {profile.small.1.1.1} :=
      wallEdgesAssigned_false (orientedStar input profile)
    rw [h]
    exact ⟨profile.small.1.1.1, Finset.mem_singleton_self _⟩
  · have h : wallEdgesAssigned target wall
        (coarseCandidate input profile).right true =
          {(orientedStar input profile).rightFirst,
            (orientedStar input profile).rightSecond} :=
      wallEdgesAssigned_true (orientedStar input profile)
    rw [h]
    exact ⟨_, Finset.mem_insert_self _ _⟩

/-- `M⁽²⁾` keeps the large direction on the retained copy of the wall. -/
theorem leafCount_fine :
    leafCount (graph target wall (fineCandidate input profile).right) =
      leafCount target := by
  refine leafCount_graph_candidate wall (fineCandidate input profile) ?_ ?_
  · have h : wallEdgesAssigned target wall
        (fineCandidate input profile).right false = {largeTarget input profile} :=
      wallEdgesAssigned_false (fineOrientation input profile)
    rw [h]
    exact ⟨largeTarget input profile, Finset.mem_singleton_self _⟩
  · have h : wallEdgesAssigned target wall
        (fineCandidate input profile).right true =
          {(fineOrientation input profile).rightFirst,
            (fineOrientation input profile).rightSecond} :=
      wallEdgesAssigned_true (fineOrientation input profile)
    rw [h]
    exact ⟨_, Finset.mem_insert_self _ _⟩

/-- `l(T⁽¹⁾) = l(T⁽²⁾)`. -/
theorem leafCount_candidates_eq :
    leafCount (candidates input profile 0).outgoingTarget =
      leafCount (candidates input profile 1).outgoingTarget := by
  show leafCount (graph target wall (coarseCandidate input profile).right) =
    leafCount (graph target wall (fineCandidate input profile).right)
  rw [leafCount_coarse, leafCount_fine]

/-! ## 2.  The two denominator products agree -/

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling (candidates input profile 0).datum coordinate)

/-- Each member's denominator product, row by row. -/
theorem denominatorProduct_eq_prod (position : Fin 2) :
    denominatorProduct (labelling input profile initial position).presentation =
      ∏ path : StablePath data,
        Nat.lcm (commonMatrix input profile position path none).den
          (incomingRowDenominator data path) :=
  denominatorProduct_of_commonMatrix _ (sourceCoordinates input profile initial)
    (targetCoordinates input profile initial) (commonMatrix input profile position)
    (fun row column ↦ squareMatrix_common input profile initial position row column)
    (commonMatrix_retained input profile position)

/-- **`D⁽¹⁾ = D⁽²⁾`, unconditionally.** -/
theorem denominatorProduct_eq :
    denominatorProduct (labelling input profile initial 0).presentation =
      denominatorProduct (labelling input profile initial 1).presentation :=
  denominatorProduct_eq_of_columns_add _ _ (sourceCoordinates input profile initial)
    (targetCoordinates input profile initial)
    (commonMatrix input profile 0) (commonMatrix input profile 1)
    (fun row column ↦ squareMatrix_common input profile initial 0 row column)
    (fun row column ↦ squareMatrix_common input profile initial 1 row column)
    (commonMatrix_retained input profile 0) (commonMatrix_retained input profile 1)
    (smallTarget input profile) (largeTarget input profile)
    (commonMatrix_new_add input profile)

/-! ## 3.  The balance -/

/-- **`prop-signed-mult`(1) for Equation (5)**, on the two members Part I's
Figure 31 lemma actually constructs. -/
theorem sum_signedMult_eq_zero :
    ∑ position : Fin 2,
        signedMult (labelling input profile initial position).presentation = 0 := by
  rw [Fin.sum_univ_two]
  exact signedMult_add_eq_zero _ _ (denominatorProduct_eq input profile initial)
    (leafCount_candidates_eq input profile)
    (determinant_balance input profile initial)

end Square

/-! ## 4.  The same with no supplied square labelling -/

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- **The fully instantiated statement**, with the canonical coordinate order
supplied by the W3 source census itself. -/
theorem sum_signedMult_canonical_eq_zero :
    ∑ position : Fin 2,
        signedMult (labelling input profile
          (canonicalInitialLabelling input profile) position).presentation = 0 :=
  sum_signedMult_eq_zero input profile _

end DraismaVargas.Count.W3Nd2UnitBalance
