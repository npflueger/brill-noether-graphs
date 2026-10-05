module

public import DraismaVargasCount.UnitWeightBalance
public import DraismaVargas.LocalCases.W3Nd3CommonBalance

@[expose] public section

/-!
# `prop-signed-mult`(1) for Equation (4): the case `{w3-r1-nd3-t3}`

**Source.**  Vargas, Part II (arXiv:2609.09109), Proposition `prop-signed-mult` (1)
and its proof ("the same cancellation holds for all other trivalent deformation
cases"); Draisma--Vargas Part I (arXiv:1909.12924), case `{w3-r1-nd3-t3}`, Figure 30
and **Equation (4)**, formalized as
`DraismaVargas.LocalCases.W3Nd3CommonBalance.determinant_balance` and
`canonical_determinant_balance`.  Where the prose of this case and Figure 30 differ
(on which value of `α` gives which member), the formalization follows Figure 30.

Equation (4) has **two** members and the unit weight vector `![1, 1]`
(`W3Nd3CommonBalance.positiveBalance`).  By `Count.UnitWeightBalance` a
two-member unit-weight limit needs no incoming row denominator at all: the
crossed column identity `new⁽¹⁾ + new⁽²⁾ = t₃ + t₄`
(`W3Nd3CommonBalance.commonMatrix_new_add`) already forces the two members'
denominator products to agree.

## What is proved, on the family Part I actually constructs

Everything below is stated for `W3Nd3CommonBalance.labelling input profile
hSame initial position`, i.e. for the two honest square labellings of the two
actual Figure 30 members `W3Nd3SourceCandidates.coarseCandidate` and
`fineCandidate`; no abstract family satisfying named hypotheses is used, and
no new structure is introduced.

* `leafCount_coarse`, `leafCount_fine` -- **unconditional**:
  `l(T⁽¹⁾) = l(T⁽²⁾) = l(T₀)`.  Both members split the trivalent wall as
  `1 + 2`, so both copies of the wall stay at valency at least two and no leaf
  is created or destroyed.  This is read off the candidates' own certified
  incidence lists via `M11SourceCandidates.candidate_target_valencies` and
  `W3Nd2SourceCandidates.wallEdgesAssigned_false` / `_true`.
* `denominatorProduct_eq` -- **unconditional**: `D⁽¹⁾ = D⁽²⁾`.
* `denominatorProduct_eq_prod` -- each member's value, row by row:
  `D⁽ᵠ⁾ = ∏_h lcm(den(new⁽ᵠ⁾(h)), d₀(h))`.  It is **not** claimed to be `D₀`.
* `sum_signedMult_eq_zero` -- `Σ_q Mult φ_q = 0` for any supplied square
  coordinate order, and `sum_signedMult_canonical_eq_zero` with no supplied
  labelling at all (`W3Nd3CommonBalance.canonicalInitialLabelling`).

## What is NOT proved

* No value of any incoming row denominator `d₀(h)`, and no claim `D⁽ᵠ⁾ = D₀`;
  only the equality of the two members' denominator products is proved, which
  is all the unit weights need.  In particular **no sharp incoming row
  denominator is used**.
* The hypotheses that remain are exactly those of Equation (4) itself: a
  `ThirdEquation.W3SourceInput`, a `W3R1SourceProfile.Nd3Profile` on its
  distinguished block, and `hSame : profile.first.1.1.1 =
  profile.second.1.1.1` (the doubled direction).  Nothing about integrality,
  the genus, the degree, or nonsingularity of either member enters.

## Consumers

The multiplicity balance at the W3 nd3 walls (Equation (4)), an input of the star
parity in step 2 of `Assembly`.
-/

namespace DraismaVargas.Count.W3Nd3UnitBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.Count.TrivalentWeight
open DraismaVargas.Count.UnitWeightBalance
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ThirdEquation
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.W3Nd3SourceCandidates
open DraismaVargas.LocalCases.W3Nd3CommonBalance
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableSourceMatrix
open DraismaVargas.LocalCases.W3Nd2SourceCandidates
  (rightOf wallEdgesAssigned_false wallEdgesAssigned_true)
open DraismaVargas.Infrastructure.TargetExpansion

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)

/-! ## 1.  The two expanded targets have the leaf count of `T₀` -/

/-- `M⁽¹⁾` keeps the doubled direction `t₃` on the retained copy of the wall
and the other two on the fresh one, so both copies are at least divalent. -/
theorem leafCount_coarse :
    leafCount (graph target wall (coarseCandidate input profile hSame).right) =
      leafCount target := by
  refine leafCount_graph_candidate wall (coarseCandidate input profile hSame) ?_ ?_
  · have h : wallEdgesAssigned target wall
        (coarseCandidate input profile hSame).right false =
          {profile.first.1.1.1} :=
      wallEdgesAssigned_false (orientedStar input profile)
    rw [h]
    exact ⟨profile.first.1.1.1, Finset.mem_singleton_self _⟩
  · have h : wallEdgesAssigned target wall
        (coarseCandidate input profile hSame).right true =
          {(orientedStar input profile).rightFirst,
            (orientedStar input profile).rightSecond} :=
      wallEdgesAssigned_true (orientedStar input profile)
    rw [h]
    exact ⟨_, Finset.mem_insert_self _ _⟩

/-- `M⁽²⁾` keeps the largest direction `t₄` on the retained copy of the wall
and the other two on the fresh one. -/
theorem leafCount_fine :
    leafCount (graph target wall (fineCandidate input profile hSame).right) =
      leafCount target := by
  refine leafCount_graph_candidate wall (fineCandidate input profile hSame) ?_ ?_
  · have h : wallEdgesAssigned target wall
        (fineCandidate input profile hSame).right false =
          {largestTarget input profile} :=
      wallEdgesAssigned_false (fineOrientation input profile)
    rw [h]
    exact ⟨largestTarget input profile, Finset.mem_singleton_self _⟩
  · have h : wallEdgesAssigned target wall
        (fineCandidate input profile hSame).right true =
          {(fineOrientation input profile).rightFirst,
            (fineOrientation input profile).rightSecond} :=
      wallEdgesAssigned_true (fineOrientation input profile)
    rw [h]
    exact ⟨_, Finset.mem_insert_self _ _⟩

/-- `l(T⁽¹⁾) = l(T⁽²⁾)`, which is what the unit weights need. -/
theorem leafCount_members_eq :
    leafCount (graph target wall (members input profile hSame 0).right) =
      leafCount (graph target wall (members input profile hSame 1).right) := by
  show leafCount (graph target wall (coarseCandidate input profile hSame).right) =
    leafCount (graph target wall (fineCandidate input profile hSame).right)
  rw [leafCount_coarse, leafCount_fine]

/-! ## 2.  The two denominator products agree -/

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling
    (members input profile hSame 0).datum coordinate)

/-- Each member's denominator product, row by row: the incoming row
denominator merged with the denominator of that member's single regrown
entry.  No incoming denominator is evaluated. -/
theorem denominatorProduct_eq_prod (position : Fin 2) :
    denominatorProduct (labelling input profile hSame initial position).presentation =
      ∏ path : StablePath data,
        Nat.lcm (commonMatrix input profile hSame position path none).den
          (incomingRowDenominator data path) :=
  denominatorProduct_of_commonMatrix _ (sourceCoordinates input profile hSame initial)
    (targetCoordinates input profile hSame initial)
    (commonMatrix input profile hSame position)
    (fun row column ↦ squareMatrix_common input profile hSame initial position row column)
    (commonMatrix_retained input profile hSame position)

/-- **`D⁽¹⁾ = D⁽²⁾`, unconditionally.**  Equation (4)'s crossed column identity
is exactly the hypothesis of `UnitWeightBalance.lcm_den_eq_of_add_eq_add`. -/
theorem denominatorProduct_eq :
    denominatorProduct (labelling input profile hSame initial 0).presentation =
      denominatorProduct (labelling input profile hSame initial 1).presentation :=
  denominatorProduct_eq_of_columns_add _ _
    (sourceCoordinates input profile hSame initial)
    (targetCoordinates input profile hSame initial)
    (commonMatrix input profile hSame 0) (commonMatrix input profile hSame 1)
    (fun row column ↦ squareMatrix_common input profile hSame initial 0 row column)
    (fun row column ↦ squareMatrix_common input profile hSame initial 1 row column)
    (commonMatrix_retained input profile hSame 0)
    (commonMatrix_retained input profile hSame 1)
    profile.first.1.1.1 (largestTarget input profile)
    (commonMatrix_new_add input profile hSame)

/-! ## 3.  The balance -/

/-- **`prop-signed-mult`(1) for Equation (4)**, on the two members Part I's
Figure 30 lemma actually constructs.  The only hypotheses are those of
Equation (4) itself. -/
theorem sum_signedMult_eq_zero :
    ∑ position : Fin 2,
        signedMult (labelling input profile hSame initial position).presentation = 0 := by
  rw [Fin.sum_univ_two]
  exact signedMult_add_eq_zero _ _ (denominatorProduct_eq input profile hSame initial)
    (leafCount_members_eq input profile hSame)
    (determinant_balance input profile hSame initial)

end Square

/-! ## 4.  The same with no supplied square labelling -/

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- **The fully instantiated statement**: the family
`W3Nd3SourceCandidates.coarseCandidate` / `fineCandidate`, the canonical
coordinate order supplied by the W3 source census itself, and no hypothesis
beyond Equation (4)'s own. -/
theorem sum_signedMult_canonical_eq_zero :
    ∑ position : Fin 2,
        signedMult (labelling input profile hSame
          (canonicalInitialLabelling input profile hSame) position).presentation = 0 :=
  sum_signedMult_eq_zero input profile hSame _

end DraismaVargas.Count.W3Nd3UnitBalance
