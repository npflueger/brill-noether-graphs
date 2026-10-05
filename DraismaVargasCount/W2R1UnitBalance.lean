module

public import DraismaVargasCount.UnitWeightBalance
public import DraismaVargas.LocalCases.W2R1LimitMatrix

@[expose] public section

/-!
# `prop-signed-mult`(1) for Equation (10): the case `{w2-r1}`

**Source.**  Vargas, Part II (arXiv:2609.09109), Proposition `prop-signed-mult` (1) and its
proof; Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r1}`, sub-cases `{w2-r1-nd3}`
(Figure 37) and `{w2-r1-nd2}` (Figure 38), **Equation (10)**, formalized as
`DraismaVargas.LocalCases.W2R1CommonBalance.LimitColumns.determinant_balance`
and `canonical_determinant_balance`, over the receipt
`W2R1CommonBalance.LimitColumns`, which
`W2R1LimitMatrix.limitColumns` inhabits on every `{w2-r1}` datum.

Equation (10) has **two** members, and its weights are *derived* rather than
posited (`W2R1CommonBalance.equation_ten_weights_normalized`): they are
`![1, 1]`.  So `Count.UnitWeightBalance` applies: the column identity
`c⁽¹⁾ + c⁽²⁾ = σ₀(2) + σ₀(3)`
(`W2R1CommonBalance.LimitColumns.weighted_column_balance`, i.e.
`W2R1LimitMatrix.equation_ten`) already forces the two denominator products to
agree.

**The `thirdRow = secondRow` caveat does not arise.**  In the `nd2` sub-case
`W2R1CommonBalance.nd2_thirdRow_eq_secondRow` makes the two members perturb
the *same* incoming stable row.  The argument below never names a row of the
perturbation: `UnitWeightBalance.lcm_den_eq_of_add_eq_add` is applied to each
incoming stable row separately, and at each row it consumes only the two-term
column identity at that row.  Whether the two perturbations sit on one row or
on two is therefore invisible to it, and no case split on `nd2` versus `nd3`
is needed anywhere in this module.

## What is proved, on the family Part I actually constructs

Stated for `W2R1CommonBalance.LimitColumns.labelling limit initial position`
with `limit = W2R1LimitMatrix.limitColumns pair hValid`, i.e. for the two
honest square labellings of the two actual members
`W2R1SourceCandidates.Pair.candidate`.  No abstract family, no new structure.

* `leafCount_candidate` -- **unconditional**: `l(T⁽ᵠ⁾) = l(T₀)` for both
  members, from `W2R1SourceCandidates.Pair.candidate_target_valencies`
  (both expand the divalent wall into the divalent/divalent `T₂`) and
  `TrivalentWeight.leafCount_graph_of_divalent_split`.  Both members in fact
  carry the *same* expansion `star.right`, so `leafCount_members_eq` is
  immediate.
* `denominatorProduct_eq_prod`, `denominatorProduct_eq` -- **unconditional**:
  `D⁽ᵠ⁾ = ∏_h lcm(den(c⁽ᵠ⁾(h)), d₀(h))` and `D⁽¹⁾ = D⁽²⁾`.  Neither is claimed
  to equal `D₀`.
* `sum_signedMult_eq_zero` -- `Σ_q Mult φ_q = 0` over any `LimitColumns`
  inhabitant and any supplied coordinate order;
  `sum_signedMult_limitColumns_eq_zero` on the inhabitant
  `W2R1LimitMatrix.limitColumns`; and `sum_signedMult_canonical_eq_zero` with
  no supplied labelling, using the census-supplied canonical order.

## What is NOT proved

No value of any incoming row denominator: **no sharp incoming-row denominator is used**.  The
remaining hypotheses are exactly Equation (10)'s: a
`W2R1SourceCandidates.Pair` and `data.Valid` (packaged as a
`SecondEquation.W2SourceInput` in the canonical statement).  Nothing about
integrality, the genus, the degree, or nonsingularity of either member enters.

## Consumers

`RegrowthWallInput.exists_w2R1_balance` (Equation (10) at every regrowth tagged `w2R1`), part
of the multiplicity input of the star parity in step 2 (trivalent walls) of
`DraismaVargasCount/Assembly.lean`.
-/

namespace DraismaVargas.Count.W2R1UnitBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.Count.TrivalentWeight
open DraismaVargas.Count.UnitWeightBalance
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2R1SourceCandidates
open DraismaVargas.LocalCases.W2R1CommonBalance
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableSourceMatrix
open DraismaVargas.Infrastructure.TargetExpansion

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

variable (pair : Pair data star)

/-! ## 1.  Both members expand the divalent wall into `T₂` -/

/-- **`l(T⁽ᵠ⁾) = l(T₀)`**: both copies of the wall stay divalent. -/
theorem leafCount_candidate (position : Fin 2) :
    leafCount (graph target wall (pair.candidate position).right) = leafCount target :=
  leafCount_graph_of_divalent_split wall _
    (pair.candidate_target_valencies position).1
    (pair.candidate_target_valencies position).2

theorem leafCount_members_eq :
    leafCount (graph target wall (pair.candidate 0).right) =
      leafCount (graph target wall (pair.candidate 1).right) := by
  rw [leafCount_candidate, leafCount_candidate]

/-! ## 2.  The column identity, with the unit weights cleared -/

/-- Equation (10) at column level with the `1 *` factors removed: this is the
exact shape `UnitWeightBalance.denominatorProduct_eq_of_columns_add`
consumes. -/
theorem commonMatrix_new_add {pair : Pair data star} (limit : LimitColumns pair)
    (hValid : data.Valid) (path : StablePath data) :
    limit.commonMatrix 0 path none + limit.commonMatrix 1 path none =
      matrix data path (star.edge 0) + matrix data path (star.edge 1) := by
  simpa using limit.weighted_column_balance hValid path

/-! ## 3.  The two denominator products agree, and the balance -/

section Square

variable {pair}
variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (limit : LimitColumns pair)
  (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)

/-- Each member's denominator product, row by row. -/
theorem denominatorProduct_eq_prod (position : Fin 2) :
    denominatorProduct (limit.labelling initial position).presentation =
      ∏ path : StablePath data,
        Nat.lcm (limit.commonMatrix position path none).den
          (incomingRowDenominator data path) :=
  denominatorProduct_of_commonMatrix _ (limit.sourceCoordinates initial)
    (LimitColumns.targetCoordinates initial) (limit.commonMatrix position)
    (fun row column ↦ limit.squareMatrix_common initial position row column)
    (limit.commonMatrix_retained position)

/-- **`D⁽¹⁾ = D⁽²⁾`, unconditionally.**  No incoming row denominator is
evaluated, and no row of either perturbation is named. -/
theorem denominatorProduct_eq (hValid : data.Valid) :
    denominatorProduct (limit.labelling initial 0).presentation =
      denominatorProduct (limit.labelling initial 1).presentation :=
  denominatorProduct_eq_of_columns_add _ _ (limit.sourceCoordinates initial)
    (LimitColumns.targetCoordinates initial)
    (limit.commonMatrix 0) (limit.commonMatrix 1)
    (fun row column ↦ limit.squareMatrix_common initial 0 row column)
    (fun row column ↦ limit.squareMatrix_common initial 1 row column)
    (limit.commonMatrix_retained 0) (limit.commonMatrix_retained 1)
    (star.edge 0) (star.edge 1) (commonMatrix_new_add limit hValid)

/-- **`prop-signed-mult`(1) for Equation (10)**, over any inhabitant of the
limit-matrix receipt and any supplied coordinate order. -/
theorem sum_signedMult_eq_zero (hValid : data.Valid) :
    ∑ position : Fin 2,
        signedMult (limit.labelling initial position).presentation = 0 := by
  rw [Fin.sum_univ_two]
  refine signedMult_add_eq_zero _ _ (denominatorProduct_eq limit initial hValid)
    (leafCount_members_eq pair) ?_
  have hDet := limit.determinant_balance hValid initial
  rw [one_mul, one_mul] at hDet
  exact hDet

end Square

/-! ## 4.  On the inhabitant Part I builds, and with no supplied labelling -/

section Constructed

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (hValid : data.Valid)

/-- The same on `W2R1LimitMatrix.limitColumns`, the inhabitant every actual
`{w2-r1}` datum supplies. -/
theorem sum_signedMult_limitColumns_eq_zero
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    ∑ position : Fin 2,
        signedMult ((W2R1LimitMatrix.limitColumns pair hValid).labelling
          initial position).presentation = 0 :=
  sum_signedMult_eq_zero _ initial hValid

end Constructed

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- **The fully instantiated statement**: the two members
`W2R1SourceCandidates.Pair.candidate`, the limit-matrix receipt Part I's
`{w2-r1}` lemma actually builds, and the canonical coordinate order supplied
by the W2 source census itself. -/
theorem sum_signedMult_canonical_eq_zero (input : W2SourceInput data star) :
    ∑ position : Fin 2,
        signedMult ((W2R1LimitMatrix.limitColumns pair input.valid).labelling
          ((W2R1LimitMatrix.limitColumns pair input.valid).canonicalInitialLabelling input)
          position).presentation = 0 :=
  sum_signedMult_limitColumns_eq_zero pair input.valid _

end DraismaVargas.Count.W2R1UnitBalance
