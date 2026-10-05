module

public import DraismaVargasCount.UnitWeightBalance
public import DraismaVargas.LocalCases.W4CommonBalance

@[expose] public section

/-!
# Equation (1), the case `{w4}`: the leaf counts, and one index hypothesis

**Source.**  Vargas, Part II, the balancing condition `prop-signed-mult`, part (1);
Draisma–Vargas Part I, Case `{w4}`, Figures 26–27 and **Equation (1)**, whose
determinant identity is formalised as
`DraismaVargas.LocalCases.W4CommonBalance.determinant_balance` and
`canonical_determinant_balance`.

Equation (1) has **three** members and the unit weight vector `![1, 1, 1]`
(`W4CommonBalance.positiveBalance`).  It is the one unit-weight case that
`Count.UnitWeightBalance`'s two-member argument does **not** reach, and the
reason is structural, not a gap in that argument:

* with two members, `new⁽¹⁾ + new⁽²⁾ = c_{p₀} + c_{p₁}` forces the two
  corrections `new⁽¹⁾ - c_{p₁}` and `new⁽²⁾ - c_{p₀}` to be negatives of each
  other, so they merge into `d₀(h)` identically
  (`UnitWeightBalance.lcm_den_eq_of_add_eq_add`);
* with three members and *four* old wall columns
  (`W4CommonBalance.commonMatrix_new_sum`) there is no such pairing, and the
  differences `new⁽ᵠ⁾ - new⁽ᵠ'⁾` are genuine sums of individual reciprocal
  dilation indices `1/|e_α|`
  (`W4OutgoingLimitMatrix.matrix_new`): an `nd2` wall block contributes
  `1/|e_α|` to exactly two of the three pairings
  (`W4OutgoingLimitMatrix.card_separating_pairings`), and an `nd3` block
  contributes its *isolated* branch's term, a different branch for each
  pairing (`W4OutgoingLimitMatrix.blockRegrownRow_nd3`,
  `sourceEdgeIndex_newSourceEdge_regrownSheet`).  If some `|e_α|` fails to
  divide `d₀(h)` then `D⁽ᵠ⁾` really does depend on `q` and
  `Σ_q Mult φ_q ≠ 0`.

So `{w4}` is **not** free on its weights.  What it needs is not the *sharp*
incoming denominators given by the index pattern along rows, but only the
divisibility half below.

## What is proved

* `leafCount_member` -- **unconditional, on the three members
  `W4OutgoingStableRows.member` that `AuxR0SourceInput.presentedFamily`
  builds**: `l(T⁽ᵠ⁾) = l(T₀)` for all three.  Each pairing splits the
  four-valent wall `2 + 2`
  (`W4TargetPairings.FourStar.card_wallEdgesAssigned_false`,
  `W4TargetPairings.FourStar.card_wallEdgesAssigned_true`), so both
  copies of the wall come out trivalent and no leaf moves.  This settles the
  leaf half of Equation (1)'s weight identification outright.
* `newColumn_den_dvd`, `denominatorProduct_eq_incoming` -- given `hIndex`,
  `D⁽ᵠ⁾ = D₀` for every `q`, not merely equality across `q`.
* `sum_signedMult_eq_zero`, `sum_signedMult_canonical_eq_zero` --
  `Σ_q Mult φ_q = 0`, given `hIndex` and nothing else.

## The index hypothesis, stated exactly

Every theorem below that is not unconditional carries the hypothesis

    hIndex : ∀ (pairing : Fin 3) (sourceBlock : WallBlock data wall)
               (path : StablePath data),
      W4OutgoingLimitMatrix.blockRegrownRow input pairing sourceBlock = some path →
        data.sourceEdgeIndex
            (W4OutgoingStableRows.blockOldSourceEdge input pairing sourceBlock) ∣
          Count.TrivalentWeight.incomingRowDenominator data path

i.e. *the dilation index of a regrowing wall block's canonical incoming
occurrence divides the incoming row denominator of the row that occurrence
carries.*  This is the **lower** half of Part II's edge-denominator lemma
`lemma-edge-deno`, case (b)
(`Count.EdgeDenominator.dvd_rowDenominator_of_rowFibre_eq_singleton` in its
rectangular form
`Count.TrivalentWeight.dvd_incomingRowDenominator_of_occurrences_eq_singleton`)
read at the wall branches; it follows at once from a simple-column census
saying that a wall branch occurrence is alone in its (row, star edge) fibre of
the incoming matrix.  It does **not** need the sharp value `d₀ = k`, and it
does **not** need the ordered walk along the row.

## What is NOT proved here

The hypothesis `hIndex` itself; no incoming row denominator is evaluated here.
Nothing is conditional on integrality of the multiplicity, on the genus, on the
degree, or on nonsingularity of any member.

## Consumers

`DraismaVargasCount.W4IncomingIndex` discharges `hIndex` (from connectedness and
genus zero of the target) and instantiates the three conditional theorems below,
completing the balance of Equation (1).
-/

namespace DraismaVargas.Count.W4UnitBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.Count.TrivalentWeight
open DraismaVargas.Count.UnitWeightBalance
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4TargetPairings
open DraismaVargas.LocalCases.W4OutgoingStableRows
open DraismaVargas.LocalCases.W4OutgoingLimitMatrix
open DraismaVargas.LocalCases.W4CommonBalance
open DraismaVargas.LocalCases.StableSourceMatrix
open DraismaVargas.Infrastructure.TargetExpansion

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}
  [DecidableEq target.edges]
  (input : AuxR0SourceInput data star)

/-! ## 1.  The three expanded targets have the leaf count of `T₀` -/

/-- **`l(T⁽ᵠ⁾) = l(T₀)` for all three members, unconditionally.**  A pairing
splits the four old wall occurrences `2 + 2`, so the retained and the fresh
copy of the wall are both trivalent. -/
theorem leafCount_member (pairing : Fin 3) :
    leafCount (graph target wall (member input pairing).right) = leafCount target := by
  refine leafCount_graph_candidate wall (member input pairing) ?_ ?_
  · refine Finset.card_pos.mp ?_
    have h : (wallEdgesAssigned target wall (member input pairing).right false).card = 2 :=
      star.card_wallEdgesAssigned_false pairing
    omega
  · refine Finset.card_pos.mp ?_
    have h : (wallEdgesAssigned target wall (member input pairing).right true).card = 2 :=
      star.card_wallEdgesAssigned_true pairing
    omega

/-! ## 2.  The denominator products, given `hIndex` -/

section Residue

variable (hIndex : ∀ (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (path : StablePath data),
    blockRegrownRow input pairing sourceBlock = some path →
      data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) ∣
        incomingRowDenominator data path)

include hIndex

/-- Each member's regrown entry is already `d₀`-integral: it is a sum of terms
`1/|e_α|` over the blocks that regrow on that row, and each such index divides
the row's incoming denominator. -/
theorem newColumn_den_dvd (pairing : Fin 3) (path : StablePath data) :
    (commonMatrix input pairing path none).den ∣ incomingRowDenominator data path := by
  classical
  have hEq : commonMatrix input pairing path none =
      ∑ sourceBlock ∈ regrowingBlocks input pairing path,
        (1 : ℚ) / data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) :=
    matrix_new input pairing path
  rw [hEq]
  refine den_sum_dvd _ _ fun sourceBlock hBlock ↦ ?_
  exact (den_one_div_natCast _).trans
    (hIndex pairing sourceBlock path
      ((mem_regrowingBlocks input pairing path sourceBlock).mp hBlock))

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling (member input 0).datum coordinate)

/-- **`D⁽ᵠ⁾ = D₀` for every member**, given `hIndex`. -/
theorem denominatorProduct_eq_incoming (pairing : Fin 3) :
    denominatorProduct (labelling input initial pairing).presentation =
      incomingDenominatorProduct data :=
  denominatorProduct_eq_incoming_of_den_dvd _ (sourceCoordinates input initial)
    (targetCoordinates input initial) (commonMatrix input pairing)
    (fun row column ↦ squareMatrix_common input initial pairing row column)
    (commonMatrix_retained input pairing)
    (newColumn_den_dvd input hIndex pairing)

/-- **Part II, `prop-signed-mult` (1), for Equation (1)**, on the three members
that `AuxR0SourceInput.presentedFamily` builds, given `hIndex`. -/
theorem sum_signedMult_eq_zero :
    ∑ pairing : Fin 3,
        signedMult (labelling input initial pairing).presentation = 0 :=
  sum_signedMult_eq_zero_of_uniform _ (incomingDenominatorProduct data)
    (leafCount target) (denominatorProduct_eq_incoming input hIndex initial)
    (fun pairing ↦ leafCount_member input pairing)
    (determinant_balance input initial)

end Square

/-- **The fully instantiated statement**: the three outgoing `{w4}`
candidates, the source input's own coordinate order, and `hIndex` as the
only hypothesis. -/
theorem sum_signedMult_canonical_eq_zero :
    ∑ pairing : Fin 3,
        signedMult (labelling input (canonicalInitialLabelling input)
          pairing).presentation = 0 :=
  sum_signedMult_eq_zero input hIndex _

end Residue

end DraismaVargas.Count.W4UnitBalance
