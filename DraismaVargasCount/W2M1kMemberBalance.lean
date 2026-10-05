module

public import DraismaVargasCount.OutgoingRowCalculus
public import DraismaVargas.LocalCases.W2M1kGaugeFamily

@[expose] public section

/-!
# `{w2-r2-nd3-M-1k}`: the member rows of `M⁽²⁾` and `M⁽³⁾`, and why `c⁽q⁾ ≠ 0` costs nothing

**Source.**  Vargas, Part II (arXiv:2609.09109), the proof of `prop-signed-mult` (1), and in
particular its parenthesis **"whenever `c⁽q⁾ ≠ 0`"**.  Draisma--Vargas Part I
(arXiv:1909.12924), Figure 33 and Equation (7).  Equation (7) is read here with the factor `2`
on both of its brackets, as in Equation (6); Part I's display carries it on the first bracket
only.  Both brackets vanish, so the conclusion is the same, and
`W2M1kCommonBalance.figure33_column_identity` proves the identity in this form.

`Count.OutgoingRowCalculus` proves the member's row calculus (`RowRamificationAtMostOne` and
`RowAtMostOneTransition` on its stable rows) on the outgoing-candidate interface, gated on
that member's own `det ≠ 0`.  This file applies it at `{w2-r2-nd3-M-1k}`: it names the two
perturbed member rows concretely, and it shows the gate costs nothing.

## Why the gate costs nothing: the four-case split

`W2M1kCommonBalance.LimitColumns.determinant_balance` is **unconditional**:

  `1·d⁽¹⁾ + 2(k-1)·d⁽²⁾ + 2(k+1)·d⁽³⁾ = 0`,

and so is `Count.TrivalentWeight.denominatorProduct_zero`, `D⁽¹⁾ = D₀`.  The two
denominator hypotheses enter only through `denominatorProduct_one`
(`D⁽²⁾ = (k-1)D₀`) and `denominatorProduct_two` (`D⁽³⁾ = (k+1)D₀`), and each is
multiplied by its own determinant in `Σ_q Mult φ_q`.  Splitting on `d⁽²⁾ = 0`
and `d⁽³⁾ = 0`:

* `d⁽²⁾ ≠ 0`, `d⁽³⁾ ≠ 0` -- both denominators are available and the identity is
  `Count.TrivalentWeight.sum_signedMult_eq_zero` as it stands;
* `d⁽²⁾ = 0`, `d⁽³⁾ ≠ 0` -- `M⁽²⁾`'s term vanishes whatever `D⁽²⁾` is, the
  balance reads `d⁽¹⁾ = -2(k+1)d⁽³⁾`, and `D₀/2^{l₀+1}·d⁽¹⁾` cancels
  `(k+1)D₀/2^{l₀}·d⁽³⁾` exactly;
* `d⁽²⁾ ≠ 0`, `d⁽³⁾ = 0` -- symmetrically, with `(k-1)` in place of `(k+1)`;
* `d⁽²⁾ = d⁽³⁾ = 0` -- the balance forces `d⁽¹⁾ = 0` and all three terms vanish,
  with **no** denominator evaluated at all.

The split is exhaustive -- two `by_cases` on decidable equalities of rationals --
and in each branch only the denominators of the members that actually contribute
are used.  That is exactly what the parenthesis "whenever `c⁽q⁾ ≠ 0`" in the proof of
`prop-signed-mult` (1) asserts, and it is why `prop-signed-mult` (1) holds without an
unconditional sharp denominator.

## What is proved

* `forall_index_dvd_secondRow_of_regrowth_of_fullDim`,
  `forall_index_dvd_thirdRow_of_regrowth_of_fullDim`,
  `incomingRowDenominator_secondRow_eq_of_regrowth_of_fullDim`,
  `incomingRowDenominator_thirdRow_eq_of_regrowth_of_fullDim` (§1) --
  `Count.RowRegrowth`'s §4 with receipt 1 (`RowRamificationAtMostOne member`,
  `RowAtMostOneTransition member`) discharged.  The partner's index is `k` and
  `Shape.one_lt_k` is `1 < k`, so the ramified-occurrence witness
  `Count.OutgoingRowCalculus` needs is free.
* `sum_signedMult_expand` (§2) -- the three signed multiplicities in one
  expression, with `D⁽¹⁾ = D₀` and the three leaf counts substituted.
  Unconditional.
* `sum_signedMult_eq_zero_of_conditional` (§2) -- **the four-case dichotomy** on
  an arbitrary `W2M1kCommonBalance.LimitColumns` receipt: the two sharp incoming
  denominators are needed only as implications *from the corresponding member's
  own determinant being nonzero*.
* `sum_signedMult_eq_zero_of_regrowth` (§3) -- the two composed: `Σ_q Mult φ_q = 0`
  with no denominator hypothesis anywhere, only the member-side regrowth data,
  and that only on the members whose determinant is nonzero.
* `limitDictionary`, `limitMemberGenus`, `memberPresentation` (§4) -- the
  `dite`-level form of `W2M1kGaugeFamily`'s two orientation dictionaries, and
  with them a `FullDimensionalSourcePresentation` for **any** position of
  `W2M1kLimitColumns.limitColumns`, gated on that position's own
  `LimitColumns.squareMatrix` determinant.
* `rowCalculus_member` (§4) -- **the member row calculus on Figure 33's members**:
  `RowRamificationAtMostOne` and `RowAtMostOneTransition` for a row of
  `M⁽²⁾` (position `1`) or `M⁽³⁾` (position `2`) carrying an occurrence of
  dilation index `≠ 1`.  Beyond `c⁽q⁾ ≠ 0` the only input is `incomingFD`, a
  full-dimensional presentation at *some* position -- the incoming chart,
  which `A04M1kWiring` already takes as a parameter.
* `rowCalculus_dividedCandidate_secondRow`,
  `rowCalculus_joinedCandidate_thirdRow` (§4) -- **the two perturbed member rows
  named**, at candidate level and with the ramified-occurrence witness supplied:
  the stable row of `e₂` in Base II.2.2.M's candidate and of `e₃` in Base
  II.1.M's, whose retained copies have index `k` by `Shape.second_index` /
  `Shape.third_index`.  These are the statements the transition siting of
  `W2M1kTransitionSiting` consumes.
* `sum_signedMult_canonical_eq_zero_of_conditional_index` (§4) -- the balance
  `Σ_q Mult φ_q = 0` of `prop-signed-mult` (1) on the canonical labelling of the family
  `W2M1kLimitColumns.limitColumns` actually builds, with `Count.IncomingSimpleColumn`'s
  row-distinctness hypothesis discharged through
  `Count.RowGeodesic.secondRow_ne_thirdRow_of_genusZero` and the two upper
  halves asked for only where the member contributes.

## What is not proved here: the hypotheses that remain explicit

* **`hTransport`** -- an index-preserving map from the
  incoming row's occurrences into the member's row occurrences other than the
  regrown one.  It is proved on the constructed members in `W2M1kRowTransport`
  (`transport_divided_secondRow`, `transport_joined_thirdRow`, and `transport_of_gauge` over
  a branch-swapped datum).
* **The siting of the regrown transition on each member** -- `hTransition`,
  `hRegrownSurvives`, `hRegrownIncident`, `hPartnerSurvives`,
  `hPartnerIncident`, `hPartnerNe`, `hTerminal`, `hPartnerIndex`.  These are
  `Count.RowRegrowth`'s own hypotheses, carried unchanged; nothing here weakens
  them.  The census facts that inhabit them at Figure 33's members are named in
  `Count.RowRegrowth`'s module docstring
  (`W2M1kStableGraph.divided_nonDanglingValency_pair`,
  `divided_new_third_stablePath_eq`, `divided_nonDanglingValency_branch`;
  `joined_nonDanglingValency_single`, `joined_new_stablePath_eq_third`,
  `joined_nonDanglingValency_double`); assembling them into the bundle -- in
  particular producing `localRamification = 1` at the regrown endpoint -- is done in
  `W2M1kTransitionSiting`, not here.
* **`incomingFD`** -- a full-dimensional presentation at one position of the
  family.  It is the incoming chart, and it is a parameter of
  `A04M1kWiring.m1kAlignedSupply` / `m1kSeparatedSupply` for the same reason.
* **`RowRamificationAtMostOne data (secondRow profile)`** on the *incoming*
  datum, consumed by `Count.RowGeodesic.secondRow_ne_thirdRow_of_genusZero`.  It
  is already explicit in
  `RowGeodesic.sum_signedMult_canonical_eq_zero_of_genusZero`; the
  codimension-one incoming datum carries no `FullDimensionalSourcePresentation`,
  so it cannot be derived the way the members' is.
* **`c⁽q⁾ ≠ 0` itself** is never proved -- it is *dispensed with*, by §2.
* Nothing here is conditional on integrality, on `D_q = D₀` (false in general),
  or on any sharp denominator not listed above.

## Non-vacuity

No structure is introduced.  Every statement is about the actual
`W2R2SourceProfile.SourceProfile` and `W2M1kSourceCandidates.Shape` of the case
and about `W2M1kLimitColumns.limitColumns`, which
`W2M1kLimitColumns.nonempty_limitColumns` inhabits unconditionally in both
orientations.  §5 records the degenerate branch of the dichotomy as an
`example`: when both perturbing members are singular the conclusion holds with
both implications supplied vacuously, so the four-case theorem has a branch that
needs nothing at all.

## Consumers

`W2M1kTransitionSiting` and `W2M1kCountBalance` (the balance on the constructed family), and
through `W2M1kIncomingTame` and `RegrowthBalances` the multiplicity input of the star parity in
step 2 (trivalent walls) of `DraismaVargasCount/Assembly.lean`.  The four-case argument of §2
applies verbatim to the other trivalent-limit balances whose denominators are conditional,
given their own analogue of `LimitColumns`.
-/

namespace DraismaVargas.Count.W2M1kMemberBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Count
open DraismaVargas.Count.TrivalentWeight
open DraismaVargas.Count.RowWalk
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W2M1kCommonBalance
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.StableSourceMatrix
open DraismaVargas.LocalCases.W2M1kSourceCandidates
open DraismaVargas.Infrastructure.TargetExpansion

/-! ## 1.  The two index halves, with the member's row calculus discharged -/

section IndexHalves

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {memberTarget : CFGraph.{0}} {memberDegree : ℕ}
  {member : GluingDatum memberTarget memberDegree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The upper half on `h₂`, from `M⁽²⁾`'s regrown transition, with the
member's row calculus discharged.**  This is
`Count.RowRegrowth.forall_index_dvd_secondRow_of_regrowth` without `hNoGlue`,
`hEnds`, `hTame` and `hOne`: the presentation supplies the first two, and
`hPartnerIndex` together with `Shape.one_lt_k` supplies the ramified occurrence
the last two need. -/
theorem forall_index_dvd_secondRow_of_regrowth_of_fullDim
    {profile : W2R2SourceProfile.SourceProfile data star block} (shape : Shape profile)
    (memberFD : FullDimensionalSourcePresentation member coordinate)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    (hPartnerIndex : member.sourceEdgeIndex partner = shape.k)
    (hTransport : ∀ edge ∈ incomingRowEdges data (secondRow profile),
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ incomingRowEdges data (secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k :=
  OutgoingRowCalculus.forall_index_dvd_of_transport_of_fullDim memberFD hTransition
    hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe
    hTerminal hPartnerIndex (by have := shape.one_lt_k; omega) hTransport

/-- **The upper half on `h₃`, from `M⁽³⁾`'s regrown transition.** -/
theorem forall_index_dvd_thirdRow_of_regrowth_of_fullDim
    {profile : W2R2SourceProfile.SourceProfile data star block} (shape : Shape profile)
    (memberFD : FullDimensionalSourcePresentation member coordinate)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    (hPartnerIndex : member.sourceEdgeIndex partner = shape.k)
    (hTransport : ∀ edge ∈ incomingRowEdges data (thirdRow profile),
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∀ edge ∈ incomingRowEdges data (thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k :=
  OutgoingRowCalculus.forall_index_dvd_of_transport_of_fullDim memberFD hTransition
    hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe
    hTerminal hPartnerIndex (by have := shape.one_lt_k; omega) hTransport

/-- **The sharp `d₀(h₂) = k`** with the member's row calculus discharged: the
upper half from `M⁽²⁾`'s regrown transition, the lower half from the column difference
of `Count.IncomingSimpleColumn`.  `hRows` is `Count.IncomingSimpleColumn`'s own
row-distinctness hypothesis and is kept. -/
theorem incomingRowDenominator_secondRow_eq_of_regrowth_of_fullDim
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (input : W2SourceInput data star) (shape : Shape profile)
    (hRows : secondRow profile ≠ thirdRow profile)
    (memberFD : FullDimensionalSourcePresentation member coordinate)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    (hPartnerIndex : member.sourceEdgeIndex partner = shape.k)
    (hTransport : ∀ edge ∈ incomingRowEdges data (secondRow profile),
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    incomingRowDenominator data (secondRow profile) = shape.k :=
  IncomingSimpleColumn.incomingRowDenominator_secondRow_eq_of_index profile input shape hRows
    (forall_index_dvd_secondRow_of_regrowth_of_fullDim shape memberFD hTransition
      hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe
      hTerminal hPartnerIndex hTransport)

/-- **The sharp `d₀(h₃) = k`** with the member's row calculus discharged. -/
theorem incomingRowDenominator_thirdRow_eq_of_regrowth_of_fullDim
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (input : W2SourceInput data star) (shape : Shape profile)
    (hRows : secondRow profile ≠ thirdRow profile)
    (memberFD : FullDimensionalSourcePresentation member coordinate)
    {memberRow : StablePath member} {regrown partner : member.SourceEdge}
    {vertex : member.SourceVertex}
    (hTransition : IsRowTransition member memberRow vertex)
    (hRegrownSurvives : ¬ IsDangling member regrown)
    (hRegrownIncident : Incident member regrown vertex)
    (hPartnerSurvives : ¬ IsDangling member partner)
    (hPartnerIncident : Incident member partner vertex)
    (hPartnerNe : partner ≠ regrown)
    (hTerminal : ∀ u : member.SourceVertex, Incident member regrown u →
      nonDanglingValency member u = 2 → u = vertex)
    (hPartnerIndex : member.sourceEdgeIndex partner = shape.k)
    (hTransport : ∀ edge ∈ incomingRowEdges data (thirdRow profile),
      ∃ image : member.SourceEdge, OnRow member memberRow image ∧ image ≠ regrown ∧
        member.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    incomingRowDenominator data (thirdRow profile) = shape.k :=
  IncomingSimpleColumn.incomingRowDenominator_thirdRow_eq_of_index profile input shape hRows
    (forall_index_dvd_thirdRow_of_regrowth_of_fullDim shape memberFD hTransition
      hRegrownSurvives hRegrownIncident hPartnerSurvives hPartnerIncident hPartnerNe
      hTerminal hPartnerIndex hTransport)

end IndexHalves

/-! ## 2.  The four-case dichotomy -/

section Dichotomy

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : Shape profile}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The three signed multiplicities in one expression, with `D⁽¹⁾ = D₀` and the
three leaf counts substituted.  No denominator hypothesis. -/
theorem sum_signedMult_expand (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (hLeaf0 : leafCount (graph target wall (limit.member 0).right) = leafCount target + 1)
    (hLeaf1 : leafCount (graph target wall (limit.member 1).right) = leafCount target)
    (hLeaf2 : leafCount (graph target wall (limit.member 2).right) = leafCount target) :
    ∑ position : Fin 3, signedMult (limit.labelling initial position).presentation =
      (incomingDenominatorProduct data : ℚ) / 2 ^ leafCount target / 2 *
          (limit.squareMatrix initial 0).det +
        (denominatorProduct (limit.labelling initial 1).presentation : ℚ) /
            2 ^ leafCount target * (limit.squareMatrix initial 1).det +
        (denominatorProduct (limit.labelling initial 2).presentation : ℚ) /
            2 ^ leafCount target * (limit.squareMatrix initial 2).det := by
  rw [Fin.sum_univ_three]
  show (denominatorProduct (limit.labelling initial 0).presentation : ℚ) /
        2 ^ leafCount (graph target wall (limit.member 0).right) *
          (limit.squareMatrix initial 0).det +
      (denominatorProduct (limit.labelling initial 1).presentation : ℚ) /
        2 ^ leafCount (graph target wall (limit.member 1).right) *
          (limit.squareMatrix initial 1).det +
      (denominatorProduct (limit.labelling initial 2).presentation : ℚ) /
        2 ^ leafCount (graph target wall (limit.member 2).right) *
          (limit.squareMatrix initial 2).det = _
  rw [denominatorProduct_zero limit initial, hLeaf0, hLeaf1, hLeaf2]
  ring

/-- The coprimality package attached to the sharp value on `e₂`'s row. -/
theorem dvd_and_coprime_second
    (hSharp : incomingRowDenominator data (secondRow profile) = shape.k) :
    shape.k ∣ incomingRowDenominator data (secondRow profile) ∧
      Nat.Coprime (shape.k - 1) (incomingRowDenominator data (secondRow profile)) := by
  have hk : 1 < shape.k := shape.one_lt_k
  refine ⟨by rw [hSharp], ?_⟩
  rw [hSharp]
  have hsucc : shape.k - 1 + 1 = shape.k := by omega
  have hc : Nat.Coprime (shape.k - 1) (shape.k - 1 + 1) := by simp
  rwa [hsucc] at hc

/-- The coprimality package attached to the sharp value on `e₃`'s row. -/
theorem dvd_and_coprime_third
    (hSharp : incomingRowDenominator data (thirdRow profile) = shape.k) :
    shape.k ∣ incomingRowDenominator data (thirdRow profile) ∧
      Nat.Coprime (shape.k + 1) (incomingRowDenominator data (thirdRow profile)) := by
  refine ⟨by rw [hSharp], ?_⟩
  rw [hSharp]
  exact Nat.Coprime.symm (by simp : Nat.Coprime shape.k (shape.k + 1))

/-- **The four-case dichotomy.**  `Σ_q Mult φ_q = 0` with the two sharp incoming
denominators needed only where the corresponding member actually contributes --
the parenthesis "whenever `c⁽q⁾ ≠ 0`" in Part II's proof of `prop-signed-mult` (1), in Lean.

The split on `d⁽²⁾ = 0` and `d⁽³⁾ = 0` is exhaustive; the two mixed branches use
`LimitColumns.determinant_balance` to trade `d⁽¹⁾` against the surviving member,
and the doubly degenerate branch evaluates no denominator at all. -/
theorem sum_signedMult_eq_zero_of_conditional (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (hLeaf0 : leafCount (graph target wall (limit.member 0).right) = leafCount target + 1)
    (hLeaf1 : leafCount (graph target wall (limit.member 1).right) = leafCount target)
    (hLeaf2 : leafCount (graph target wall (limit.member 2).right) = leafCount target)
    (hSecond : (limit.squareMatrix initial 1).det ≠ 0 →
      incomingRowDenominator data (secondRow profile) = shape.k)
    (hThird : (limit.squareMatrix initial 2).det ≠ 0 →
      incomingRowDenominator data (thirdRow profile) = shape.k) :
    ∑ position : Fin 3, signedMult (limit.labelling initial position).presentation = 0 := by
  have hk : 1 < shape.k := shape.one_lt_k
  have hcast1 : ((shape.k - 1 : ℕ) : ℚ) = (shape.k : ℚ) - 1 := by
    have h : ((shape.k - 1 : ℕ) : ℤ) = (shape.k : ℤ) - 1 := by omega
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) h
  have hcast2 : ((shape.k + 1 : ℕ) : ℚ) = (shape.k : ℚ) + 1 := by push_cast; ring
  have hBal := limit.determinant_balance input initial
  have hExpand := sum_signedMult_expand limit initial hLeaf0 hLeaf1 hLeaf2
  by_cases h1 : (limit.squareMatrix initial 1).det = 0
  · by_cases h2 : (limit.squareMatrix initial 2).det = 0
    · have h0 : (limit.squareMatrix initial 0).det = 0 := by
        rw [h1, h2] at hBal; linarith
      rw [hExpand, h0, h1, h2]; ring
    · obtain ⟨hDvd3, hCop3⟩ := dvd_and_coprime_third (hThird h2)
      rw [hExpand, h1, denominatorProduct_two input limit initial hDvd3 hCop3]
      rw [h1] at hBal
      push_cast [hcast2]
      field_simp
      nlinarith [hBal]
  · by_cases h2 : (limit.squareMatrix initial 2).det = 0
    · obtain ⟨hDvd2, hCop2⟩ := dvd_and_coprime_second (hSecond h1)
      rw [hExpand, h2, denominatorProduct_one input limit initial hDvd2 hCop2]
      rw [h2] at hBal
      push_cast [hcast1]
      field_simp
      nlinarith [hBal]
    · obtain ⟨hDvd2, hCop2⟩ := dvd_and_coprime_second (hSecond h1)
      obtain ⟨hDvd3, hCop3⟩ := dvd_and_coprime_third (hThird h2)
      exact sum_signedMult_eq_zero input limit initial hLeaf0 hLeaf1 hLeaf2
        hDvd2 hCop2 hDvd3 hCop3

end Dichotomy

/-! ## 3.  The two composed: no denominator hypothesis anywhere -/

section Composed

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : Shape profile}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`prop-signed-mult` (1) for `{w2-r2-nd3-M-1k}` with no denominator
hypothesis.**

What is asked of each perturbing member -- its full-dimensional presentation,
the siting of its regrown transition, and the occurrence transport `hTransport`
-- is asked *only under that member's own `det ≠ 0`*, which is precisely where
`Count.OutgoingRowCalculus` can supply the row calculus.  Where the determinant
vanishes nothing at all is required: §2's dichotomy absorbs the term. -/
theorem sum_signedMult_eq_zero_of_regrowth (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (hLeaf0 : leafCount (graph target wall (limit.member 0).right) = leafCount target + 1)
    (hLeaf1 : leafCount (graph target wall (limit.member 1).right) = leafCount target)
    (hLeaf2 : leafCount (graph target wall (limit.member 2).right) = leafCount target)
    (hRows : secondRow profile ≠ thirdRow profile)
    (hSecond : (limit.squareMatrix initial 1).det ≠ 0 →
      ∃ (_memberFD : FullDimensionalSourcePresentation (limit.member 1).datum coordinate)
        (memberRow : StablePath (limit.member 1).datum)
        (regrown partner : (limit.member 1).datum.SourceEdge)
        (vertex : (limit.member 1).datum.SourceVertex),
        IsRowTransition (limit.member 1).datum memberRow vertex ∧
        ¬ IsDangling (limit.member 1).datum regrown ∧
        Incident (limit.member 1).datum regrown vertex ∧
        ¬ IsDangling (limit.member 1).datum partner ∧
        Incident (limit.member 1).datum partner vertex ∧ partner ≠ regrown ∧
        (∀ u : (limit.member 1).datum.SourceVertex,
          Incident (limit.member 1).datum regrown u →
          nonDanglingValency (limit.member 1).datum u = 2 → u = vertex) ∧
        (limit.member 1).datum.sourceEdgeIndex partner = shape.k ∧
        ∀ edge ∈ incomingRowEdges data (secondRow profile),
          ∃ image : (limit.member 1).datum.SourceEdge,
            OnRow (limit.member 1).datum memberRow image ∧ image ≠ regrown ∧
              (limit.member 1).datum.sourceEdgeIndex image = data.sourceEdgeIndex edge)
    (hThird : (limit.squareMatrix initial 2).det ≠ 0 →
      ∃ (_memberFD : FullDimensionalSourcePresentation (limit.member 2).datum coordinate)
        (memberRow : StablePath (limit.member 2).datum)
        (regrown partner : (limit.member 2).datum.SourceEdge)
        (vertex : (limit.member 2).datum.SourceVertex),
        IsRowTransition (limit.member 2).datum memberRow vertex ∧
        ¬ IsDangling (limit.member 2).datum regrown ∧
        Incident (limit.member 2).datum regrown vertex ∧
        ¬ IsDangling (limit.member 2).datum partner ∧
        Incident (limit.member 2).datum partner vertex ∧ partner ≠ regrown ∧
        (∀ u : (limit.member 2).datum.SourceVertex,
          Incident (limit.member 2).datum regrown u →
          nonDanglingValency (limit.member 2).datum u = 2 → u = vertex) ∧
        (limit.member 2).datum.sourceEdgeIndex partner = shape.k ∧
        ∀ edge ∈ incomingRowEdges data (thirdRow profile),
          ∃ image : (limit.member 2).datum.SourceEdge,
            OnRow (limit.member 2).datum memberRow image ∧ image ≠ regrown ∧
              (limit.member 2).datum.sourceEdgeIndex image = data.sourceEdgeIndex edge) :
    ∑ position : Fin 3, signedMult (limit.labelling initial position).presentation = 0 := by
  refine sum_signedMult_eq_zero_of_conditional input limit initial hLeaf0 hLeaf1 hLeaf2
    (fun hdet ↦ ?_) (fun hdet ↦ ?_)
  · obtain ⟨memberFD, memberRow, regrown, partner, vertex, hTransition, hRegrownSurvives,
      hRegrownIncident, hPartnerSurvives, hPartnerIncident, hPartnerNe, hTerminal,
      hPartnerIndex, hTransport⟩ := hSecond hdet
    exact incomingRowDenominator_secondRow_eq_of_regrowth_of_fullDim profile input shape hRows
      memberFD hTransition hRegrownSurvives hRegrownIncident hPartnerSurvives
      hPartnerIncident hPartnerNe hTerminal hPartnerIndex hTransport
  · obtain ⟨memberFD, memberRow, regrown, partner, vertex, hTransition, hRegrownSurvives,
      hRegrownIncident, hPartnerSurvives, hPartnerIncident, hPartnerNe, hTerminal,
      hPartnerIndex, hTransport⟩ := hThird hdet
    exact incomingRowDenominator_thirdRow_eq_of_regrowth_of_fullDim profile input shape hRows
      memberFD hTransition hRegrownSurvives hRegrownIncident hPartnerSurvives
      hPartnerIncident hPartnerNe hTerminal hPartnerIndex hTransport

end Composed

/-! ## 4.  On the family Part I actually constructs

`W2M1kLimitColumns.limitColumns` is a `dite` on `pinSheet profile 0 = pinSheet
profile 1`, and `W2M1kGaugeFamily`'s dictionaries and genus receipts are stated
against the two named orientations.  `limitDictionary` and `limitMemberGenus`
carry them across the `dite`, exactly as
`W2M1kLeafStableGraph.leafPositionDictionary` carries the leaf dictionary across
a position identification, and `memberPresentation` then produces Figure 33's
certified exit at **any** position, gated on that position's own determinant. -/

section Constructed

open DraismaVargas.LocalCases.W2M1kLimitColumns

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The three dictionaries against the incoming stable graph, at the positions
of `W2M1kLimitColumns.limitColumns` itself rather than of a named
orientation. -/
noncomputable def limitDictionary (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (position : Fin 3) :
    StableGraphIncidence.Equivalence data
      ((limitColumns input shape hConnected hGenus).member position).datum := by
  classical
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · exact cast (congrArg (fun limit : LimitColumns profile shape ↦
      StableGraphIncidence.Equivalence data (limit.member position).datum)
      (limitColumns_eq_alignedOrientation input shape hConnected hGenus hAligned)).symm
      (W2M1kGaugeFamily.alignedDictionary input shape
        (exists_leafPair shape hAligned).some hConnected hGenus position)
  · exact cast (congrArg (fun limit : LimitColumns profile shape ↦
      StableGraphIncidence.Equivalence data (limit.member position).datum)
      (limitColumns_eq_separatedOrientation input shape hConnected hGenus hAligned)).symm
      (W2M1kGaugeFamily.separatedDictionary input shape
        (exists_dividedData shape hAligned).some hConnected hGenus position)

/-- The three source-genus receipts, at the positions of
`W2M1kLimitColumns.limitColumns` itself. -/
theorem limitMemberGenus (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (position : Fin 3) :
    genus ((limitColumns input shape hConnected hGenus).member position).datum.sourceGraph =
      genus data.sourceGraph := by
  classical
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [limitColumns_eq_alignedOrientation input shape hConnected hGenus hAligned]
    exact W2M1kGaugeFamily.alignedMemberGenus input shape _ hConnected hGenus position
  · rw [limitColumns_eq_separatedOrientation input shape hConnected hGenus hAligned]
    exact W2M1kGaugeFamily.separatedMemberGenus input shape _ hConnected hGenus position

/-- **Figure 33's certified exit at any position of the constructed family.**
`W2M1kStableIncidence.presentationAtOfDictionaries` with both dictionaries and
both genus receipts discharged; the only inputs left are the incoming chart
`incomingFD` and the outgoing member's own `det ≠ 0`. -/
noncomputable def memberPresentation (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming outgoing : Fin 3)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member incoming).datum coordinate)
    (hDet : ((limitColumns input shape hConnected hGenus).squareMatrix
      initial outgoing).det ≠ 0) :
    FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member outgoing).datum coordinate :=
  W2M1kStableIncidence.presentationAtOfDictionaries
    (limitColumns input shape hConnected hGenus) incoming outgoing
    (limitDictionary input shape hConnected hGenus incoming)
    (limitDictionary input shape hConnected hGenus outgoing)
    input.valid hConnected hGenus
    (limitMemberGenus input shape hConnected hGenus incoming)
    (limitMemberGenus input shape hConnected hGenus outgoing)
    initial incomingFD hDet

/-- It presents the family's own honest labelling at that position. -/
theorem memberPresentation_presentation_eq (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming outgoing : Fin 3)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member incoming).datum coordinate)
    (hDet : ((limitColumns input shape hConnected hGenus).squareMatrix
      initial outgoing).det ≠ 0) :
    (memberPresentation input shape hConnected hGenus incoming outgoing initial incomingFD
        hDet).labelling.presentation =
      ((limitColumns input shape hConnected hGenus).labelling initial outgoing).presentation :=
  rfl

/-- **The member row calculus on Figure 33's members.**  A stable row of the member at
position `outgoing` -- `M⁽²⁾` at `1`, `M⁽³⁾` at `2` -- carrying one occurrence of
dilation index `≠ 1` has ramification at most one at every interior vertex and
at most one transition.

The hypotheses are exactly two: that member's own determinant is nonzero
(Part II's `c⁽q⁾ ≠ 0`), and a full-dimensional presentation at some
position of the family, which is the incoming chart.  On the two
perturbed rows the ramified occurrence is free: the member's copy of `e₂`
(resp. `e₃`) has index `k` and `Shape.one_lt_k` is `1 < k`. -/
theorem rowCalculus_member (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming outgoing : Fin 3)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member incoming).datum coordinate)
    (hDet : ((limitColumns input shape hConnected hGenus).squareMatrix
      initial outgoing).det ≠ 0)
    {memberRow : StablePath ((limitColumns input shape hConnected hGenus).member outgoing).datum}
    {edge : ((limitColumns input shape hConnected hGenus).member outgoing).datum.SourceEdge}
    (hEdge : OnRow ((limitColumns input shape hConnected hGenus).member outgoing).datum
      memberRow edge)
    (hIndex : ((limitColumns input shape hConnected hGenus).member
      outgoing).datum.sourceEdgeIndex edge ≠ 1) :
    RowRamificationAtMostOne
        ((limitColumns input shape hConnected hGenus).member outgoing).datum memberRow ∧
      RowAtMostOneTransition
        ((limitColumns input shape hConnected hGenus).member outgoing).datum memberRow :=
  OutgoingRowCalculus.rowCalculus_of_index_ne_one
    (memberPresentation input shape hConnected hGenus incoming outgoing initial incomingFD hDet)
    hEdge hIndex

/-! ### The two perturbed member rows, named

Figure 33's `M⁽²⁾` is `W2M1kSourceCandidates.DividedData.candidate` (Base
II.2.2.M) and its perturbed row is the row of the retained copy of `e₂`
(`W2M1kStableGraph.divided_new_third_stablePath_eq` puts the residual new
occurrence of index `k-1` there).  `M⁽³⁾` is `joinedCandidate` (Base II.1.M) and
its perturbed row is the row of the retained copy of `e₃`
(`joined_new_stablePath_eq_third`, new occurrence of index `k+1`).  In both
cases the retained copy has the incoming index -- `k`, by `Shape.second_index`
and `Shape.third_index` -- so the ramified-occurrence witness §3 of
`Count.OutgoingRowCalculus` asks for is free, and **the member row calculus on these rows
is these two statements**.

Figure 33's member 2 as it appears at position `1` of the aligned orientation is
the *remote* copy, obtained by instantiating the divided definitions at
`W2M1kSwapped.swappedData`; the statement below takes `data`, `profile`, `shape`
and `divided` as parameters, so it applies there by substitution, exactly as
`W2M1kStableLift` does. -/

/-- **The row calculus on `M⁽²⁾`'s perturbed row.**  `RowRamificationAtMostOne` and
`RowAtMostOneTransition` on the stable row of `e₂` in Base II.2.2.M's candidate,
with `c⁽²⁾ ≠ 0` the only gate (it is what produces `memberFD`). -/
theorem rowCalculus_dividedCandidate_secondRow (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (memberFD : FullDimensionalSourcePresentation
      (DividedData.candidate shape divided).datum coordinate) :
    RowRamificationAtMostOne (DividedData.candidate shape divided).datum
        (NonDanglingEdge.stablePath
          ⟨(DividedData.candidate shape divided).oldSourceEdge profile.second.1,
            ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
              profile.second_survives⟩) ∧
      RowAtMostOneTransition (DividedData.candidate shape divided).datum
        (NonDanglingEdge.stablePath
          ⟨(DividedData.candidate shape divided).oldSourceEdge profile.second.1,
            ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
              profile.second_survives⟩) :=
  OutgoingRowCalculus.rowCalculus_of_index_ne_one memberFD
    ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.second_survives,
      rfl⟩
    (by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge, shape.second_index]
      have := shape.one_lt_k
      omega)

/-- **The row calculus on `M⁽³⁾`'s perturbed row.**  The same on the stable row of `e₃`
in Base II.1.M's candidate, gated on `c⁽³⁾ ≠ 0`. -/
theorem rowCalculus_joinedCandidate_thirdRow (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (memberFD : FullDimensionalSourcePresentation
      (joinedCandidate star geometry).datum coordinate) :
    RowRamificationAtMostOne (joinedCandidate star geometry).datum
        (NonDanglingEdge.stablePath
          ⟨(joinedCandidate star geometry).oldSourceEdge profile.third.1,
            ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
              profile.third_survives⟩) ∧
      RowAtMostOneTransition (joinedCandidate star geometry).datum
        (NonDanglingEdge.stablePath
          ⟨(joinedCandidate star geometry).oldSourceEdge profile.third.1,
            ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
              profile.third_survives⟩) :=
  OutgoingRowCalculus.rowCalculus_of_index_ne_one memberFD
    ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.third_survives,
      rfl⟩
    (by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge, shape.third_index]
      have := shape.one_lt_k
      omega)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- **The balance with the denominator hypotheses restricted to the
contributing members.**  `prop-signed-mult` (1) for `{w2-r2-nd3-M-1k}` on the
canonical labelling of the family `W2M1kLimitColumns.limitColumns` builds, with
`Count.IncomingSimpleColumn`'s row-distinctness hypothesis discharged by
`Count.RowGeodesic.secondRow_ne_thirdRow_of_genusZero` and the two upper halves
asked for only when the member that needs them has nonzero determinant.

Compare `Count.RowGeodesic.sum_signedMult_canonical_eq_zero_of_genusZero`, whose
`hIndex2` and `hIndex3` are unconditional. -/
theorem sum_signedMult_canonical_eq_zero_of_conditional_index
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hTame : RowRamificationAtMostOne data (secondRow profile))
    (hIndex2 : ((limitColumns input shape hConnected hGenus).squareMatrix
        ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input) 1).det ≠ 0 →
      ∀ edge ∈ incomingRowEdges data (secondRow profile),
        data.sourceEdgeIndex edge ∣ shape.k)
    (hIndex3 : ((limitColumns input shape hConnected hGenus).squareMatrix
        ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input) 2).det ≠ 0 →
      ∀ edge ∈ incomingRowEdges data (thirdRow profile),
        data.sourceEdgeIndex edge ∣ shape.k) :
    ∑ position : Fin 3, signedMult
        ((limitColumns input shape hConnected hGenus).labelling
          ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input)
            position).presentation = 0 := by
  have hRows : secondRow profile ≠ thirdRow profile :=
    RowGeodesic.secondRow_ne_thirdRow_of_genusZero hConnected hGenus input.dangling_no_glue hTame
  exact sum_signedMult_eq_zero_of_conditional input _ _
    (leafCount_member_zero input shape hConnected hGenus)
    (leafCount_member_one input shape hConnected hGenus)
    (leafCount_member_two input shape hConnected hGenus)
    (fun hdet ↦ IncomingSimpleColumn.incomingRowDenominator_secondRow_eq_of_index profile
      input shape hRows (hIndex2 hdet))
    (fun hdet ↦ IncomingSimpleColumn.incomingRowDenominator_thirdRow_eq_of_index profile
      input shape hRows (hIndex3 hdet))

/-! ## 5.  Non-vacuity: the degenerate branch of the dichotomy

When both perturbing members are singular the conclusion holds with both
implications supplied vacuously -- no denominator, no transport, no member
presentation.  This is the fourth case of §2, and it is the case in which
`prop-signed-mult` (1) is true for reasons that have nothing to do with
`lemma-edge-deno`. -/

/-- **The dichotomy is inhabited.**  Both perturbing determinants zero: the
balance forces the third and `Σ_q Mult φ_q = 0` outright. -/
example (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hTame : RowRamificationAtMostOne data (secondRow profile))
    (h1 : ((limitColumns input shape hConnected hGenus).squareMatrix
      ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input) 1).det = 0)
    (h2 : ((limitColumns input shape hConnected hGenus).squareMatrix
      ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input) 2).det = 0) :
    ∑ position : Fin 3, signedMult
        ((limitColumns input shape hConnected hGenus).labelling
          ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input)
            position).presentation = 0 :=
  sum_signedMult_canonical_eq_zero_of_conditional_index input shape hConnected hGenus hTame
    (fun hdet ↦ absurd h1 hdet) (fun hdet ↦ absurd h2 hdet)

end Constructed

end DraismaVargas.Count.W2M1kMemberBalance
