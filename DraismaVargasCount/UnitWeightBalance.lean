module

public import DraismaVargasCount.TrivalentWeight

@[expose] public section

/-!
# The unit-weight trivalent balance, case-independently

**Source.**  Vargas, Part II (arXiv:2609.09109), Proposition
`prop-signed-mult` (1) and its proof; the determinant identities of
Draisma--Vargas Part I (arXiv:1909.12924) for the trivalent deformation cases
whose weight vector is `(1, 1)`, i.e. Equation (4) (`{w3-r1-nd3-t3}`,
Figure 30), Equation (5) (`{w3-r1-nd2}`, Figure 31) and Equation (10)
(`{w2-r1}`, Figures 37--38).

For those cases the weight identification
`weight q · D₀/2^{l(T₀)} = D_q/2^{l(T_q)}` degenerates: with all weights `1`
the identity `Σ_q det A_q = 0` becomes `Σ_q Mult φ_q = 0` as soon as
`D_q / 2^{l(T_q)}` is the **same for every member**.  This module proves, once
and for all, that the two conditions hold for any **two**-member family whose
regrown columns satisfy Part I's column identity

    new column of `M⁽¹⁾` + new column of `M⁽²⁾` = old column `p₀` + old column `p₁`

at every incoming stable row, and whose two expanded targets have the same
leaf count.  Nothing case-specific enters, and -- this is the point -- **no
incoming row denominator is evaluated**: the sharp incoming row denominators,
which `Count.TrivalentWeight`'s `sum_signedMult_canonical_eq_zero` assumes for
the representative case `{w2-r2-nd3-M-1k}`, are not needed here.

## Why the two-member case is free

`rowDenominator_of_commonMatrix` (the `LimitColumns`-free form of
`TrivalentWeight.rowDenominator_member`) gives, for each member `q` and each
incoming stable row `h`,

    d_q(h) = lcm( den(new_q(h)), d₀(h) ).

The crux `lcm_den_eq_of_add_eq_add` says that if `a + b = u + v` with
`den u ∣ d` and `den v ∣ d`, then `lcm (den a) d = lcm (den b) d`: writing
`c = a - v = u - b`, both sides equal `lcm (den c) d`, because merging a
rational whose denominator already divides `d` into `d` changes nothing
(`lcm_den_add_left`).  Applied with `u`, `v` the two old columns at the row
-- whose denominators divide `d₀(h)` by definition of `d₀` -- this gives
`d₀-relative equality of the two members' row denominators at every row`,
hence `D⁽¹⁾ = D⁽²⁾`, with no knowledge of `d₀(h)` whatsoever.  The common value
is **not** claimed to be `D₀`; it is `∏_h lcm(den(new₁(h)), d₀(h))`, which can
be a proper multiple of `D₀`.

With three or more members the argument fails, and is expected to: the
correction terms `new_q - (old column)` then no longer differ by a sign, and
the individual dilation indices reappear.  That is why Equation (1)
(`{w4}`, three members, weights `(1,1,1)`) is **not** free on its weights;
`denominatorProduct_eq_incoming_of_den_dvd` and
`sum_signedMult_eq_zero_of_uniform` below are the interface it uses instead,
`Count.W4UnitBalance` states the one divisibility hypothesis it needs there,
and `Count.W4IncomingIndex` discharges it.

## What is proved

* `den_add_dvd`, `lcm_den_add_left`, **`lcm_den_eq_of_add_eq_add`** -- the
  arithmetic, with no hypothesis beyond the stated divisibilities.
* `rowDenominator_of_commonMatrix`, `denominatorProduct_of_commonMatrix` --
  a member's row denominators and denominator product read off any
  description of its honest square matrix in common `StablePath data` ×
  `Option target.edges` coordinates whose `some` part is the incoming matrix.
  This is `TrivalentWeight.rowDenominator_member` with the `LimitColumns`
  structure of the case `{w2-r2-nd3-M-1k}` unpacked into the two fields it uses.
* `denominatorProduct_eq_of_columns_add` -- `D⁽¹⁾ = D⁽²⁾` from the column
  identity alone.
* `signedMult_add_eq_zero` and `signedMult_add_eq_zero_of_columns_add` -- the
  balance `Mult φ⁽¹⁾ + Mult φ⁽²⁾ = 0`.
* `leafCount_graph_of_nonleaf_split` -- the sibling of
  `TrivalentWeight.leafCount_graph_of_divalent_split`: any split of the wall
  leaving both copies of valency at least two preserves the leaf count.
  `leafCount_graph_candidate` reads the two valencies off a
  `BalancedGlobal.Candidate`'s own certified incidence lists through
  `M11SourceCandidates.candidate_target_valencies`, and
  `length_leftEdges_eq_card` / `length_rightEdges_eq_card` turn those lists
  into `TargetExpansion.wallEdgesAssigned` cardinalities.

## What is not proved here

* Nothing about three-member families, and nothing about `{w4}`.
* No value of any incoming row denominator `d₀(h)`, and no claim that
  `D_q = D₀`.  Only the *equality across the two members* is proved.
* The leaf counts are an explicit hypothesis of the balance theorems; the
  per-case modules discharge them from the target valencies of their
  candidates.
* Nothing here is conditional on integrality of the multiplicity, on the
  genus, on the degree, or on nonsingularity of any member.

## Non-vacuity

No structure is introduced.  Every theorem is applied, on the family the Part
I lemmas actually construct, in `Count.W3Nd3UnitBalance`,
`Count.W3Nd2UnitBalance`, `Count.W2R1UnitBalance` and `Count.W4UnitBalance`.

## Use

The balancing identities of Part I, Equations (4), (5) and (10), in
multiplicity form, and through `Count.W4UnitBalance` Equation (1): cases of the
trivalent walls (step 2 of `DraismaVargasCount.Assembly`).
-/

namespace DraismaVargas.Count.UnitWeightBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.Count.TrivalentWeight
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableSourceMatrix
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.Infrastructure.TargetExpansion

/-! ## 1.  The arithmetic crux -/

theorem den_add_dvd {x y : ℚ} {N : ℕ} (hx : x.den ∣ N) (hy : y.den ∣ N) :
    (x + y).den ∣ N := by
  refine den_dvd_of_integral_mul _ ?_
  obtain ⟨a, ha⟩ := integral_mul_of_den_dvd x hx
  obtain ⟨b, hb⟩ := integral_mul_of_den_dvd y hy
  exact ⟨a + b, by push_cast [← ha, ← hb]; ring⟩

theorem den_neg (x : ℚ) : (-x).den = x.den := by simp

theorem den_sum_dvd {ι : Type*} (s : Finset ι) (f : ι → ℚ) {N : ℕ}
    (h : ∀ i ∈ s, (f i).den ∣ N) : (∑ i ∈ s, f i).den ∣ N := by
  refine den_dvd_of_integral_mul _ ?_
  rw [Finset.mul_sum]
  exact integral_sum s _ fun i hi ↦ integral_mul_of_den_dvd (f i) (h i hi)

/-- The denominator of a reciprocal dilation index divides that index. -/
theorem den_one_div_natCast (n : ℕ) : ((1 : ℚ) / (n : ℚ)).den ∣ n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]

/-- Merging into `d` a rational whose denominator already divides `d` changes
nothing: `lcm (den (x + c)) d = lcm (den c) d` whenever `den x ∣ d`. -/
theorem lcm_den_add_left (x c : ℚ) {d : ℕ} (hx : x.den ∣ d) :
    Nat.lcm (x + c).den d = Nat.lcm c.den d := by
  refine Nat.dvd_antisymm (Nat.lcm_dvd ?_ (Nat.dvd_lcm_right _ _))
    (Nat.lcm_dvd ?_ (Nat.dvd_lcm_right _ _))
  · exact den_add_dvd (hx.trans (Nat.dvd_lcm_right _ _)) (Nat.dvd_lcm_left _ _)
  · have key : ((x + c) + (-x)).den ∣ Nat.lcm (x + c).den d :=
      den_add_dvd (Nat.dvd_lcm_left _ _)
        (((den_neg x) ▸ hx : (-x).den ∣ d).trans (Nat.dvd_lcm_right _ _))
    rwa [show (x + c) + (-x) = c by ring] at key

/-- **The unit-weight crux.**  If `a + b = u + v` and the denominators of `u`
and `v` both divide `d`, then `a` and `b` merge into `d` the same way.  No
value of `d`, and no value of `den a` or `den b`, is needed. -/
theorem lcm_den_eq_of_add_eq_add {a b u v : ℚ} {d : ℕ}
    (hu : u.den ∣ d) (hv : v.den ∣ d) (h : a + b = u + v) :
    Nat.lcm a.den d = Nat.lcm b.den d := by
  have e1 : Nat.lcm a.den d = Nat.lcm (a - v).den d := by
    have h1 := lcm_den_add_left v (a - v) hv
    rwa [show v + (a - v) = a by ring] at h1
  have e2 : Nat.lcm b.den d = Nat.lcm (-(a - v)).den d := by
    have h2 := lcm_den_add_left u (-(a - v)) hu
    rwa [show u + -(a - v) = b by linarith] at h2
  rw [e1, e2, den_neg]

/-! ## 2.  A member's row denominators from its common-coordinate matrix -/

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- **`TrivalentWeight.rowDenominator_member`, without the M-1k `LimitColumns`.**
Whenever a member's honest square matrix is described in the common
coordinates -- incoming stable rows through `src`, `Option target.edges`
columns through `tgt` -- and its retained columns are the incoming ones, its
row denominator is the incoming one merged with the denominator of the single
regrown entry. -/
theorem rowDenominator_of_commonMatrix
    {target' : CFGraph} {degree' : ℕ} {datum' : GluingDatum target' degree'}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (lab : StableLengthMatrixLabelling datum' coordinate)
    (src : StablePath data ≃ coordinate) (tgt : coordinate ≃ Option target.edges)
    (common : StablePath data → Option target.edges → ℚ)
    (hCommon : ∀ row column,
      GluingDatum.LengthMatrixPresentation.matrix lab.presentation row column =
        common (src.symm row) (tgt column))
    (hRetained : ∀ (path : StablePath data) (place : target.edges),
      common path (some place) = StableSourceMatrix.matrix data path place)
    (row : coordinate) :
    rowDenominator lab.presentation row =
      Nat.lcm (common (src.symm row) none).den
        (incomingRowDenominator data (src.symm row)) := by
  classical
  have hStep : rowDenominator lab.presentation row =
      commonDenominator Finset.univ
        (fun o : Option target.edges ↦ common (src.symm row) o) := by
    rw [rowDenominator,
      show (GluingDatum.LengthMatrixPresentation.matrix lab.presentation row) =
        fun column ↦ common (src.symm row) (tgt column) from funext (hCommon row)]
    exact commonDenominator_equiv tgt _
  rw [hStep, commonDenominator_option]
  exact congrArg (Nat.lcm _)
    (congrArg (commonDenominator Finset.univ) (funext fun place ↦ hRetained _ place))

/-- `D_φ = ∏_h lcm(den(new(h)), d₀(h))`, over the incoming stable rows. -/
theorem denominatorProduct_of_commonMatrix
    {target' : CFGraph} {degree' : ℕ} {datum' : GluingDatum target' degree'}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (lab : StableLengthMatrixLabelling datum' coordinate)
    (src : StablePath data ≃ coordinate) (tgt : coordinate ≃ Option target.edges)
    (common : StablePath data → Option target.edges → ℚ)
    (hCommon : ∀ row column,
      GluingDatum.LengthMatrixPresentation.matrix lab.presentation row column =
        common (src.symm row) (tgt column))
    (hRetained : ∀ (path : StablePath data) (place : target.edges),
      common path (some place) = StableSourceMatrix.matrix data path place) :
    denominatorProduct lab.presentation =
      ∏ path : StablePath data,
        Nat.lcm (common path none).den (incomingRowDenominator data path) := by
  classical
  rw [denominatorProduct,
    Finset.prod_congr rfl fun row _ ↦
      rowDenominator_of_commonMatrix lab src tgt common hCommon hRetained row]
  exact Fintype.prod_equiv src.symm _ _ fun _ ↦ rfl

/-- **`D_φ = D₀` when every regrown entry is already `d₀`-integral.**  This is
the shape a family with more than two members needs; the hypothesis is
`lemma-edge-deno` (b)'s *lower* half at the perturbed rows, not its sharp
value. -/
theorem denominatorProduct_eq_incoming_of_den_dvd
    {target' : CFGraph} {degree' : ℕ} {datum' : GluingDatum target' degree'}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (lab : StableLengthMatrixLabelling datum' coordinate)
    (src : StablePath data ≃ coordinate) (tgt : coordinate ≃ Option target.edges)
    (common : StablePath data → Option target.edges → ℚ)
    (hCommon : ∀ row column,
      GluingDatum.LengthMatrixPresentation.matrix lab.presentation row column =
        common (src.symm row) (tgt column))
    (hRetained : ∀ (path : StablePath data) (place : target.edges),
      common path (some place) = StableSourceMatrix.matrix data path place)
    (hNew : ∀ path : StablePath data,
      (common path none).den ∣ incomingRowDenominator data path) :
    denominatorProduct lab.presentation = incomingDenominatorProduct data := by
  rw [denominatorProduct_of_commonMatrix lab src tgt common hCommon hRetained]
  exact Finset.prod_congr rfl fun path _ ↦ lcm_den_eq_right (hNew path)

/-- **`D⁽¹⁾ = D⁽²⁾` from Part I's column identity alone.**  The two members'
regrown columns add up to two old columns at every incoming stable row; no
incoming row denominator is evaluated. -/
theorem denominatorProduct_eq_of_columns_add
    {T₀ T₁ : CFGraph} {d₀ d₁ : ℕ}
    {datum₀ : GluingDatum T₀ d₀} {datum₁ : GluingDatum T₁ d₁}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (lab₀ : StableLengthMatrixLabelling datum₀ coordinate)
    (lab₁ : StableLengthMatrixLabelling datum₁ coordinate)
    (src : StablePath data ≃ coordinate) (tgt : coordinate ≃ Option target.edges)
    (common₀ common₁ : StablePath data → Option target.edges → ℚ)
    (hCommon₀ : ∀ row column,
      GluingDatum.LengthMatrixPresentation.matrix lab₀.presentation row column =
        common₀ (src.symm row) (tgt column))
    (hCommon₁ : ∀ row column,
      GluingDatum.LengthMatrixPresentation.matrix lab₁.presentation row column =
        common₁ (src.symm row) (tgt column))
    (hRetained₀ : ∀ (path : StablePath data) (place : target.edges),
      common₀ path (some place) = StableSourceMatrix.matrix data path place)
    (hRetained₁ : ∀ (path : StablePath data) (place : target.edges),
      common₁ path (some place) = StableSourceMatrix.matrix data path place)
    (place₀ place₁ : target.edges)
    (hNewSum : ∀ path : StablePath data,
      common₀ path none + common₁ path none =
        StableSourceMatrix.matrix data path place₀ +
          StableSourceMatrix.matrix data path place₁) :
    denominatorProduct lab₀.presentation = denominatorProduct lab₁.presentation := by
  rw [denominatorProduct_of_commonMatrix lab₀ src tgt common₀ hCommon₀ hRetained₀,
    denominatorProduct_of_commonMatrix lab₁ src tgt common₁ hCommon₁ hRetained₁]
  refine Finset.prod_congr rfl fun path _ ↦ ?_
  exact lcm_den_eq_of_add_eq_add
    (den_dvd_incomingRowDenominator path place₀)
    (den_dvd_incomingRowDenominator path place₁) (hNewSum path)

/-! ## 3.  The balance -/

/-- Two members with equal denominator products, equal target leaf counts and
opposite determinants have opposite signed multiplicities. -/
theorem signedMult_add_eq_zero
    {T₀ T₁ : CFGraph} {d₀ d₁ : ℕ}
    {datum₀ : GluingDatum T₀ d₀} {datum₁ : GluingDatum T₁ d₁}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (p₀ : datum₀.LengthMatrixPresentation coordinate)
    (p₁ : datum₁.LengthMatrixPresentation coordinate)
    (hDen : denominatorProduct p₀ = denominatorProduct p₁)
    (hLeaf : leafCount T₀ = leafCount T₁)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix p₀).det +
      (GluingDatum.LengthMatrixPresentation.matrix p₁).det = 0) :
    signedMult p₀ + signedMult p₁ = 0 := by
  unfold signedMult
  rw [hDen, hLeaf]
  have hFactor :
      (denominatorProduct p₁ : ℚ) / 2 ^ leafCount T₁ *
          (GluingDatum.LengthMatrixPresentation.matrix p₀).det +
        (denominatorProduct p₁ : ℚ) / 2 ^ leafCount T₁ *
          (GluingDatum.LengthMatrixPresentation.matrix p₁).det =
      (denominatorProduct p₁ : ℚ) / 2 ^ leafCount T₁ *
        ((GluingDatum.LengthMatrixPresentation.matrix p₀).det +
          (GluingDatum.LengthMatrixPresentation.matrix p₁).det) := by ring
  rw [hFactor, hDet, mul_zero]

/-- **`prop-signed-mult`(1) for a two-member unit-weight trivalent limit.**
The hypotheses are exactly Part I's column identity, the equality of the two
expanded targets' leaf counts, and Part I's determinant identity.  No incoming
row denominator, no dilation index, and no nonsingularity enters. -/
theorem signedMult_add_eq_zero_of_columns_add
    {T₀ T₁ : CFGraph} {d₀ d₁ : ℕ}
    {datum₀ : GluingDatum T₀ d₀} {datum₁ : GluingDatum T₁ d₁}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (lab₀ : StableLengthMatrixLabelling datum₀ coordinate)
    (lab₁ : StableLengthMatrixLabelling datum₁ coordinate)
    (src : StablePath data ≃ coordinate) (tgt : coordinate ≃ Option target.edges)
    (common₀ common₁ : StablePath data → Option target.edges → ℚ)
    (hCommon₀ : ∀ row column,
      GluingDatum.LengthMatrixPresentation.matrix lab₀.presentation row column =
        common₀ (src.symm row) (tgt column))
    (hCommon₁ : ∀ row column,
      GluingDatum.LengthMatrixPresentation.matrix lab₁.presentation row column =
        common₁ (src.symm row) (tgt column))
    (hRetained₀ : ∀ (path : StablePath data) (place : target.edges),
      common₀ path (some place) = StableSourceMatrix.matrix data path place)
    (hRetained₁ : ∀ (path : StablePath data) (place : target.edges),
      common₁ path (some place) = StableSourceMatrix.matrix data path place)
    (place₀ place₁ : target.edges)
    (hNewSum : ∀ path : StablePath data,
      common₀ path none + common₁ path none =
        StableSourceMatrix.matrix data path place₀ +
          StableSourceMatrix.matrix data path place₁)
    (hLeaf : leafCount T₀ = leafCount T₁)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix lab₀.presentation).det +
      (GluingDatum.LengthMatrixPresentation.matrix lab₁.presentation).det = 0) :
    signedMult lab₀.presentation + signedMult lab₁.presentation = 0 :=
  signedMult_add_eq_zero _ _
    (denominatorProduct_eq_of_columns_add lab₀ lab₁ src tgt common₀ common₁
      hCommon₀ hCommon₁ hRetained₀ hRetained₁ place₀ place₁ hNewSum) hLeaf hDet

/-- **The balance for any number of members with a common `D/2^l`.**  With all
weights `1` the determinant identity `Σ_q det A_q = 0` is exactly
`Σ_q Mult φ_q = 0` once the denominator products and the leaf counts agree
across the family. -/
theorem sum_signedMult_eq_zero_of_uniform
    {n : ℕ} {outTarget : Fin n → CFGraph} {outDegree : Fin n → ℕ}
    {outDatum : ∀ q, GluingDatum (outTarget q) (outDegree q)}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (p : ∀ q, (outDatum q).LengthMatrixPresentation coordinate)
    (product leaves : ℕ)
    (hDen : ∀ q, denominatorProduct (p q) = product)
    (hLeaf : ∀ q, leafCount (outTarget q) = leaves)
    (hDet : ∑ q : Fin n,
      (GluingDatum.LengthMatrixPresentation.matrix (p q)).det = 0) :
    ∑ q : Fin n, signedMult (p q) = 0 := by
  have hTerm : ∀ q : Fin n, signedMult (p q) =
      (product : ℚ) / 2 ^ leaves *
        (GluingDatum.LengthMatrixPresentation.matrix (p q)).det := by
    intro q
    unfold signedMult
    rw [hDen q, hLeaf q]
  rw [Finset.sum_congr rfl fun q _ ↦ hTerm q, ← Finset.mul_sum, hDet, mul_zero]

/-! ## 4.  Leaf counts of the expanded targets -/

section LeafCount

variable {target : CFGraph} (wall : target.V)

/-- **A split leaving both copies of the wall at valency at least two
preserves the leaf count.**  The sibling of
`TrivalentWeight.leafCount_graph_of_divalent_split` that the three-valent
walls of Equations (4) and (5) need, where one copy is trivalent. -/
theorem leafCount_graph_of_nonleaf_split (right : target.edges → Bool)
    (hOld : 2 ≤ (GluingDatum.incidentEdges
      (target := graph target wall right) (oldVertex target wall)).card)
    (hFresh : 2 ≤ (GluingDatum.incidentEdges
      (target := graph target wall right) (freshVertex target)).card) :
    leafCount (graph target wall right) = leafCount target := by
  have hSplit := card_incidentEdges_wall_split wall right
  have hWall : leafIndicator target wall = 0 :=
    leafIndicator_eq_zero _ _ (by omega)
  have hOldInd : leafIndicator (graph target wall right) (oldVertex target wall) = 0 :=
    leafIndicator_eq_zero _ _ (by omega)
  have hFreshInd : leafIndicator (graph target wall right) (freshVertex target) = 0 :=
    leafIndicator_eq_zero _ _ (by omega)
  have h := leafCount_graph wall right
  omega

variable {degree : ℕ} {data : GluingDatum target degree}

theorem length_leftEdges_eq_card
    (candidate : BalancedGlobal.Candidate target degree data wall) :
    candidate.leftEdges.length =
      (wallEdgesAssigned target wall candidate.right false).card := by
  simpa using congrArg Multiset.card candidate.leftEdges_eq

theorem length_rightEdges_eq_card
    (candidate : BalancedGlobal.Candidate target degree data wall) :
    candidate.rightEdges.length =
      (wallEdgesAssigned target wall candidate.right true).card := by
  simpa using congrArg Multiset.card candidate.rightEdges_eq

/-- **A candidate that puts at least one old wall occurrence on each side
preserves the leaf count**, read off its own certified incidence lists. -/
theorem leafCount_graph_candidate
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (hLeft : (wallEdgesAssigned target wall candidate.right false).Nonempty)
    (hRight : (wallEdgesAssigned target wall candidate.right true).Nonempty) :
    leafCount (graph target wall candidate.right) = leafCount target := by
  obtain ⟨hOld, hFresh⟩ := M11SourceCandidates.candidate_target_valencies candidate
  have hL := length_leftEdges_eq_card wall candidate
  have hR := length_rightEdges_eq_card wall candidate
  have hLpos := Finset.card_pos.mpr hLeft
  have hRpos := Finset.card_pos.mpr hRight
  exact leafCount_graph_of_nonleaf_split wall candidate.right (by omega) (by omega)

end LeafCount

end DraismaVargas.Count.UnitWeightBalance
