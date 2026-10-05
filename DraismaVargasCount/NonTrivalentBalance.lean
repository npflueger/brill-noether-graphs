module

public import DraismaVargasCount.Multiplicity
public import DraismaVargasCount.TrivalentWeight
public import DraismaVargas.LocalCases.OuterWalk
public import DraismaVargas.LocalCases.IncomingTargetExpansion

@[expose] public section

/-!
# `lm:change-comb-type`(2): equal signed multiplicity across a non-trivalent limit

**Source.**  Vargas, Part II (arXiv:2609.09109), `lm:change-comb-type`: two full-dimensional
morphisms `φ_q`, `φ_{q'}` specializing to the same non-trivalent limit `φ₀` by contracting
`t₁` satisfy `k₁^{(q)} det A_{φ_q} = k₁^{(q')} det A_{φ_{q'}}` and, because
`d₁^{(q)} = k₁^{(q)}` while the other row denominators and the leaf count agree,
`Mult φ_q = Mult φ_{q'}`.

The determinant half is Part I's
`DraismaVargas.LocalCases.NonTrivalentLinkMatrix.corner_mul_det_eq` (the common
minor, from `AgreeOffColumn` and the two corner-supported rows).  This file is
the weight half and the assembly, stated on Part I's non-trivalent limit interface
`DraismaVargas.LocalCases.OuterWalk.WallData` / `TypeChangeLink`, which
`NonTrivalentValencyTwoBaseOneLink.link_all` inhabits at every wall of the walk with no
hypothesis -- so it covers valencies four, three and two at once, the valency-four `K = 0`
family among them, rather than one family at a time.

The corner arithmetic of §1 and the core identity of §2 are used by the type-change
analysis (`NonTrivalentCorner`, `NonTrivalentLeafNormalization`, `ValencyThreeTypeMatch`).
The balance across a type-change link is proved with no hypothesis in
`Count/NonTrivalentNonfacetDenominator.lean`
(`NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink`); the form in §4 below
carries three hypotheses.

## What is proved

**§1, the arithmetic of a corner-supported row (unconditional).**
* `rowDenominator_eq_den_corner` -- if row `r` of a presentation vanishes off the
  column `c`, then `d_r` is exactly the denominator of the corner entry
  `A r c`.  With a corner `1/k` this is the paper's `d₁ = k₁`, and
  `rowDenominator_eq_of_corner_eq_one_div` states it in that form: it is
  **proved here from the row's own support, not assumed and not taken from the
  trichotomy of `Count.EdgeDenominator`** -- the trichotomy gives divisibility, which is
  weaker than what the corner identity needs.
* `denominatorProduct_eq_corner_mul` -- `D_φ = d_r · ∏_{i ≠ r} d_i`, and
  `denominatorProduct_mul_corner` -- `D_φ · A r c = (∏_{i ≠ r} d_i) · num(A r c)`.
* `rowDenominator_eq_of_agree_of_den_eq`,
  `prod_rowDenominator_erase_eq_of_agree_of_den_eq` -- the reduction of "the
  other rows do not move" to a **per-row** statement at the wall column: two
  presentations agreeing off `c` have the same `d_i` at a row `i` as soon as
  their two entries in column `c` have the same denominator.
* `matrix_eq_one_div_of_occurrences_eq_singleton`,
  `num_eq_one_of_occurrences_eq_singleton`,
  `rowDenominator_eq_index_of_occurrences_eq_singleton` -- a length-matrix entry
  is `∑ 1/|e|` over the occurrences of its row above its column
  (`LocalCases.StableSourceMatrix.matrix`), so a **single** occurrence displays
  the entry as `1/k`, its numerator as `1`, and -- if the row is supported on
  that column -- the row denominator as exactly `k`.  This is the source's "the
  only non-zero entry of that row is `1/k₁^{(q)}`" and its `d₁ = k₁`.

**§2, the core identity (unconditional, case-independent).**
* `signedMult_eq_of_weightedCorner` -- from `AgreeOffColumn`, the two
  corner-supported rows, a nonzero incoming corner and the single hypothesis
  `W_out · c_out = W_in · c_in` (with `W = D_φ / 2^{l(T)}` the weight of
  `Count.signedMult`), the two signed multiplicities are **equal**.  This is
  `corner_mul_det_eq` multiplied by the weights, exactly as in the source.
* `weightedCorner_eq_of_rows` -- that hypothesis from the paper's three
  ingredients: equal leaf counts, equal `∏_{i ≠ r} d_i`, equal corner numerators.
* `signedMult_eq_of_rows`, `absMult_eq_of_rows` -- the two composed, and
  `signedMult_eq_of_reciprocal_corners` / `absMult_eq_of_reciprocal_corners`
  with the corners displayed as `1/k_in`, `1/k_out`.

**§3, leaf counts.**
* `leafCount_of_cfGraphIso`, `leafCount_graph_eq_of_nonleaf` -- the leaf-count
  tools: `l(T)` is a graph-isomorphism invariant, and two splittings of one wall
  that leave both copies non-monovalent have the same leaf count.

**§4, on Part I's non-trivalent limit interface.**
* `rowDenominator_incoming_facet`, `rowDenominator_outgoing_facet` -- `d₁ = k₁`
  for the incoming and the outgoing member of *every* `TypeChangeLink`, with no
  hypothesis: both vanishing rows are supported on the contracted column
  (`WallData.incomingMatrix_facet_eq_zero`,
  `TypeChangeLink.outgoingMatrix_facet_eq_zero`).
* `signedMult_eq_of_typeChangeLink` -- the outgoing member's signed multiplicity equals the
  incoming member's, given the three named hypotheses `hLeaf`, `hOther`, `hNum` below.
  `absMult_eq_...`, `signedMult_eq_of_typeChangeLink_of_reciprocal_corners` and
  `signedMult_eq_of_typeChangeLink_of_simple_corner` are its corollaries; the
  last replaces `hNum` by "each member's contracted row has exactly one
  occurrence above the contracted target occurrence".
* `leafCount_outgoing_eq_incoming` -- the hypothesis `hLeaf` reduced to four
  geometric facts about the two splittings of the wall vertex (the outgoing
  candidate puts an old occurrence on each side; neither endpoint of the
  contracted occurrence is a leaf of the incoming target).  The reduction uses
  `IncomingTargetExpansion.graphIso`: the incoming target *is* the contracted
  target re-expanded, so both members' targets are expansions of one graph at
  one vertex.

## The three hypotheses of `signedMult_eq_of_typeChangeLink`

1. `hLeaf : leafCount (outgoing target) = leafCount wd.coverTarget`.
   `leafCount_outgoing_eq_incoming` reduces it to: the outgoing candidate
   assigns at least one old wall occurrence to each side, and neither endpoint
   of the contracted occurrence is a leaf of the incoming target.  The second
   half is **not vacuous**: Part II itself splits the case, `k₁` being `1/2`
   when `t₁` is incident to a leaf, so a leaf-incident contraction needs its own corner
   bookkeeping and is not covered here.
2. `hOther : ∏_{i ≠ facet} d_i^{out} = ∏_{i ≠ facet} d_i^{in}`.
   `AgreeOffColumn` gives the two matrices equal *off* the contracted column
   only, and `Count.rowDenominator` is the l.c.m. over the **whole** row, so this
   does not follow from the agreement (the regrown entries are not integral in general).
   `prod_rowDenominator_erase_eq_of_agree_of_den_eq` reduces it to: for each row
   other than the contracted one, the two entries in the contracted column have
   the same denominator.  Nothing here supplies that.
3. `hNum : num (outgoing corner) = num (incoming corner)`, i.e. both corner
   entries are reciprocals of positive integers (`1/k₁^{(q)}`, `1/k₁^{(q')}`).
   The interface gives only `0 < corner` (`WallData.incoming_corner_pos`,
   `TypeChangeLink.corner_pos`).
   `signedMult_eq_of_typeChangeLink_of_simple_corner` reduces it, with no
   hypothesis of its own, to: *each member's contracted row has exactly one
   occurrence above the contracted target occurrence*
   (`LocalCases.StableSourceMatrix.occurrences … = {e}`).  That is the shape
   `Count.RowGeodesic.occurrences_eq_singleton_of_genusZero` produces, but that
   theorem carries `RowRamificationAtMostOne` and `DanglingEdgeNoGlue`, neither of
   which the interface supplies, so the step is not taken here.

`NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink` proves the same balance
without any of the three.

Beyond those: nothing here is conditional on integrality of a multiplicity, on
oddness, or on the genus or degree of the source.  No member, limit or star is
constructed.  No new structure is introduced, so there is nothing to witness for
non-vacuity beyond Part I's `WallData`/`TypeChangeLink`, whose inhabitants are
`OuterWalk.nonempty_wallData_caterpillar` and
`NonTrivalentValencyTwoBaseOneLink.link_all`.

## Consumers

The type counts across non-trivalent limits, which need `Mult φ_q = Mult φ_{q'}` across
the limit before they can count types; they feed the type changes (step 3 of the
genus-six assembly).
-/

namespace DraismaVargas.Count.NonTrivalentBalance

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.NonTrivalentLinkMatrix
open DraismaVargas.Count.TrivalentWeight (leafIndicator leafIndicator_eq_zero leafCount_graph)

/-! ## 1.  The arithmetic of a corner-supported row -/

section Arithmetic

variable {targetIn targetOut : CFGraph} {degIn degOut : ℕ}
  {dataIn : GluingDatum targetIn degIn} {dataOut : GluingDatum targetOut degOut}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`d_r` is the denominator of the corner entry**, for a row supported on a
single column.  Every other entry of the row is `0`, whose denominator is `1`. -/
theorem rowDenominator_eq_den_corner
    (p : dataIn.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hrow : ∀ c, c ≠ col → matrix p row c = 0) :
    rowDenominator p row = (matrix p row col).den := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine Finset.lcm_dvd ?_
    intro j _
    by_cases hj : j = col
    · subst hj
      exact dvd_rfl
    · rw [hrow j hj]
      simp
  · exact den_dvd_commonDenominator _ _ (Finset.mem_univ col)

/-- **The paper's `d₁ = k₁`**, read off the corner entry `1/k₁`. -/
theorem rowDenominator_eq_of_corner_eq_one_div
    (p : dataIn.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hrow : ∀ c, c ≠ col → matrix p row c = 0) {k : ℕ} (hk : 0 < k)
    (hcorner : matrix p row col = 1 / (k : ℚ)) :
    rowDenominator p row = k := by
  rw [rowDenominator_eq_den_corner p hrow, hcorner, one_div, Rat.inv_natCast_den_of_pos hk]

/-- The numerator of a reciprocal of a positive natural number is `1`. -/
theorem num_eq_one_of_eq_one_div {q : ℚ} {k : ℕ} (hk : 0 < k) (h : q = 1 / (k : ℚ)) :
    q.num = 1 := by
  rw [h, one_div, Rat.inv_natCast_num_of_pos hk]

/-- `D_φ = d_r · ∏_{i ≠ r} d_i`. -/
theorem denominatorProduct_eq_corner_mul
    (p : dataIn.LengthMatrixPresentation coordinate) (row : coordinate) :
    denominatorProduct p =
      rowDenominator p row * ∏ i ∈ Finset.univ.erase row, rowDenominator p i :=
  (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ row)).symm

/-- **The denominator-weighted corner** of a corner-supported row: `D_φ · A r c`
is `(∏_{i ≠ r} d_i) · num (A r c)`. -/
theorem denominatorProduct_mul_corner
    (p : dataIn.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hrow : ∀ c, c ≠ col → matrix p row c = 0) :
    (denominatorProduct p : ℚ) * matrix p row col =
      (∏ i ∈ Finset.univ.erase row, rowDenominator p i : ℕ) *
        ((matrix p row col).num : ℚ) := by
  rw [denominatorProduct_eq_corner_mul p row, rowDenominator_eq_den_corner p hrow]
  push_cast
  rw [mul_comm ((matrix p row col).den : ℚ), mul_assoc, Rat.den_mul_eq_num]

/-- **Off the wall column the row denominators are decided by one entry.**  Two
presentations agreeing off `col` have the same `d_i` at a row `i` as soon as
their entries in the column `col` have the same denominator. -/
theorem rowDenominator_eq_of_agree_of_den_eq
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {col : coordinate}
    (hagree : AgreeOffColumn (matrix pIn) (matrix pOut) col) (row : coordinate)
    (hden : (matrix pOut row col).den = (matrix pIn row col).den) :
    rowDenominator pOut row = rowDenominator pIn row := by
  unfold rowDenominator commonDenominator
  refine Finset.lcm_congr rfl ?_
  intro j _
  by_cases hj : j = col
  · subst hj
    exact hden
  · rw [← hagree row j hj]

/-- The product over the other rows, from the same input. -/
theorem prod_rowDenominator_erase_eq_of_agree_of_den_eq
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {col : coordinate}
    (hagree : AgreeOffColumn (matrix pIn) (matrix pOut) col) (row : coordinate)
    (hden : ∀ i, i ≠ row → (matrix pOut i col).den = (matrix pIn i col).den) :
    ∏ i ∈ Finset.univ.erase row, rowDenominator pOut i =
      ∏ i ∈ Finset.univ.erase row, rowDenominator pIn i := by
  refine Finset.prod_congr rfl ?_
  intro i hi
  exact rowDenominator_eq_of_agree_of_den_eq pIn pOut hagree i
    (hden i (Finset.mem_erase.mp hi).1)

end Arithmetic

/-! ### A matrix entry carried by a single occurrence -/

section SingleOccurrence

open DraismaVargas.LocalCases.W4StableSource (StableLengthMatrixLabelling)

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **An entry carried by one occurrence is the reciprocal of its index.**  A
length-matrix entry is the sum of `1/|e|` over the occurrences of its row above
its column (`StableSourceMatrix.matrix`), so a singleton occurrence set displays
the entry as `1/k`. -/
theorem matrix_eq_one_div_of_occurrences_eq_singleton
    (labelling : StableLengthMatrixLabelling data coordinate) (row col : coordinate)
    {edge : data.SourceEdge}
    (hocc : StableSourceMatrix.occurrences data (labelling.row.symm row)
      (labelling.targetEdge col) = {edge}) :
    matrix labelling.presentation row col = 1 / (data.sourceEdgeIndex edge : ℚ) := by
  rw [StableSourceMatrix.labelling_matrix_eq]
  show (∑ e ∈ StableSourceMatrix.occurrences data (labelling.row.symm row)
    (labelling.targetEdge col), (1 : ℚ) / data.sourceEdgeIndex e) = _
  rw [hocc, Finset.sum_singleton]

/-- Hence its numerator is `1`: this is the paper's "the only non-zero entry of
that row is `1/k₁`". -/
theorem num_eq_one_of_occurrences_eq_singleton
    (labelling : StableLengthMatrixLabelling data coordinate) (row col : coordinate)
    {edge : data.SourceEdge}
    (hocc : StableSourceMatrix.occurrences data (labelling.row.symm row)
      (labelling.targetEdge col) = {edge}) :
    (matrix labelling.presentation row col).num = 1 :=
  num_eq_one_of_eq_one_div (data.sourceEdgeIndex_pos edge)
    (matrix_eq_one_div_of_occurrences_eq_singleton labelling row col hocc)

/-- And its row denominator, if the row is supported on that column, is exactly
that index -- the paper's `d₁ = k₁`. -/
theorem rowDenominator_eq_index_of_occurrences_eq_singleton
    (labelling : StableLengthMatrixLabelling data coordinate) {row col : coordinate}
    (hrow : ∀ c, c ≠ col → matrix labelling.presentation row c = 0)
    {edge : data.SourceEdge}
    (hocc : StableSourceMatrix.occurrences data (labelling.row.symm row)
      (labelling.targetEdge col) = {edge}) :
    rowDenominator labelling.presentation row = data.sourceEdgeIndex edge :=
  rowDenominator_eq_of_corner_eq_one_div _ hrow (data.sourceEdgeIndex_pos edge)
    (matrix_eq_one_div_of_occurrences_eq_singleton labelling row col hocc)

end SingleOccurrence

/-! ## 2.  The core identity -/

section Core

variable {targetIn targetOut : CFGraph} {degIn degOut : ℕ}
  {dataIn : GluingDatum targetIn degIn} {dataOut : GluingDatum targetOut degOut}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The weight `D_φ / 2^{l(T)}` of `Count.signedMult`. -/
noncomputable def weight {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    (p : data.LengthMatrixPresentation coordinate) : ℚ :=
  (denominatorProduct p : ℚ) / 2 ^ leafCount target

theorem weight_pos {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    (p : data.LengthMatrixPresentation coordinate) : 0 < weight p := by
  have hnum : (0 : ℚ) < (denominatorProduct p : ℚ) := by
    exact_mod_cast denominatorProduct_pos p
  unfold weight
  positivity

theorem signedMult_eq_weight_mul {target : CFGraph} {degree : ℕ}
    {data : GluingDatum target degree} (p : data.LengthMatrixPresentation coordinate) :
    signedMult p = weight p * (matrix p).det := rfl

/-- **The core of `lm:change-comb-type`(2).**  Multiplying the common-minor
identity `corner_mul_det_eq` by the two weights: if the *denominator-weighted
corners* agree then the signed multiplicities agree.  Nothing is assumed about
either member beyond the two corner-supported rows and a nonzero incoming
corner. -/
theorem signedMult_eq_of_weightedCorner
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hagree : AgreeOffColumn (matrix pIn) (matrix pOut) col)
    (hrowIn : ∀ c, c ≠ col → matrix pIn row c = 0)
    (hrowOut : ∀ c, c ≠ col → matrix pOut row c = 0)
    (hcornerIn : matrix pIn row col ≠ 0)
    (hweighted : weight pOut * matrix pOut row col = weight pIn * matrix pIn row col) :
    signedMult pOut = signedMult pIn := by
  have hminor := corner_mul_det_eq hagree hrowIn hrowOut
  refine mul_right_cancel₀ hcornerIn ?_
  calc signedMult pOut * matrix pIn row col
      = weight pOut * (matrix pIn row col * (matrix pOut).det) := by
        rw [signedMult_eq_weight_mul]; ring
    _ = weight pOut * (matrix pOut row col * (matrix pIn).det) := by rw [hminor]
    _ = (weight pOut * matrix pOut row col) * (matrix pIn).det := by ring
    _ = (weight pIn * matrix pIn row col) * (matrix pIn).det := by rw [hweighted]
    _ = signedMult pIn * matrix pIn row col := by
        rw [signedMult_eq_weight_mul]; ring

/-- **The paper's three ingredients give the weighted-corner identity**: equal
leaf counts, equal denominator products off the contracted row, equal corner
numerators. -/
theorem weightedCorner_eq_of_rows
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hrowIn : ∀ c, c ≠ col → matrix pIn row c = 0)
    (hrowOut : ∀ c, c ≠ col → matrix pOut row c = 0)
    (hleaf : leafCount targetOut = leafCount targetIn)
    (hother : ∏ i ∈ Finset.univ.erase row, rowDenominator pOut i =
      ∏ i ∈ Finset.univ.erase row, rowDenominator pIn i)
    (hnum : (matrix pOut row col).num = (matrix pIn row col).num) :
    weight pOut * matrix pOut row col = weight pIn * matrix pIn row col := by
  have hOut : (denominatorProduct pOut : ℚ) * matrix pOut row col =
      (∏ i ∈ Finset.univ.erase row, rowDenominator pOut i : ℕ) *
        ((matrix pOut row col).num : ℚ) :=
    denominatorProduct_mul_corner pOut hrowOut
  have hIn : (denominatorProduct pIn : ℚ) * matrix pIn row col =
      (∏ i ∈ Finset.univ.erase row, rowDenominator pIn i : ℕ) *
        ((matrix pIn row col).num : ℚ) :=
    denominatorProduct_mul_corner pIn hrowIn
  have hpow : (2 : ℚ) ^ leafCount targetOut = 2 ^ leafCount targetIn := by rw [hleaf]
  unfold weight
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, hOut, hIn, hother, hnum, hpow]

/-- **`lm:change-comb-type`(2), assembled**: equal signed multiplicity across a
non-trivalent limit. -/
theorem signedMult_eq_of_rows
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hagree : AgreeOffColumn (matrix pIn) (matrix pOut) col)
    (hrowIn : ∀ c, c ≠ col → matrix pIn row c = 0)
    (hrowOut : ∀ c, c ≠ col → matrix pOut row c = 0)
    (hcornerIn : matrix pIn row col ≠ 0)
    (hleaf : leafCount targetOut = leafCount targetIn)
    (hother : ∏ i ∈ Finset.univ.erase row, rowDenominator pOut i =
      ∏ i ∈ Finset.univ.erase row, rowDenominator pIn i)
    (hnum : (matrix pOut row col).num = (matrix pIn row col).num) :
    signedMult pOut = signedMult pIn :=
  signedMult_eq_of_weightedCorner pIn pOut hagree hrowIn hrowOut hcornerIn
    (weightedCorner_eq_of_rows pIn pOut hrowIn hrowOut hleaf hother hnum)

/-- The unsigned form. -/
theorem absMult_eq_of_rows
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hagree : AgreeOffColumn (matrix pIn) (matrix pOut) col)
    (hrowIn : ∀ c, c ≠ col → matrix pIn row c = 0)
    (hrowOut : ∀ c, c ≠ col → matrix pOut row c = 0)
    (hcornerIn : matrix pIn row col ≠ 0)
    (hleaf : leafCount targetOut = leafCount targetIn)
    (hother : ∏ i ∈ Finset.univ.erase row, rowDenominator pOut i =
      ∏ i ∈ Finset.univ.erase row, rowDenominator pIn i)
    (hnum : (matrix pOut row col).num = (matrix pIn row col).num) :
    absMult pOut = absMult pIn := by
  unfold absMult
  rw [signedMult_eq_of_rows pIn pOut hagree hrowIn hrowOut hcornerIn hleaf hother hnum]

/-- The same with the corners displayed as `1/k₁^{(q)}`, `1/k₁^{(q')}`, which is
how the source writes them; the row denominators `d₁ = k₁` are then **proved**,
not assumed. -/
theorem signedMult_eq_of_reciprocal_corners
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hagree : AgreeOffColumn (matrix pIn) (matrix pOut) col)
    (hrowIn : ∀ c, c ≠ col → matrix pIn row c = 0)
    (hrowOut : ∀ c, c ≠ col → matrix pOut row c = 0)
    {kIn kOut : ℕ} (hkIn : 0 < kIn) (hkOut : 0 < kOut)
    (hcornerIn : matrix pIn row col = 1 / (kIn : ℚ))
    (hcornerOut : matrix pOut row col = 1 / (kOut : ℚ))
    (hleaf : leafCount targetOut = leafCount targetIn)
    (hother : ∏ i ∈ Finset.univ.erase row, rowDenominator pOut i =
      ∏ i ∈ Finset.univ.erase row, rowDenominator pIn i) :
    signedMult pOut = signedMult pIn := by
  refine signedMult_eq_of_rows pIn pOut hagree hrowIn hrowOut ?_ hleaf hother ?_
  · rw [hcornerIn]
    exact one_div_ne_zero (by exact_mod_cast hkIn.ne')
  · rw [num_eq_one_of_eq_one_div hkOut hcornerOut, num_eq_one_of_eq_one_div hkIn hcornerIn]

/-- The unsigned form, with reciprocal corners. -/
theorem absMult_eq_of_reciprocal_corners
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hagree : AgreeOffColumn (matrix pIn) (matrix pOut) col)
    (hrowIn : ∀ c, c ≠ col → matrix pIn row c = 0)
    (hrowOut : ∀ c, c ≠ col → matrix pOut row c = 0)
    {kIn kOut : ℕ} (hkIn : 0 < kIn) (hkOut : 0 < kOut)
    (hcornerIn : matrix pIn row col = 1 / (kIn : ℚ))
    (hcornerOut : matrix pOut row col = 1 / (kOut : ℚ))
    (hleaf : leafCount targetOut = leafCount targetIn)
    (hother : ∏ i ∈ Finset.univ.erase row, rowDenominator pOut i =
      ∏ i ∈ Finset.univ.erase row, rowDenominator pIn i) :
    absMult pOut = absMult pIn := by
  unfold absMult
  rw [signedMult_eq_of_reciprocal_corners pIn pOut hagree hrowIn hrowOut hkIn hkOut
    hcornerIn hcornerOut hleaf hother]

end Core

/-! ## 3.  Leaf counts -/

section Leaves

universe u

/-- **`l(T)` is a graph-isomorphism invariant.**  The occurrence bijection of
`GluingTransport.edgeEquiv` carries incident occurrences to incident
occurrences. -/
theorem leafCount_of_cfGraphIso {G H : CFGraph.{u}} (iso : Utilities.CFGraphIso G H) :
    leafCount H = leafCount G := by
  classical
  have hleaf : ∀ y : H.V, IsLeafVertex H y ↔ IsLeafVertex G (iso.vertexEquiv.symm y) := by
    intro y
    unfold IsLeafVertex
    rw [GluingTransport.incidentEdges_map iso y, Finset.card_map]
  have hmap : leafVertices H = (leafVertices G).map iso.vertexEquiv.toEmbedding := by
    ext y
    rw [Finset.mem_map_equiv, mem_leafVertices, mem_leafVertices]
    exact hleaf y
  rw [leafCount, leafCount, hmap, Finset.card_map]

/-- **Two splittings of one wall with no monovalent copy have the same leaf
count.**  The leaf indicator of the wall vertex cancels between the two
instances of `TrivalentWeight.leafCount_graph`. -/
theorem leafCount_graph_eq_of_nonleaf {C : CFGraph} (w : C.V)
    (first second : C.edges → Bool)
    (h1o : (GluingDatum.incidentEdges (target := graph C w first)
      (oldVertex C w)).card ≠ 1)
    (h1f : (GluingDatum.incidentEdges (target := graph C w first)
      (freshVertex C)).card ≠ 1)
    (h2o : (GluingDatum.incidentEdges (target := graph C w second)
      (oldVertex C w)).card ≠ 1)
    (h2f : (GluingDatum.incidentEdges (target := graph C w second)
      (freshVertex C)).card ≠ 1) :
    leafCount (graph C w first) = leafCount (graph C w second) := by
  have e1 := leafCount_graph w first
  have e2 := leafCount_graph w second
  rw [leafIndicator_eq_zero _ _ h1o, leafIndicator_eq_zero _ _ h1f] at e1
  rw [leafIndicator_eq_zero _ _ h2o, leafIndicator_eq_zero _ _ h2f] at e2
  omega

end Leaves

/-! ## 4.  On Part I's non-trivalent limit interface -/

section Landed

open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.LocalCases.FullDimensionalSource

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {degree : ℕ} {ambient : Infrastructure.CubicDarts.CubicDartGraph D V}
  {label : D → coordinate} {m : ambient.MoveData}
  {arrival : FacetArrival degree ambient label (label m.base)}
  {wd : WallData arrival} (link : TypeChangeLink m wd)

/-- **`d₁ = k₁` for the incoming member**, with no hypothesis: its vanishing row
is supported on the contracted column, so its row denominator is the denominator
of the corner entry. -/
theorem rowDenominator_incoming_facet :
    rowDenominator wd.fullDim.labelling.presentation (label m.base) =
      (wd.incomingMatrix (label m.base) wd.column).den :=
  rowDenominator_eq_den_corner _ (fun c hc ↦ wd.incomingMatrix_facet_eq_zero c hc)

/-- **`d₁ = k₁` for the outgoing member**, with no hypothesis. -/
theorem rowDenominator_outgoing_facet :
    rowDenominator link.outgoingFD.labelling.presentation (label m.base) =
      (link.outgoingMatrix (label m.base) wd.column).den :=
  rowDenominator_eq_den_corner _ (fun c hc ↦ link.outgoingMatrix_facet_eq_zero c hc)

/-- **Equal signed multiplicity across a type-change link, from three hypotheses.**
Across any type-change link -- that is, across any non-trivalent limit of the walk, at
valency four, three or two alike -- the outgoing member's signed multiplicity equals the
incoming member's, given the three hypotheses `hLeaf`, `hOther`, `hNum` named in this
module's header.  `NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink` proves
the same with no hypothesis. -/
theorem signedMult_eq_of_typeChangeLink
    (hLeaf : leafCount (graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        link.candidate.right) = leafCount wd.coverTarget)
    (hOther : ∏ i ∈ Finset.univ.erase (label m.base),
        rowDenominator link.outgoingFD.labelling.presentation i =
      ∏ i ∈ Finset.univ.erase (label m.base),
        rowDenominator wd.fullDim.labelling.presentation i)
    (hNum : (link.outgoingMatrix (label m.base) wd.column).num =
      (wd.incomingMatrix (label m.base) wd.column).num) :
    fdSignedMult link.outgoingFD = fdSignedMult wd.fullDim :=
  signedMult_eq_of_rows _ _ link.agree
    (fun c hc ↦ wd.incomingMatrix_facet_eq_zero c hc)
    (fun c hc ↦ link.outgoingMatrix_facet_eq_zero c hc)
    wd.incoming_corner_ne_zero hLeaf hOther hNum

/-- The unsigned form. -/
theorem absMult_eq_of_typeChangeLink
    (hLeaf : leafCount (graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        link.candidate.right) = leafCount wd.coverTarget)
    (hOther : ∏ i ∈ Finset.univ.erase (label m.base),
        rowDenominator link.outgoingFD.labelling.presentation i =
      ∏ i ∈ Finset.univ.erase (label m.base),
        rowDenominator wd.fullDim.labelling.presentation i)
    (hNum : (link.outgoingMatrix (label m.base) wd.column).num =
      (wd.incomingMatrix (label m.base) wd.column).num) :
    fdAbsMult link.outgoingFD = fdAbsMult wd.fullDim :=
  congrArg abs (signedMult_eq_of_typeChangeLink link hLeaf hOther hNum)

/-- The same with the two corners displayed as `1/k₁^{(q)}` and `1/k₁^{(q')}`,
which is how the source writes them; the hypothesis `hNum` is then discharged and
`rowDenominator_incoming_facet` / `rowDenominator_outgoing_facet` read
`d₁^{(q)} = k₁^{(q)}`. -/
theorem signedMult_eq_of_typeChangeLink_of_reciprocal_corners
    {kIn kOut : ℕ} (hkIn : 0 < kIn) (hkOut : 0 < kOut)
    (hcornerIn : wd.incomingMatrix (label m.base) wd.column = 1 / (kIn : ℚ))
    (hcornerOut : link.outgoingMatrix (label m.base) wd.column = 1 / (kOut : ℚ))
    (hLeaf : leafCount (graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        link.candidate.right) = leafCount wd.coverTarget)
    (hOther : ∏ i ∈ Finset.univ.erase (label m.base),
        rowDenominator link.outgoingFD.labelling.presentation i =
      ∏ i ∈ Finset.univ.erase (label m.base),
        rowDenominator wd.fullDim.labelling.presentation i) :
    fdSignedMult link.outgoingFD = fdSignedMult wd.fullDim :=
  signedMult_eq_of_reciprocal_corners _ _ link.agree
    (fun c hc ↦ wd.incomingMatrix_facet_eq_zero c hc)
    (fun c hc ↦ link.outgoingMatrix_facet_eq_zero c hc)
    hkIn hkOut hcornerIn hcornerOut hLeaf hOther

/-- **The hypothesis `hLeaf`, reduced.**  The incoming target *is* the contracted
target re-expanded at the same vertex (`IncomingTargetExpansion.graphIso`), so
both members' targets are splittings of one graph at one vertex and the leaf
counts agree as soon as neither splitting leaves a monovalent copy of the wall.
The two outgoing conditions are what
`Count.UnitWeightBalance.leafCount_graph_candidate` reads off a candidate's own
certified incidence lists; the two incoming conditions say that neither endpoint
of the contracted occurrence is a leaf of the incoming target. -/
theorem leafCount_outgoing_eq_incoming
    (hOutOld : (GluingDatum.incidentEdges
      (target := graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        link.candidate.right)
      (oldVertex _ ⟨wd.a, wd.hab⟩)).card ≠ 1)
    (hOutFresh : (GluingDatum.incidentEdges
      (target := graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        link.candidate.right)
      (freshVertex _)).card ≠ 1)
    (hInOld : (GluingDatum.incidentEdges
      (target := graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        (IncomingTargetExpansion.right wd.hc wd.hab wd.hOne))
      (oldVertex _ ⟨wd.a, wd.hab⟩)).card ≠ 1)
    (hInFresh : (GluingDatum.incidentEdges
      (target := graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        (IncomingTargetExpansion.right wd.hc wd.hab wd.hOne))
      (freshVertex _)).card ≠ 1) :
    leafCount (graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        link.candidate.right) = leafCount wd.coverTarget := by
  rw [leafCount_of_cfGraphIso
    (IncomingTargetExpansion.graphIso wd.hc wd.hab wd.hOne)]
  exact leafCount_graph_eq_of_nonleaf _ _ _ hOutOld hOutFresh hInOld hInFresh

/-- **The hypothesis `hNum`, reduced to the paper's own sentence.**  If the
contracted row of each member has exactly one occurrence above the contracted
target occurrence -- so that its sole nonzero entry is `1/k₁^{(q)}` -- then the
corner numerators are both `1` and `hNum` is discharged.  This is the shape
`Count.RowGeodesic.occurrences_eq_singleton_of_genusZero` produces, modulo that
theorem's `RowRamificationAtMostOne` hypothesis. -/
theorem signedMult_eq_of_typeChangeLink_of_simple_corner
    {edgeIn : wd.cover.SourceEdge} {edgeOut : link.candidate.datum.SourceEdge}
    (hoccIn : StableSourceMatrix.occurrences wd.cover
      (wd.fullDim.labelling.row.symm (label m.base))
      (wd.fullDim.labelling.targetEdge wd.column) = {edgeIn})
    (hoccOut : StableSourceMatrix.occurrences link.candidate.datum
      (link.outgoingFD.labelling.row.symm (label m.base))
      (link.outgoingFD.labelling.targetEdge wd.column) = {edgeOut})
    (hLeaf : leafCount (graph (contract wd.coverTarget wd.hab wd.hOne) ⟨wd.a, wd.hab⟩
        link.candidate.right) = leafCount wd.coverTarget)
    (hOther : ∏ i ∈ Finset.univ.erase (label m.base),
        rowDenominator link.outgoingFD.labelling.presentation i =
      ∏ i ∈ Finset.univ.erase (label m.base),
        rowDenominator wd.fullDim.labelling.presentation i) :
    fdSignedMult link.outgoingFD = fdSignedMult wd.fullDim :=
  signedMult_eq_of_typeChangeLink link hLeaf hOther
    ((num_eq_one_of_occurrences_eq_singleton _ _ _ hoccOut).trans
      (num_eq_one_of_occurrences_eq_singleton _ _ _ hoccIn).symm)

end Landed

end DraismaVargas.Count.NonTrivalentBalance
