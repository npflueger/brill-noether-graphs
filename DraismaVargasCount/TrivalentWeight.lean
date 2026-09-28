import DraismaVargasCount.Multiplicity
import DraismaVargas.LocalCases.W2M1kLimitColumns

/-!
# The weight identification in the representative trivalent case

**Source.**  Vargas, Part II (arXiv:2609.09109), Proposition
`prop-signed-mult` (1) and its proof: at a codimension-one limit with
trivalent `H(φ₀)` the signed determinantal multiplicities of the
full-dimensional morphisms specialising to it sum to zero.  The proof is
carried out there on the representative case `{w2-r2-nd3-M-1k}`, whose
determinant relation is Equation (7) of Draisma--Vargas Part I
(arXiv:1909.12924), with Figure 33, formalized as
`DraismaVargas.LocalCases.W2M1kCommonBalance.LimitColumns.determinant_balance`
and `canonical_determinant_balance` and inhabited unconditionally by
`DraismaVargas.LocalCases.W2M1kLimitColumns.limitColumns`.

The Lean determinant balance is **twice** Part II's: Part I's Equation (7) is
`1·c⁽¹⁾ + 2(k-1)·c⁽²⁾ + 2(k+1)·c⁽³⁾ = 0`, while the proof in Part II writes
`½·c⁽¹⁾ + (k-1)·c⁽²⁾ + (k+1)·c⁽³⁾ = 0`.  Consequently the weight ratio proved
here carries that factor two in the denominator:

    weight q · (D₀ / 2^{l(T₀)+1})  =  D_q / 2^{l(T_q)}          (q = 0, 1, 2)

with `weight = ![1, 2(k-1), 2(k+1)]` the weight vector of
`W2M1kCommonBalance.LimitColumns.family`, `D₀` the denominator product of the
**incoming codimension-one** matrix `A₀` and `l(T₀) = leafCount target`.  Part
II's normalisation `weight q · D₀/2^{l(T₀)} = D_q/2^{l(T_q)}` is this identity
with its weights halved.

## What is proved

* `commonDenominator_option`, `commonDenominator_equiv`, and
  **`lcm_den_add_unit_inv`** -- the arithmetic crux: if a row's common
  denominator `d` is a multiple of `a` and coprime to `b`, then perturbing one
  entry by `±1/(ab)` multiplies the row's common denominator by exactly `b`.
* `incomingRowDenominator`, `incomingDenominatorProduct` -- the paper's
  `d_{0,i}` and `D₀`, read off `StableSourceMatrix.matrix`, which is the
  rectangular matrix the codimension-one limit actually has.  The square
  `Count.rowDenominator` of `DraismaVargasCount.Multiplicity` cannot be used
  there.
* `incomingRowDenominator_dvd_of_forall_index_dvd` and
  `dvd_incomingRowDenominator_of_occurrences_eq_singleton` -- the rectangular
  analogues of the two halves of `Count.EdgeDenominator`'s case (b), and
  `incomingRowDenominator_eq_of_index_dvd_of_simple`, their combination.
* `rowDenominator_member` -- **unconditional**: each member's row denominator
  is `lcm` of the incoming one with the denominator of its single regrown
  entry.  Only the agreement of the retained columns with `A₀` enters.
* `secondNewColumn_eq`, `thirdNewColumn_eq` -- **unconditional**: Figure 33's
  regrown columns are the old `t₂`, `t₃` columns of `A₀` perturbed by
  `+1/(k(k-1))` on `e₂`'s row, resp. `-1/(k(k+1))` on `e₃`'s row, and nowhere
  else.  `firstNewColumn_den` -- `M⁽¹⁾`'s regrown column is integral.
* `denominatorProduct_zero` -- **unconditional**: `D⁽¹⁾ = D₀`.
  `denominatorProduct_one`, `denominatorProduct_two` -- `D⁽²⁾ = (k-1)·D₀` and
  `D⁽³⁾ = (k+1)·D₀`, given the two incoming row denominators below.
* `card_incidentEdges_graph`, `card_incidentEdges_oldVertex`,
  `card_incidentEdges_wall_split`, `leafCount_graph` -- **unconditional**
  leaf-count arithmetic for `TargetExpansion.graph`, and
  `leafCount_graph_of_leaf_split` / `leafCount_graph_of_divalent_split`.
* `leafCount_member_zero/one/two` -- **unconditional, on the family Part I
  constructs**: `l(T⁽¹⁾) = l(T₀) + 1` and `l(T⁽²⁾) = l(T⁽³⁾) = l(T₀)`, in both
  orientations of `W2M1kLimitColumns.limitColumns`.  The regrown column really
  does change the leaf count by one, and only at `M⁽¹⁾`, because Base I.a's
  retained wall copy is monovalent
  (`W2M1kSourceCandidates.leaf_target_valencies`) while the other two splits
  are divalent/divalent.
* `weight_zero_eq_ratio`, `weight_one_eq_ratio`, `weight_two_eq_ratio` -- the
  weight identification, one position at a time.
* `sum_signedMult_eq_zero` -- `Σ_q Mult φ_q = 0` for any inhabitant of
  `LimitColumns`, and `sum_signedMult_limitColumns_eq_zero`,
  `sum_signedMult_limitColumns_eq_zero_of_sharp`,
  `sum_signedMult_canonical_eq_zero` -- the same on the family
  `W2M1kLimitColumns.limitColumns` actually builds, in the last case with no
  supplied square labelling.

## What is not proved here: the two hypotheses

`sum_signedMult_canonical_eq_zero` assumes

    incomingRowDenominator data (secondRow profile) = shape.k
    incomingRowDenominator data (thirdRow profile)  = shape.k

that is, `lemma-edge-deno` (b) in its **sharp** form on rows `h₂` and `h₃` of
the **incoming codimension-one matrix `A₀`** -- not on any member.  The weaker
`sum_signedMult_limitColumns_eq_zero` shows exactly what is used: `k ∣ d₀` (the
lower half) and `Nat.Coprime (k∓1) d₀` (implied by the upper half `d₀ ∣ k`).
Neither half is proved here:

* the **lower** half needs a simple column, `occurrences data (secondRow
  profile) (star.edge profile.doubleLabel) = {profile.second.1}`, i.e. that no
  background occurrence of the incoming wall lies on `e₂`'s stable row above
  `t₂`.  `W2M1kCommonBalance.double_matrix_decomposition` splits that fibre as
  `{e₁, e₂} ∪ backgroundOccurrences`, and nothing here makes the background
  part empty (`DraismaVargasCount.IncomingSimpleColumn` obtains `k ∣ d₀` on
  these two rows without it, from `e₂` and `e₃` lying on different incoming
  stable rows);
* the **upper** half needs `∀ e ∈ incomingRowEdges data (secondRow profile),
  sourceEdgeIndex e ∣ k`, an instance of the global index pattern of a stable
  row along its ordered walk (compare `Count.EdgeDenominator`'s
  `RowIndexConstant`), which is not constructed here.

Both halves are needed for the *statement*, not merely for this proof: if
`d₀(h₂) = k·m` with `gcd(m, k-1) > 1` then `D⁽²⁾/D⁽¹⁾ ≠ k-1` and the signed
multiplicities do not sum to zero.

Nothing here is conditional on integrality of the multiplicity, on the genus,
on the degree, or on nonsingularity of any member.

## Non-vacuity

Every statement below is about the family
`W2M1kLimitColumns.limitColumns input shape hConnected hGenus`, which
`W2M1kLimitColumns.nonempty_limitColumns` inhabits unconditionally on the
case's actual input, in both orientations; no abstract family satisfying named
hypotheses is used, and no new structure is introduced.

## Use

This is the balancing identity of Part I, Equation (7), in multiplicity form:
the representative case of Part II's proof of `prop-signed-mult` (1), for the
trivalent walls (step 2 of `DraismaVargasCount.Assembly`).  The other trivalent
wall types reuse its case-independent parts -- the denominator arithmetic of
§1--§2 and the leaf counts of §6 (see `DraismaVargasCount.UnitWeightBalance`).
The two hypotheses above are the sharp form of `lemma-edge-deno` (b) and the
global index pattern of a stable row.
-/

namespace DraismaVargas.Count.TrivalentWeight

open DraismaVargas.Infrastructure
open DraismaVargas.Count

/-! ## 1. Generic denominator arithmetic -/

theorem commonDenominator_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℚ) :
    commonDenominator Finset.univ (fun i ↦ f (e i)) = commonDenominator Finset.univ f := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun i _ ↦ ?_
    exact den_dvd_commonDenominator Finset.univ f (Finset.mem_univ (e i))
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun j _ ↦ ?_
    have := den_dvd_commonDenominator Finset.univ (fun i ↦ f (e i))
      (Finset.mem_univ (e.symm j))
    simpa using this

theorem commonDenominator_option {ι : Type*} [Fintype ι] (f : Option ι → ℚ) :
    commonDenominator Finset.univ f =
      Nat.lcm (f none).den (commonDenominator Finset.univ (fun i ↦ f (some i))) := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine (commonDenominator_dvd_iff _ _ _).mpr fun o _ ↦ ?_
    cases o with
    | none => exact Nat.dvd_lcm_left _ _
    | some i =>
        exact dvd_trans (den_dvd_commonDenominator Finset.univ (fun i ↦ f (some i))
          (Finset.mem_univ i)) (Nat.dvd_lcm_right _ _)
  · refine Nat.lcm_dvd (den_dvd_commonDenominator Finset.univ f (Finset.mem_univ none)) ?_
    refine (commonDenominator_dvd_iff _ _ _).mpr fun i _ ↦ ?_
    exact den_dvd_commonDenominator Finset.univ f (Finset.mem_univ (some i))

theorem natCast_dvd_of_integral_div {m n : ℕ} (hn : 0 < n)
    (h : Integral ((m : ℚ) / (n : ℚ))) : n ∣ m := by
  obtain ⟨z, hz⟩ := h
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℚ) = (z : ℚ) * (n : ℚ) := by
    field_simp at hz
    linarith
  have hInt : (m : ℤ) = z * (n : ℤ) := by exact_mod_cast this
  exact Int.natCast_dvd_natCast.mp ⟨z, by rw [hInt]; ring⟩


theorem lcm_den_eq_right {d : ℕ} {q : ℚ} (h : q.den ∣ d) : Nat.lcm q.den d = d :=
  Nat.dvd_antisymm (Nat.lcm_dvd h dvd_rfl) (Nat.dvd_lcm_right _ _)

/-- **The arithmetic crux of the weight identification.**  Adding `±1/(ab)` to
one entry of a row whose common denominator `d` is a multiple of `a` and is
coprime to `b` multiplies that row's common denominator by exactly `b`. -/
theorem lcm_den_add_unit_inv {ι : Type*} [Fintype ι] (g : ι → ℚ) (j : ι)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {c : ℤ} (hc : c = 1 ∨ c = -1)
    (hA : a ∣ commonDenominator Finset.univ g)
    (hCop : Nat.Coprime b (commonDenominator Finset.univ g)) :
    Nat.lcm (g j + (c : ℚ) / ((a : ℚ) * (b : ℚ))).den
        (commonDenominator Finset.univ g) =
      b * commonDenominator Finset.univ g := by
  set d := commonDenominator Finset.univ g with hdDef
  set n : ℚ := g j + (c : ℚ) / ((a : ℚ) * (b : ℚ)) with hnDef
  have hdPos : 0 < d := commonDenominator_pos _ _
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  obtain ⟨e, he⟩ := hA
  have hde : (d : ℚ) = (a : ℚ) * (e : ℚ) := by exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℚ)) he
  obtain ⟨w, hw⟩ := integral_commonDenominator_mul (Finset.univ : Finset ι) g (Finset.mem_univ j)
  -- upper bound
  have h1 : ((b * d : ℕ) : ℚ) * n = (b : ℚ) * ((d : ℚ) * g j) + (c : ℚ) * (e : ℚ) := by
    rw [hnDef]
    push_cast
    rw [hde]
    field_simp
  have hInt1 : Integral (((b * d : ℕ) : ℚ) * n) :=
    ⟨(b : ℤ) * w + c * (e : ℤ), by rw [h1, hw]; push_cast; ring⟩
  have hUpper : n.den ∣ b * d := den_dvd_of_integral_mul n hInt1
  -- lower bound
  obtain ⟨m, hm⟩ : Integral ((n.den : ℚ) * n) := integral_mul_of_den_dvd n dvd_rfl
  have h2 : ((d * n.den : ℕ) : ℚ) / ((a * b : ℕ) : ℚ) =
      (c : ℚ) * ((d : ℚ) * ((n.den : ℚ) * n) - (n.den : ℚ) * ((d : ℚ) * g j)) := by
    rw [hnDef]
    push_cast
    field_simp
    rcases hc with rfl | rfl <;> ring
  have hInt2 : Integral (((d * n.den : ℕ) : ℚ) / ((a * b : ℕ) : ℚ)) := by
    refine ⟨c * ((d : ℤ) * m - (n.den : ℤ) * w), ?_⟩
    rw [h2, hm, hw]
    push_cast
    ring
  have habPos : 0 < a * b := Nat.mul_pos ha hb
  have hab : a * b ∣ d * n.den := natCast_dvd_of_integral_div habPos hInt2
  have hbd : b ∣ d * n.den := dvd_trans (Dvd.intro_left a rfl) hab
  have hbden : b ∣ n.den := hCop.dvd_of_dvd_mul_left hbd
  refine Nat.dvd_antisymm (Nat.lcm_dvd hUpper (dvd_mul_left d b)) ?_
  exact hCop.mul_dvd_of_dvd_of_dvd (dvd_trans hbden (Nat.dvd_lcm_left _ _))
    (Nat.dvd_lcm_right _ _)


/-! ## 2. The incoming row denominators and the members' row denominators -/

open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W2M1kCommonBalance
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.StableSourceMatrix
open DraismaVargas.LocalCases.W2M1kSourceCandidates
open DraismaVargas.Infrastructure.TargetExpansion

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : W2M1kSourceCandidates.Shape profile}

/-- `d_{0,i}`: the least common denominator of one row of the incoming
codimension-one matrix `A₀`.  `A₀` is rectangular, so this is read off
`StableSourceMatrix.matrix` and not off a square presentation. -/
noncomputable def incomingRowDenominator (data : GluingDatum target degree)
    (path : StablePath data) : ℕ :=
  commonDenominator Finset.univ (fun place ↦ StableSourceMatrix.matrix data path place)

/-- `D₀ = ∏ᵢ d_{0,i}`. -/
noncomputable def incomingDenominatorProduct (data : GluingDatum target degree) : ℕ :=
  ∏ path : StablePath data, incomingRowDenominator data path

theorem incomingRowDenominator_pos (path : StablePath data) :
    0 < incomingRowDenominator data path := commonDenominator_pos _ _

theorem den_dvd_incomingRowDenominator (path : StablePath data) (place : target.edges) :
    (StableSourceMatrix.matrix data path place).den ∣ incomingRowDenominator data path :=
  den_dvd_commonDenominator _ _ (Finset.mem_univ place)

/-- **Each member's row denominator is the incoming one, merged with the
denominator of the single regrown entry.**  Nothing but the agreement of the
retained columns with `A₀` enters. -/
theorem rowDenominator_member (limit : LimitColumns profile shape)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) (row : coordinate) :
    rowDenominator (limit.labelling initial position).presentation row =
      Nat.lcm (newColumn profile shape position
          ((limit.sourceCoordinates initial).symm row)).den
        (incomingRowDenominator data ((limit.sourceCoordinates initial).symm row)) := by
  classical
  have hEntry : ∀ column : coordinate,
      matrix (limit.labelling initial position).presentation row column =
        limit.commonMatrix position ((limit.sourceCoordinates initial).symm row)
          (limit.targetCoordinates initial column) :=
    fun column ↦ limit.squareMatrix_common initial position row column
  have hStep : rowDenominator (limit.labelling initial position).presentation row =
      commonDenominator Finset.univ
        (fun o : Option target.edges ↦
          limit.commonMatrix position ((limit.sourceCoordinates initial).symm row) o) := by
    rw [rowDenominator]
    rw [show (matrix (limit.labelling initial position).presentation row) =
        fun column ↦ limit.commonMatrix position
          ((limit.sourceCoordinates initial).symm row)
          (limit.targetCoordinates initial column) from funext hEntry]
    exact commonDenominator_equiv (limit.targetCoordinates initial) _
  rw [hStep, commonDenominator_option]
  congr 1
  · rw [limit.commonMatrix_new]
  · exact congrArg (commonDenominator Finset.univ)
      (funext fun place ↦ limit.commonMatrix_retained position _ place)


/-! ### The two halves of `lemma-edge-deno` (b) for an incoming row

These are the rectangular analogues of `Count.EdgeDenominator`'s
`rowDenominator_dvd_of_forall_index_dvd` and
`dvd_rowDenominator_of_rowFibre_eq_singleton`; those are stated for
a *square* `StableLengthMatrixLabelling`, which the codimension-one incoming
matrix does not have. -/

/-- The surviving occurrences displayed on one incoming stable row. -/
noncomputable def incomingRowEdges (data : GluingDatum target degree)
    (path : StablePath data) : Finset data.SourceEdge := by
  classical
  exact (Finset.univ : Finset data.SourceEdge).filter fun edge ↦
    ∃ hSurvives : ¬ IsDangling data edge,
      NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path

theorem mem_incomingRowEdges (path : StablePath data) (edge : data.SourceEdge) :
    edge ∈ incomingRowEdges data path ↔
      ∃ hSurvives : ¬ IsDangling data edge,
        NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data) = path := by
  classical
  simp [incomingRowEdges]

/-- **The upper half**: if every index on the incoming row divides `N` then so
does `d_{0,i}`. -/
theorem incomingRowDenominator_dvd_of_forall_index_dvd (path : StablePath data) {N : ℕ}
    (hIndex : ∀ edge ∈ incomingRowEdges data path, data.sourceEdgeIndex edge ∣ N) :
    incomingRowDenominator data path ∣ N := by
  classical
  refine commonDenominator_dvd_of_integral _ _ ?_
  intro place _
  show Integral ((N : ℚ) * ∑ edge ∈ StableSourceMatrix.occurrences data path place,
    (1 : ℚ) / data.sourceEdgeIndex edge)
  rw [Finset.mul_sum]
  refine integral_sum _ _ ?_
  intro edge hEdge
  obtain ⟨factor, hFactor⟩ := hIndex edge ((mem_incomingRowEdges path edge).mpr
    ((StableSourceMatrix.mem_occurrences path place edge).mp hEdge).1)
  refine ⟨factor, ?_⟩
  have hPos : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
    exact_mod_cast (GluingDatum.sourceEdgeIndex_pos data edge).ne'
  rw [hFactor]
  push_cast
  field_simp

/-- **The lower half**: a simple column of the incoming row forces its index to
divide `d_{0,i}`. -/
theorem dvd_incomingRowDenominator_of_occurrences_eq_singleton
    (path : StablePath data) (place : target.edges) {edge : data.SourceEdge}
    (hFibre : StableSourceMatrix.occurrences data path place = {edge}) :
    data.sourceEdgeIndex edge ∣ incomingRowDenominator data path := by
  classical
  have hInt : Integral ((incomingRowDenominator data path : ℚ) *
      StableSourceMatrix.matrix data path place) :=
    integral_commonDenominator_mul _ _ (Finset.mem_univ place)
  rw [show StableSourceMatrix.matrix data path place =
      ∑ e ∈ StableSourceMatrix.occurrences data path place,
        (1 : ℚ) / data.sourceEdgeIndex e from rfl, hFibre, Finset.sum_singleton] at hInt
  obtain ⟨value, hValue⟩ := hInt
  have hPos : (data.sourceEdgeIndex edge : ℚ) ≠ 0 := by
    exact_mod_cast (GluingDatum.sourceEdgeIndex_pos data edge).ne'
  have hRat : ((incomingRowDenominator data path : ℕ) : ℚ) =
      (data.sourceEdgeIndex edge : ℚ) * (value : ℚ) := by
    field_simp at hValue
    linarith
  have hInt' : ((incomingRowDenominator data path : ℕ) : ℤ) =
      ((data.sourceEdgeIndex edge : ℕ) : ℤ) * value := by exact_mod_cast hRat
  exact Int.natCast_dvd_natCast.mp ⟨value, hInt'⟩

/-- **`lemma-edge-deno` (b) for an incoming row**: the sharp value `d_{0,i} = k`
from the two halves.  The first hypothesis is an instance of the global index
pattern of a stable row; the second is a census fact about the incoming wall. -/
theorem incomingRowDenominator_eq_of_index_dvd_of_simple (path : StablePath data)
    (place : target.edges) {edge : data.SourceEdge} {index : ℕ}
    (hIndex : ∀ e ∈ incomingRowEdges data path, data.sourceEdgeIndex e ∣ index)
    (hFibre : StableSourceMatrix.occurrences data path place = {edge})
    (hEdgeIndex : data.sourceEdgeIndex edge = index) :
    incomingRowDenominator data path = index :=
  Nat.dvd_antisymm (incomingRowDenominator_dvd_of_forall_index_dvd path hIndex)
    (hEdgeIndex ▸ dvd_incomingRowDenominator_of_occurrences_eq_singleton path place hFibre)

/-! ## 3. Figure 33's three regrown columns, as `A₀` entries plus one correction -/

/-- `M⁽¹⁾`'s regrown column is integral at every row: its two surviving new
occurrences have index one. -/
theorem firstNewColumn_den (path : StablePath data) :
    (firstNewColumn profile path).den = 1 := by
  unfold firstNewColumn
  split_ifs <;> norm_num

/-- **`M⁽²⁾`'s regrown column is the old `t₂` column, corrected by `1/(k(k-1))`
on `e₂`'s row alone.**  The correction is `1/(k-1) - 1/k`, and the two
backgrounds cancel by `background_sum_eq`. -/
theorem secondNewColumn_eq (input : W2SourceInput data star)
    (shape : W2M1kSourceCandidates.Shape profile) (path : StablePath data) :
    secondNewColumn profile shape path =
      StableSourceMatrix.matrix data path (star.edge profile.doubleLabel) +
        (if path = secondRow profile then
          ((1 : ℤ) : ℚ) / ((shape.k : ℚ) * (((shape.k - 1 : ℕ)) : ℚ)) else 0) := by
  have hk : 1 < shape.k := shape.one_lt_k
  have hk0 : (shape.k : ℚ) ≠ 0 := by positivity
  have hk1 : ((shape.k - 1 : ℕ) : ℚ) = (shape.k : ℚ) - 1 := by
    have : ((shape.k - 1 : ℕ) : ℤ) = (shape.k : ℤ) - 1 := by omega
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) this
  have hk1' : (shape.k : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < (shape.k : ℚ) := by exact_mod_cast hk
    linarith
  rw [secondNewColumn, double_matrix_decomposition profile path,
    first_index_cast profile shape, second_index_cast profile shape,
    background_sum_eq profile input path 0 profile.doubleLabel, hk1]
  split_ifs <;> field_simp <;> ring

/-- **`M⁽³⁾`'s regrown column is the old `t₃` column, corrected by
`-1/(k(k+1))` on `e₃`'s row alone.** -/
theorem thirdNewColumn_eq (input : W2SourceInput data star)
    (shape : W2M1kSourceCandidates.Shape profile) (path : StablePath data) :
    thirdNewColumn profile shape path =
      StableSourceMatrix.matrix data path (star.edge profile.singleLabel) +
        (if path = thirdRow profile then
          ((-1 : ℤ) : ℚ) / ((shape.k : ℚ) * (((shape.k + 1 : ℕ)) : ℚ)) else 0) := by
  have hk : 1 < shape.k := shape.one_lt_k
  have hk0 : (shape.k : ℚ) ≠ 0 := by positivity
  have hk1 : ((shape.k + 1 : ℕ) : ℚ) = (shape.k : ℚ) + 1 := by push_cast; ring
  have hk1' : (shape.k : ℚ) + 1 ≠ 0 := by positivity
  rw [thirdNewColumn, single_matrix_decomposition profile path,
    third_index_cast profile shape,
    background_sum_eq profile input path 0 profile.singleLabel, hk1]
  split_ifs <;> field_simp <;> ring


/-! ## 4. The three members' row denominators -/

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **`M⁽¹⁾` changes no row denominator**: its regrown column is integral. -/
theorem rowDenominator_zero (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (row : coordinate) :
    rowDenominator (limit.labelling initial 0).presentation row =
      incomingRowDenominator data ((limit.sourceCoordinates initial).symm row) := by
  rw [rowDenominator_member limit initial 0 row, newColumn_zero, firstNewColumn_den,
    Nat.lcm_one_left]

/-- **`M⁽²⁾` changes no row denominator off `e₂`'s row.** -/
theorem rowDenominator_one_of_ne (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (row : coordinate)
    (hRow : (limit.sourceCoordinates initial).symm row ≠ secondRow profile) :
    rowDenominator (limit.labelling initial 1).presentation row =
      incomingRowDenominator data ((limit.sourceCoordinates initial).symm row) := by
  rw [rowDenominator_member limit initial 1 row, newColumn_one,
    secondNewColumn_eq input shape _, if_neg hRow, add_zero]
  exact lcm_den_eq_right (den_dvd_incomingRowDenominator _ _)

/-- **`M⁽²⁾` multiplies `e₂`'s row denominator by `k-1`**, given that the
incoming denominator of that row is a multiple of `k` and coprime to `k-1`. -/
theorem rowDenominator_one_at (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (row : coordinate)
    (hRow : (limit.sourceCoordinates initial).symm row = secondRow profile)
    (hDvd : shape.k ∣ incomingRowDenominator data (secondRow profile))
    (hCop : Nat.Coprime (shape.k - 1) (incomingRowDenominator data (secondRow profile))) :
    rowDenominator (limit.labelling initial 1).presentation row =
      (shape.k - 1) * incomingRowDenominator data (secondRow profile) := by
  have hk : 1 < shape.k := shape.one_lt_k
  rw [rowDenominator_member limit initial 1 row, newColumn_one,
    secondNewColumn_eq input shape _, if_pos hRow, hRow]
  exact lcm_den_add_unit_inv (fun place ↦ StableSourceMatrix.matrix data (secondRow profile) place)
    (star.edge profile.doubleLabel) (by omega) (by omega) (Or.inl rfl) hDvd hCop

/-- **`M⁽³⁾` changes no row denominator off `e₃`'s row.** -/
theorem rowDenominator_two_of_ne (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (row : coordinate)
    (hRow : (limit.sourceCoordinates initial).symm row ≠ thirdRow profile) :
    rowDenominator (limit.labelling initial 2).presentation row =
      incomingRowDenominator data ((limit.sourceCoordinates initial).symm row) := by
  rw [rowDenominator_member limit initial 2 row, newColumn_two,
    thirdNewColumn_eq input shape _, if_neg hRow, add_zero]
  exact lcm_den_eq_right (den_dvd_incomingRowDenominator _ _)

/-- **`M⁽³⁾` multiplies `e₃`'s row denominator by `k+1`.** -/
theorem rowDenominator_two_at (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (row : coordinate)
    (hRow : (limit.sourceCoordinates initial).symm row = thirdRow profile)
    (hDvd : shape.k ∣ incomingRowDenominator data (thirdRow profile))
    (hCop : Nat.Coprime (shape.k + 1) (incomingRowDenominator data (thirdRow profile))) :
    rowDenominator (limit.labelling initial 2).presentation row =
      (shape.k + 1) * incomingRowDenominator data (thirdRow profile) := by
  have hk : 1 < shape.k := shape.one_lt_k
  rw [rowDenominator_member limit initial 2 row, newColumn_two,
    thirdNewColumn_eq input shape _, if_pos hRow, hRow]
  exact lcm_den_add_unit_inv (fun place ↦ StableSourceMatrix.matrix data (thirdRow profile) place)
    (star.edge profile.singleLabel) (by omega) (by omega) (Or.inr rfl) hDvd hCop


/-! ## 5. The denominator products `D⁽ᵠ⁾` -/

open scoped Classical in
/-- **`D⁽¹⁾ = D₀`.**  Unconditional. -/
theorem denominatorProduct_zero (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    denominatorProduct (limit.labelling initial 0).presentation =
      incomingDenominatorProduct data := by
  rw [denominatorProduct, incomingDenominatorProduct,
    ← Equiv.prod_comp (limit.sourceCoordinates initial)
      (fun row ↦ rowDenominator (limit.labelling initial 0).presentation row)]
  refine Finset.prod_congr rfl fun path _ ↦ ?_
  rw [rowDenominator_zero limit initial, Equiv.symm_apply_apply]

open scoped Classical in
/-- **`D⁽²⁾ = (k-1) · D₀`**, given the incoming denominator of `e₂`'s row. -/
theorem denominatorProduct_one (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (hDvd : shape.k ∣ incomingRowDenominator data (secondRow profile))
    (hCop : Nat.Coprime (shape.k - 1) (incomingRowDenominator data (secondRow profile))) :
    denominatorProduct (limit.labelling initial 1).presentation =
      (shape.k - 1) * incomingDenominatorProduct data := by
  rw [denominatorProduct, incomingDenominatorProduct,
    ← Equiv.prod_comp (limit.sourceCoordinates initial)
      (fun row ↦ rowDenominator (limit.labelling initial 1).presentation row)]
  have hTerm : ∀ path : StablePath data,
      rowDenominator (limit.labelling initial 1).presentation
          (limit.sourceCoordinates initial path) =
        (if path = secondRow profile then shape.k - 1 else 1) *
          incomingRowDenominator data path := by
    intro path
    by_cases hPath : path = secondRow profile
    · rw [rowDenominator_one_at input limit initial _
        (by rw [Equiv.symm_apply_apply]; exact hPath) hDvd hCop, if_pos hPath, hPath]
    · rw [rowDenominator_one_of_ne input limit initial _
        (by rw [Equiv.symm_apply_apply]; exact hPath), Equiv.symm_apply_apply,
        if_neg hPath, one_mul]
  rw [Finset.prod_congr rfl fun path _ ↦ hTerm path, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ (secondRow profile) (fun _ ↦ shape.k - 1),
    if_pos (Finset.mem_univ _)]

open scoped Classical in
/-- **`D⁽³⁾ = (k+1) · D₀`**, given the incoming denominator of `e₃`'s row. -/
theorem denominatorProduct_two (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (hDvd : shape.k ∣ incomingRowDenominator data (thirdRow profile))
    (hCop : Nat.Coprime (shape.k + 1) (incomingRowDenominator data (thirdRow profile))) :
    denominatorProduct (limit.labelling initial 2).presentation =
      (shape.k + 1) * incomingDenominatorProduct data := by
  rw [denominatorProduct, incomingDenominatorProduct,
    ← Equiv.prod_comp (limit.sourceCoordinates initial)
      (fun row ↦ rowDenominator (limit.labelling initial 2).presentation row)]
  have hTerm : ∀ path : StablePath data,
      rowDenominator (limit.labelling initial 2).presentation
          (limit.sourceCoordinates initial path) =
        (if path = thirdRow profile then shape.k + 1 else 1) *
          incomingRowDenominator data path := by
    intro path
    by_cases hPath : path = thirdRow profile
    · rw [rowDenominator_two_at input limit initial _
        (by rw [Equiv.symm_apply_apply]; exact hPath) hDvd hCop, if_pos hPath, hPath]
    · rw [rowDenominator_two_of_ne input limit initial _
        (by rw [Equiv.symm_apply_apply]; exact hPath), Equiv.symm_apply_apply,
        if_neg hPath, one_mul]
  rw [Finset.prod_congr rfl fun path _ ↦ hTerm path, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ (thirdRow profile) (fun _ ↦ shape.k + 1),
    if_pos (Finset.mem_univ _)]


/-! ## 6. The leaf counts of the three expanded targets -/

/-- Splitting a sum off one distinguished point, for two families agreeing
away from it. -/
theorem sum_indicator_split {α : Type*} [Fintype α] [DecidableEq α] (a : α) (f g : α → ℕ)
    (h : ∀ x, x ≠ a → f x = g x) : (∑ x, f x) + g a = (∑ x, g x) + f a := by
  have h1 := Finset.add_sum_erase (Finset.univ : Finset α) f (Finset.mem_univ a)
  have h2 := Finset.add_sum_erase (Finset.univ : Finset α) g (Finset.mem_univ a)
  have h3 : ∑ x ∈ (Finset.univ : Finset α).erase a, f x =
      ∑ x ∈ (Finset.univ : Finset α).erase a, g x :=
    Finset.sum_congr rfl fun x hx ↦ h x (Finset.ne_of_mem_erase hx)
  omega

section LeafCount

variable {target : CFGraph} (wall : target.V)

open scoped Classical in
/-- The incidence count in an expanded target, split into the new edge and
the old occurrences. -/
theorem card_incidentEdges_graph (right : target.edges → Bool) (v : Vertex target) :
    (GluingDatum.incidentEdges (target := graph target wall right) v).card =
      (if (newEnds target wall).1 = v ∨ (newEnds target wall).2 = v then 1 else 0) +
        ((Finset.univ : Finset target.edges).filter fun e ↦
          (oldEnds target wall right e).1 = v ∨ (oldEnds target wall right e).2 = v).card := by
  unfold GluingDatum.incidentEdges
  rw [Finset.card_filter, ← Equiv.sum_comp (occurrenceEquiv target wall right),
    Fintype.sum_option, Finset.card_filter]
  simp only [occurrenceEquiv_none, occurrenceEquiv_some]
  congr 1
  · exact if_congr Iff.rfl rfl rfl
  · exact Finset.sum_congr rfl fun x _ ↦ if_congr Iff.rfl rfl rfl

open scoped Classical in
/-- Away from the wall an old vertex keeps its incidence count. -/
theorem card_incidentEdges_oldVertex (right : target.edges → Bool)
    {v : target.V} (hne : v ≠ wall) :
    (GluingDatum.incidentEdges
        (target := graph target wall right) (oldVertex target v)).card =
      (GluingDatum.incidentEdges (target := target) v).card := by
  have hNew : ¬ ((newEnds target wall).1 = oldVertex target v ∨
      (newEnds target wall).2 = oldVertex target v) := by
    rintro (h | h)
    · exact hne (congrArg (contractVertex target wall) h).symm
    · exact Sum.inr_ne_inl h
  refine (card_incidentEdges_graph wall right (oldVertex target v)).trans ?_
  rw [if_neg hNew, zero_add]
  refine congrArg Finset.card (Finset.filter_congr fun e _ ↦ ?_)
  exact or_congr (expandedEndpoint_eq_oldVertex_iff_of_ne target wall right e _ v hne)
    (expandedEndpoint_eq_oldVertex_iff_of_ne target wall right e _ v hne)

open scoped Classical in
/-- The two copies of the wall share the new edge and split the old wall
occurrences between them. -/
theorem card_incidentEdges_wall_split (right : target.edges → Bool) :
    (GluingDatum.incidentEdges
        (target := graph target wall right) (oldVertex target wall)).card +
      (GluingDatum.incidentEdges
        (target := graph target wall right) (freshVertex target)).card =
      (GluingDatum.incidentEdges (target := target) wall).card + 2 := by
  have hOldCard := card_incidentEdges_graph wall right (oldVertex target wall)
  have hFreshCard := card_incidentEdges_graph wall right (freshVertex target)
  have hPosOld : (newEnds target wall).1 = oldVertex target wall ∨
      (newEnds target wall).2 = oldVertex target wall := Or.inl rfl
  have hPosFresh : (newEnds target wall).1 = freshVertex target ∨
      (newEnds target wall).2 = freshVertex target := Or.inr rfl
  rw [if_pos hPosOld] at hOldCard
  rw [if_pos hPosFresh] at hFreshCard
  have hOldFilter : ((Finset.univ : Finset target.edges).filter fun e ↦
      (oldEnds target wall right e).1 = oldVertex target wall ∨
        (oldEnds target wall right e).2 = oldVertex target wall).card =
      ((GluingDatum.incidentEdges (target := target) wall).filter
        fun e ↦ right e = false).card := by
    refine congrArg Finset.card ?_
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      oldEnds_incident_oldVertex_iff target wall right e, GluingDatum.incidentEdges]
  have hFreshFilter : ((Finset.univ : Finset target.edges).filter fun e ↦
      (oldEnds target wall right e).1 = freshVertex target ∨
        (oldEnds target wall right e).2 = freshVertex target).card =
      ((GluingDatum.incidentEdges (target := target) wall).filter
        fun e ↦ right e = true).card := by
    refine congrArg Finset.card ?_
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      oldEnds_incident_freshVertex_iff target wall right e, GluingDatum.incidentEdges]
  have hEq : ((GluingDatum.incidentEdges (target := target) wall).filter
        fun e ↦ ¬ (right e = false)) =
      (GluingDatum.incidentEdges (target := target) wall).filter fun e ↦ right e = true := by
    ext e
    cases hb : right e <;> simp [hb]
  have hCards := Finset.card_filter_add_card_filter_not
    (s := GluingDatum.incidentEdges (target := target) wall) (p := fun e ↦ right e = false)
  rw [hEq] at hCards
  omega

/-- The leaf indicator of a vertex, packaged so that its decidability
instance is fixed at the definition site. -/
noncomputable def leafIndicator (G : CFGraph) (v : G.V) : ℕ :=
  if IsLeafVertex G v then 1 else 0

theorem leafIndicator_eq_one (G : CFGraph) (v : G.V)
    (h : (GluingDatum.incidentEdges v).card = 1) : leafIndicator G v = 1 :=
  if_pos h

theorem leafIndicator_eq_zero (G : CFGraph) (v : G.V)
    (h : (GluingDatum.incidentEdges v).card ≠ 1) : leafIndicator G v = 0 :=
  if_neg h

theorem leafCount_eq_sum_leafIndicator (G : CFGraph) :
    leafCount G = ∑ v, leafIndicator G v := by
  rw [leafCount, leafVertices, Finset.card_filter]
  rfl

/-- **Splitting the wall moves the leaf count by the two new valencies.** -/
theorem leafCount_graph (right : target.edges → Bool) :
    leafCount (graph target wall right) + leafIndicator target wall =
      leafCount target +
        leafIndicator (graph target wall right) (oldVertex target wall) +
        leafIndicator (graph target wall right) (freshVertex target) := by
  have hLeafG : leafCount (graph target wall right) =
      (∑ v : target.V, leafIndicator (graph target wall right) (oldVertex target v)) +
        leafIndicator (graph target wall right) (freshVertex target) := by
    rw [leafCount_eq_sum_leafIndicator]
    exact sum_vertices target wall right (leafIndicator (graph target wall right))
  have hLeafT := leafCount_eq_sum_leafIndicator target
  have hOld : ∀ v : target.V, v ≠ wall →
      leafIndicator (graph target wall right) (oldVertex target v) = leafIndicator target v := by
    intro v hv
    by_cases hc : (GluingDatum.incidentEdges (target := target) v).card = 1
    · rw [leafIndicator_eq_one (graph target wall right) (oldVertex target v)
        (by rw [card_incidentEdges_oldVertex wall right hv]; exact hc),
        leafIndicator_eq_one target v hc]
    · rw [leafIndicator_eq_zero (graph target wall right) (oldVertex target v)
        (by rw [card_incidentEdges_oldVertex wall right hv]; exact hc),
        leafIndicator_eq_zero target v hc]
  have hSplit := sum_indicator_split wall
    (fun v ↦ leafIndicator (graph target wall right) (oldVertex target v))
    (fun v ↦ leafIndicator target v) hOld
  omega

/-- **`M⁽¹⁾`'s target has one more leaf**: Base I.a regrows the new edge at a
target leaf, so the retained copy of the wall is monovalent. -/
theorem leafCount_graph_of_leaf_split (right : target.edges → Bool)
    (hOld : (GluingDatum.incidentEdges
      (target := graph target wall right) (oldVertex target wall)).card = 1)
    (hFresh : (GluingDatum.incidentEdges
      (target := graph target wall right) (freshVertex target)).card = 3) :
    leafCount (graph target wall right) = leafCount target + 1 := by
  have hSplit := card_incidentEdges_wall_split wall right
  have hWall : leafIndicator target wall = 0 :=
    leafIndicator_eq_zero _ _ (by omega)
  have hOldInd : leafIndicator (graph target wall right) (oldVertex target wall) = 1 :=
    leafIndicator_eq_one _ _ hOld
  have hFreshInd : leafIndicator (graph target wall right) (freshVertex target) = 0 :=
    leafIndicator_eq_zero _ _ (by omega)
  have h := leafCount_graph wall right
  omega

/-- **`M⁽²⁾` and `M⁽³⁾` leave the leaf count alone**: both copies of the wall
stay divalent. -/
theorem leafCount_graph_of_divalent_split (right : target.edges → Bool)
    (hOld : (GluingDatum.incidentEdges
      (target := graph target wall right) (oldVertex target wall)).card = 2)
    (hFresh : (GluingDatum.incidentEdges
      (target := graph target wall right) (freshVertex target)).card = 2) :
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

end LeafCount


/-! ## 7. The balancing identity for the multiplicities -/

section Balance

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : W2M1kSourceCandidates.Shape profile}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The signed multiplicities of Figure 33's three members sum to zero.**

The three remaining hypotheses are exactly the geometric inputs: the three
target leaf counts (discharged below on the constructed family) and, for `e₂`'s
and `e₃`'s row of the incoming codimension-one matrix, that its denominator is
a multiple of `k` and coprime to `k∓1`.  Both are implied by
`lemma-edge-deno` (b) on those two rows, `d_{0,2} = d_{0,3} = k`. -/
theorem sum_signedMult_eq_zero (input : W2SourceInput data star)
    (limit : LimitColumns profile shape)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (hLeaf0 : leafCount (graph target wall (limit.member 0).right) = leafCount target + 1)
    (hLeaf1 : leafCount (graph target wall (limit.member 1).right) = leafCount target)
    (hLeaf2 : leafCount (graph target wall (limit.member 2).right) = leafCount target)
    (hDvd2 : shape.k ∣ incomingRowDenominator data (secondRow profile))
    (hCop2 : Nat.Coprime (shape.k - 1) (incomingRowDenominator data (secondRow profile)))
    (hDvd3 : shape.k ∣ incomingRowDenominator data (thirdRow profile))
    (hCop3 : Nat.Coprime (shape.k + 1) (incomingRowDenominator data (thirdRow profile))) :
    ∑ position : Fin 3, signedMult (limit.labelling initial position).presentation = 0 := by
  have hk : 1 < shape.k := shape.one_lt_k
  have hcast1 : ((shape.k - 1 : ℕ) : ℚ) = (shape.k : ℚ) - 1 := by
    have : ((shape.k - 1 : ℕ) : ℤ) = (shape.k : ℤ) - 1 := by omega
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) this
  have hcast2 : ((shape.k + 1 : ℕ) : ℚ) = (shape.k : ℚ) + 1 := by push_cast; ring
  have hBal := limit.determinant_balance input initial
  have hPow : (2 : ℚ) ^ leafCount target ≠ 0 := by positivity
  set D : ℚ := (incomingDenominatorProduct data : ℚ) with hD
  set d0 : ℚ := (limit.squareMatrix initial 0).det with hd0
  set d1 : ℚ := (limit.squareMatrix initial 1).det with hd1
  set d2 : ℚ := (limit.squareMatrix initial 2).det with hd2
  have hExpand : ∑ position : Fin 3,
      signedMult (limit.labelling initial position).presentation =
      (D / 2 ^ leafCount target / 2) *
        (1 * d0 + 2 * ((shape.k : ℚ) - 1) * d1 + 2 * ((shape.k : ℚ) + 1) * d2) := by
    rw [Fin.sum_univ_three]
    show (denominatorProduct (limit.labelling initial 0).presentation : ℚ) /
          2 ^ leafCount (graph target wall (limit.member 0).right) * d0 +
        (denominatorProduct (limit.labelling initial 1).presentation : ℚ) /
          2 ^ leafCount (graph target wall (limit.member 1).right) * d1 +
        (denominatorProduct (limit.labelling initial 2).presentation : ℚ) /
          2 ^ leafCount (graph target wall (limit.member 2).right) * d2 = _
    rw [denominatorProduct_zero limit initial,
      denominatorProduct_one input limit initial hDvd2 hCop2,
      denominatorProduct_two input limit initial hDvd3 hCop3,
      hLeaf0, hLeaf1, hLeaf2]
    push_cast [hcast1, hcast2]
    rw [← hD]
    field_simp
    ring
  rw [hExpand, hBal, mul_zero]

end Balance


/-! ### The weight identification itself -/

section Weights

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : W2M1kSourceCandidates.Shape profile}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (input : W2SourceInput data star) (limit : LimitColumns profile shape)
  (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)

/-- **Equation (7)'s first weight is the multiplicity ratio.**  `1 = weight 0`
of `LimitColumns.family`. -/
theorem weight_zero_eq_ratio
    (hLeaf0 : leafCount (graph target wall (limit.member 0).right) = leafCount target + 1) :
    (1 : ℚ) * ((incomingDenominatorProduct data : ℚ) / 2 ^ (leafCount target + 1)) =
      (denominatorProduct (limit.labelling initial 0).presentation : ℚ) /
        2 ^ leafCount (graph target wall (limit.member 0).right) := by
  rw [denominatorProduct_zero limit initial, hLeaf0, one_mul]

include input in
/-- **Equation (7)'s second weight is the multiplicity ratio**, given `e₂`'s
incoming row denominator.  `2(k-1) = weight 1`. -/
theorem weight_one_eq_ratio
    (hLeaf1 : leafCount (graph target wall (limit.member 1).right) = leafCount target)
    (hDvd2 : shape.k ∣ incomingRowDenominator data (secondRow profile))
    (hCop2 : Nat.Coprime (shape.k - 1) (incomingRowDenominator data (secondRow profile))) :
    (2 * ((shape.k : ℚ) - 1)) *
        ((incomingDenominatorProduct data : ℚ) / 2 ^ (leafCount target + 1)) =
      (denominatorProduct (limit.labelling initial 1).presentation : ℚ) /
        2 ^ leafCount (graph target wall (limit.member 1).right) := by
  have hk : 1 < shape.k := shape.one_lt_k
  have hcast1 : ((shape.k - 1 : ℕ) : ℚ) = (shape.k : ℚ) - 1 := by
    have : ((shape.k - 1 : ℕ) : ℤ) = (shape.k : ℤ) - 1 := by omega
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) this
  have hPow : (2 : ℚ) ^ leafCount target ≠ 0 := by positivity
  rw [denominatorProduct_one input limit initial hDvd2 hCop2, hLeaf1]
  push_cast [hcast1]
  field_simp
  ring

include input in
/-- **Equation (7)'s third weight is the multiplicity ratio**, given `e₃`'s
incoming row denominator.  `2(k+1) = weight 2`. -/
theorem weight_two_eq_ratio
    (hLeaf2 : leafCount (graph target wall (limit.member 2).right) = leafCount target)
    (hDvd3 : shape.k ∣ incomingRowDenominator data (thirdRow profile))
    (hCop3 : Nat.Coprime (shape.k + 1) (incomingRowDenominator data (thirdRow profile))) :
    (2 * ((shape.k : ℚ) + 1)) *
        ((incomingDenominatorProduct data : ℚ) / 2 ^ (leafCount target + 1)) =
      (denominatorProduct (limit.labelling initial 2).presentation : ℚ) /
        2 ^ leafCount (graph target wall (limit.member 2).right) := by
  have hk : 1 < shape.k := shape.one_lt_k
  have hcast2 : ((shape.k + 1 : ℕ) : ℚ) = (shape.k : ℚ) + 1 := by push_cast; ring
  have hPow : (2 : ℚ) ^ leafCount target ≠ 0 := by positivity
  rw [denominatorProduct_two input limit initial hDvd3 hCop3, hLeaf2]
  push_cast [hcast2]
  field_simp
  ring

end Weights

/-! ## 8. The leaf counts and the balance on the constructed family -/

section Constructed

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Base I.a's candidate regrows at a target leaf. -/
theorem leafCount_leafPair_candidate (input : W2SourceInput data star)
    (shape : W2M1kSourceCandidates.Shape profile) (pair : LeafPair profile) :
    leafCount (graph target wall (LeafPair.candidate input shape pair).right) =
      leafCount target + 1 :=
  leafCount_graph_of_leaf_split wall _
    (W2M1kSourceCandidates.leaf_target_valencies input shape pair).1
    (W2M1kSourceCandidates.leaf_target_valencies input shape pair).2

/-- Base II.2.2.M's candidate regrows at a divalent pair. -/
theorem leafCount_dividedData_candidate (shape : W2M1kSourceCandidates.Shape profile)
    (divided : DividedData profile) :
    leafCount (graph target wall (DividedData.candidate shape divided).right) =
      leafCount target :=
  leafCount_graph_of_divalent_split wall _
    (W2M1kSourceCandidates.divided_target_valencies shape divided).1
    (W2M1kSourceCandidates.divided_target_valencies shape divided).2

/-- Base II.1.M's candidate regrows at a divalent pair. -/
theorem leafCount_joined_candidate (geometry : GlobalM1k.Geometry data wall) :
    leafCount (graph target wall (joinedCandidate star geometry).right) = leafCount target :=
  leafCount_graph_of_divalent_split wall _
    (W2M1kSourceCandidates.joined_target_valencies geometry).1
    (W2M1kSourceCandidates.joined_target_valencies geometry).2

/-! ### The same, read off the five member constructors -/

theorem leafCount_localLeafMember (input : W2SourceInput data star)
    (shape : W2M1kSourceCandidates.Shape profile) (pair : LeafPair profile) :
    leafCount (graph target wall
        (W2M1kLimitColumns.localLeafMember input shape pair).right) =
      leafCount target + 1 :=
  leafCount_leafPair_candidate input shape pair

theorem leafCount_remoteLeafMember (input : W2SourceInput data star)
    (shape : W2M1kSourceCandidates.Shape profile) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (pair : LeafPair (W2M1kTransport.swapProfile profile input.valid.1 other hOther)) :
    leafCount (graph target wall
        (W2M1kLimitColumns.remoteLeafMember input shape other hOther pair).right) =
      leafCount target + 1 :=
  leafCount_leafPair_candidate (W2M1kTransport.swapInput input other hOther)
    (W2M1kTransport.swapShape shape input.valid.1 other hOther) pair

theorem leafCount_localDividedMember (input : W2SourceInput data star)
    (shape : W2M1kSourceCandidates.Shape profile) (divided : DividedData profile) :
    leafCount (graph target wall
        (W2M1kLimitColumns.localDividedMember input shape divided).right) =
      leafCount target :=
  leafCount_dividedData_candidate shape divided

theorem leafCount_remoteDividedMember (input : W2SourceInput data star)
    (shape : W2M1kSourceCandidates.Shape profile) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (divided : DividedData (W2M1kTransport.swapProfile profile input.valid.1 other hOther)) :
    leafCount (graph target wall
        (W2M1kLimitColumns.remoteDividedMember input shape other hOther divided).right) =
      leafCount target :=
  leafCount_dividedData_candidate
    (W2M1kTransport.swapShape shape input.valid.1 other hOther) divided

theorem leafCount_joinedMember (input : W2SourceInput data star)
    (shape : W2M1kSourceCandidates.Shape profile)
    (geometry : GlobalM1k.Geometry data wall) :
    leafCount (graph target wall
        (W2M1kLimitColumns.joinedMember input shape geometry).right) = leafCount target :=
  leafCount_joined_candidate geometry

variable (input : W2SourceInput data star) (shape : W2M1kSourceCandidates.Shape profile)
  (hConnected : graph_connected target) (hGenus : genus target = 0)

/-- `M⁽¹⁾`'s expanded target has one more leaf, on the actual constructed
family, in either orientation. -/
theorem leafCount_member_zero :
    leafCount (graph target wall
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).member 0).right) =
      leafCount target + 1 := by
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [W2M1kLimitColumns.limitColumns_eq_alignedOrientation input shape hConnected hGenus
      hAligned, W2M1kLimitColumns.alignedOrientation_member_zero]
    exact leafCount_localLeafMember _ _ _
  · rw [W2M1kLimitColumns.limitColumns_eq_separatedOrientation input shape hConnected hGenus
      hAligned, W2M1kLimitColumns.separatedOrientation_member_zero]
    exact leafCount_remoteLeafMember _ _ _ _ _

/-- `M⁽²⁾`'s expanded target has the same leaf count. -/
theorem leafCount_member_one :
    leafCount (graph target wall
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).member 1).right) =
      leafCount target := by
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [W2M1kLimitColumns.limitColumns_eq_alignedOrientation input shape hConnected hGenus
      hAligned, W2M1kLimitColumns.alignedOrientation_member_one]
    exact leafCount_remoteDividedMember _ _ _ _ _
  · rw [W2M1kLimitColumns.limitColumns_eq_separatedOrientation input shape hConnected hGenus
      hAligned, W2M1kLimitColumns.separatedOrientation_member_one]
    exact leafCount_localDividedMember _ _ _

/-- `M⁽³⁾`'s expanded target has the same leaf count. -/
theorem leafCount_member_two :
    leafCount (graph target wall
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).member 2).right) =
      leafCount target := by
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [W2M1kLimitColumns.limitColumns_eq_alignedOrientation input shape hConnected hGenus
      hAligned, W2M1kLimitColumns.alignedOrientation_member_two]
    exact leafCount_joinedMember _ _ _
  · rw [W2M1kLimitColumns.limitColumns_eq_separatedOrientation input shape hConnected hGenus
      hAligned, W2M1kLimitColumns.separatedOrientation_member_two]
    exact leafCount_joinedMember _ _ _

/-- **Proposition `prop-signed-mult` (1) for `{w2-r2-nd3-M-1k}`, on the family
Part I actually constructs.**  Its only hypotheses beyond the data of the
family concern the two incoming row denominators. -/
theorem sum_signedMult_limitColumns_eq_zero
    (initial : StableLengthMatrixLabelling
      ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    (hDvd2 : shape.k ∣ incomingRowDenominator data (secondRow profile))
    (hCop2 : Nat.Coprime (shape.k - 1) (incomingRowDenominator data (secondRow profile)))
    (hDvd3 : shape.k ∣ incomingRowDenominator data (thirdRow profile))
    (hCop3 : Nat.Coprime (shape.k + 1) (incomingRowDenominator data (thirdRow profile))) :
    ∑ position : Fin 3, signedMult
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).labelling
          initial position).presentation = 0 :=
  sum_signedMult_eq_zero input _ initial
    (leafCount_member_zero input shape hConnected hGenus)
    (leafCount_member_one input shape hConnected hGenus)
    (leafCount_member_two input shape hConnected hGenus) hDvd2 hCop2 hDvd3 hCop3

/-- The same with the sharp `lemma-edge-deno` (b) value `d₀ = k` on `e₂`'s and
`e₃`'s incoming rows, which is the form Part II's proof states. -/
theorem sum_signedMult_limitColumns_eq_zero_of_sharp
    (initial : StableLengthMatrixLabelling
      ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    (hSecond : incomingRowDenominator data (secondRow profile) = shape.k)
    (hThird : incomingRowDenominator data (thirdRow profile) = shape.k) :
    ∑ position : Fin 3, signedMult
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).labelling
          initial position).presentation = 0 := by
  have hk : 1 < shape.k := shape.one_lt_k
  have hDvd2 : shape.k ∣ incomingRowDenominator data (secondRow profile) := by
    rw [hSecond]
  have hDvd3 : shape.k ∣ incomingRowDenominator data (thirdRow profile) := by
    rw [hThird]
  have hCop2 : Nat.Coprime (shape.k - 1) (incomingRowDenominator data (secondRow profile)) := by
    rw [hSecond]
    have hsucc : shape.k - 1 + 1 = shape.k := by omega
    have hc : Nat.Coprime (shape.k - 1) (shape.k - 1 + 1) := by simp
    rwa [hsucc] at hc
  have hCop3 : Nat.Coprime (shape.k + 1) (incomingRowDenominator data (thirdRow profile)) := by
    rw [hThird]
    exact Nat.Coprime.symm (by simp : Nat.Coprime shape.k (shape.k + 1))
  exact sum_signedMult_limitColumns_eq_zero input shape hConnected hGenus initial
    hDvd2 hCop2 hDvd3 hCop3

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- **The fully instantiated statement**: no supplied square labelling, the
family the Part I lemma builds, and the sharp incoming row denominators as the
only hypotheses. -/
theorem sum_signedMult_canonical_eq_zero
    (hSecond : incomingRowDenominator data (secondRow profile) = shape.k)
    (hThird : incomingRowDenominator data (thirdRow profile) = shape.k) :
    ∑ position : Fin 3, signedMult
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).labelling
          ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).canonicalInitialLabelling
            input) position).presentation = 0 :=
  sum_signedMult_limitColumns_eq_zero_of_sharp input shape hConnected hGenus _ hSecond hThird

end Constructed

end DraismaVargas.Count.TrivalentWeight
