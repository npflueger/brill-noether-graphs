module

public import DraismaVargasCount.W2R1StarCensusProof
public import DraismaVargasCount.W2PMultiplicityBalance
public import DraismaVargas.LocalCases.W2PGraphTracking

@[expose] public section

/-!
# The W2P star census, Stages 1 and 3, and Stage 2 reduced to transports

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-P}`, Figure 35 and
**Equation (9)**; Vargas, Part II (arXiv:2609.09109): the star of a wall and
`prop-signed-mult`.  Engine `StarCensusEngine`; the same pattern as
`M11StarCensusProof` (three positions, loop walls) and `W3Nd2StarCensusProof`.  This is
the P case of the star parity in step 2 of `Assembly`: exhaustion of the star, and
uniqueness with multiplicity.  The census splits into (a) every nonsingular position
is a star class (Stage 1), (b) every star class is a position (Stage 2), and
(c) distinct positions are distinct classes (Stage 3).

## The result, in one paragraph

`RegrowthWallInput.FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2P` is reduced to the single
residue `W2PStarExhaustion` (`familyStarParity_w2P_of_exhaustion`), which is *equivalent*
to the census `W2PStarCensus` (`w2PStarExhaustion_iff`): the star is in bijection with the
**nonsingular** positions of Equation (9), each class carrying its term's `|num|`.  **(a)
and (c) are proved at every core, degree, positive request and Equation (9) presentation,
with no hypothesis.**  Equation (9) has three members and non-unit weights `k₁+1`, `k₂+1`,
`k₁+k₂`, so a position may be singular (it then contributes `0` and is not a star class),
and the weights play no role in the parity: the census reads the *terms* of the balance.
Separation is by the regrown columns `c(e₁)/(k₁+1) + c(e₂)/k₂ + s`,
`c(e₁)/k₁ + c(e₂)/(k₂+1) + s`, `c(e₃)/(k₁+k₂) + s`: the third differs from the other two
at every wall (evaluate at the rows `r₁`, `r₂` of `e₁`, `e₂`), and the first two agree only
at a **loop** (`r₁ = r₂`, which also forces `k₁ = k₂`), which no full-dimensional first
member admits -- the loop row would be a lollipop row with two occurrences carrying the
retained `e₁`, `e₂` and a regrown occurrence.

## What is proved

* **Stage 1 (a).**  `coreGraphData_branchSquare` (every one-block limit-chain member,
  family-free, through `LimitChainTwoBlock.GraphData.ofOneBlock` and
  `W2R1StarCensusProof.graphData_branchSquare`); `branchSquare`, `matrix_retained`,
  `matrix_new`, `row_mk` at Figure 35's three members; `member`: position `q` as a member
  of the wall's star for any full-dimensional presentation, wall-anchored.  `lab`,
  `Nonsingular`, `nonsingular_incoming`, `fdAt`, `rep`, `multNat_rep`,
  `signedMult_eq_zero` (singular positions contribute nothing), `integral_signedMult`,
  `sum_signedMult_eq_zero` (Equation (9), `W2PMultiplicityBalance.sum_signedMult_eq_zero`).
* **Stage 3 (c), unconditional.**  `backgroundColumn_nonneg`, `firstNew_pos`,
  `thirdNew_ne_firstNew`, `thirdNew_ne_secondNew`, `firstRow_eq_of_new_eq` (column
  arithmetic); `two_le_incidenceCount_of_loop`, `card_rowEdges_of_loop` (a family-free
  lollipop count: two occurrences at one branch vertex on one row make it a two-occurrence
  row in every full-dimensional presentation of an equivalent datum); `loop_false` (no
  full-dimensional member whose regrown column meets the loop row);
  `newColumn_eq_of_frameIso`, `not_rel_01`, `not_rel_02`, `not_rel_12`,
  `rep_eq_of_cls_eq`, `repCls_injective`.
* **Stage 2 reduced to transports.**  `PositionTransport`, `exhausts_of_transports` (the
  receipt carries the position's nonsingularity, as at M-11), over the valency-free
  `PlacementSpec` / `memberResolution` / `memberNorm` pattern of `W3Nd2StarCensusProof`.
* **Assembly.**  `Exhausts`, `repCls_surjective`, `census_of_exhaustion`,
  `exhaustion_of_census`, `starParityAt_of_census` (through
  `StarCensusEngine.starParityAt_of_census`), `starParityAt_of_exhaustion`; `W2PStarCensus`,
  `W2PStarExhaustion`, `w2PStarCensus_of_exhaustion`, `exhaustion_of_w2PStarCensus`,
  `w2PStarExhaustion_iff`, `familyStarParity_w2P_of_census`, and
  `familyStarParity_w2P_of_exhaustion`.

## What is NOT proved (every hypothesis, explicitly)

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2P` is not proved in this file.**  Its exact
  residue here is `W2PStarExhaustion` (Stage 2 (b): every star member is a frame isomorph
  of a nonsingular position).  *Interface*: equivalent to `W2PStarCensus`
  (`w2PStarExhaustion_iff`).  **The residue is discharged in the companion
  `W2PStarExhaustionProof`** (`w2PStarExhaustion`, and the family clause
  `familyStarParity_w2P`).
* **What Stage 2 needs** (the hypothesis of `exhausts_of_transports`): for each star member
  `m` with limit isomorphism `ψ`, a placement and a `ResolutionExpansionFree.TransportFree`
  along `ψ` onto a nonsingular position's pasted resolution; that needs the wall's
  `W2SourceInput`, `SourceProfile` and `Shape` pulled back along `ψ` and Part I's incoming
  census (`W2PIncomingCensus` / `W2PIncomingMatching`) at `m`; all of it is done in
  `W2PStarExhaustionProof`.
* **No wall carrying the tag is exhibited.**  Computer experiments with genus-six walls
  found no P wall, so the census has not been tested numerically at an instance.
* Nothing here depends on genus six or degree four except the instantiation of the
  family clause.

## Tempting inferences, checked

* *Does (c) fail when the balance has more terms or non-unit weights?*  **The balance does
  have three terms and non-unit weights, but (c) does not fail**: `not_rel_01`,
  `not_rel_02`, `not_rel_12` hold at every wall.  The pair `{0, 2}` and `{1, 2}` separate
  by column arithmetic alone; the pair `{0, 1}` is the delicate one -- the regrown columns
  agree exactly when `r₁ = r₂` and `k₁ = k₂`, and it takes the lollipop argument
  (`loop_false`) to rule that out, the same shape as M-11's loop walls.  Star parity
  follows from the census whatever the weights (`starParityAt_of_census`): parity is read
  off the integral terms `signedMult`, and the singular terms vanish.  Had `0` and `1`
  collapsed, parity would genuinely have failed through this route: their terms would be
  equal, `m₂ = -2 m₀`, and the one collapsed class would be odd whenever `m₀` is.
* **Reuse.**  The receipt of `W3Nd2StarCensusProof` and `M11StarCensusProof`'s
  `candidate_*`, `three_le_card_rowEdges`, `exists_occurrence_of_matrix_ne_zero` are
  imported.  `card_rowEdges_of_loop` restates the *argument* of
  `M11StarCensusProof.loopRow_lollipop` family-free (that lemma is stated for the M-11
  profile and its two-sheet block, so it cannot be reused at a `Shape` profile).

## Consumers

`W2PStarExhaustionProof` (the exhaustion and the unconditional clause), and through it the
`w2P` clause of the star parity (step 2 of `Assembly`).
-/

namespace DraismaVargas.Count.W2PStarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W2R1Target SecondEquation W4Assembly W2R2SourceProfile W2PSourceCandidates
open W3Nd2StarCensusProof (PlacementSpec memberResolution memberNorm)

/-! ## 1.  Branch squares, and the lollipop count at a loop -/

section Local

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}

/-- **The branch square of any one-block limit-chain member**
(`LimitChainCore.GraphData`), through its singleton-anchor two-block instance. -/
theorem coreGraphData_branchSquare (rd : LimitChainCore.GraphData data wall)
    (v : BranchVertex data) :
    data.sourceEndpoint (contractVertex target wall (rd.equivalence.vertex v).1.1.1)
        (rd.equivalence.vertex v).1.1.2 = v.1 := by
  rw [← LimitChainTwoBlock.GraphData.equivalence_vertex_ofOneBlock rd v]
  exact W2R1StarCensusProof.graphData_branchSquare
    (LimitChainTwoBlock.GraphData.ofOneBlock rd) v

/-- Two distinct occurrences at one source vertex on one stable row: the row meets the
vertex at least twice. -/
theorem two_le_incidenceCount_of_loop {v : data.SourceVertex} {e e' : NonDanglingEdge data}
    (hNe : e ≠ e') (he : Incident data e.1 v) (he' : Incident data e'.1 v)
    (hRow : e'.stablePath = e.stablePath) :
    2 ≤ StablePathCount.incidenceCount data v e.stablePath := by
  classical
  have hSub : ({e, e'} : Finset (NonDanglingEdge data)) ⊆
      (StablePathCount.incidentEdges data v).filter
        (fun x ↦ x.stablePath = e.stablePath) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr he, rfl⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr he', hRow⟩
  have h := Finset.card_le_card hSub
  rw [Finset.card_pair hNe] at h
  exact h

/-- **A loop row at a branch vertex is a lollipop row in every full-dimensional
presentation of an equivalent datum**: it has exactly two occurrences
(`PassOnceLollipopWitness.card_rowEdges_eq_two_of_loopRow`).  Family-free: M-11's
`M11StarCensusProof.loopRow_lollipop` with the loop given by two occurrences. -/
theorem card_rowEdges_of_loop (A : BranchVertex data) {e e' : NonDanglingEdge data}
    (hNe : e ≠ e') (he : Incident data e.1 A.1) (he' : Incident data e'.1 A.1)
    (hRow : e'.stablePath = e.stablePath)
    {T : CFGraph.{0}} {D : GluingDatum T degree} {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fd : FullDimensionalSourcePresentation D coordinate)
    (E : StableGraphIncidence.Equivalence data D) :
    (EdgeDenominator.rowEdges fd.labelling (fd.labelling.row (E.row e.stablePath))).card
      = 2 := by
  classical
  have h2 : 2 ≤ StablePathCount.incidenceCount D (E.vertex A).1 (E.row e.stablePath) := by
    rw [← E.incidence A e.stablePath]
    exact two_le_incidenceCount_of_loop hNe he he' hRow
  have hSum := NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex D fd.valid.1
    fd.pathEnds (E.row e.stablePath)
  have hle : StablePathCount.incidenceCount D (E.vertex A).1 (E.row e.stablePath) ≤ 2 := by
    rw [← hSum]
    exact Finset.single_le_sum
      (f := fun v : BranchVertex D ↦ StablePathCount.incidenceCount D v.1 (E.row e.stablePath))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (E.vertex A))
  have hTwo := le_antisymm hle h2
  have hBranch : 3 ≤ nonDanglingValency D (E.vertex A).1 := (E.vertex A).2
  obtain ⟨leaf, hLeaf, hLeafRow⟩ :=
    LollipopLeafRow.exists_leafRow_eq_of_loopRow fd (by omega) hTwo
  exact PassOnceLollipopWitness.card_rowEdges_eq_two_of_loopRow fd hBranch hTwo hLeaf hLeafRow

end Local

/-! ## 2.  Figure 35's three members over an arbitrary datum -/

section Members

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall} {block : WallBlock data wall}
  {profile : SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)

/-- **The branch square of Figure 35's member `q`.** -/
theorem branchSquare (q : Fin 3) (v : BranchVertex data) :
    data.sourceEndpoint
        (contractVertex target wall ((W2PArbitraryExit.equivalence input shape q).vertex v).1.1.1)
        ((W2PArbitraryExit.equivalence input shape q).vertex v).1.1.2 = v.1 := by
  fin_cases q
  · exact coreGraphData_branchSquare (W2PGraphData.firstGraphData shape input) v
  · exact coreGraphData_branchSquare (W2PGraphData.secondGraphData shape input) v
  · exact coreGraphData_branchSquare (W2PGraphData.thirdGraphData shape input) v

/-- The member's retained columns are the wall's, through its stable-graph equivalence. -/
theorem matrix_retained (q : Fin 3) (path : StablePath data) (place : target.edges) :
    StableSourceMatrix.matrix (W2PCommonBalance.members profile shape q).datum
        ((W2PArbitraryExit.equivalence input shape q).row path)
        (occurrenceEquiv target wall (W2PCommonBalance.members profile shape q).right
          (some place)) =
      StableSourceMatrix.matrix data path place := by
  rw [W2PArbitraryExit.equivalence_row]
  exact (W2PLimitMatrix.limitColumns input shape).retained q path place

/-- The member's regrown column is Figure 35's, through its stable-graph equivalence. -/
theorem matrix_new (q : Fin 3) (path : StablePath data) :
    StableSourceMatrix.matrix (W2PCommonBalance.members profile shape q).datum
        ((W2PArbitraryExit.equivalence input shape q).row path)
        (occurrenceEquiv target wall (W2PCommonBalance.members profile shape q).right none) =
      W2PCommonBalance.newColumn profile q path := by
  rw [W2PArbitraryExit.equivalence_row]
  exact (W2PLimitMatrix.limitColumns input shape).regrown q path

/-- The row of a retained occurrence is the equivalence's row of the incoming one. -/
theorem row_mk (q : Fin 3) (e : NonDanglingEdge data) :
    (W2PArbitraryExit.equivalence input shape q).row e.stablePath =
      (ResolutionAwayFromWall.retainedEdge (W2PCommonBalance.members profile shape q)
        input.valid.1 e).stablePath := by
  fin_cases q <;> rfl

end Members

/-! ## 3.  The regrown columns separate, except at a loop

Figure 35's regrown columns (`W2PCommonBalance.firstNewColumn` …) are
`c(e₁)/(k₁+1) + c(e₂)/k₂ + s`, `c(e₁)/k₁ + c(e₂)/(k₂+1) + s` and `c(e₃)/(k₁+k₂) + s`,
where `c(eᵢ)` is the indicator of `eᵢ`'s stable row `rᵢ` and `s ≥ 0` is the common
background.  The third differs from each of the first two at every wall (evaluate at `r₁`
and `r₂`).  The first two agree only if `r₁ = r₂` (and `k₁ = k₂`): a *loop* at the
distinguished vertex. -/

section Columns

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall} {block : WallBlock data wall}
  (profile : SourceProfile data star block)

theorem backgroundColumn_nonneg (star : TwoStar target wall) (block : WallBlock data wall)
    (path : StablePath data) (label : Fin 2) :
    0 ≤ W2PCommonBalance.backgroundColumn star block path label :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

private theorem index_pos (edge : data.SourceEdge) : (0 : ℚ) < data.sourceEdgeIndex edge := by
  exact_mod_cast StableLocalProperties.sourceEdgeIndex_pos data edge

/-- **The first regrown column is positive on `e₁`'s row.** -/
theorem firstNew_pos :
    0 < W2PCommonBalance.newColumn profile 0 (W2PCommonBalance.firstRow profile) := by
  classical
  have h1 := index_pos profile.first.1
  have h2 := index_pos profile.second.1
  have hs := backgroundColumn_nonneg star block (W2PCommonBalance.firstRow profile)
    profile.doubleLabel
  simp only [W2PCommonBalance.newColumn_zero, W2PCommonBalance.firstNewColumn, ↓reduceIte]
  have : (0 : ℚ) ≤ (if W2PCommonBalance.firstRow profile = W2PCommonBalance.secondRow profile
      then (1 : ℚ) else 0) / (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    split_ifs <;> positivity
  have h3 : (0 : ℚ) < 1 / ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) := by positivity
  linarith

/-- **The third regrown column is not the first**, at every wall. -/
theorem thirdNew_ne_firstNew
    (h : ∀ path, W2PCommonBalance.newColumn profile 2 path =
      W2PCommonBalance.newColumn profile 0 path) : False := by
  classical
  have h1 := h (W2PCommonBalance.firstRow profile)
  have h2 := h (W2PCommonBalance.secondRow profile)
  have ha := index_pos profile.first.1
  have hb := index_pos profile.second.1
  simp only [W2PCommonBalance.newColumn_zero, W2PCommonBalance.newColumn_two,
    W2PCommonBalance.firstNewColumn, W2PCommonBalance.thirdNewColumn] at h1 h2
  set a : ℚ := (data.sourceEdgeIndex profile.first.1 : ℚ)
  set b : ℚ := (data.sourceEdgeIndex profile.second.1 : ℚ)
  have hab : 1 / (a + b) ≤ 1 / b := one_div_le_one_div_of_le hb (by linarith)
  have hpa : 0 < 1 / (a + 1) := by positivity
  have hpb : 0 < 1 / b := by positivity
  have hpab : 0 < 1 / (a + b) := by positivity
  have hpa' : 0 < 1 / a := by positivity
  have hpb' : 0 < 1 / (b + 1) := by positivity
  split_ifs at h1 h2 <;> (try simp only [zero_div] at h1 h2) <;>
    first
    | linarith
    | exact absurd ((‹W2PCommonBalance.firstRow profile = W2PCommonBalance.thirdRow profile›).trans
        (‹W2PCommonBalance.secondRow profile = W2PCommonBalance.thirdRow profile›).symm)
        ‹¬ W2PCommonBalance.firstRow profile = W2PCommonBalance.secondRow profile›

/-- **The third regrown column is not the second**, at every wall. -/
theorem thirdNew_ne_secondNew
    (h : ∀ path, W2PCommonBalance.newColumn profile 2 path =
      W2PCommonBalance.newColumn profile 1 path) : False := by
  classical
  have h1 := h (W2PCommonBalance.firstRow profile)
  have h2 := h (W2PCommonBalance.secondRow profile)
  have ha := index_pos profile.first.1
  have hb := index_pos profile.second.1
  simp only [W2PCommonBalance.newColumn_one, W2PCommonBalance.newColumn_two,
    W2PCommonBalance.secondNewColumn, W2PCommonBalance.thirdNewColumn] at h1 h2
  set a : ℚ := (data.sourceEdgeIndex profile.first.1 : ℚ)
  set b : ℚ := (data.sourceEdgeIndex profile.second.1 : ℚ)
  have hab : 1 / (a + b) ≤ 1 / a := one_div_le_one_div_of_le ha (by linarith)
  have hpa : 0 < 1 / (a + 1) := by positivity
  have hpb : 0 < 1 / b := by positivity
  have hpab : 0 < 1 / (a + b) := by positivity
  have hpa' : 0 < 1 / a := by positivity
  have hpb' : 0 < 1 / (b + 1) := by positivity
  split_ifs at h1 h2 <;> (try simp only [zero_div] at h1 h2) <;>
    first
    | linarith
    | exact absurd ((‹W2PCommonBalance.firstRow profile = W2PCommonBalance.thirdRow profile›).trans
        (‹W2PCommonBalance.secondRow profile = W2PCommonBalance.thirdRow profile›).symm)
        ‹¬ W2PCommonBalance.firstRow profile = W2PCommonBalance.secondRow profile›

/-- **Equal first and second regrown columns force a loop**: `e₁` and `e₂` on one stable
row. -/
theorem firstRow_eq_of_new_eq
    (h : ∀ path, W2PCommonBalance.newColumn profile 1 path =
      W2PCommonBalance.newColumn profile 0 path) :
    W2PCommonBalance.firstRow profile = W2PCommonBalance.secondRow profile := by
  classical
  by_contra hNe
  have h1 := h (W2PCommonBalance.firstRow profile)
  have ha := index_pos profile.first.1
  simp only [W2PCommonBalance.newColumn_zero, W2PCommonBalance.newColumn_one,
    W2PCommonBalance.firstNewColumn, W2PCommonBalance.secondNewColumn, ↓reduceIte,
    ite_eq_right hNe, zero_div, add_zero] at h1
  set a : ℚ := (data.sourceEdgeIndex profile.first.1 : ℚ)
  have hlt : 1 / (a + 1) < 1 / a := one_div_lt_one_div_of_lt ha (by linarith)
  linarith

end Columns

/-! ## 4.  No loop under a full-dimensional first or second member

At a loop (`r₁ = r₂`) the loop row of any full-dimensional member is a lollipop row with
exactly two occurrences (`card_rowEdges_of_loop`).  At Figure 35's first and second
members it carries three: the retained copies of `e₁` and `e₂`, and a regrown occurrence
(the regrown column is nonzero there).  This is the W2P analogue of
`M11StarCensusProof.split_false`. -/

section NoLoop

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall} {block : WallBlock data wall}
  {profile : SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)

include input in
/-- **A loop wall has no full-dimensional member whose regrown column meets the loop
row.** -/
theorem loop_false
    (hRow : W2PCommonBalance.firstRow profile = W2PCommonBalance.secondRow profile)
    (q : Fin 3) (hq : W2PCommonBalance.newColumn profile q (W2PCommonBalance.firstRow profile) ≠ 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape q).datum
      coordinate) : False := by
  classical
  let c := W2PCommonBalance.members profile shape q
  let E := W2PArbitraryExit.equivalence input shape q
  let e1 : NonDanglingEdge data := ⟨profile.first.1, profile.first_survives⟩
  let e2 : NonDanglingEdge data := ⟨profile.second.1, profile.second_survives⟩
  have hNe : e1 ≠ e2 := fun h ↦
    profile.first_ne_second (Subtype.ext (congrArg (fun e : NonDanglingEdge data ↦ e.1) h))
  let A : BranchVertex data := ⟨WallBlock.sourceVertex data wall block, profile.valency.ge⟩
  have hTwo := card_rowEdges_of_loop A hNe profile.first.2 profile.second.2 hRow.symm fd E
  set R := E.row e1.stablePath with hR
  have hNew := matrix_new input shape q e1.stablePath
  obtain ⟨z, hzSurv, hzRow, hzTarget⟩ :=
    M11StarCensusProof.exists_occurrence_of_matrix_ne_zero (hNew.trans_ne hq)
  let x := ResolutionAwayFromWall.retainedEdge c input.valid.1 e1
  let y := ResolutionAwayFromWall.retainedEdge c input.valid.1 e2
  have hxR : x.stablePath = R := (row_mk input shape q e1).symm
  have hyR : y.stablePath = R :=
    (row_mk input shape q e2).symm.trans (congrArg E.row hRow.symm)
  have hx : x.1 ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨x.2, congrArg fd.labelling.row hxR⟩
  have hy : y.1 ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨y.2, congrArg fd.labelling.row hyR⟩
  have hz : z ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨hzSurv, congrArg fd.labelling.row hzRow⟩
  have hxy : x.1 ≠ y.1 := by
    intro h
    exact hNe (ResolutionAwayFromWall.retainedEdge_injective c input.valid.1 (Subtype.ext h))
  have hTargetNe : ∀ e : NonDanglingEdge data,
      (ResolutionAwayFromWall.retainedEdge c input.valid.1 e).1 ≠ z := by
    intro e h
    have h' := congrArg (fun e : c.datum.SourceEdge ↦ e.1.1) h
    rw [hzTarget] at h'
    exact Option.some_ne_none _ ((occurrenceEquiv target wall c.right).injective h')
  have h3 := M11StarCensusProof.three_le_card_rowEdges fd.labelling (fd.labelling.row R) hx hy
    hz hxy (hTargetNe _) (hTargetNe _)
  omega

end NoLoop

/-! ## 5.  The three positions of Equation (9) as members of the wall's star (Stage 1) -/

section Positions

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)

/-- **Position `q` of Equation (9) is a member of the wall's star**, for any
full-dimensional presentation of its datum.  All three Figure 35 members are
wall-anchored (`M = w.limit`, `φ = refl`). -/
noncomputable def member (q : Fin 3)
    (fd : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape q).datum
      (Fin p)) :
    GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := W2PArbitraryExit.equivalence input shape q) (fd := fd)
    (hRetained := matrix_retained input shape q)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
    (hOld := M11StarCensusProof.candidate_old _) (hEdge := M11StarCensusProof.candidate_edge _)
    (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans
      (branchSquare input shape q v))
    (M11StarCensusProof.refl_rowSquare w _ _ (row_mk input shape q))

/-- The frame of position `q`. -/
noncomputable abbrev frameAt (q : Fin 3)
    (fd : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape q).datum
      (Fin p)) :=
  StarCensusEngine.frame w hy (W2PCommonBalance.members profile shape q).datum
    (W2PArbitraryExit.equivalence input shape q) fd

/-- A frame isomorphism between positions preserves the regrown column. -/
theorem newColumn_eq_of_frameIso {q q' : Fin 3}
    {fd : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape q).datum
      (Fin p)}
    {fd' : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape q').datum
      (Fin p)}
    (fi : GeometricSegmentWalls.FrameIso (frameAt w hy input shape q fd)
      (frameAt w hy input shape q' fd')) (path : StablePath w.limit) :
    W2PCommonBalance.newColumn profile q' path = W2PCommonBalance.newColumn profile q path := by
  have h := StarCensusEngine.frameIso_matrix_new
    (E := W2PArbitraryExit.equivalence input shape q)
    (E' := W2PArbitraryExit.equivalence input shape q')
    (matrix_retained input shape q) (matrix_retained input shape q') fi path
  rwa [matrix_new, matrix_new] at h

/-- **Positions `0` and `2` are distinct star classes**, at every wall. -/
theorem not_rel_02
    (fd0 : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape 0).datum
      (Fin p))
    (fd2 : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape 2).datum
      (Fin p)) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frameAt w hy input shape 0 fd0)
      (frameAt w hy input shape 2 fd2)) := fun ⟨fi⟩ ↦
  thirdNew_ne_firstNew profile (newColumn_eq_of_frameIso w hy input shape fi)

/-- **Positions `1` and `2` are distinct star classes**, at every wall. -/
theorem not_rel_12
    (fd1 : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape 1).datum
      (Fin p))
    (fd2 : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape 2).datum
      (Fin p)) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frameAt w hy input shape 1 fd1)
      (frameAt w hy input shape 2 fd2)) := fun ⟨fi⟩ ↦
  thirdNew_ne_secondNew profile (newColumn_eq_of_frameIso w hy input shape fi)

/-- **Positions `0` and `1` are distinct star classes**, at every wall: equal regrown
columns force a loop (`firstRow_eq_of_new_eq`), and a loop has no full-dimensional first
member (`loop_false`). -/
theorem not_rel_01
    (fd0 : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape 0).datum
      (Fin p))
    (fd1 : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape 1).datum
      (Fin p)) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frameAt w hy input shape 0 fd0)
      (frameAt w hy input shape 1 fd1)) := fun ⟨fi⟩ ↦
  loop_false input shape
    (firstRow_eq_of_new_eq profile (newColumn_eq_of_frameIso w hy input shape fi)) 0
    (firstNew_pos profile).ne' fd0

end Positions

/-! ## 6.  The nonsingular positions of Equation (9) as star classes -/

section Census

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (W2PCommonBalance.members profile shape incoming).datum (Fin p))

/-- Equation (9)'s labelling of position `q`, induced from the incoming presentation. -/
noncomputable abbrev lab (q : Fin 3) :=
  W2PArbitraryExit.outgoingLabelling input shape incoming incomingFD q

/-- The nonsingular positions of Equation (9). -/
def Nonsingular (q : Fin 3) : Prop :=
  (GluingDatum.LengthMatrixPresentation.matrix (lab w input shape incomingFD q).presentation).det ≠ 0

/-- **The incoming position is nonsingular**: transport to the common member and back is
the identity (`W2PArbitraryExit.outgoingLabelling_self`). -/
theorem nonsingular_incoming : Nonsingular w input shape incomingFD incoming := by
  unfold Nonsingular lab
  rw [W2PArbitraryExit.outgoingLabelling_self input shape incoming incomingFD]
  exact incomingFD.det_ne_zero

/-- The full-dimensional presentation of a nonsingular position, transported from the
incoming one. -/
noncomputable def fdAt (q : Fin 3) (hq : Nonsingular w input shape incomingFD q) :
    FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape q).datum (Fin p) :=
  W2PArbitraryExit.outgoingPresentation input shape (W4StarParity.limitTarget_connected w)
    (W4StarParity.limitTarget_genus w) incoming q incomingFD hq

/-- **The star member of a nonsingular position of Equation (9).** -/
noncomputable def rep (q : Fin 3) (hq : Nonsingular w input shape incomingFD q) :
    GeometricStar.StarMember hy w :=
  member w hy input shape q (fdAt w input shape incomingFD q hq)

/-- **The multiplicity of a position's star class is its term of Equation (9)**, up to
sign. -/
theorem multNat_rep (q : Fin 3) (hq : Nonsingular w input shape incomingFD q) :
    (GeometricStar.Star.toFibre (rep w hy input shape incomingFD q hq).cls).multNat =
      (signedMult (lab w input shape incomingFD q).presentation).num.natAbs :=
  M11StarCensusProof.num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)

/-- A singular position contributes nothing to Equation (9). -/
theorem signedMult_eq_zero (q : Fin 3) (hq : ¬ Nonsingular w input shape incomingFD q) :
    signedMult (lab w input shape incomingFD q).presentation = 0 := by
  unfold Nonsingular at hq
  rw [not_not] at hq
  unfold signedMult
  rw [hq, mul_zero]

/-- **Every term of Equation (9) is an integer.** -/
theorem integral_signedMult (q : Fin 3) :
    ∃ value : ℤ, signedMult (lab w input shape incomingFD q).presentation = (value : ℚ) := by
  by_cases hq : Nonsingular w input shape incomingFD q
  · exact isIntegralMultiplicity (fdAt w input shape incomingFD q hq)
  · exact ⟨0, by rw [signedMult_eq_zero w input shape incomingFD q hq, Int.cast_zero]⟩

/-- **Equation (9) in the incoming presentation's labelling**
(`W2PMultiplicityBalance.sum_signedMult_eq_zero`). -/
theorem sum_signedMult_eq_zero :
    ∑ q : Fin 3, signedMult (lab w input shape incomingFD q).presentation = 0 :=
  W2PMultiplicityBalance.sum_signedMult_eq_zero input shape
    (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w) incoming
    incomingFD

end Census

/-! ## 7.  The census from exhaustion (Stage 2 residue) -/

section Assembly

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (W2PCommonBalance.members profile shape incoming).datum (Fin p))

/-- **Distinct nonsingular positions are distinct star classes** (Stage 3), at every
wall. -/
theorem rep_eq_of_cls_eq (q : Fin 3) (hq : Nonsingular w input shape incomingFD q)
    (q' : Fin 3) (hq' : Nonsingular w input shape incomingFD q')
    (h : (rep w hy input shape incomingFD q hq).cls =
      (rep w hy input shape incomingFD q' hq').cls) : q = q' := by
  have hRel := Quotient.exact h
  have hRel' : Nonempty (GeometricSegmentWalls.FrameIso
      (rep w hy input shape incomingFD q' hq').member.frame
      (rep w hy input shape incomingFD q hq).member.frame) :=
    hRel.elim fun fi ↦ ⟨fi.symm⟩
  fin_cases q <;> fin_cases q'
  · rfl
  · exact (not_rel_01 w hy input shape _ _ hRel).elim
  · exact (not_rel_02 w hy input shape _ _ hRel).elim
  · exact (not_rel_01 w hy input shape _ _ hRel').elim
  · rfl
  · exact (not_rel_12 w hy input shape _ _ hRel).elim
  · exact (not_rel_02 w hy input shape _ _ hRel').elim
  · exact (not_rel_12 w hy input shape _ _ hRel').elim
  · rfl

/-- The positions' classes, as a map from the nonsingular positions to the star. -/
noncomputable def repCls (q : {q : Fin 3 // Nonsingular w input shape incomingFD q}) :
    GeometricStar.Star hy w :=
  (rep w hy input shape incomingFD q.1 q.2).cls

theorem repCls_injective : Function.Injective (repCls w hy input shape incomingFD) :=
  fun a b h ↦ Subtype.ext (rep_eq_of_cls_eq w hy input shape incomingFD a.1 a.2 b.1 b.2 h)

/-- **The exhaustion residue at one wall** (Stage 2): every member of the star is in the
class of some nonsingular position.  *Interface*: with Stages 1 and 3 it is equivalent to
the census at this wall (`census_of_exhaustion`, `exhaustion_of_census`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ q : Fin 3,
    ∃ hq : Nonsingular w input shape incomingFD q,
      member.cls = (rep w hy input shape incomingFD q hq).cls

theorem repCls_surjective (hExh : Exhausts w hy input shape incomingFD) :
    Function.Surjective (repCls w hy input shape incomingFD) := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨q, hq, h⟩ := hExh member
  exact ⟨⟨q, hq⟩, h.symm⟩

/-- **The W2P census at one wall from exhaustion.** -/
theorem census_of_exhaustion (hExh : Exhausts w hy input shape incomingFD) :
    ∃ e : {q : Fin 3 // Nonsingular w input shape incomingFD q} ≃ GeometricStar.Star hy w,
      ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
        (signedMult (lab w input shape incomingFD q.1).presentation).num.natAbs :=
  ⟨Equiv.ofBijective _ ⟨repCls_injective w hy input shape incomingFD,
      repCls_surjective w hy input shape incomingFD hExh⟩,
    fun q ↦ multNat_rep w hy input shape incomingFD q.1 q.2⟩

/-- **Interface: the census implies exhaustion.** -/
theorem exhaustion_of_census
    (e : {q : Fin 3 // Nonsingular w input shape incomingFD q} ≃ GeometricStar.Star hy w) :
    Exhausts w hy input shape incomingFD := by
  classical
  have hBij : Function.Bijective (repCls w hy input shape incomingFD) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨repCls_injective w hy input shape incomingFD, Fintype.card_congr e⟩
  intro member
  obtain ⟨q, hq⟩ := hBij.2 member.cls
  exact ⟨q.1, q.2, hq.symm⟩

/-- **The star clause from Equation (9) and the census**: the singular positions
contribute `0`, the census reads the nonsingular ones as the star
(`StarCensusEngine.starParityAt_of_census`).  Non-unit weights `k₁+1`, `k₂+1`, `k₁+k₂` do
not matter: parity is read off the terms, not the weights. -/
theorem starParityAt_of_census
    (e : {q : Fin 3 // Nonsingular w input shape incomingFD q} ≃ GeometricStar.Star hy w)
    (hmult : ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
      (signedMult (lab w input shape incomingFD q.1).presentation).num.natAbs) :
    RegrowthWallInput.StarParityAt hy w :=
  StarCensusEngine.starParityAt_of_census
    (fun q ↦ signedMult (lab w input shape incomingFD q).presentation)
    (integral_signedMult w input shape incomingFD)
    (sum_signedMult_eq_zero w input shape incomingFD)
    (Nonsingular w input shape incomingFD) (signedMult_eq_zero w input shape incomingFD) e hmult

/-- **Stage 2 is the whole content of the clause at a wall.** -/
theorem starParityAt_of_exhaustion (hExh : Exhausts w hy input shape incomingFD) :
    RegrowthWallInput.StarParityAt hy w := by
  obtain ⟨e, hmult⟩ := census_of_exhaustion w hy input shape incomingFD hExh
  exact starParityAt_of_census w hy input shape incomingFD e hmult

end Assembly

/-! ## 8.  Stage 2 reduced to decoupled transports -/

section Transport

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (W2PCommonBalance.members profile shape incoming).datum (Fin p))

/-- **The receipt a member must present to be received at position `q`**: a decoupled
transport, along its limit isomorphism, from its own normal form at some placement onto
the position's pasted resolution. -/
abbrev PositionTransport (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : PlacementSpec other placement) (q : Fin 3) : Type :=
  ResolutionExpansionFree.TransportFree
    (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm) (mergeVertex other) (mergeVertex w)
    placement (W2PCommonBalance.members profile shape q).right
    (memberResolution other placement hPlacement)
    (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q))

/-- **Stage 2 reduced to transports**: if every star member presents a decoupled
transport onto some nonsingular position, from its own normal form at some placement,
the star is exhausted by the positions. -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w,
      ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
      ∃ hPlacement : PlacementSpec member.member placement,
      ∃ q : Fin 3, ∃ _ : Nonsingular w input shape incomingFD q,
        Nonempty (PositionTransport w hy shape member.member ψ placement hPlacement q)) :
    Exhausts w hy input shape incomingFD := by
  intro member
  obtain ⟨ψ, placement, hPlacement, q, hq, ⟨t⟩⟩ := h member
  refine ⟨q, hq, ?_⟩
  have hNV := M11WallExhaustion.sourceVertexMap_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  have hNE := M11WallExhaustion.retainedSourceEdge_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
    (E := W2PArbitraryExit.equivalence input shape q)
    (fd := fdAt w input shape incomingFD q hq)
    (hRetained := matrix_retained input shape q)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
    (hOld := M11StarCensusProof.candidate_old _)
    (hEdge := M11StarCensusProof.candidate_edge _)
    (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans
      (branchSquare input shape q v))
    (M11StarCensusProof.refl_rowSquare w _ _ (row_mk input shape q))
    (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _
      (W2PCommonBalance.members profile shape q).exterior) rfl
    member ψ (memberNorm member.member placement hPlacement) hNV hNE t

end Transport

/-! ## 9.  The family clause -/

section Family

/-- **The W2P star census**: at every `w2P` regrowth, for every Equation (9)
presentation, the nonsingular positions are the star, class by class, with their
multiplicities. -/
def W2PStarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2P →
    ∀ (star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W2SourceInput w.limit star) (block : WallBlock w.limit (mergeVertex w))
      (profile : SourceProfile w.limit star block) (shape : Shape profile) (incoming : Fin 3)
      (incomingFD : FullDimensionalSourcePresentation
        (W2PCommonBalance.members profile shape incoming).datum (Fin p)),
      ∃ e : {q : Fin 3 // Nonsingular w input shape incomingFD q} ≃ GeometricStar.Star hy w,
        ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
          (signedMult (lab w input shape incomingFD q.1).presentation).num.natAbs

/-- **Stage 2's residue, family-wide**: at every `w2P` regrowth, for every Equation (9)
presentation, every star member is in the class of a nonsingular position.
*Interface*: equivalent to `W2PStarCensus` (`w2PStarExhaustion_iff`). -/
def W2PStarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2P →
    ∀ (star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W2SourceInput w.limit star) (block : WallBlock w.limit (mergeVertex w))
      (profile : SourceProfile w.limit star block) (shape : Shape profile) (incoming : Fin 3)
      (incomingFD : FullDimensionalSourcePresentation
        (W2PCommonBalance.members profile shape incoming).datum (Fin p)),
      Exhausts w hy input shape incomingFD

variable {degree n p : ℕ}

theorem w2PStarCensus_of_exhaustion (hExh : W2PStarExhaustion degree n p) :
    W2PStarCensus degree n p :=
  fun core y hy w cls htag star input block profile shape incoming incomingFD ↦
    census_of_exhaustion w hy input shape incomingFD
      (hExh core y hy w cls htag star input block profile shape incoming incomingFD)

theorem exhaustion_of_w2PStarCensus (hCensus : W2PStarCensus degree n p) :
    W2PStarExhaustion degree n p :=
  fun core y hy w cls htag star input block profile shape incoming incomingFD ↦
    exhaustion_of_census w hy input shape incomingFD
      (hCensus core y hy w cls htag star input block profile shape incoming incomingFD).choose

/-- **Interface**: exhaustion is equivalent to the census. -/
theorem w2PStarExhaustion_iff :
    W2PStarExhaustion degree n p ↔ W2PStarCensus degree n p :=
  ⟨w2PStarCensus_of_exhaustion, exhaustion_of_w2PStarCensus⟩

/-- **`FamilyStarParity … .w2P` from the W2P star census**: Equation (9) at the regrowth
(`RegrowthWallInput.exists_w2P_balance`) read mod two through the census. -/
theorem familyStarParity_w2P_of_census (h : W2PStarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w2P := by
  intro core y hy w cls htag
  obtain ⟨star, input, block, profile, shape, incoming, fd, -⟩ :=
    RegrowthWallInput.exists_w2P_balance w hy cls htag
  obtain ⟨e, hmult⟩ := h core y hy w cls htag star input block profile shape incoming fd
  exact starParityAt_of_census w hy input shape fd e hmult

/-- **The `w2P` clause of `FamilyStarParity` at genus six and degree four**, modulo
Stage 2's exhaustion alone. -/
theorem familyStarParity_w2P_of_exhaustion
    (hExh : W2PStarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2P :=
  familyStarParity_w2P_of_census (w2PStarCensus_of_exhaustion hExh)

end Family

end DraismaVargas.Count.W2PStarCensusProof
