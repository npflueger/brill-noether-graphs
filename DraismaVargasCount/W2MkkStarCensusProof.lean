import DraismaVargasCount.W2M1kStarCensusProof

/-!
# The M-kk star census, Stages 1 and 3, and Stage 2 reduced to transports

Sources: Draisma–Vargas Part I, Case `{w2-r2-nd3-M-kk}`, Figure 34 and **Equation (8)**;
Vargas, Part II, the star of a wall.  The census machinery is
`DraismaVargasCount.StarCensusEngine`; the balance is `RegrowthBalances.exists_w2Mkk_balance`
and `DraismaVargasCount.W2MkkIncomingDenominator`; the anchors follow
`W2M1kStarCensusProof.DAnchor`.  This file concerns the star of an M-kk wall: it proves
that the nonsingular positions of Equation (8) are distinct classes of the star with the
multiplicities of Equation (8) (Stages 1 and 3), and reduces the statement that they
exhaust the star (Stage 2) to transports.

## The result, in one paragraph

`RegrowthWallInput.FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2Mkk` is reduced to the single
statement `W2MkkStarExhaustion` (`familyStarParity_w2Mkk_of_exhaustion`), equivalent to the
census `W2MkkStarCensus` (`w2MkkStarExhaustion_iff`); it is proved in
`DraismaVargasCount.W2MkkStarExhaustionProof`.  The positions are those of
`W2MkkLimitColumns.limitColumns input shape detach distinguished`, for **every** detach
datum and distinguished sheet (the family takes both as parameters).  Every position is
anchored at the wall (`limitAnchor`: the identity at the detaching member the datum carries
and at `M⁽³⁾`, the inverse branch swap at the other detaching member, in either
orientation), every nonsingular position is presented by the regrowth's own cover, and
Equation (8) holds at every initial labelling in `Fin p` from any one nonsingular position.
Separation is by the regrown columns `c(e₁)/(k₁-1) + c(e₂)/k₂ + s`,
`c(e₁)/k₁ + c(e₂)/(k₂-1) + s`, `c(e₃)/(k₁+k₂) + s`: the third differs from the first at
`e₁`'s row and from the second at `e₂`'s; the first two agree only at a **loop**
(`r₁ = r₂`, and then only if `k₁ = k₂`), which no full-dimensional detaching member admits
(`loop_false`, the lollipop count), and when positions `0` and `1` are both nonsingular the
one over the limit is such a member.

## What is proved

* **Anchors.**  `Anchor`, `Anchor.retained`, `Anchor.matrix_new`, `localAnchor`,
  `joinedAnchor`, `remoteAnchor`, `columns`, `anchorOf`, `anchorOf_iff`, `firstAnchor`,
  `secondAnchor`, `limitAnchor`.
* **Stage 1 (a).**  `lab`, `Nonsingular`, `fdAt`, `rep`, `multNat_rep`,
  `signedMult_eq_zero`, `integral_signedMult`, `sum_signedMult_eq_zero`.
* **Stage 3 (c), unconditional.**  `backgroundColumn_nonneg`, `one_lt_first_cast`,
  `one_lt_second_cast`, `thirdNew_ne_firstNew`, `thirdNew_ne_secondNew`,
  `firstRow_eq_of_new_eq`, `localMember_new_ne_zero`, `loop_false`,
  `newColumn_eq_of_frameIso`, `not_rel_02`, `not_rel_12`, `not_rel_01`,
  `rep_eq_of_cls_eq`, `repCls_injective`.
* **Stage 2 reduced to transports.**  `PositionTransport`, `exhausts_of_transports`.
* **Assembly.**  `Exhausts`, `repCls_surjective`, `census_of_exhaustion`,
  `exhaustion_of_census`, `starParityAt_of_census`, `starParityAt_of_exhaustion`;
  `W2MkkStarCensus`, `W2MkkStarExhaustion`, `w2MkkStarCensus_of_exhaustion`,
  `exhaustion_of_w2MkkStarCensus`, `w2MkkStarExhaustion_iff`,
  `familyStarParity_w2Mkk_of_census`, `familyStarParity_w2Mkk_of_exhaustion`.

## What is NOT proved here

* **Exhaustion is not proved here**; it is `W2MkkStarExhaustionProof.w2MkkStarExhaustion`,
  which makes the clause unconditional.
* No wall carrying the tag is exhibited.

## Consumers

`DraismaVargasCount.W2MkkStarExhaustionProof`, which gives the `w2Mkk` clause for the
trivalent wall step of `DraismaVargasCount.Assembly`.
-/

namespace DraismaVargas.Count.W2MkkStarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W2R1Target SecondEquation W4Assembly W2R2SourceProfile
open W2MkkSourceCandidates W2MkkLimitColumns W2MkkTransport
open W2MkkCommonBalance (LimitMember LimitColumns)
open W3Nd2StarCensusProof (PlacementSpec memberResolution memberNorm)
open W2M1kStarCensusProof (DAnchor)

/-! ## 1.  The three Figure 34 members, anchored -/

section Anchor

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree)

/-- A Figure 34 member (`W2MkkCommonBalance.LimitMember`), anchored at the wall. -/
abbrev Anchor (m : LimitMember w.limit (mergeVertex w)) := DAnchor w m.datum m.row

variable {w}

/-- The member's retained columns are the wall's. -/
theorem Anchor.retained {m : LimitMember w.limit (mergeVertex w)} (A : Anchor w m)
    (path : StablePath w.limit) (place : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix m.datum (A.E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) m.right (some place)) =
      StableSourceMatrix.matrix w.limit path place :=
  DAnchor.retained A m.retained path place

/-- The regrown column, read through the anchor's rows, is the member's own. -/
theorem Anchor.matrix_new {m : LimitMember w.limit (mergeVertex w)} (A : Anchor w m)
    (path : StablePath w.limit) :
    StableSourceMatrix.matrix m.datum (A.E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) m.right none) =
      m.newColumnValue path := by
  rw [A.E_row]
  rfl

variable {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)

/-- A detaching member over the limit (`M⁽¹⁾` or `M⁽²⁾`, by the datum), anchored by the
identity. -/
noncomputable def localAnchor (detach : DetachData profile) :
    Anchor w (localMember input shape detach) :=
  DAnchor.refl (detach.candidate shape) (W2MkkGraphData.detachEquivalence input shape detach)
    (detach_sourceGenus shape detach)
    (fun v ↦ W2PStarCensusProof.coreGraphData_branchSquare
      (W2MkkGraphData.detachGraphData input shape detach) v)
    (fun _ ↦ rfl)

/-- `M⁽³⁾` (Base II.1.M), anchored by the identity. -/
noncomputable def joinedAnchor (distinguished : Fin degree) :
    Anchor w (joinedMember input shape distinguished) :=
  DAnchor.refl (joinedCandidate profile distinguished)
    (W2MkkGraphData.joinedEquivalence input shape distinguished)
    (joined_sourceGenus profile distinguished)
    (fun v ↦ W2PStarCensusProof.coreGraphData_branchSquare
      (W2MkkGraphData.joinedGraphData input shape distinguished) v)
    (fun _ ↦ rfl)

/-- The remote detaching member over the branch-swapped copy, anchored by the inverse
swap. -/
noncomputable def remoteAnchor (other : Fin degree)
    (hOther : (w.limit.vertexPartition (mergeVertex w)).Rel (pinSheet profile) other) :
    Anchor w (remoteMember input shape other hOther) :=
  DAnchor.swap (swapRelabeling profile other hOther) (swap_vertexPartition_wall other hOther)
    ((remoteDetach input shape other hOther).candidate (swapShape shape input.valid.1 other hOther))
    (W2MkkGraphData.detachEquivalence (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther))
    (detach_sourceGenus (swapShape shape input.valid.1 other hOther)
      (remoteDetach input shape other hOther))
    (fun v ↦ W2PStarCensusProof.coreGraphData_branchSquare
      (W2MkkGraphData.detachGraphData (swapInput input other hOther)
        (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther)) v)
    (fun _ _ ↦ rfl)

end Anchor

/-! ## 2.  The positions of Equation (8), anchored -/

section Positions

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree}
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (detach : DetachData profile) (distinguished : Fin degree)

/-- Equation (8)'s family at the wall: `W2MkkLimitColumns.limitColumns`, with the wall's own
connectedness and genus facts (`RegrowthBalances.limit_connected`,
`RegrowthBalances.limit_genus`). -/
noncomputable abbrev columns : LimitColumns profile shape :=
  limitColumns input shape detach distinguished (RegrowthBalances.limit_connected w)
    (RegrowthBalances.limit_genus w)

/-- An anchor family along an equation of families. -/
noncomputable def anchorOf {L L' : LimitColumns profile shape} (h : L = L')
    (a : ∀ j, Anchor w (L'.member j)) (j : Fin 3) : Anchor w (L.member j) :=
  cast (congrArg (fun L : LimitColumns profile shape ↦ Anchor w (L.member j)) h.symm) (a j)

theorem anchorOf_iff {L L' : LimitColumns profile shape} (h : L = L')
    (a : ∀ j, Anchor w (L'.member j)) (j : Fin 3)
    (F : ∀ m : LimitMember w.limit (mergeVertex w), Anchor w m → Prop) :
    F (L.member j) (anchorOf shape h a j) ↔ F (L'.member j) (a j) := by
  subst h
  rfl

/-- The anchors of the Base II.2.1.M orientation: `M⁽¹⁾` and `M⁽³⁾` over the limit,
`M⁽²⁾` remote. -/
noncomputable def firstAnchor (member : FirstMember profile) :
    ∀ j, Anchor w ((firstOrientation input shape member distinguished
      (RegrowthBalances.limit_connected w) (RegrowthBalances.limit_genus w)).member j)
  | ⟨0, _⟩ => localAnchor input shape member.toDetachData
  | ⟨1, _⟩ => remoteAnchor input shape (secondSheet profile) (secondSheet_together profile)
  | ⟨2, _⟩ => joinedAnchor input shape distinguished

/-- The anchors of the Base II.2.2.M orientation: `M⁽²⁾` and `M⁽³⁾` over the limit,
`M⁽¹⁾` remote. -/
noncomputable def secondAnchor (member : SecondMember profile) :
    ∀ j, Anchor w ((secondOrientation input shape member distinguished
      (RegrowthBalances.limit_connected w) (RegrowthBalances.limit_genus w)).member j)
  | ⟨0, _⟩ => remoteAnchor input shape (firstSheet profile) (firstSheet_together profile)
  | ⟨1, _⟩ => localAnchor input shape member.toDetachData
  | ⟨2, _⟩ => joinedAnchor input shape distinguished

/-- **Every position of Equation (8) is anchored at the wall**, in both orientations. -/
noncomputable def limitAnchor (j : Fin 3) :
    Anchor w ((columns input shape detach distinguished).member j) :=
  if hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile) then
    anchorOf shape (limitColumns_eq_firstOrientation input shape detach distinguished _ _ hPin)
      (firstAnchor input shape distinguished ⟨detach, hPin⟩) j
  else
    anchorOf shape (limitColumns_eq_secondOrientation input shape detach distinguished _ _ hPin
        ((pinSheet_mem shape).resolve_left hPin))
      (secondAnchor input shape distinguished ⟨detach, (pinSheet_mem shape).resolve_left hPin⟩) j

end Positions

/-! ## 3.  The nonsingular positions of Equation (8) as star members (Stage 1) -/

section Census

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (detach : DetachData profile) (distinguished : Fin degree)
  (initial : StableLengthMatrixLabelling
    ((columns input shape detach distinguished).member 0).datum (Fin p))

/-- Equation (8)'s labelling of position `j`, induced from the initial one. -/
noncomputable abbrev lab (j : Fin 3) :=
  (columns input shape detach distinguished).labelling initial j

/-- The nonsingular positions of Equation (8). -/
def Nonsingular (j : Fin 3) : Prop :=
  ((columns input shape detach distinguished).squareMatrix initial j).det ≠ 0

/-- The full-dimensional presentation of a nonsingular position, from the regrowth's own
cover (`RegrowthBalances.regrowthPresentation`). -/
noncomputable def fdAt (j : Fin 3) (hj : Nonsingular w input shape detach distinguished initial j) :
    FullDimensionalSourcePresentation ((columns input shape detach distinguished).member j).datum
      (Fin p) :=
  RegrowthBalances.regrowthPresentation w hy (limitAnchor input shape detach distinguished j).E
    (((columns input shape detach distinguished).member j).valid_of_old input.valid)
    (limitAnchor input shape detach distinguished j).genus_eq
    (lab w input shape detach distinguished initial j) hj

/-- **The star member of a nonsingular position of Equation (8).** -/
noncomputable def rep (j : Fin 3) (hj : Nonsingular w input shape detach distinguished initial j) :
    GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := (limitAnchor input shape detach distinguished j).E)
    (fd := fdAt w hy input shape detach distinguished initial j hj)
    (hRetained := Anchor.retained (limitAnchor input shape detach distinguished j))
    (M := (limitAnchor input shape detach distinguished j).M)
    (φ := (limitAnchor input shape detach distinguished j).φ)
    (hMerge := (limitAnchor input shape detach distinguished j).hMerge)
    (hOld := (limitAnchor input shape detach distinguished j).hOld)
    (hEdge := (limitAnchor input shape detach distinguished j).hEdge)
    (limitAnchor input shape detach distinguished j).hV
    (limitAnchor input shape detach distinguished j).hR

/-- **The multiplicity of a position's star class is its term of Equation (8)**, up to
sign. -/
theorem multNat_rep (j : Fin 3) (hj : Nonsingular w input shape detach distinguished initial j) :
    (GeometricStar.Star.toFibre (rep w hy input shape detach distinguished initial j
        hj).cls).multNat =
      (signedMult (lab w input shape detach distinguished initial j).presentation).num.natAbs :=
  M11StarCensusProof.num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)

/-- A singular position contributes nothing to Equation (8). -/
theorem signedMult_eq_zero (j : Fin 3)
    (hj : ¬ Nonsingular w input shape detach distinguished initial j) :
    signedMult (lab w input shape detach distinguished initial j).presentation = 0 := by
  unfold Nonsingular at hj
  rw [not_not] at hj
  unfold signedMult
  rw [show GluingDatum.LengthMatrixPresentation.matrix
      (lab w input shape detach distinguished initial j).presentation =
    (columns input shape detach distinguished).squareMatrix initial j from rfl, hj, mul_zero]

include hy in
/-- **Every term of Equation (8) is an integer.** -/
theorem integral_signedMult (j : Fin 3) :
    ∃ value : ℤ,
      signedMult (lab w input shape detach distinguished initial j).presentation = (value : ℚ) := by
  by_cases hj : Nonsingular w input shape detach distinguished initial j
  · exact isIntegralMultiplicity (fdAt w hy input shape detach distinguished initial j hj)
  · exact ⟨0, by rw [signedMult_eq_zero w input shape detach distinguished initial j hj,
      Int.cast_zero]⟩

include hy in
/-- **Equation (8) at the wall, in the initial labelling**: from a nonsingular position's
own presentation (`W2MkkIncomingDenominator.sum_signedMult_eq_zero`), and trivially when
every position is singular. -/
theorem sum_signedMult_eq_zero :
    ∑ j : Fin 3, signedMult (lab w input shape detach distinguished initial j).presentation =
      0 := by
  by_cases h : ∃ j, Nonsingular w input shape detach distinguished initial j
  · obtain ⟨j, hj⟩ := h
    exact W2MkkIncomingDenominator.sum_signedMult_eq_zero input shape detach distinguished _ _
      j initial (fdAt w hy input shape detach distinguished initial j hj)
  · simp only [not_exists] at h
    exact Finset.sum_eq_zero fun j _ ↦
      signedMult_eq_zero w input shape detach distinguished initial j (h j)

end Census

/-! ## 4.  The regrown columns separate, except at a loop

Figure 34's regrown columns are `c(e₁)/(k₁-1) + c(e₂)/k₂ + s`,
`c(e₁)/k₁ + c(e₂)/(k₂-1) + s` and `c(e₃)/(k₁+k₂) + s`.  The third differs from the first
at `e₁`'s row and from the second at `e₂`'s; the first two agree only at a loop
(`r₁ = r₂`, and then only if `k₁ = k₂`), which no full-dimensional detaching member
admits (`loop_false`, the lollipop count of `W2PStarCensusProof.card_rowEdges_of_loop`). -/

section Columns

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall} {block : WallBlock data wall}
  {profile : SourceProfile data star block}

theorem backgroundColumn_nonneg (path : StablePath data) (label : Fin 2) :
    0 ≤ W2MkkCommonBalance.backgroundColumn star block path label :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

theorem one_lt_first_cast (shape : Shape profile) :
    (1 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) := by
  exact_mod_cast shape.one_lt_first

theorem one_lt_second_cast (shape : Shape profile) :
    (1 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) := by
  exact_mod_cast shape.one_lt_second

/-- `M⁽³⁾`'s column is never `M⁽¹⁾`'s: at `e₁`'s row the first is at most `1/(k₁+k₂)`
above the background, the second at least `1/(k₁-1)`. -/
theorem thirdNew_ne_firstNew (shape : Shape profile)
    (h : ∀ path, W2MkkCommonBalance.thirdNewColumn profile path =
      W2MkkCommonBalance.firstNewColumn profile path) : False := by
  have h1 := h (W2MkkCommonBalance.firstRow profile)
  have ha := one_lt_first_cast shape
  have hb := one_lt_second_cast shape
  simp only [W2MkkCommonBalance.thirdNewColumn, W2MkkCommonBalance.firstNewColumn,
    ite_true] at h1
  set a : ℚ := (data.sourceEdgeIndex profile.first.1 : ℚ)
  set b : ℚ := (data.sourceEdgeIndex profile.second.1 : ℚ)
  have hA : (if W2MkkCommonBalance.firstRow profile = W2MkkCommonBalance.thirdRow profile
      then (1 : ℚ) else 0) / (a + b) ≤ 1 / (a + b) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    split_ifs <;> norm_num
  have hB : (0 : ℚ) ≤ (if W2MkkCommonBalance.firstRow profile =
      W2MkkCommonBalance.secondRow profile then (1 : ℚ) else 0) / b := by
    apply div_nonneg _ (by linarith)
    split_ifs <;> norm_num
  have hC : 1 / (a + b) < 1 / (a - 1) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  linarith

/-- `M⁽³⁾`'s column is never `M⁽²⁾`'s (the mirror, at `e₂`'s row). -/
theorem thirdNew_ne_secondNew (shape : Shape profile)
    (h : ∀ path, W2MkkCommonBalance.thirdNewColumn profile path =
      W2MkkCommonBalance.secondNewColumn profile path) : False := by
  have h1 := h (W2MkkCommonBalance.secondRow profile)
  have ha := one_lt_first_cast shape
  have hb := one_lt_second_cast shape
  simp only [W2MkkCommonBalance.thirdNewColumn, W2MkkCommonBalance.secondNewColumn,
    ite_true] at h1
  set a : ℚ := (data.sourceEdgeIndex profile.first.1 : ℚ)
  set b : ℚ := (data.sourceEdgeIndex profile.second.1 : ℚ)
  have hA : (if W2MkkCommonBalance.secondRow profile = W2MkkCommonBalance.thirdRow profile
      then (1 : ℚ) else 0) / (a + b) ≤ 1 / (a + b) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    split_ifs <;> norm_num
  have hB : (0 : ℚ) ≤ (if W2MkkCommonBalance.secondRow profile =
      W2MkkCommonBalance.firstRow profile then (1 : ℚ) else 0) / a := by
    apply div_nonneg _ (by linarith)
    split_ifs <;> norm_num
  have hC : 1 / (a + b) < 1 / (b - 1) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  linarith

/-- **Equal `M⁽¹⁾` and `M⁽²⁾` columns force a loop**: `e₁` and `e₂` on one stable row. -/
theorem firstRow_eq_of_new_eq (shape : Shape profile)
    (h : ∀ path, W2MkkCommonBalance.secondNewColumn profile path =
      W2MkkCommonBalance.firstNewColumn profile path) :
    W2MkkCommonBalance.firstRow profile = W2MkkCommonBalance.secondRow profile := by
  classical
  by_contra hNe
  have h1 := h (W2MkkCommonBalance.firstRow profile)
  have ha := one_lt_first_cast shape
  simp only [W2MkkCommonBalance.firstNewColumn, W2MkkCommonBalance.secondNewColumn,
    ite_true, if_neg hNe, zero_div, add_zero] at h1
  set a : ℚ := (data.sourceEdgeIndex profile.first.1 : ℚ)
  have hlt : 1 / a < 1 / (a - 1) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
  linarith

variable (input : W2SourceInput data star) (shape : Shape profile)

/-- A detaching member's regrown column meets `e₁`'s row. -/
theorem localMember_new_ne_zero (detach : DetachData profile) :
    (localMember input shape detach).newColumnValue (W2MkkCommonBalance.firstRow profile) ≠ 0 := by
  have ha := one_lt_first_cast shape
  have hb := one_lt_second_cast shape
  have hs := backgroundColumn_nonneg (star := star) (block := block)
    (W2MkkCommonBalance.firstRow profile) profile.doubleLabel
  have hB1 : (0 : ℚ) ≤ (if W2MkkCommonBalance.firstRow profile =
      W2MkkCommonBalance.secondRow profile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    apply div_nonneg _ (by linarith)
    split_ifs <;> norm_num
  have hB2 : (0 : ℚ) ≤ (if W2MkkCommonBalance.firstRow profile =
      W2MkkCommonBalance.secondRow profile then (1 : ℚ) else 0) /
        ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) := by
    apply div_nonneg _ (by linarith)
    split_ifs <;> norm_num
  rcases pinSheet_mem shape with hPin | hPin
  · rw [localMember_regrown_first input shape ⟨detach, hPin⟩]
    simp only [W2MkkCommonBalance.firstNewColumn, ite_true]
    have : (0 : ℚ) < 1 / ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) :=
      one_div_pos.mpr (by linarith)
    linarith
  · rw [localMember_regrown_second input shape ⟨detach, hPin⟩]
    simp only [W2MkkCommonBalance.secondNewColumn, ite_true]
    have : (0 : ℚ) < 1 / (data.sourceEdgeIndex profile.first.1 : ℚ) :=
      one_div_pos.mpr (by linarith)
    linarith

include input in
/-- **A loop wall has no full-dimensional detaching member**: the loop row would be a
lollipop row with two occurrences (`W2PStarCensusProof.card_rowEdges_of_loop`), while it
carries the retained `e₁`, `e₂` and a regrown occurrence. -/
theorem loop_false
    (hRow : W2MkkCommonBalance.firstRow profile = W2MkkCommonBalance.secondRow profile)
    (detach : DetachData profile)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (detach.candidate shape).datum coordinate) :
    False := by
  classical
  let c := detach.candidate shape
  let E := W2MkkGraphData.detachEquivalence input shape detach
  let e1 : NonDanglingEdge data := ⟨profile.first.1, profile.first_survives⟩
  let e2 : NonDanglingEdge data := ⟨profile.second.1, profile.second_survives⟩
  have hNe : e1 ≠ e2 := fun h ↦
    profile.first_ne_second (Subtype.ext (congrArg (fun e : NonDanglingEdge data ↦ e.1) h))
  let A : BranchVertex data := ⟨WallBlock.sourceVertex data wall block, profile.valency.ge⟩
  have hTwo := W2PStarCensusProof.card_rowEdges_of_loop A hNe profile.first.2 profile.second.2
    hRow.symm fd E
  set R := E.row e1.stablePath with hR
  have hNew : StableSourceMatrix.matrix c.datum R (occurrenceEquiv target wall c.right none) ≠ 0 :=
    localMember_new_ne_zero input shape detach
  obtain ⟨z, hzSurv, hzRow, hzTarget⟩ := M11StarCensusProof.exists_occurrence_of_matrix_ne_zero hNew
  let x := ResolutionAwayFromWall.retainedEdge c input.valid.1 e1
  let y := ResolutionAwayFromWall.retainedEdge c input.valid.1 e2
  have hxR : x.stablePath = R := rfl
  have hyR : y.stablePath = R :=
    (show y.stablePath = E.row e2.stablePath from rfl).trans (congrArg E.row hRow.symm)
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

end Columns

section Separation

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (detach : DetachData profile) (distinguished : Fin degree)
  (initial : StableLengthMatrixLabelling
    ((columns input shape detach distinguished).member 0).datum (Fin p))

/-- A frame isomorphism between positions preserves the regrown column. -/
theorem newColumn_eq_of_frameIso {j j' : Fin 3}
    {hj : Nonsingular w input shape detach distinguished initial j}
    {hj' : Nonsingular w input shape detach distinguished initial j'}
    (fi : GeometricSegmentWalls.FrameIso
      (rep w hy input shape detach distinguished initial j hj).member.frame
      (rep w hy input shape detach distinguished initial j' hj').member.frame)
    (path : StablePath w.limit) :
    W2MkkCommonBalance.newColumn profile j' path = W2MkkCommonBalance.newColumn profile j path := by
  have h := StarCensusEngine.frameIso_matrix_new
    (E := (limitAnchor input shape detach distinguished j).E)
    (E' := (limitAnchor input shape detach distinguished j').E)
    (Anchor.retained (limitAnchor input shape detach distinguished j))
    (Anchor.retained (limitAnchor input shape detach distinguished j')) fi path
  rwa [Anchor.matrix_new, Anchor.matrix_new, (columns input shape detach distinguished).regrown,
    (columns input shape detach distinguished).regrown] at h

theorem not_rel_02 {h0 : Nonsingular w input shape detach distinguished initial 0}
    {h2 : Nonsingular w input shape detach distinguished initial 2} :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso
      (rep w hy input shape detach distinguished initial 0 h0).member.frame
      (rep w hy input shape detach distinguished initial 2 h2).member.frame) := fun ⟨fi⟩ ↦
  thirdNew_ne_firstNew shape (newColumn_eq_of_frameIso w hy input shape detach distinguished
    initial fi)

theorem not_rel_12 {h1 : Nonsingular w input shape detach distinguished initial 1}
    {h2 : Nonsingular w input shape detach distinguished initial 2} :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso
      (rep w hy input shape detach distinguished initial 1 h1).member.frame
      (rep w hy input shape detach distinguished initial 2 h2).member.frame) := fun ⟨fi⟩ ↦
  thirdNew_ne_secondNew shape (newColumn_eq_of_frameIso w hy input shape detach distinguished
    initial fi)

/-- **`M⁽¹⁾` and `M⁽²⁾` are distinct star classes**: equal columns force a loop, and the
local detaching position (nonsingular by hypothesis) is a full-dimensional detaching
member. -/
theorem not_rel_01 {h0 : Nonsingular w input shape detach distinguished initial 0}
    {h1 : Nonsingular w input shape detach distinguished initial 1} :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso
      (rep w hy input shape detach distinguished initial 0 h0).member.frame
      (rep w hy input shape detach distinguished initial 1 h1).member.frame) := by
  rintro ⟨fi⟩
  have hRow := firstRow_eq_of_new_eq shape
    (newColumn_eq_of_frameIso w hy input shape detach distinguished initial fi)
  by_cases hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
  · exact loop_false input shape hRow detach
      ((limitColumns_member_zero_of_first input shape detach distinguished _ _ hPin) ▸
        fdAt w hy input shape detach distinguished initial 0 h0)
  · exact loop_false input shape hRow detach
      ((limitColumns_member_one_of_second input shape detach distinguished _ _ hPin
        ((pinSheet_mem shape).resolve_left hPin)) ▸
        fdAt w hy input shape detach distinguished initial 1 h1)

end Separation

/-! ## 5.  The census from exhaustion (Stage 2) -/

section Assembly

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (detach : DetachData profile) (distinguished : Fin degree)
  (initial : StableLengthMatrixLabelling
    ((columns input shape detach distinguished).member 0).datum (Fin p))

/-- **Distinct nonsingular positions are distinct star classes** (Stage 3), at every
wall. -/
theorem rep_eq_of_cls_eq (j : Fin 3) (hj : Nonsingular w input shape detach distinguished initial j)
    (j' : Fin 3) (hj' : Nonsingular w input shape detach distinguished initial j')
    (h : (rep w hy input shape detach distinguished initial j hj).cls = (rep w hy input shape
        detach distinguished initial j' hj').cls) : j = j' := by
  have hRel := Quotient.exact h
  have hRel' : Nonempty (GeometricSegmentWalls.FrameIso (rep w hy input shape detach distinguished
      initial j' hj').member.frame
      (rep w hy input shape detach distinguished initial j hj).member.frame) :=
    hRel.elim fun fi ↦ ⟨fi.symm⟩
  fin_cases j <;> fin_cases j'
  · rfl
  · exact (not_rel_01 w hy input shape detach distinguished initial hRel).elim
  · exact (not_rel_02 w hy input shape detach distinguished initial hRel).elim
  · exact (not_rel_01 w hy input shape detach distinguished initial hRel').elim
  · rfl
  · exact (not_rel_12 w hy input shape detach distinguished initial hRel).elim
  · exact (not_rel_02 w hy input shape detach distinguished initial hRel').elim
  · exact (not_rel_12 w hy input shape detach distinguished initial hRel').elim
  · rfl

/-- The positions' classes, as a map from the nonsingular positions to the star. -/
noncomputable def repCls (j : {j : Fin 3 // Nonsingular w input shape detach distinguished initial
    j}) :
    GeometricStar.Star hy w :=
  (rep w hy input shape detach distinguished initial j.1 j.2).cls

theorem repCls_injective : Function.Injective (repCls w hy input shape detach distinguished
    initial) :=
  fun a b h ↦ Subtype.ext (rep_eq_of_cls_eq w hy input shape detach distinguished initial a.1 a.2
      b.1 b.2 h)

/-- **Exhaustion at one wall** (Stage 2): every member of the star is in the
class of some nonsingular position.  *Interface*: with Stages 1 and 3 it is equivalent to
the census at this wall (`census_of_exhaustion`, `exhaustion_of_census`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ j : Fin 3,
    ∃ hj : Nonsingular w input shape detach distinguished initial j, member.cls = (rep w hy input
        shape detach distinguished initial j hj).cls

theorem repCls_surjective (hExh : Exhausts w hy input shape detach distinguished initial) :
    Function.Surjective (repCls w hy input shape detach distinguished initial) := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨j, hj, h⟩ := hExh member
  exact ⟨⟨j, hj⟩, h.symm⟩

/-- **The M-kk census at one wall from exhaustion.** -/
theorem census_of_exhaustion (hExh : Exhausts w hy input shape detach distinguished initial) :
    ∃ e : {j : Fin 3 // Nonsingular w input shape detach distinguished initial j} ≃
        GeometricStar.Star hy w,
      ∀ j, (GeometricStar.Star.toFibre (e j)).multNat =
        (signedMult (lab w input shape detach distinguished initial j.1).presentation).num.natAbs :=
  ⟨Equiv.ofBijective _ ⟨repCls_injective w hy input shape detach distinguished initial,
      repCls_surjective w hy input shape detach distinguished initial hExh⟩,
    fun j ↦ multNat_rep w hy input shape detach distinguished initial j.1 j.2⟩

/-- **Interface: the census implies exhaustion.** -/
theorem exhaustion_of_census
    (e : {j : Fin 3 // Nonsingular w input shape detach distinguished initial j} ≃
        GeometricStar.Star hy w) :
    Exhausts w hy input shape detach distinguished initial := by
  classical
  have hBij : Function.Bijective (repCls w hy input shape detach distinguished initial) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨repCls_injective w hy input shape detach distinguished initial, Fintype.card_congr e⟩
  intro member
  obtain ⟨j, hj⟩ := hBij.2 member.cls
  exact ⟨j.1, j.2, hj.symm⟩

/-- **The star clause from Equation (8) and the census**: the singular positions
contribute `0`, the census reads the nonsingular ones as the star
(`StarCensusEngine.starParityAt_of_census`). -/
theorem starParityAt_of_census
    (e : {j : Fin 3 // Nonsingular w input shape detach distinguished initial j} ≃
        GeometricStar.Star hy w)
    (hmult : ∀ j, (GeometricStar.Star.toFibre (e j)).multNat =
      (signedMult (lab w input shape detach distinguished initial j.1).presentation).num.natAbs) :
    RegrowthWallInput.StarParityAt hy w :=
  StarCensusEngine.starParityAt_of_census (fun j ↦ signedMult (lab w input shape detach
      distinguished initial j).presentation)
    (integral_signedMult w hy input shape detach distinguished initial) (sum_signedMult_eq_zero w
        hy input shape detach distinguished initial)
    (Nonsingular w input shape detach distinguished initial) (signedMult_eq_zero w input shape
        detach distinguished initial) e hmult

/-- **Stage 2 is the whole content of the clause at a wall.** -/
theorem starParityAt_of_exhaustion (hExh : Exhausts w hy input shape detach distinguished initial) :
    RegrowthWallInput.StarParityAt hy w := by
  obtain ⟨e, hmult⟩ := census_of_exhaustion w hy input shape detach distinguished initial hExh
  exact starParityAt_of_census w hy input shape detach distinguished initial e hmult

end Assembly

/-! ## 6.  Stage 2 reduced to decoupled transports -/

section Transport

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (detach : DetachData profile) (distinguished : Fin degree)
  (initial : StableLengthMatrixLabelling
    ((columns input shape detach distinguished).member 0).datum (Fin p))

/-- **What a member must present to be received at position `j`**: a decoupled
transport, along its limit isomorphism composed with the position's anchor inverse, from
its own normal form at some placement onto the position's pasted resolution. -/
abbrev PositionTransport (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : PlacementSpec other placement) (j : Fin 3) : Type :=
  ResolutionExpansionFree.TransportFree
    (ψ.datum.trans (limitAnchor input shape detach distinguished j).φ.symm) (mergeVertex other)
    (mergeVertex w) placement ((columns input shape detach distinguished).member j).right
    (memberResolution other placement hPlacement)
    (limitAnchor input shape detach distinguished j).res

/-- **Stage 2 reduced to transports.** -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w,
      ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
      ∃ hPlacement : PlacementSpec member.member placement,
      ∃ j : Fin 3, ∃ _ : Nonsingular w input shape detach distinguished initial j,
        Nonempty (PositionTransport w hy input shape detach distinguished member.member ψ
          placement hPlacement j)) :
    Exhausts w hy input shape detach distinguished initial := by
  intro member
  obtain ⟨ψ, placement, hPlacement, j, hj, ⟨t⟩⟩ := h member
  refine ⟨j, hj, ?_⟩
  have hNV := M11WallExhaustion.sourceVertexMap_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  have hNE := M11WallExhaustion.retainedSourceEdge_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
    (E := (limitAnchor input shape detach distinguished j).E)
    (fd := fdAt w hy input shape detach distinguished initial j hj)
    (hRetained := Anchor.retained (limitAnchor input shape detach distinguished j))
    (M := (limitAnchor input shape detach distinguished j).M)
    (φ := (limitAnchor input shape detach distinguished j).φ)
    (hMerge := (limitAnchor input shape detach distinguished j).hMerge)
    (hOld := (limitAnchor input shape detach distinguished j).hOld)
    (hEdge := (limitAnchor input shape detach distinguished j).hEdge)
    (limitAnchor input shape detach distinguished j).hV
    (limitAnchor input shape detach distinguished j).hR
    (compat := (limitAnchor input shape detach distinguished j).compat)
    (limitAnchor input shape detach distinguished j).hD
    member ψ (memberNorm member.member placement hPlacement) hNV hNE t

end Transport

/-! ## 7.  The family clause -/

section Family

/-- **The M-kk star census**: at every `w2Mkk` regrowth, for every Equation (8) family and
labelling, the nonsingular positions are the star, class by class, with their
multiplicities. -/
def W2MkkStarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2Mkk →
    ∀ (star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W2SourceInput w.limit star) (block : WallBlock w.limit (mergeVertex w))
      (profile : SourceProfile w.limit star block) (shape : Shape profile)
      (detach : DetachData profile) (distinguished : Fin degree)
      (initial : StableLengthMatrixLabelling
        ((columns input shape detach distinguished).member 0).datum (Fin p)),
      ∃ e : {j : Fin 3 // Nonsingular w input shape detach distinguished initial j} ≃
          GeometricStar.Star hy w,
        ∀ j, (GeometricStar.Star.toFibre (e j)).multNat =
          (signedMult (lab w input shape detach distinguished initial j.1).presentation).num.natAbs

/-- **Stage 2 (exhaustion), family-wide.**  *Interface*: equivalent to `W2MkkStarCensus`
(`w2MkkStarExhaustion_iff`). -/
def W2MkkStarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2Mkk →
    ∀ (star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W2SourceInput w.limit star) (block : WallBlock w.limit (mergeVertex w))
      (profile : SourceProfile w.limit star block) (shape : Shape profile)
      (detach : DetachData profile) (distinguished : Fin degree)
      (initial : StableLengthMatrixLabelling
        ((columns input shape detach distinguished).member 0).datum (Fin p)),
      Exhausts w hy input shape detach distinguished initial

variable {degree n p : ℕ}

theorem w2MkkStarCensus_of_exhaustion (hExh : W2MkkStarExhaustion degree n p) :
    W2MkkStarCensus degree n p :=
  fun core y hy w cls htag star input block profile shape detach distinguished initial ↦
    census_of_exhaustion w hy input shape detach distinguished initial
      (hExh core y hy w cls htag star input block profile shape detach distinguished initial)

theorem exhaustion_of_w2MkkStarCensus (hCensus : W2MkkStarCensus degree n p) :
    W2MkkStarExhaustion degree n p :=
  fun core y hy w cls htag star input block profile shape detach distinguished initial ↦
    exhaustion_of_census w hy input shape detach distinguished initial
      (hCensus core y hy w cls htag star input block profile shape detach distinguished
        initial).choose

/-- **Interface**: exhaustion is equivalent to the census. -/
theorem w2MkkStarExhaustion_iff :
    W2MkkStarExhaustion degree n p ↔ W2MkkStarCensus degree n p :=
  ⟨w2MkkStarCensus_of_exhaustion, exhaustion_of_w2MkkStarCensus⟩

/-- **`FamilyStarParity … .w2Mkk` from the M-kk star census**: Equation (8) at the
regrowth, read mod two through the census, at the wall labelling of position `0`
(`StarCensusEngine.labelling`). -/
theorem familyStarParity_w2Mkk_of_census (h : W2MkkStarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w2Mkk := by
  intro core y hy w cls htag
  obtain ⟨star, input, block, profile, shape, detach, distinguished, -⟩ :=
    RegrowthBalances.exists_w2Mkk_balance w hy cls htag
  let initial := StarCensusEngine.labelling w hy
    ((columns input shape detach distinguished).member 0).datum
    (limitAnchor input shape detach distinguished 0).E
  obtain ⟨e, hmult⟩ :=
    h core y hy w cls htag star input block profile shape detach distinguished initial
  exact starParityAt_of_census w hy input shape detach distinguished initial e hmult

/-- **The `w2Mkk` clause of `FamilyStarParity` at genus six and degree four**, modulo
Stage 2's exhaustion alone. -/
theorem familyStarParity_w2Mkk_of_exhaustion
    (hExh : W2MkkStarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2Mkk :=
  familyStarParity_w2Mkk_of_census (w2MkkStarCensus_of_exhaustion hExh)

end Family

end DraismaVargas.Count.W2MkkStarCensusProof
