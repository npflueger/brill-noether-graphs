module

public import DraismaVargasCount.IntegerCount.StarBalance
public import DraismaVargasCount.M11StarExhaustionProof
public import DraismaVargasCount.W2M1kStarExhaustionProof
public import DraismaVargasCount.W2MkkStarExhaustionProof
public import DraismaVargasCount.W2PStarExhaustionProof
public import DraismaVargasCount.W2R1StarExhaustionProof

@[expose] public section

/-!
# The balance by sides at the divalent walls

The integer twins of the five divalent family clauses of `EvenGenusParity.familyStarParity`
(Equations (6)--(10) of Draisma--Vargas Part I): `M11StarParityFree.familyStarParity_w2M11_of_census`
and `W2M1kStarExhaustionProof.familyStarParity_w2M1k_general`, `…_w2Mkk_general`,
`…_w2P_general`, `…_w2R1_general`.  The route is that of `StarBalanceW3`: a `SignedStarCensus`
from the census as constructed (`repCls`, made bijective by the family's exhaustion theorem),
the family's balance and integrality lemmas, and a side law.

**The side law (done once for all five families).**  Every W2 family
labels its positions in the same shape (`…CommonBalance.LimitColumns.labelling`,
`M11CommonBalance.labelling`): rows through the position's row bijection from the wall's
stable paths followed by one map `sourceCoordinates` common to all positions, columns through
one map `targetCoordinates` to `Option` of the limit target's edges followed by the position's
occurrence map.  The engine labelling `StarCensusEngine.labelling` has exactly the same shape,
with the wall's inherited row labels and `W4StarParity.columnEquiv w`, and each family's
position frames are engine frames whose dictionary rows are that row bijection.  So the two
labellings of one position differ by a row permutation and a column permutation that do not
depend on the position (`labellingSign`, `det_labelling_eq`), and the engine side law
`opensToward_engineFrame_iff` transfers with the one sign `commonSign`
(`opensToward_engineFrame_iff_of_common`).

## Contents

* `labellingSign`, `det_labelling_eq`, `signedMult_eq_mul_det`, `pos_mul_signedMult_iff`,
  `pos_mul_signedMult_labelling_iff`: two labellings of one datum.
* `commonSign`, `commonNumerator`, `commonNumerator_neg`, `opensToward_engineFrame_iff_of_common`:
  the side law in a labelling sharing the engine's coordinate shape.
* `familyStarBalance_w2M11`, `…_w2M1k`, `…_w2Mkk`, `…_w2P`, `…_w2R1`: the five clauses.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation (matrix)
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Two labellings of one datum: the sign of the signed multiplicity

Two labellings of one datum on one coordinate type differ by a row and a column permutation
(`matrix_labelling_submatrix`), so their determinants differ by the product of the two signs,
and their signed multiplicities, which are positive multiples of the determinants, have signs
related by the same factor. -/

section Labellings

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- The sign relating two labellings of one datum: the sign of the row permutation times the
sign of the column permutation. -/
noncomputable def labellingSign (L L' : StableLengthMatrixLabelling data coordinate) : ℚ :=
  ((Equiv.Perm.sign (L.row.symm.trans L'.row) *
    Equiv.Perm.sign (L.targetEdge.trans L'.targetEdge.symm) : ℤˣ) : ℤ)

/-- **The determinants of two labellings differ by `labellingSign`.** -/
theorem det_labelling_eq (L L' : StableLengthMatrixLabelling data coordinate) :
    (matrix L.presentation).det = labellingSign L L' * (matrix L'.presentation).det := by
  rw [matrix_labelling_submatrix L L', labellingSign,
    show (matrix L'.presentation).submatrix (L.row.symm.trans L'.row)
        (L.targetEdge.trans L'.targetEdge.symm) =
      ((matrix L'.presentation).submatrix (L.row.symm.trans L'.row) id).submatrix id
        (L.targetEdge.trans L'.targetEdge.symm) from rfl,
    Matrix.det_permute', Matrix.det_permute]
  push_cast
  ring

/-- The signed multiplicity is a positive multiple of the determinant. -/
theorem signedMult_eq_mul_det (P : data.LengthMatrixPresentation coordinate) :
    signedMult P = ((denominatorProduct P : ℚ) / 2 ^ leafCount target) * (matrix P).det := rfl

theorem signedMult_factor_pos (P : data.LengthMatrixPresentation coordinate) :
    (0 : ℚ) < (denominatorProduct P : ℚ) / 2 ^ leafCount target := by
  have := denominatorProduct_pos P
  positivity

/-- **The sign of a product with a signed multiplicity is that of the product with the
determinant.** -/
theorem pos_mul_signedMult_iff (N : ℚ) (P : data.LengthMatrixPresentation coordinate) :
    0 < N * signedMult P ↔ 0 < N * (matrix P).det := by
  rw [signedMult_eq_mul_det, show N * ((denominatorProduct P : ℚ) / 2 ^ leafCount target *
    (matrix P).det) = (N * (matrix P).det) * ((denominatorProduct P : ℚ) / 2 ^ leafCount target)
    by ring]
  exact mul_pos_iff_of_pos_right (signedMult_factor_pos P)

/-- **The side condition read in another labelling**: `0 < N · Mult(L)` exactly when
`0 < (labellingSign L L' · N) · Mult(L')`. -/
theorem pos_mul_signedMult_labelling_iff (N : ℚ) (L L' : StableLengthMatrixLabelling data coordinate) :
    0 < N * signedMult L.presentation ↔ 0 < labellingSign L L' * N * signedMult L'.presentation := by
  rw [pos_mul_signedMult_iff, pos_mul_signedMult_iff, det_labelling_eq L L', ← mul_assoc,
    mul_comm N]

end Labellings

/-! ## 2.  The side law for a labelling sharing the engine's row and column coordinates

Every W2 family labels its positions the same way: the rows through the position's row
bijection from the wall's stable paths, then one coordinate map `rowCoord` common to all
positions; the columns through one coordinate map `colCoord` to `Option` of the limit
target's edges, common to all positions, then the position's occurrence map.  The engine
labelling (`StarCensusEngine.labelling`) has the same shape, with the wall's inherited row
labels and `W4StarParity.columnEquiv w`.  So the two labellings of one position differ by
permutations that do not depend on the position, and the side law of the engine labelling
(`opensToward_engineFrame_iff`) transfers with one sign, `commonSign`. -/

section Common

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The sign relating the engine labelling to a labelling with row coordinates `rowCoord` and
column coordinates `colCoord`. -/
noncomputable def commonSign (w : Regrowth core y degree) (hy : Nondegenerate y)
    (rowCoord : W4StableSource.StablePath w.limit ≃ Fin p)
    (colCoord : Fin p ≃ Option (w.frame.limitTarget w.column).edges) : ℚ :=
  ((Equiv.Perm.sign ((InheritedLimitRows.rowLabel w hy).symm.trans rowCoord) *
    Equiv.Perm.sign ((W4StarParity.columnEquiv w).trans colCoord.symm) : ℤˣ) : ℤ)

/-- The numerator of the side law in such a labelling. -/
noncomputable def commonNumerator (w : Regrowth core y degree) (hy : Nondegenerate y)
    (rowCoord : W4StableSource.StablePath w.limit ≃ Fin p)
    (colCoord : Fin p ≃ Option (w.frame.limitTarget w.column).edges) (d : Fin p → ℚ) : ℚ :=
  commonSign w hy rowCoord colCoord * wallNumeratorAt w d

theorem commonNumerator_neg (w : Regrowth core y degree) (hy : Nondegenerate y)
    (rowCoord : W4StableSource.StablePath w.limit ≃ Fin p)
    (colCoord : Fin p ≃ Option (w.frame.limitTarget w.column).edges) (d : Fin p → ℚ) :
    commonNumerator w hy rowCoord colCoord (-d) = -commonNumerator w hy rowCoord colCoord d := by
  rw [commonNumerator, commonNumerator, wallNumeratorAt_neg, mul_neg]

/-- **The side law in a common labelling.**  An engine position frame opens toward `d` exactly
when `commonNumerator … d` and the signed multiplicity of `L` have the same strict sign, for any
labelling `L` of the position whose rows read the wall's stable paths through `E` and then
`rowCoord`, and whose columns read `colCoord` and then the position's occurrence map. -/
theorem opensToward_engineFrame_iff_of_common (w : Regrowth core y degree) (hy : Nondegenerate y)
    {right : (w.frame.limitTarget w.column).edges → Bool}
    {D : GluingDatum (TargetExpansion.graph (w.frame.limitTarget w.column)
      (W4WallExhaustion.mergeVertex w) right) degree}
    {E : StableGraphIncidence.Equivalence w.limit D}
    (fd : FullDimensionalSource.FullDimensionalSourcePresentation D (Fin p))
    (hRetained : ∀ (path : W4StableSource.StablePath w.limit)
      (place : (w.frame.limitTarget w.column).edges),
      StableSourceMatrix.matrix D (E.row path)
          (TargetExpansion.occurrenceEquiv (w.frame.limitTarget w.column)
            (W4WallExhaustion.mergeVertex w) right (some place)) =
        StableSourceMatrix.matrix w.limit path place)
    (rowCoord : W4StableSource.StablePath w.limit ≃ Fin p)
    (colCoord : Fin p ≃ Option (w.frame.limitTarget w.column).edges)
    (L : StableLengthMatrixLabelling D (Fin p))
    (hRow : ∀ path, L.row (E.row path) = rowCoord path)
    (hCol : ∀ c, L.targetEdge c = TargetExpansion.occurrenceEquiv (w.frame.limitTarget w.column)
      (W4WallExhaustion.mergeVertex w) right (colCoord c))
    (d : Fin p → ℚ) :
    OpensToward (GeometricFibre.cls ((StarCensusEngine.frame w hy D E fd).member y)) d ↔
      0 < commonNumerator w hy rowCoord colCoord d * signedMult L.presentation := by
  rw [opensToward_engineFrame_iff w hy fd hRetained d,
    pos_mul_signedMult_labelling_iff _ _ L, commonNumerator]
  have hσ : (StarCensusEngine.labelling w hy D E).row.symm.trans L.row =
      (InheritedLimitRows.rowLabel w hy).symm.trans rowCoord := by
    refine Equiv.ext fun x ↦ ?_
    change L.row (E.row ((InheritedLimitRows.rowLabel w hy).symm x)) = _
    rw [hRow]
    rfl
  have hτ : (StarCensusEngine.labelling w hy D E).targetEdge.trans L.targetEdge.symm =
      (W4StarParity.columnEquiv w).trans colCoord.symm := by
    refine Equiv.ext fun x ↦ ?_
    change L.targetEdge.symm (TargetExpansion.occurrenceEquiv (w.frame.limitTarget w.column)
      (W4WallExhaustion.mergeVertex w) right (W4StarParity.columnEquiv w x)) = _
    rw [Equiv.symm_apply_eq, hCol]
    simp
  rw [labellingSign, hσ, hτ, commonSign]

end Common

/-- **W2 M11 (Equation (6)) is balanced by sides.**  Proved.  Census
`M11StarExhaustionProof.m11StarExhaustion`; balance `M11StarParityFree.exists_balance`; the
parity consumer `M11StarParityFree.starParityAt_of_census` shows the bookkeeping. -/
theorem familyStarBalance_w2M11 (degree n p : ℕ) : FamilyStarBalance degree n p .w2M11 := by
  intro core y hy w cls htag
  obtain ⟨star, input, block, profile, hCard, incoming, fd, hbal⟩ :=
    M11StarParityFree.exists_balance w hy cls htag
  have hExh := M11StarExhaustionProof.m11StarExhaustion degree n p core y hy w cls htag star
    input block profile hCard incoming fd
  have hBij : Function.Bijective (M11StarCensusProof.repCls w hy input profile hCard fd) :=
    ⟨M11StarCensusProof.repCls_injective w hy input profile hCard fd
        (M11StarCensusProof.not_sameDoubleRow_of_regrowth w hy input profile hCard),
      M11StarCensusProof.repCls_surjective w hy input profile hCard fd hExh⟩
  let initial := M11FullDimensional.initialLabelling input profile hCard incoming fd
  let rowCoord := M11CommonBalance.sourceCoordinates input profile hCard initial
  let colCoord := M11CommonBalance.targetCoordinates input profile hCard initial
  have hSide : ∀ (q : {q // M11StarParityFree.Nonsingular input profile hCard incoming fd q})
      (d : Fin p → ℚ),
      OpensToward
          (GeometricStar.Star.toFibre (M11StarCensusProof.repCls w hy input profile hCard fd q)) d ↔
        0 < commonNumerator w hy rowCoord colCoord d *
          signedMult (M11StarParityFree.lab input profile hCard incoming fd q.1).presentation := by
    rintro ⟨⟨_ | _ | _ | k, hk⟩, hq⟩ d
    · exact opensToward_engineFrame_iff_of_common w hy
        (E := M11SplitStableGraph.equivalence input profile hCard)
        (M11StarCensusProof.fdAt w input profile hCard fd _ hq)
        (M11SplitLimitMatrix.matrix_retained input profile hCard) rowCoord colCoord
        (M11StarParityFree.lab input profile hCard incoming fd ⟨0, hk⟩)
        (fun path ↦ congrArg rowCoord
          ((M11CommonBalance.rowEquiv input profile hCard 0).symm_apply_apply path))
        (fun _ ↦ rfl) d
    · exact opensToward_engineFrame_iff_of_common w hy
        (E := M11StableGraphs.remote input profile hCard)
        (M11StarCensusProof.fdAt w input profile hCard fd _ hq)
        (M11RemoteLimitMatrix.matrix_retained input profile hCard) rowCoord colCoord
        (M11StarParityFree.lab input profile hCard incoming fd ⟨1, hk⟩)
        (fun path ↦ congrArg rowCoord
          ((M11CommonBalance.rowEquiv input profile hCard 1).symm_apply_apply path))
        (fun _ ↦ rfl) d
    · exact opensToward_engineFrame_iff_of_common w hy
        (E := M11JoinedStableGraph.equivalence input profile hCard)
        (M11StarCensusProof.fdAt w input profile hCard fd _ hq)
        (M11JoinedLimitMatrix.matrix_retained input profile hCard) rowCoord colCoord
        (M11StarParityFree.lab input profile hCard incoming fd ⟨2, hk⟩)
        (fun path ↦ congrArg rowCoord
          ((M11CommonBalance.rowEquiv input profile hCard 2).symm_apply_apply path))
        (fun _ ↦ rfl) d
    · omega
  exact starBalanceAt_of_signedCensus
    { ι := Fin 3
      term := fun q ↦ signedMult (M11StarParityFree.lab input profile hCard incoming fd q).presentation
      integral := M11StarParityFree.integral_signedMult (W4StarParity.limitTarget_connected w)
        (W4StarParity.limitTarget_genus w)
      balance := hbal
      nonsingular := M11StarParityFree.Nonsingular input profile hCard incoming fd
      zero_of_singular := fun q hq ↦ by
        unfold M11StarParityFree.Nonsingular at hq
        rw [not_not] at hq
        rw [signedMult_eq_mul_det, hq, mul_zero]
      equiv := Equiv.ofBijective _ hBij
      multNat_equiv := fun q ↦ M11StarCensusProof.multNat_rep w hy input profile hCard fd q.1 q.2
      numerator := commonNumerator w hy rowCoord colCoord
      numerator_neg := commonNumerator_neg w hy _ _
      side := hSide }

/-- **W2 M1k (Equation (7)) is balanced by sides.**  Proved.  Census
`W2M1kStarExhaustionProof.w2M1kStarExhaustion`, map `W2M1kStarCensusProof.repCls`; balance
`RegrowthBalances.exists_w2M1k_balance`; parity consumer
`W2M1kStarCensusProof.starParityAt_of_census`. -/
theorem familyStarBalance_w2M1k (degree n p : ℕ) : FamilyStarBalance degree n p .w2M1k := by
  intro core y hy w cls htag
  obtain ⟨star, input, block, profile, shape, -⟩ :=
    RegrowthBalances.exists_w2M1k_balance w hy cls htag
  let L := W2M1kStarCensusProof.columns input shape
  let initial := StarCensusEngine.labelling w hy (L.member 0).datum
    (W2M1kStarCensusProof.limitAnchor input shape 0).E
  have hExh := W2M1kStarExhaustionProof.w2M1kStarExhaustion degree n p core y hy w cls htag star
    input block profile shape initial
  have hBij : Function.Bijective (W2M1kStarCensusProof.repCls w hy input shape initial) :=
    ⟨W2M1kStarCensusProof.repCls_injective w hy input shape initial,
      W2M1kStarCensusProof.repCls_surjective w hy input shape initial hExh⟩
  have hSide : ∀ (j : {j // W2M1kStarCensusProof.Nonsingular w input shape initial j})
      (d : Fin p → ℚ),
      OpensToward
          (GeometricStar.Star.toFibre (W2M1kStarCensusProof.repCls w hy input shape initial j)) d ↔
        0 < commonNumerator w hy (L.sourceCoordinates initial) (L.targetCoordinates initial) d *
          signedMult (W2M1kStarCensusProof.lab w input shape initial j.1).presentation :=
    fun j d ↦
    opensToward_engineFrame_iff_of_common w hy (E := (W2M1kStarCensusProof.limitAnchor input shape j.1).E)
      (W2M1kStarCensusProof.fdAt w hy input shape initial j.1 j.2)
      (W2M1kStarCensusProof.limitAnchor input shape j.1).retained _ _
      (W2M1kStarCensusProof.lab w input shape initial j.1)
      (fun path ↦ by
        rw [(W2M1kStarCensusProof.limitAnchor input shape j.1).E_row]
        exact congrArg (L.sourceCoordinates initial) ((L.member j.1).row.symm_apply_apply path))
      (fun _ ↦ rfl) d
  exact starBalanceAt_of_signedCensus
    { ι := Fin 3
      term := fun j ↦ signedMult (W2M1kStarCensusProof.lab w input shape initial j).presentation
      integral := W2M1kStarCensusProof.integral_signedMult w hy input shape initial
      balance := W2M1kStarCensusProof.sum_signedMult_eq_zero w hy input shape initial
      nonsingular := W2M1kStarCensusProof.Nonsingular w input shape initial
      zero_of_singular := W2M1kStarCensusProof.signedMult_eq_zero w input shape initial
      equiv := Equiv.ofBijective _ hBij
      multNat_equiv := fun j ↦ W2M1kStarCensusProof.multNat_rep w hy input shape initial j.1 j.2
      numerator := commonNumerator w hy (L.sourceCoordinates initial) (L.targetCoordinates initial)
      numerator_neg := commonNumerator_neg w hy _ _
      side := hSide }

/-- **W2 Mkk (Equation (8)) is balanced by sides.**  Proved.  Census
`W2MkkStarExhaustionProof.w2MkkStarExhaustion`, map `W2MkkStarCensusProof.repCls`; balance
`RegrowthBalances.exists_w2Mkk_balance`; parity consumer
`W2MkkStarCensusProof.starParityAt_of_census`. -/
theorem familyStarBalance_w2Mkk (degree n p : ℕ) : FamilyStarBalance degree n p .w2Mkk := by
  intro core y hy w cls htag
  obtain ⟨star, input, block, profile, shape, detach, distinguished, -⟩ :=
    RegrowthBalances.exists_w2Mkk_balance w hy cls htag
  let L := W2MkkStarCensusProof.columns input shape detach distinguished
  let initial := StarCensusEngine.labelling w hy (L.member 0).datum
    (W2MkkStarCensusProof.limitAnchor input shape detach distinguished 0).E
  have hExh := W2MkkStarExhaustionProof.w2MkkStarExhaustion degree n p core y hy w cls htag star
    input block profile shape detach distinguished initial
  have hBij : Function.Bijective
      (W2MkkStarCensusProof.repCls w hy input shape detach distinguished initial) :=
    ⟨W2MkkStarCensusProof.repCls_injective w hy input shape detach distinguished initial,
      W2MkkStarCensusProof.repCls_surjective w hy input shape detach distinguished initial hExh⟩
  have hSide : ∀ (j : {j // W2MkkStarCensusProof.Nonsingular w input shape detach distinguished
        initial j}) (d : Fin p → ℚ),
      OpensToward (GeometricStar.Star.toFibre
          (W2MkkStarCensusProof.repCls w hy input shape detach distinguished initial j)) d ↔
        0 < commonNumerator w hy (L.sourceCoordinates initial) (L.targetCoordinates initial) d *
          signedMult
            (W2MkkStarCensusProof.lab w input shape detach distinguished initial j.1).presentation :=
    fun j d ↦
    opensToward_engineFrame_iff_of_common w hy
      (E := (W2MkkStarCensusProof.limitAnchor input shape detach distinguished j.1).E)
      (W2MkkStarCensusProof.fdAt w hy input shape detach distinguished initial j.1 j.2)
      (W2MkkStarCensusProof.Anchor.retained
        (W2MkkStarCensusProof.limitAnchor input shape detach distinguished j.1)) _ _
      (W2MkkStarCensusProof.lab w input shape detach distinguished initial j.1)
      (fun path ↦ by
        rw [(W2MkkStarCensusProof.limitAnchor input shape detach distinguished j.1).E_row]
        exact congrArg (L.sourceCoordinates initial) ((L.member j.1).row.symm_apply_apply path))
      (fun _ ↦ rfl) d
  exact starBalanceAt_of_signedCensus
    { ι := Fin 3
      term := fun j ↦
        signedMult (W2MkkStarCensusProof.lab w input shape detach distinguished initial j).presentation
      integral := W2MkkStarCensusProof.integral_signedMult w hy input shape detach distinguished
        initial
      balance := W2MkkStarCensusProof.sum_signedMult_eq_zero w hy input shape detach distinguished
        initial
      nonsingular := W2MkkStarCensusProof.Nonsingular w input shape detach distinguished initial
      zero_of_singular := W2MkkStarCensusProof.signedMult_eq_zero w input shape detach distinguished
        initial
      equiv := Equiv.ofBijective _ hBij
      multNat_equiv := fun j ↦
        W2MkkStarCensusProof.multNat_rep w hy input shape detach distinguished initial j.1 j.2
      numerator := commonNumerator w hy (L.sourceCoordinates initial) (L.targetCoordinates initial)
      numerator_neg := commonNumerator_neg w hy _ _
      side := hSide }

/-- **W2 P (Equation (9)) is balanced by sides.**  Proved.  Census
`W2PStarExhaustionProof.w2PStarExhaustion`, map `W2PStarCensusProof.repCls`; balance
`RegrowthWallInput.exists_w2P_balance`; parity consumer `W2PStarCensusProof.starParityAt_of_census`. -/
theorem familyStarBalance_w2P (degree n p : ℕ) : FamilyStarBalance degree n p .w2P := by
  intro core y hy w cls htag
  obtain ⟨star, input, block, profile, shape, incoming, fd, -⟩ :=
    RegrowthWallInput.exists_w2P_balance w hy cls htag
  have hExh := W2PStarExhaustionProof.w2PStarExhaustion degree n p core y hy w cls htag star
    input block profile shape incoming fd
  have hBij : Function.Bijective (W2PStarCensusProof.repCls w hy input shape fd) :=
    ⟨W2PStarCensusProof.repCls_injective w hy input shape fd,
      W2PStarCensusProof.repCls_surjective w hy input shape fd hExh⟩
  let L := W2PLimitMatrix.limitColumns input shape
  let initial := W2PArbitraryExit.initialLabelling input shape incoming fd
  have hSide : ∀ (q : {q // W2PStarCensusProof.Nonsingular w input shape fd q})
      (d : Fin p → ℚ),
      OpensToward (GeometricStar.Star.toFibre (W2PStarCensusProof.repCls w hy input shape fd q))
          d ↔
        0 < commonNumerator w hy (L.sourceCoordinates initial)
          (W2PCommonBalance.LimitColumns.targetCoordinates initial) d *
          signedMult (W2PStarCensusProof.lab w input shape fd q.1).presentation := fun q d ↦
    opensToward_engineFrame_iff_of_common w hy (E := W2PArbitraryExit.equivalence input shape q.1)
      (W2PStarCensusProof.fdAt w input shape fd q.1 q.2)
      (W2PStarCensusProof.matrix_retained input shape q.1) _ _
      (W2PStarCensusProof.lab w input shape fd q.1)
      (fun path ↦ by
        rw [W2PArbitraryExit.equivalence_row]
        exact congrArg (L.sourceCoordinates initial) ((L.row q.1).symm_apply_apply path))
      (fun _ ↦ rfl) d
  exact starBalanceAt_of_signedCensus
    { ι := Fin 3
      term := fun q ↦ signedMult (W2PStarCensusProof.lab w input shape fd q).presentation
      integral := W2PStarCensusProof.integral_signedMult w input shape fd
      balance := W2PStarCensusProof.sum_signedMult_eq_zero w input shape fd
      nonsingular := W2PStarCensusProof.Nonsingular w input shape fd
      zero_of_singular := W2PStarCensusProof.signedMult_eq_zero w input shape fd
      equiv := Equiv.ofBijective _ hBij
      multNat_equiv := fun q ↦ W2PStarCensusProof.multNat_rep w hy input shape fd q.1 q.2
      numerator := commonNumerator w hy (L.sourceCoordinates initial)
        (W2PCommonBalance.LimitColumns.targetCoordinates initial)
      numerator_neg := commonNumerator_neg w hy _ _
      side := hSide }

/-- **W2 R1 (Equation (10)) is balanced by sides.**  Proved.  Census
`W2R1StarExhaustionProof.w2R1StarExhaustion`, map `W2R1StarCensusProof.repCls`
(`Fin 2 ≃ Star`); balance `RegrowthWallInput.exists_w2R1_balance` with
`W2R1StarCensusProof.exists_incoming`.  Two classes with `m₀ = -m₁`: the side law says they open
on opposite sides, which here comes out of the common side law
(`opensToward_engineFrame_iff_of_common`) with no case analysis. -/
theorem familyStarBalance_w2R1 (degree n p : ℕ) : FamilyStarBalance degree n p .w2R1 := by
  intro core y hy w cls htag
  obtain ⟨star, input, pair, -⟩ := RegrowthWallInput.exists_w2R1_balance w cls htag
  obtain ⟨incoming, ⟨fd⟩⟩ := W2R1StarCensusProof.exists_incoming w hy pair
  have hExh := W2R1StarExhaustionProof.w2R1StarExhaustion degree n p core y hy w cls htag star
    input pair incoming fd
  have hBij : Function.Bijective (W2R1StarCensusProof.repCls w hy pair input.valid fd) :=
    ⟨W2R1StarCensusProof.repCls_injective w hy pair input.valid fd,
      W2R1StarCensusProof.repCls_surjective w hy pair input.valid fd hExh⟩
  let L := W2R1LimitMatrix.limitColumns pair input.valid
  let initial := W2R1GraphData.initialLabelling pair input.valid incoming fd
  have hSide : ∀ (q : Fin 2) (d : Fin p → ℚ),
      OpensToward (GeometricStar.Star.toFibre (W2R1StarCensusProof.repCls w hy pair input.valid fd q)) d ↔
        0 < commonNumerator w hy (L.sourceCoordinates initial)
          (W2R1CommonBalance.LimitColumns.targetCoordinates initial) d *
          signedMult (W2R1StarCensusProof.lab w pair input.valid fd q).presentation := fun q d ↦
    opensToward_engineFrame_iff_of_common w hy (E := W2R1GraphData.equivalence pair input.valid q)
        (W2R1StarCensusProof.fdAt w pair input.valid fd q)
        (W2R1RowDescent.matrix_retained pair input.valid q) _ _
        (W2R1StarCensusProof.lab w pair input.valid fd q)
        (fun path ↦ congrArg (L.sourceCoordinates initial) ((L.row q).symm_apply_apply path))
        (fun _ ↦ rfl) d
  exact starBalanceAt_of_signedCensus
    { ι := Fin 2
      term := fun q ↦ signedMult (W2R1StarCensusProof.lab w pair input.valid fd q).presentation
      integral := W2R1StarCensusProof.integral_signedMult w pair input.valid fd
      balance := W2R1StarCensusProof.sum_signedMult_eq_zero w pair input.valid fd
      nonsingular := fun _ ↦ True
      zero_of_singular := fun _ h ↦ (h trivial).elim
      equiv := (Equiv.subtypeUnivEquiv fun _ ↦ trivial).trans (Equiv.ofBijective _ hBij)
      multNat_equiv := fun q ↦ W2R1StarCensusProof.multNat_rep w hy pair input.valid fd q.1
      numerator := commonNumerator w hy (L.sourceCoordinates initial)
        (W2R1CommonBalance.LimitColumns.targetCoordinates initial)
      numerator_neg := commonNumerator_neg w hy _ _
      side := fun q d ↦ hSide q.1 d }

end DraismaVargas.Count.IntegerCount
