module

public import DraismaVargasCount.IntegerCount.StarBalance
public import DraismaVargasCount.W3FourStarExhaustionProof
public import DraismaVargasCount.W3ShiftStarExhaustionProof
public import DraismaVargasCount.W3Nd3StarExhaustionProof
public import DraismaVargasCount.W3Nd2StarExhaustionProof

@[expose] public section

/-!
# The balance by sides at the trivalent walls

The integer twins of the four trivalent family clauses of `EvenGenusParity.familyStarParity`:
`W3FourStarCensusProof.familyStarParity_w3Four_of_census`,
`W3ShiftStarCensusProof.familyStarParity_w3Shift_of_census`,
`W3Nd3StarCensusProof.familyStarParity_w3Nd3_of_census` and
`W3Nd2StarCensusProof.familyStarParity_w3Nd2_of_census`, each fed by its exhaustion module's
`…StarCensus` (Equations (2)--(5) of Draisma--Vargas Part I).

Every one of them is proved the same way: a `SignedStarCensus` from the family's
census **as constructed** (`Setup.repCls`, `repCls`; the `…StarCensus` propositions hide the
map behind `∃ e`), the family's balance and integrality lemmas, and a side law.  The side law is
the only new content.  Each family's star members are `StarCensusEngine.starMember`s, whose
frames all satisfy `det_mul_coordsAt_engineFrame`: in the **engine labelling** the side law is
free.  What a family must add is that its balance terms have, position by position, the sign of
the engine labelling's signed multiplicity times one common sign.

## Contents

* `signedMult_eq_sign_mul_of_matrix_eq` (proved, generic): two presentations of one datum whose
  matrices differ by a row and a column reindexing have signed multiplicities differing by the
  sign of the composite permutation.
* `familyStarBalance_w3Shift` (the model case): the balance is in the engine labelling.
* `familyStarBalance_w3Four`, `familyStarBalance_w3Nd3`, `familyStarBalance_w3Nd2` (proved): the
  engine labelling of each position is the balance labelling reindexed by row and column maps
  that do not depend on the position (`w3Four_engLab_matrix`, `nd3_signedMult_engine0/1`,
  `nd2_signedMult_engine0/1`), so the side law is `opensToward_engineFrame_iff` with the
  numerator multiplied by one common sign.  The W4 shortcut (engine
  labelling *equal* to the balance labelling) is not available here: `w3Four`'s balance lives
  over `Option` edges, and the nd3/nd2 balances take their coordinates from the incoming cover's
  labelling, not from the wall's inherited row labels.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)

/-- Target edges are compared classically, as in the public W3 family files. -/
noncomputable local instance instDecidableEqEdgesW3 {target : CFGraph} :
    DecidableEq target.edges := Classical.decEq _

section SignCompare

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- **Two presentations of one datum whose matrices differ by a row and a column reindexing
have signed multiplicities differing by the sign of the composite permutation.**  If
`P r c = Q (ρ r) (γ c)`, then `Mult P = sign (γ⁻¹ ∘ ρ) · Mult Q`: reindex `Q` along `γ` on both
sides (`signedMult_reindex`), then permute its rows by `γ⁻¹ ∘ ρ` (`signedMult_reindexRows`).
This is the sign comparison, proved once: a family whose balance
labelling and engine labelling differ by reindexings `ρ`, `γ` **that do not depend on the
position** gets its side law from the engine's with one common sign. -/
theorem signedMult_eq_sign_mul_of_matrix_eq (P : data.LengthMatrixPresentation κ)
    (Q : data.LengthMatrixPresentation κ') (ρ γ : κ ≃ κ')
    (h : ∀ r c, GluingDatum.LengthMatrixPresentation.matrix P r c =
      GluingDatum.LengthMatrixPresentation.matrix Q (ρ r) (γ c)) :
    signedMult P = (Equiv.Perm.sign (ρ.trans γ.symm) : ℚ) * signedMult Q := by
  rw [← signedMult_reindex Q γ, ← signedMult_reindexRows]
  apply W3FourStarCensusProof.signedMult_congr
  funext r c
  rw [h, matrix_reindexRows, matrix_reindex]
  simp

end SignCompare

section W3Four

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}

/-- **The engine matrix of a Figure 28 member is its receipt matrix, reindexed by maps that do
not depend on the member**: rows through `rowLabel⁻¹` then the limit's own row labelling
`S.lab.row`, columns through the wall's coordinates `W4StarParity.columnEquiv w`.  Both matrices
are the member's natural matrix (`labelling_matrix_eq`, `honest_matrix`), and the two row
dictionaries agree because `(S.anchor i).E` has the gauge's rows (`GaugeAnchor.E_row`). -/
theorem w3Four_engLab_matrix (S : W3FourStarCensusProof.Setup w) (hy : Nondegenerate y)
    (i : Fin 4) (r c : Fin p) :
    GluingDatum.LengthMatrixPresentation.matrix (S.engLab hy i).presentation r c =
      GluingDatum.LengthMatrixPresentation.matrix (S.receipts.presentation i)
        (S.lab.row ((InheritedLimitRows.rowLabel w hy).symm r)) (W4StarParity.columnEquiv w c) := by
  rw [StableSourceMatrix.labelling_matrix_eq, ← S.honest_matrix i,
    StableSourceMatrix.labelling_matrix_eq]
  change StableSourceMatrix.matrix _ (((S.anchor i).E (S.cd i)).row
      ((InheritedLimitRows.rowLabel w hy).symm r)) _ =
    StableSourceMatrix.matrix _ ((S.cd i).rowEquiv
      (S.lab.row ((InheritedLimitRows.rowLabel w hy).symm r))) _
  rw [W3FourStarCensusProof.GaugeAnchor.E_row, W3FourRegrownColumn.ColumnData.rowEquiv_apply,
    Equiv.symm_apply_apply]
  rfl

/-- **The engine multiplicity of a Figure 28 member is its term of Equation (2) times one
common sign.** -/
theorem w3Four_signedMult_engLab (S : W3FourStarCensusProof.Setup w) (hy : Nondegenerate y)
    (i : Fin 4) :
    signedMult (S.engLab hy i).presentation =
      (Equiv.Perm.sign (((InheritedLimitRows.rowLabel w hy).symm.trans S.lab.row).trans
        (W4StarParity.columnEquiv w).symm) : ℚ) * signedMult (S.receipts.presentation i) :=
  signedMult_eq_sign_mul_of_matrix_eq _ _ _ _ (w3Four_engLab_matrix S hy i)

end W3Four

section W3Nd3


variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (hy : Nondegenerate y)
  {star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)}
  (input : ThirdEquation.W3SourceInput w.limit star)
  (profile : W3R1SourceProfile.Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
    (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p))

/-- The common sign relating the engine labelling of Equation (4)'s members to their labelling
in the incoming presentation's coordinates. -/
noncomputable def nd3Sign : ℚ :=
  (Equiv.Perm.sign
    (((InheritedLimitRows.rowLabel w hy).symm.trans
        (W3Nd3CommonBalance.sourceCoordinates input profile hSame
          (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD))).trans
      ((W4StarParity.columnEquiv w).trans
        (W3Nd3CommonBalance.targetCoordinates input profile hSame
          (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD)).symm).symm)
    : ℚ)

/-- **The engine multiplicity of Figure 30's coarse member is its term of Equation (4) times
the common sign.**  Both labellings read the member's natural matrix through the family's
stable-path dictionary (`W3Nd3CommonBalance.rowEquiv`, the row map of the engine's
equivalence) and its canonical columns; they differ only in the q-independent coordinate maps. -/
theorem nd3_signedMult_engine0 :
    signedMult (StarCensusEngine.labelling w hy
      (W3Nd3SourceCandidates.coarseCandidate input profile hSame).datum
      (W3Nd3LimitMatrix.coarseStableGraphEquivalence input profile hSame)).presentation =
    nd3Sign hy input profile hSame incoming incomingFD *
      signedMult
        (W3Nd3StarCensusProof.lab input profile hSame incoming incomingFD 0).presentation := by
  refine signedMult_eq_sign_mul_of_matrix_eq _ _ _ _ fun r c ↦ ?_
  rw [StableSourceMatrix.labelling_matrix_eq]
  refine Eq.trans ?_ (W3Nd3CommonBalance.squareMatrix_common input profile hSame _ 0 _ _).symm
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rfl

/-- The same for Figure 30's fine member. -/
theorem nd3_signedMult_engine1 :
    signedMult (StarCensusEngine.labelling w hy
      (W3Nd3SourceCandidates.fineCandidate input profile hSame).datum
      (W3Nd3LimitMatrix.fineStableGraphEquivalence input profile hSame)).presentation =
    nd3Sign hy input profile hSame incoming incomingFD *
      signedMult
        (W3Nd3StarCensusProof.lab input profile hSame incoming incomingFD 1).presentation := by
  refine signedMult_eq_sign_mul_of_matrix_eq _ _ _ _ fun r c ↦ ?_
  rw [StableSourceMatrix.labelling_matrix_eq]
  refine Eq.trans ?_ (W3Nd3CommonBalance.squareMatrix_common input profile hSame _ 1 _ _).symm
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rfl

end W3Nd3

/-- **The side law at Figure 30's coarse member.** -/
theorem nd3_side0 {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
    {w : Regrowth core y degree} (hy : Nondegenerate y)
    {star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)}
    (input : ThirdEquation.W3SourceInput w.limit star)
    (profile : W3R1SourceProfile.Nd3Profile w.limit input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p))
    (hq : W3Nd3StarCensusProof.Nonsingular input profile hSame incoming incomingFD 0)
    (d : Fin p → ℚ) :
    OpensToward (GeometricStar.Star.toFibre
      (W3Nd3StarCensusProof.rep w hy input profile hSame incoming incomingFD 0 hq).cls) d ↔
    0 < nd3Sign hy input profile hSame incoming incomingFD * wallNumeratorAt w d *
      signedMult
        (W3Nd3StarCensusProof.lab input profile hSame incoming incomingFD 0).presentation := by
  have h := opensToward_engineFrame_iff w hy
    (D := (W3Nd3SourceCandidates.coarseCandidate input profile hSame).datum)
    (E := W3Nd3LimitMatrix.coarseStableGraphEquivalence input profile hSame)
    (W3Nd3StarCensusProof.fdAt w input profile hSame incoming incomingFD 0 hq)
    (W3Nd3LimitMatrix.coarse_matrix_retained input profile hSame) d
  rw [nd3_signedMult_engine0 hy input profile hSame incoming incomingFD] at h
  have hrep : (W3Nd3StarCensusProof.rep w hy input profile hSame incoming incomingFD 0 hq).member =
      StarCensusEngine.regrowth w hy
        (D := (W3Nd3SourceCandidates.coarseCandidate input profile hSame).datum)
        (E := W3Nd3LimitMatrix.coarseStableGraphEquivalence input profile hSame)
        (W3Nd3StarCensusProof.fdAt w input profile hSame incoming incomingFD 0 hq)
        (W3Nd3LimitMatrix.coarse_matrix_retained input profile hSame) := rfl
  rw [GeometricStar.Star.toFibre_cls, hrep]
  exact h.trans (iff_of_eq (congrArg _ (by ring)))

/-- **The side law at Figure 30's fine member.** -/
theorem nd3_side1 {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
    {w : Regrowth core y degree} (hy : Nondegenerate y)
    {star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)}
    (input : ThirdEquation.W3SourceInput w.limit star)
    (profile : W3R1SourceProfile.Nd3Profile w.limit input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p))
    (hq : W3Nd3StarCensusProof.Nonsingular input profile hSame incoming incomingFD 1)
    (d : Fin p → ℚ) :
    OpensToward (GeometricStar.Star.toFibre
      (W3Nd3StarCensusProof.rep w hy input profile hSame incoming incomingFD 1 hq).cls) d ↔
    0 < nd3Sign hy input profile hSame incoming incomingFD * wallNumeratorAt w d *
      signedMult
        (W3Nd3StarCensusProof.lab input profile hSame incoming incomingFD 1).presentation := by
  have h := opensToward_engineFrame_iff w hy
    (D := (W3Nd3SourceCandidates.fineCandidate input profile hSame).datum)
    (E := W3Nd3LimitMatrix.fineStableGraphEquivalence input profile hSame)
    (W3Nd3StarCensusProof.fdAt w input profile hSame incoming incomingFD 1 hq)
    (W3Nd3LimitMatrix.fine_matrix_retained input profile hSame) d
  rw [nd3_signedMult_engine1 hy input profile hSame incoming incomingFD] at h
  have hrep : (W3Nd3StarCensusProof.rep w hy input profile hSame incoming incomingFD 1 hq).member =
      StarCensusEngine.regrowth w hy
        (D := (W3Nd3SourceCandidates.fineCandidate input profile hSame).datum)
        (E := W3Nd3LimitMatrix.fineStableGraphEquivalence input profile hSame)
        (W3Nd3StarCensusProof.fdAt w input profile hSame incoming incomingFD 1 hq)
        (W3Nd3LimitMatrix.fine_matrix_retained input profile hSame) := rfl
  rw [GeometricStar.Star.toFibre_cls, hrep]
  exact h.trans (iff_of_eq (congrArg _ (by ring)))

/-- **The side law of Equation (4)**, at both positions, with the numerator
`nd3Sign · wallNumeratorAt w`. -/
theorem nd3_side {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
    {w : Regrowth core y degree} (hy : Nondegenerate y)
    {star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)}
    (input : ThirdEquation.W3SourceInput w.limit star)
    (profile : W3R1SourceProfile.Nd3Profile w.limit input.distinguishedBlock)
    (hSame : profile.first.1.1.1 = profile.second.1.1.1)
    (incoming : Fin 2)
    (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
      (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p))
    (q : Fin 2) (hq : W3Nd3StarCensusProof.Nonsingular input profile hSame incoming incomingFD q)
    (d : Fin p → ℚ) :
    OpensToward (GeometricStar.Star.toFibre
      (W3Nd3StarCensusProof.rep w hy input profile hSame incoming incomingFD q hq).cls) d ↔
    0 < nd3Sign hy input profile hSame incoming incomingFD * wallNumeratorAt w d *
      signedMult
        (W3Nd3StarCensusProof.lab input profile hSame incoming incomingFD q).presentation := by
  rcases q with ⟨_ | _ | _, hlt⟩
  · exact nd3_side0 hy input profile hSame incoming incomingFD hq d
  · exact nd3_side1 hy input profile hSame incoming incomingFD hq d
  · omega

section W3Nd2

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (hy : Nondegenerate y)
  {star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (W4WallExhaustion.mergeVertex w)}
  (input : ThirdEquation.W3SourceInput w.limit star)
  (profile : W3R1SourceProfile.Nd2Profile w.limit input.distinguishedBlock)
  {incoming : Fin 2}
  (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p))

/-- The common sign relating the engine labelling of Equation (5)'s members to their labelling
in the incoming presentation's coordinates. -/
noncomputable def nd2Sign : ℚ :=
  (Equiv.Perm.sign
    (((InheritedLimitRows.rowLabel w hy).symm.trans
        (W3Nd2CommonBalance.sourceCoordinates input profile
          (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD))).trans
      ((W4StarParity.columnEquiv w).trans
        (W3Nd2CommonBalance.targetCoordinates input profile
          (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD)).symm).symm)
    : ℚ)

/-- **The engine multiplicity of Figure 31's coarse member is its term of Equation (5) times
the common sign**, as for nd3. -/
theorem nd2_signedMult_engine0 :
    signedMult (StarCensusEngine.labelling w hy
      (W3Nd2SourceCandidates.coarseCandidate input profile).datum
      (W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile)).presentation =
    nd2Sign hy input profile incomingFD *
      signedMult (W3Nd2StarCensusProof.lab w input profile incomingFD 0).presentation := by
  refine signedMult_eq_sign_mul_of_matrix_eq _ _ _ _ fun r c ↦ ?_
  rw [StableSourceMatrix.labelling_matrix_eq]
  refine Eq.trans ?_ (W3Nd2CommonBalance.squareMatrix_common input profile _ 0 _ _).symm
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rfl

/-- The same for Figure 31's fine member. -/
theorem nd2_signedMult_engine1 :
    signedMult (StarCensusEngine.labelling w hy
      (W3Nd2FineCandidates.fineCandidate input profile).datum
      (W3Nd2FineStableGraph.fineStableGraphEquivalence input profile)).presentation =
    nd2Sign hy input profile incomingFD *
      signedMult (W3Nd2StarCensusProof.lab w input profile incomingFD 1).presentation := by
  refine signedMult_eq_sign_mul_of_matrix_eq _ _ _ _ fun r c ↦ ?_
  rw [StableSourceMatrix.labelling_matrix_eq]
  refine Eq.trans ?_ (W3Nd2CommonBalance.squareMatrix_common input profile _ 1 _ _).symm
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rfl

/-- **The side law at Figure 31's coarse member.** -/
theorem nd2_side0 (d : Fin p → ℚ) :
    OpensToward (GeometricStar.Star.toFibre
      (W3Nd2StarCensusProof.rep w hy input profile incomingFD 0).cls) d ↔
    0 < nd2Sign hy input profile incomingFD * wallNumeratorAt w d *
      signedMult (W3Nd2StarCensusProof.lab w input profile incomingFD 0).presentation := by
  have h := opensToward_engineFrame_iff w hy
    (D := (W3Nd2SourceCandidates.coarseCandidate input profile).datum)
    (E := W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile)
    (W3Nd2StarCensusProof.fdAt w input profile incomingFD 0)
    (W3Nd2CoarseLimitMatrix.matrix_retained input profile) d
  rw [nd2_signedMult_engine0 hy input profile incomingFD] at h
  have hrep : (W3Nd2StarCensusProof.rep w hy input profile incomingFD 0).member =
      StarCensusEngine.regrowth w hy
        (D := (W3Nd2SourceCandidates.coarseCandidate input profile).datum)
        (E := W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile)
        (W3Nd2StarCensusProof.fdAt w input profile incomingFD 0)
        (W3Nd2CoarseLimitMatrix.matrix_retained input profile) := rfl
  rw [GeometricStar.Star.toFibre_cls, hrep]
  exact h.trans (iff_of_eq (congrArg _ (by ring)))

/-- **The side law at Figure 31's fine member.** -/
theorem nd2_side1 (d : Fin p → ℚ) :
    OpensToward (GeometricStar.Star.toFibre
      (W3Nd2StarCensusProof.rep w hy input profile incomingFD 1).cls) d ↔
    0 < nd2Sign hy input profile incomingFD * wallNumeratorAt w d *
      signedMult (W3Nd2StarCensusProof.lab w input profile incomingFD 1).presentation := by
  have h := opensToward_engineFrame_iff w hy
    (D := (W3Nd2FineCandidates.fineCandidate input profile).datum)
    (E := W3Nd2FineStableGraph.fineStableGraphEquivalence input profile)
    (W3Nd2StarCensusProof.fdAt w input profile incomingFD 1)
    (W3Nd2FineLimitMatrix.matrix_retained input profile) d
  rw [nd2_signedMult_engine1 hy input profile incomingFD] at h
  have hrep : (W3Nd2StarCensusProof.rep w hy input profile incomingFD 1).member =
      StarCensusEngine.regrowth w hy
        (D := (W3Nd2FineCandidates.fineCandidate input profile).datum)
        (E := W3Nd2FineStableGraph.fineStableGraphEquivalence input profile)
        (W3Nd2StarCensusProof.fdAt w input profile incomingFD 1)
        (W3Nd2FineLimitMatrix.matrix_retained input profile) := rfl
  rw [GeometricStar.Star.toFibre_cls, hrep]
  exact h.trans (iff_of_eq (congrArg _ (by ring)))

/-- **The side law of Equation (5)**, at both positions. -/
theorem nd2_side (q : Fin 2) (d : Fin p → ℚ) :
    OpensToward (GeometricStar.Star.toFibre
      (W3Nd2StarCensusProof.rep w hy input profile incomingFD q).cls) d ↔
    0 < nd2Sign hy input profile incomingFD * wallNumeratorAt w d *
      signedMult (W3Nd2StarCensusProof.lab w input profile incomingFD q).presentation := by
  rcases q with ⟨_ | _ | _, hlt⟩
  · exact nd2_side0 hy input profile incomingFD d
  · exact nd2_side1 hy input profile incomingFD d
  · omega

end W3Nd2

/-- **W3Four (Equation (2), Figure 28) is balanced by sides.**

*Proof.*  Census: `W3FourStarExhaustionProof.w3FourStarExhaustion` with
`Setup.census_of_exhaustion` (map `Equiv.ofBijective (S.repCls hy)`), terms
`signedMult (S.receipts.presentation i)`, `Setup.sum_signedMult`, `Setup.integral_signedMult`,
`Setup.signedMult_eq_zero`.  Side law: `Setup.absMult_engLab` relates the receipt terms to the
engine labelling only in absolute value; the sign relation is uniform in `i`
(`w3Four_signedMult_engLab`): the engine matrix is the receipt matrix with rows read through
`rowLabel⁻¹` and `S.lab.row`, and columns through `W4StarParity.columnEquiv w`, for every `i`.
So the side law is `opensToward_engineFrame_iff` with the numerator times that one sign. -/
theorem familyStarBalance_w3Four (degree n p : ℕ) : FamilyStarBalance degree n p .w3Four := by
  intro core y hy w cls htag
  obtain ⟨S⟩ := W3FourStarCensusProof.exists_setup w cls htag
  have hExh := W3FourStarExhaustionProof.w3FourStarExhaustion degree n p core y hy w cls htag S
  have hBij : Function.Bijective (S.repCls hy) := by
    refine ⟨S.repCls_injective hy, Quotient.ind fun member ↦ ?_⟩
    obtain ⟨i, hi, h⟩ := hExh member
    exact ⟨⟨i, hi⟩, h.symm⟩
  exact starBalanceAt_of_signedCensus
    { ι := Fin 4
      term := fun i ↦ signedMult (S.receipts.presentation i)
      integral := S.integral_signedMult hy
      balance := S.sum_signedMult hy
      nonsingular := S.Nonsingular
      zero_of_singular := S.signedMult_eq_zero
      equiv := Equiv.ofBijective _ hBij
      multNat_equiv := fun i ↦ S.multNat_rep hy i.1 i.2
      numerator := fun d ↦ (Equiv.Perm.sign (((InheritedLimitRows.rowLabel w hy).symm.trans
        S.lab.row).trans (W4StarParity.columnEquiv w).symm) : ℚ) * wallNumeratorAt w d
      numerator_neg := fun d ↦ by simp only [wallNumeratorAt_neg, mul_neg]
      side := fun i d ↦ by
        refine (opensToward_engineFrame_iff w hy (S.fdAt hy i.1 i.2)
          ((S.anchor i.1).retained (S.cd i.1)) d).trans ?_
        rw [w3Four_signedMult_engLab S hy i.1]
        exact iff_of_eq (congrArg _ (by ring)) }

/-- **W3Shift (Equation (3)) is balanced by sides.**  Proved; it is the model case of the route.
Its census terms are already `signedMult (S.engLab hy i).presentation`
(`W3ShiftStarCensusProof.Setup.multNat_rep` is `rfl`), the engine labelling itself, so the side
law is `opensToward_engineFrame_iff` with `numerator := wallNumeratorAt w`.  Census: the map
`S.repCls`, bijective by `W3ShiftStarExhaustionProof.w3ShiftStarExhaustion`; balance
`Setup.sum_signedMult`.  The other nine families follow this template; what each adds is the
sign of its balance labelling against the engine labelling. -/
theorem familyStarBalance_w3Shift (degree n p : ℕ) : FamilyStarBalance degree n p .w3Shift := by
  intro core y hy w cls htag
  obtain ⟨S⟩ := W3ShiftStarCensusProof.exists_setup w cls htag
  have hExh := W3ShiftStarExhaustionProof.w3ShiftStarExhaustion degree n p core y hy w cls htag S
  have hBij : Function.Bijective (S.repCls hy) := by
    refine ⟨S.repCls_injective hy, Quotient.ind fun member ↦ ?_⟩
    obtain ⟨i, hi, h⟩ := hExh member
    exact ⟨⟨i, hi⟩, h.symm⟩
  exact starBalanceAt_of_signedCensus
    { ι := W3ShiftSixMemberMatrices.MemberIndex
      term := fun i ↦ signedMult (S.engLab hy i).presentation
      integral := S.integral_signedMult hy
      balance := S.sum_signedMult hy
      nonsingular := S.Nonsingular hy
      zero_of_singular := S.signedMult_eq_zero hy
      equiv := Equiv.ofBijective _ hBij
      multNat_equiv := fun i ↦ S.multNat_rep hy i.1 i.2
      numerator := wallNumeratorAt w
      numerator_neg := wallNumeratorAt_neg w
      side := fun i d ↦ opensToward_engineFrame_iff w hy (S.fdAt hy i.1 i.2) (S.retained i.1) d }

/-- **W3 nd3 (Equation (4)) is balanced by sides.**

*Proof.*  Census: `W3Nd3StarExhaustionProof.w3Nd3StarExhaustion`, map `repCls`,
balance from `W3Nd3StarCensusProof.exists_balance`.  Two positions, both nonsingular, with
`m₀ = -m₁`; the side law says the two classes open on opposite sides.  It is
`opensToward_engineFrame_iff` with the numerator times `nd3Sign` (`nd3_side`). -/
theorem familyStarBalance_w3Nd3 (degree n p : ℕ) :
    FamilyStarBalance degree n p .w3Nd3CoarseFine := by
  intro core y hy w cls htag
  obtain ⟨star, input, profile, hSame, incoming, fd, hbal⟩ :=
    W3Nd3StarCensusProof.exists_balance w hy cls htag
  have hExh := W3Nd3StarExhaustionProof.w3Nd3StarExhaustion degree n p core y hy w cls htag
    star input profile hSame incoming fd
  have hBij : Function.Bijective
      (W3Nd3StarCensusProof.repCls w hy input profile hSame incoming fd) := by
    refine ⟨W3Nd3StarCensusProof.repCls_injective w hy input profile hSame incoming fd,
      Quotient.ind fun member ↦ ?_⟩
    obtain ⟨q, hq, h⟩ := hExh member
    exact ⟨⟨q, hq⟩, h.symm⟩
  exact starBalanceAt_of_signedCensus
    { ι := Fin 2
      term := fun q ↦
        signedMult (W3Nd3StarCensusProof.lab input profile hSame incoming fd q).presentation
      integral := W3Nd3StarCensusProof.integral_signedMult w input profile hSame incoming fd
      balance := hbal
      nonsingular := W3Nd3StarCensusProof.Nonsingular input profile hSame incoming fd
      zero_of_singular := W3Nd3StarCensusProof.signedMult_eq_zero w input profile hSame incoming fd
      equiv := Equiv.ofBijective _ hBij
      multNat_equiv := fun q ↦
        W3Nd3StarCensusProof.multNat_rep w hy input profile hSame incoming fd q.1 q.2
      numerator := fun d ↦ nd3Sign hy input profile hSame incoming fd * wallNumeratorAt w d
      numerator_neg := fun d ↦ by simp only [wallNumeratorAt_neg, mul_neg]
      side := fun q d ↦ nd3_side hy input profile hSame incoming fd q.1 q.2 d }

/-- **W3 nd2 (Equation (5)) is balanced by sides.**

*Proof.*  Census: `W3Nd2StarExhaustionProof.w3Nd2StarExhaustion`, map `repCls`
(`Fin 2 ≃ Star`), terms `signedMult (W3Nd2StarCensusProof.lab w input profile incomingFD q)`,
balance `RegrowthWallInput.exists_w3Nd2_balance` with `W3Nd2StarCensusProof.exists_incoming`.
As for nd3: the two classes open on opposite sides; the side law is `nd2_side`. -/
theorem familyStarBalance_w3Nd2 (degree n p : ℕ) :
    FamilyStarBalance degree n p .w3Nd2CoarseFine := by
  intro core y hy w cls htag
  obtain ⟨star, input, profile, -⟩ := RegrowthWallInput.exists_w3Nd2_balance w cls htag
  obtain ⟨incoming, ⟨fd⟩⟩ := W3Nd2StarCensusProof.exists_incoming w hy input profile
  have hExh := W3Nd2StarExhaustionProof.w3Nd2StarExhaustion degree n p core y hy w cls htag
    star input profile incoming fd
  have hBij : Function.Bijective (W3Nd2StarCensusProof.repCls w hy input profile fd) :=
    ⟨W3Nd2StarCensusProof.repCls_injective w hy input profile fd,
      W3Nd2StarCensusProof.repCls_surjective w hy input profile fd hExh⟩
  exact starBalanceAt_of_signedCensus
    { ι := Fin 2
      term := fun q ↦ signedMult (W3Nd2StarCensusProof.lab w input profile fd q).presentation
      integral := W3Nd2StarCensusProof.integral_signedMult w input profile fd
      balance := W3Nd2StarCensusProof.sum_signedMult_eq_zero w input profile fd
      nonsingular := fun _ ↦ True
      zero_of_singular := fun _ h ↦ (h trivial).elim
      equiv := (Equiv.subtypeUnivEquiv fun _ ↦ trivial).trans (Equiv.ofBijective _ hBij)
      multNat_equiv := fun q ↦ W3Nd2StarCensusProof.multNat_rep w hy input profile fd q.1
      numerator := fun d ↦ nd2Sign hy input profile fd * wallNumeratorAt w d
      numerator_neg := fun d ↦ by simp only [wallNumeratorAt_neg, mul_neg]
      side := fun q d ↦ nd2_side hy input profile fd q.1 d }

end DraismaVargas.Count.IntegerCount
