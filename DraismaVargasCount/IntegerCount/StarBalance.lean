module

public import DraismaVargasCount.IntegerCount.Transport
public import DraismaVargasCount.RegrowthWallInput
public import DraismaVargasCount.StarCensusEngine
public import DraismaVargasCount.FacetMachine

@[expose] public section

/-!
# The balance of a star, by sides

The integer twin of `RegrowthWallInput.StarParityAt` / `FamilyStarParity`.
`StarParityAt hy w` says only that the star of a wall carries an even number of odd classes; it
forgets **on which side of the wall each class is open**, and the integer count needs exactly
that.  Here the side is read intrinsically, without a segment: a class `c` at the wall request
`y` *opens toward* a direction `d` (`OpensToward c d`) when it is open at `y + s • d` for all
small `s > 0`.

**`StarBalanceAt hy w`**: for every direction `d`, the star classes opening toward `d` and those
opening toward `-d` carry the same total multiplicity.  This is Vargas's balancing condition
(Part II, `prop-signed-mult`) read with the side law (`ConeSide`): every member of the star has
its wall coordinate vanishing on one common hyperplane (the span of the labelled limit), the
side of a member is `sign (Mult) · sign (C d)` for a common numerator `C`, and `Σ Mult = 0`.
For `d` in the hyperplane no class opens either way, and both sums are `0`.

## Contents

* `OpensToward`, `starSideSum`, `StarBalanceAt`, `FamilyStarBalance`, `starBalanceAt_of_family`
  (proved).
* `coordsAt_add_smul`, `opensToward_cls_iff` (proved): a frame degenerate
  at `y` in the column `col` opens toward `d` exactly when its `col` coordinate of `d` is
  positive.
* `SignedStarCensus`, `SignedStarCensus.sideEquiv`, `SignedStarCensus.starSideSum_eq` and
  `starBalanceAt_of_signedCensus` (proved): the shape each family supplies — an exact census of
  the star by the nonsingular positions of a vanishing integral balance, **together with the
  side law** `OpensToward (e i) d ↔ 0 < N d * term i` for one odd numerator `N` — and the
  arithmetic that turns it into `StarBalanceAt`.
* `frameNumerator`, `frameNumerator_neg`, `det_mul_coordsAt_of_agree`,
  `opensToward_cls_iff_of_agree` (proved): the side law of `ConeSide` for frames reading the
  request in one slot order and agreeing with one matrix off one column.
* `wallNumeratorAt`, `wallNumeratorAt_neg`, `det_mul_coordsAt_engineFrame`,
  `opensToward_engineFrame_iff` (proved): **the side law is generic for the frames of
  `StarCensusEngine`.**  Every position frame `StarCensusEngine.frame w hy D E fd` has
  the wall's slot order and agrees with the wall frame off the wall column, so
  `det · (wall coordinate of d)` is the same number `wallNumeratorAt w d` for all of them.  With
  `ConeSide.sign_fdSignedMult_eq_sign_det` this is the side law in the **engine labelling**.  A
  family whose balance is stated in the engine labelling (`W3Shift`: its terms are
  `signedMult (S.engLab hy i).presentation`) gets its side law from this alone — and
  `StarBalanceW3.familyStarBalance_w3Shift` is proved that way; the others must also show that
  their balance labelling has, position by position, the sign of the engine labelling times one
  common sign.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)
open DraismaVargas.LocalCases.ClassifiedContinuation (SourceCase)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  The side of a class, and the balance of a star -/

/-- **A class at the request `y` opens toward the direction `d`**: it is open at `y + s • d` for
every small `s > 0`, read through the request-fibre identification. -/
def OpensToward (c : GeometricFibre core y degree) (d : Fin p → ℚ) : Prop :=
  ∃ ε : ℚ, 0 < ε ∧ ∀ s : ℚ, 0 < s → s ≤ ε →
    (GeometricSegmentWalls.fibreEquiv core degree y (y + s • d) c).Open

/-- The total multiplicity of the star classes of `w` that open toward `d`. -/
noncomputable def starSideSum (hy : Nondegenerate y) (w : Regrowth core y degree)
    (d : Fin p → ℚ) : ℕ :=
  ∑ᶠ c : {c : GeometricFibre core y degree //
    GeometricStar.IsStarClass hy w c ∧ OpensToward c d}, c.1.multNat

/-- **The balance of a star, by sides**: in every direction, the star classes on the two sides
carry the same total multiplicity.  The integer twin of `RegrowthWallInput.StarParityAt`. -/
def StarBalanceAt (hy : Nondegenerate y) (w : Regrowth core y degree) : Prop :=
  ∀ d : Fin p → ℚ, starSideSum hy w d = starSideSum hy w (-d)

/-- **The per-family obligation, integer form.**  The integer twin of
`RegrowthWallInput.FamilyStarParity`, with the same binders. -/
def FamilyStarBalance (degree n p : ℕ) (tag : SourceCase) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (W4WallExhaustion.mergeVertex w)),
    cls.sourceCase = tag → StarBalanceAt hy w

/-- The ten families together give the balance at every regrowth: every regrowth's limit is
classified (`RegrowthWallInput.nonempty_classification`).  The twin of
`RegrowthWallInput.starParityAt_of_family`. -/
theorem starBalanceAt_of_family (h : ∀ tag, FamilyStarBalance degree n p tag)
    (hy : Nondegenerate y) (w : Regrowth core y degree) : StarBalanceAt hy w :=
  h (RegrowthWallInput.classification w hy).sourceCase core y hy w
    (RegrowthWallInput.classification w hy) rfl

/-! ## 2.  Opening toward a direction, on a frame -/

/-- A frame coordinate is affine along a ray. -/
theorem coordsAt_add_smul (k : Frame core degree) (y d : Fin p → ℚ) (s : ℚ) (col : Fin p) :
    k.coordsAt (y + s • d) col = k.coordsAt y col + s * k.coordsAt d col := by
  simp only [Frame.coordsAt_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ ↦ by ring

/-- **A frame degenerate at `y` in the column `col` opens toward `d` exactly when its `col`
coordinate of `d` is positive**: the other coordinates are positive at `y` and stay so for small
`s`, and the `col` coordinate of `y + s • d` is `s` times that of `d`. -/
theorem opensToward_cls_iff {k : Frame core degree} {col : Fin p} (h : k.DegenerateAt y col)
    (d : Fin p → ℚ) :
    OpensToward (GeometricFibre.cls (k.member y)) d ↔ 0 < k.coordsAt d col := by
  have hopen : ∀ s : ℚ, (GeometricSegmentWalls.fibreEquiv core degree y (y + s • d)
      (GeometricFibre.cls (k.member y))).Open ↔ ∀ c, 0 < k.coordsAt (y + s • d) c := by
    intro s
    rw [GeometricSegmentWalls.fibreEquiv_cls, Frame.of_member, GeometricFibre.open_cls]
    exact Iff.rfl
  constructor
  · rintro ⟨ε, hε, hall⟩
    have h1 := (hopen ε).mp (hall ε hε le_rfl) col
    rw [coordsAt_add_smul, h.1, zero_add] at h1
    exact pos_of_mul_pos_right h1 hε.le
  · intro hd
    obtain ⟨δ, hδ, hle⟩ := FacetMachine.exists_pos_le_of_finite
      (fun c ↦ if c = col then 1 else k.coordsAt y c / (|k.coordsAt d c| + 1))
      (fun c ↦ by
        by_cases hc : c = col
        · simp [hc]
        · simp only [hc, ite_false]
          exact div_pos (h.2 c hc) (by positivity))
    refine ⟨δ, hδ, fun s hs hsδ ↦ (hopen s).mpr fun c ↦ ?_⟩
    rw [coordsAt_add_smul]
    by_cases hc : c = col
    · subst hc
      rw [h.1, zero_add]
      exact mul_pos hs hd
    · have hyc := h.2 c hc
      have hb : δ ≤ k.coordsAt y c / (|k.coordsAt d c| + 1) := by
        simpa [hc] using hle c
      have hpos : (0 : ℚ) < |k.coordsAt d c| + 1 := by positivity
      have hs' : s * (|k.coordsAt d c| + 1) ≤ k.coordsAt y c := by
        have := (le_div_iff₀ hpos).mp (hsδ.trans hb)
        exact this
      have habs : -(s * |k.coordsAt d c|) ≤ s * k.coordsAt d c := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_abs_le _) hs.le
      nlinarith

/-! ## 3.  A signed census, and the balance it gives -/

/-- **A signed census of a star**: an exact census by the nonsingular positions of a vanishing
integral balance (as every family supplies, see `StarCensusEngine.starParityAt_of_census`),
**with the side law**: the class of position `i` opens toward `d` exactly when
`0 < numerator d * term i`, for one odd function `numerator`.  The side law is the new content
of the integer count at a trivalent wall; the census and the balance exist for all ten families.

The census must be the actual one, not merely "some bijection with the right `multNat`": the
families' `…StarCensus` propositions are stated with `∃ e`, which forgets which class is which
position, so a family proves its signed census at the level of its `rep`/`repCls`. -/
structure SignedStarCensus (hy : Nondegenerate y) (w : Regrowth core y degree) where
  /-- The positions of the family's balance. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The terms of the balance. -/
  term : ι → ℚ
  integral : ∀ i, ∃ value : ℤ, term i = (value : ℚ)
  balance : ∑ i, term i = 0
  /-- The positions that are actual members. -/
  nonsingular : ι → Prop
  zero_of_singular : ∀ i, ¬ nonsingular i → term i = 0
  /-- The census. -/
  equiv : {i // nonsingular i} ≃ GeometricStar.Star hy w
  multNat_equiv : ∀ i, (GeometricStar.Star.toFibre (equiv i)).multNat = (term i.1).num.natAbs
  /-- The common numerator of the wall coordinate. -/
  numerator : (Fin p → ℚ) → ℚ
  numerator_neg : ∀ d, numerator (-d) = -numerator d
  /-- **The side law.** -/
  side : ∀ i d, OpensToward (GeometricStar.Star.toFibre (equiv i)) d ↔ 0 < numerator d * term i.1

attribute [instance] SignedStarCensus.fintype

/-- The positions with a given side condition, read as star classes. -/
noncomputable def SignedStarCensus.sideEquiv {hy : Nondegenerate y} {w : Regrowth core y degree}
    (C : SignedStarCensus hy w) (d : Fin p → ℚ) :
    {i : C.ι // 0 < C.numerator d * C.term i} ≃
      {c : GeometricFibre core y degree // GeometricStar.IsStarClass hy w c ∧ OpensToward c d} :=
  have hns : ∀ i, 0 < C.numerator d * C.term i → C.nonsingular i := fun i h ↦ by
    by_contra hn
    rw [C.zero_of_singular i hn, mul_zero] at h
    exact lt_irrefl _ h
  Equiv.ofBijective
    (fun i ↦ ⟨GeometricStar.Star.toFibre (C.equiv ⟨i.1, hns i.1 i.2⟩),
      (GeometricStar.Star.equivSubtype hy w (C.equiv ⟨i.1, hns i.1 i.2⟩)).2,
      (C.side ⟨i.1, hns i.1 i.2⟩ d).mpr i.2⟩)
    ⟨fun i j h ↦ by
      have h1 := GeometricStar.Star.toFibre_injective (congrArg Subtype.val h)
      exact Subtype.ext (Subtype.mk.inj (C.equiv.injective h1)),
    fun ⟨c, hc, ho⟩ ↦ by
      obtain ⟨s, hs⟩ := (GeometricStar.Star.equivSubtype hy w).surjective ⟨c, hc⟩
      have hsc : GeometricStar.Star.toFibre s = c := congrArg Subtype.val hs
      have hk : GeometricStar.Star.toFibre (C.equiv (C.equiv.symm s)) = c := by
        rw [Equiv.apply_symm_apply, hsc]
      have hpos := (C.side (C.equiv.symm s) d).mp (hk ▸ ho)
      refine ⟨⟨(C.equiv.symm s).1, hpos⟩, Subtype.ext ?_⟩
      show GeometricStar.Star.toFibre (C.equiv ⟨(C.equiv.symm s).1, _⟩) = c
      exact hk⟩

/-- The side sum of a signed census, as a sum of absolute terms over positions. -/
theorem SignedStarCensus.starSideSum_eq {hy : Nondegenerate y} {w : Regrowth core y degree}
    (C : SignedStarCensus hy w) (d : Fin p → ℚ)
    [DecidablePred fun i ↦ 0 < C.numerator d * C.term i] :
    (starSideSum hy w d : ℚ) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < C.numerator d * C.term i), |C.term i| := by
  have hns : ∀ i, 0 < C.numerator d * C.term i → C.nonsingular i := fun i h ↦ by
    by_contra hn
    rw [C.zero_of_singular i hn, mul_zero] at h
    exact lt_irrefl _ h
  unfold starSideSum
  rw [← finsum_comp_equiv (C.sideEquiv d), finsum_eq_sum_of_fintype, Nat.cast_sum,
    Finset.sum_subtype (p := fun i ↦ 0 < C.numerator d * C.term i)
      (Finset.univ.filter fun i ↦ 0 < C.numerator d * C.term i) (fun i ↦ by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hm := C.multNat_equiv ⟨i.1, hns i.1 i.2⟩
  have hval : ((C.sideEquiv d i).1.multNat : ℚ) = ((C.term i.1).num.natAbs : ℚ) := by
    exact_mod_cast hm
  rw [hval]
  obtain ⟨v, hv⟩ := C.integral i.1
  rw [hv, Rat.num_intCast, Nat.cast_natAbs, Int.cast_abs]

/-- **A signed census gives the balance by sides.**  Through `SignedStarCensus.sideEquiv`,
`starSideSum hy w d` is `Σ_{0 < N d · term i} |term i|`.  If `N d = 0` both sides are empty.  If
`N d > 0` the two sides are `Σ_{term > 0} term` and `Σ_{term < 0} (-term)`, which agree because
`Σ term = 0`; `N d < 0` is the mirror image. -/
theorem starBalanceAt_of_signedCensus {hy : Nondegenerate y} {w : Regrowth core y degree}
    (C : SignedStarCensus hy w) : StarBalanceAt hy w := by
  classical
  intro d
  apply Nat.cast_injective (R := ℚ)
  rw [C.starSideSum_eq d, C.starSideSum_eq (-d), C.numerator_neg]
  -- the balance, split by the sign of the term
  have hsplit : ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < C.term i), |C.term i| =
      ∑ i ∈ Finset.univ.filter (fun i ↦ C.term i < 0), |C.term i| := by
    have hbal := C.balance
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ 0 < C.term i),
      ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun i ↦ ¬ 0 < C.term i)
        (fun i ↦ C.term i < 0)] at hbal
    have hzero : ∑ i ∈ (Finset.univ.filter fun i ↦ ¬ 0 < C.term i).filter
        (fun i ↦ ¬ C.term i < 0), C.term i = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact le_antisymm (not_lt.mp hi.1) (not_lt.mp hi.2)
    have hpos : ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < C.term i), |C.term i| =
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < C.term i), C.term i :=
      Finset.sum_congr rfl fun i hi ↦ abs_of_pos (Finset.mem_filter.mp hi).2
    have hneg : ∑ i ∈ Finset.univ.filter (fun i ↦ C.term i < 0), |C.term i| =
        ∑ i ∈ (Finset.univ.filter fun i ↦ ¬ 0 < C.term i).filter (fun i ↦ C.term i < 0),
          -C.term i := by
      rw [Finset.filter_filter]
      refine Finset.sum_congr ?_ fun i hi ↦ abs_of_neg (Finset.mem_filter.mp hi).2.2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ ⟨not_lt.mpr h.le, h⟩, fun h ↦ h.2⟩
    rw [hpos, hneg, Finset.sum_neg_distrib]
    linarith
  rcases lt_trichotomy (C.numerator d) 0 with hN | hN | hN
  · have h1 : ∀ i, (0 < C.numerator d * C.term i ↔ C.term i < 0) := fun i ↦
      ⟨fun h ↦ neg_of_mul_pos_right h hN.le, fun h ↦ mul_pos_of_neg_of_neg hN h⟩
    have h2 : ∀ i, (0 < -C.numerator d * C.term i ↔ 0 < C.term i) := fun i ↦
      ⟨fun h ↦ pos_of_mul_pos_right h (neg_pos.mpr hN).le,
        fun h ↦ mul_pos (neg_pos.mpr hN) h⟩
    rw [Finset.filter_congr fun i _ ↦ h1 i, Finset.filter_congr fun i _ ↦ h2 i]
    exact hsplit.symm
  · rw [hN, neg_zero]
  · have h1 : ∀ i, (0 < C.numerator d * C.term i ↔ 0 < C.term i) := fun i ↦
      ⟨fun h ↦ pos_of_mul_pos_right h hN.le, fun h ↦ mul_pos hN h⟩
    have h2 : ∀ i, (0 < -C.numerator d * C.term i ↔ C.term i < 0) := fun i ↦
      ⟨fun h ↦ neg_of_mul_pos_right h (neg_neg_of_pos hN).le,
        fun h ↦ mul_pos_of_neg_of_neg (neg_neg_of_pos hN) h⟩
    rw [Finset.filter_congr fun i _ ↦ h1 i, Finset.filter_congr fun i _ ↦ h2 i]
    exact hsplit

/-! ## 4.  The side law for frames that agree off one column

The side law of `ConeSide`, in the form a `SignedStarCensus` asks for.  Frames reading the
request through one slot order `σ` and agreeing with one matrix `M` off one column `col` have
one numerator `frameNumerator M σ col d`; a frame degenerate in `col` opens toward `d` exactly
when that numerator and its signed multiplicity have the same strict sign.  A family can apply it
to whichever representatives of its star classes share a labelling: the engine frames (§5), or
frames built from its own balance labellings. -/

/-- **The common numerator of frames agreeing with `M` off `col` in the slot order `σ`**: the
Cramer determinant of `M` with the column `col` replaced by `d` read through `σ`. -/
noncomputable def frameNumerator (M : Matrix (Fin p) (Fin p) ℚ) (σ : Fin p ≃ Fin p)
    (col : Fin p) (d : Fin p → ℚ) : ℚ :=
  (Matrix.updateCol M col fun r ↦ d (σ r)).det

theorem frameNumerator_neg (M : Matrix (Fin p) (Fin p) ℚ) (σ : Fin p ≃ Fin p) (col : Fin p)
    (d : Fin p → ℚ) : frameNumerator M σ col (-d) = -frameNumerator M σ col d := by
  rw [frameNumerator, frameNumerator,
    show (fun r ↦ (-d) (σ r)) = (-1 : ℚ) • fun r ↦ d (σ r) by funext r; simp,
    Matrix.det_updateCol_smul]
  ring

/-- **`det · (wall coordinate of d)` is the common numerator**, for a frame reading the request
through `σ` and agreeing with `M` off `col` (`ConeSide.wallNumerator_eq_cramer`). -/
theorem det_mul_coordsAt_of_agree (k : Frame core degree) (col : Fin p)
    (M : Matrix (Fin p) (Fin p) ℚ) (σ : Fin p ≃ Fin p) (hslot : k.slot = σ)
    (hagree : ∀ r c, c ≠ col → k.matrix r c = M r c) (d : Fin p → ℚ) :
    k.matrix.det * k.coordsAt d col = frameNumerator M σ col d := by
  have h := ConeSide.wallNumerator_eq_cramer k col d
  rw [ConeSide.wallNumerator, hslot] at h
  rw [h, Matrix.cramer_apply, frameNumerator]
  congr 1
  ext r c
  by_cases hc : c = col
  · subst hc
    simp [Matrix.updateCol_self]
  · rw [Matrix.updateCol_ne hc, Matrix.updateCol_ne hc]
    exact hagree r c hc

/-- **The side law, for a frame agreeing with `M` off its degenerate column.** -/
theorem opensToward_cls_iff_of_agree (k : Frame core degree) {col : Fin p}
    (hdeg : k.DegenerateAt y col) (M : Matrix (Fin p) (Fin p) ℚ) (σ : Fin p ≃ Fin p)
    (hslot : k.slot = σ) (hagree : ∀ r c, c ≠ col → k.matrix r c = M r c) (d : Fin p → ℚ) :
    OpensToward (GeometricFibre.cls (k.member y)) d ↔
      0 < frameNumerator M σ col d * fdSignedMult k.fullDim := by
  rw [opensToward_cls_iff hdeg, ← det_mul_coordsAt_of_agree k col M σ hslot hagree d]
  have hsign := ConeSide.sign_fdSignedMult_eq_sign_det k
  have hprod : 0 < k.matrix.det * fdSignedMult k.fullDim := by
    rcases lt_or_gt_of_ne k.det_ne_zero with hneg | hpos
    · have h1 : SignType.sign k.matrix.det = -1 := sign_neg hneg
      rw [h1, sign_eq_neg_one_iff] at hsign
      exact mul_pos_of_neg_of_neg hneg hsign
    · have h1 : SignType.sign k.matrix.det = 1 := sign_pos hpos
      rw [h1, sign_eq_one_iff] at hsign
      exact mul_pos hpos hsign
  rw [show k.matrix.det * k.coordsAt d col * fdSignedMult k.fullDim =
      k.coordsAt d col * (k.matrix.det * fdSignedMult k.fullDim) by ring]
  exact (mul_pos_iff_of_pos_right hprod).symm

/-! ## 5.  The side law is generic for the engine's position frames -/

/-- **The common numerator of a wall**: the Cramer determinant of the wall frame's matrix in the
wall's slot order, with the wall column replaced by `d`. -/
noncomputable def wallNumeratorAt (w : Regrowth core y degree) (d : Fin p → ℚ) : ℚ :=
  (Matrix.updateCol (Matrix.of fun r c ↦ w.frame.matrix (w.frame.slot.symm r) c) w.column d).det

/-- The common numerator is odd in the direction. -/
theorem wallNumeratorAt_neg (w : Regrowth core y degree) (d : Fin p → ℚ) :
    wallNumeratorAt w (-d) = -wallNumeratorAt w d := by
  rw [wallNumeratorAt, wallNumeratorAt, show -d = (-1 : ℚ) • d by simp,
    Matrix.det_updateCol_smul]
  ring

/-- **Every engine position frame has the wall's numerator**: `det A · (A⁻¹ d)_wall` is the same
for all of them.  This is `ConeSide.wallNumerator_eq_cramer` with `StarCensusEngine.frame_slot`
(the slot order is the identity) and `StarCensusEngine.labelling_matrix_retained` (the matrix
agrees with the wall frame off the wall column). -/
theorem det_mul_coordsAt_engineFrame (w : Regrowth core y degree) (hy : Nondegenerate y)
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
    (d : Fin p → ℚ) :
    (StarCensusEngine.frame w hy D E fd).matrix.det *
        (StarCensusEngine.frame w hy D E fd).coordsAt d w.column = wallNumeratorAt w d := by
  exact det_mul_coordsAt_of_agree _ w.column _ (Equiv.refl _)
    (StarCensusEngine.frame_slot w hy D E fd)
    (fun r c hc ↦ StarCensusEngine.labelling_matrix_retained w hy hRetained r c hc) d

/-- **The side law in the engine labelling.**  An engine position frame opens toward `d`
exactly when `wallNumeratorAt w d` and its own signed multiplicity (in the engine labelling) have
the same strict sign.  Every star member built by `StarCensusEngine.starMember` is such a frame
(its regrowth is `StarCensusEngine.regrowth`), so a family whose balance terms are these signed
multiplicities, up to one positive or one negative factor, has its side law here. -/
theorem opensToward_engineFrame_iff (w : Regrowth core y degree) (hy : Nondegenerate y)
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
    (d : Fin p → ℚ) :
    OpensToward (GeometricFibre.cls ((StarCensusEngine.frame w hy D E fd).member y)) d ↔
      0 < wallNumeratorAt w d * signedMult (StarCensusEngine.labelling w hy D E).presentation := by
  exact opensToward_cls_iff_of_agree _ (StarCensusEngine.frame_degenerate w hy fd hRetained) _
    (Equiv.refl _) (StarCensusEngine.frame_slot w hy D E fd)
    (fun r c hc ↦ StarCensusEngine.labelling_matrix_retained w hy hRetained r c hc) d

end DraismaVargas.Count.IntegerCount
