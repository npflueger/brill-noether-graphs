module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailMarks
public import DraismaVargasMarkedCount.MarkedCountGeneral.Rigidity

@[expose] public section

/-!
# Restriction over the tails: the restriction of a frame, as a typed frame

For a frame `f` over the tailed core:

* the lower index `lowerIdx T hc f j`, the number of ascents of the slopes of tail `j`
  (`lowerNat`, `= (aⱼ + 1 - s_1)/2`), with `Σⱼ lowerIdx = #lone sheets` (`sum_lowerNat`);
* the slopes `slopeSeq T hc f j`, a slope sequence with `lowerIdx j` ascents (`isSlopeSeq_sPath`,
  from `Rigidity.exists_slopeSeq`);
* the typed frame `typedFrame T hc f` of type `aⱼ - 2 lowerIdx j` in degree `d - Σ lowerIdx`, whose
  datum is `dat` (module `RestrictTailDatum`) at `m = d - Σ lowerIdx` (definitionally);
* its coordinates (`coordsAt_typedFrame`, `coordsAt_tail`) and the multiplicity identity
  `typedAbsMult (typedFrame f) = f.absMult` (`typedAbsMult_typedFrame`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.MarkedCountGeneral.Sheets (IsNew IsLone restrictSheets inclSV inclSE)
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction
open scoped Matrix

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) (f : Frame T.H degree)

/-! ## 1.  The lower index and the slopes -/

/-- The number of ascents of the tail at `j`: `(aⱼ + 1 - s_1)/2`. -/
def lowerNat (j : Fin k) : ℕ := (c j + 2 - sPath T hc (f.member 0) j 0) / 2

theorem blockExcess_nonneg (j : Fin k) : 0 ≤ blockExcess T hc (f.member 0) j := by
  unfold blockExcess
  refine Finset.sum_nonneg fun i _ ↦ ?_
  rw [mSpine_sub_eq]
  split_ifs <;> norm_num

theorem two_mul_lowerNat (j : Fin k) :
    2 * lowerNat T hc f j + sPath T hc (f.member 0) j 0 = c j + 2 := by
  have h := two_mul_blockExcess T hc (f.member 0) j
  have h0 := blockExcess_nonneg T hc f j
  unfold lowerNat
  omega

theorem lowerNat_eq (j : Fin k) : (lowerNat T hc f j : ℤ) = blockExcess T hc (f.member 0) j := by
  have h := two_mul_blockExcess T hc (f.member 0) j
  have h1 := two_mul_lowerNat T hc f j
  omega

theorem lowerNat_lt (j : Fin k) : lowerNat T hc f j < (c j + 1) / 2 + 1 := by
  have h1 := two_mul_lowerNat T hc f j
  have h2 := one_le_sPath T hc (f.member 0) j 0
  omega

/-- **The lower index** of a frame. -/
def lowerIdx : ∀ j, Fin ((c j + 1) / 2 + 1) := fun j ↦ ⟨lowerNat T hc f j, lowerNat_lt T hc f j⟩

/-- **The number of shed sheets is the number of ascents.** -/
theorem sum_lowerNat : ∑ j, (lowerIdx T hc f j : ℕ) = nShed T hc (f.member 0) := by
  have h := card_loneSet_eq T hc (f.member 0)
  have h2 : (∑ j, (lowerIdx T hc f j : ℕ) : ℤ) = ∑ j, blockExcess T hc (f.member 0) j := by
    exact Finset.sum_congr rfl fun j _ ↦ lowerNat_eq T hc f j
  exact_mod_cast h2.trans h.symm

/-- The degree of the restriction. -/
abbrev mDeg : ℕ := degree - ∑ j, (lowerIdx T hc f j : ℕ)

theorem mDeg_add : mDeg T hc f + nShed T hc (f.member 0) = degree := by
  have h1 := sum_lowerNat T hc f
  have h2 := nShed_lt T hc (f.member 0)
  unfold mDeg
  omega

theorem sPath_eq_slope (j : Fin k) (i : Fin (c j + 1)) :
    sPath T hc (f.member 0) j i = slope (T.cubic hc) (cat T j) f i := by
  rw [slope_eq]; rfl

/-- **The slopes form a slope sequence** with `lowerIdx j` ascents. -/
theorem isSlopeSeq_sPath (j : Fin k) :
    IsSlopeSeq (c j + 1) (lowerIdx T hc f j) (fun i ↦ sPath T hc (f.member 0) j i) := by
  obtain ⟨J', s, -, hs⟩ := exists_slopeSeq (T.cubic hc) (cat T j) f
  have hfun : s.1 = fun i ↦ sPath T hc (f.member 0) j i := by
    funext i; rw [hs i, sPath_eq_slope]
  have hJ : J' = lowerIdx T hc f j := by
    have h4 := s.2.2.2.2 ⟨0, by omega⟩ rfl
    rw [hfun] at h4
    have h1 := two_mul_lowerNat T hc f j
    change J' = lowerNat T hc f j
    simp only at h4
    have : (⟨0, by omega⟩ : Fin (c j + 1)) = 0 := rfl
    rw [this] at h4
    omega
  have := s.2
  rw [hfun, hJ] at this
  exact this

/-- **The slopes** of a frame. -/
def slopeSeq (j : Fin k) : SlopeSeq (c j + 1) (lowerIdx T hc f j) :=
  ⟨fun i ↦ sPath T hc (f.member 0) j i, isSlopeSeq_sPath T hc f j⟩

/-! ## 2.  The typed frame

Stated for any lower index `J` equal to `lowerIdx` (`hJ`), so that two isomorphic frames give
typed frames of literally the same type (module `RestrictTailIso`). -/

section At

variable (J : ∀ j, Fin ((c j + 1) / 2 + 1)) (hJ : ∀ j, (J j : ℕ) = lowerNat T hc f j)

/-- The degree `d - Σ J`. -/
abbrev mDegAt (d₀ : ℕ) (J₀ : ∀ j, Fin ((c j + 1) / 2 + 1)) : ℕ := d₀ - ∑ j, (J₀ j : ℕ)

include hJ in
theorem sum_J : ∑ j, (J j : ℕ) = nShed T hc (f.member 0) := by
  rw [← sum_lowerNat T hc f]
  exact Finset.sum_congr rfl fun j _ ↦ hJ j

include hJ in
theorem mDegAt_add : mDegAt degree J + nShed T hc (f.member 0) = degree := by
  have h1 := sum_J T hc f J hJ
  have h2 := nShed_lt T hc (f.member 0)
  unfold mDegAt
  omega

/-- **The slopes**, at the lower index `J`. -/
def slopeSeqAt (j : Fin k) : SlopeSeq (c j + 1) (J j) :=
  ⟨fun i ↦ sPath T hc (f.member 0) j i, by
    rw [show J j = lowerIdx T hc f j from Fin.ext (hJ j)]; exact isSlopeSeq_sPath T hc f j⟩

/-- The type `aⱼ - 2 Jⱼ`. -/
abbrev lowerTypeAt (j : Fin k) : ℕ := c j + 1 - 2 * (J j : ℕ)

/-- The datum of the restriction, in degree `d - Σ J`. -/
abbrev tDataAt : GluingDatum (rTarget T hc (f.member 0)) (mDegAt degree J) :=
  dat T hc (f.member 0) (mDegAt degree J) (mDegAt_add T hc f J hJ)

include hJ in
theorem lowerTypeAt_eq (j : Fin k) : lowerTypeAt J j + 1 = sPath T hc (f.member 0) j 0 := by
  have := two_mul_lowerNat T hc f j
  have := one_le_sPath T hc (f.member 0) j 0
  change c j + 1 - 2 * (J j : ℕ) + 1 = _
  rw [hJ j]
  omega

theorem genus_tDataAt :
    genus (tDataAt T hc f J hJ).sourceGraph =
      genus (f.member 0).data.sourceGraph - ∑ j, ((c j : ℤ) + 1) := by
  set M := f.member 0
  have hS := Sheets.genus_restrictSheets (rData T hc M) (split T hc M (mDegAt degree J) (mDegAt_add T hc f J hJ))
    (isLone_split T hc M (mDegAt degree J) (mDegAt_add T hc f J hJ)) (m_pos T hc M (mDegAt degree J) (mDegAt_add T hc f J hJ))
  have hT := rTarget_genus T hc M
  unfold genus at hT
  rw [Fintype.card_fin, Multiset.card_coe] at hS
  have hG := genus_rData T hc M
  have hN := card_loneSet_eq T hc M
  have hE : (∑ j, ((c j : ℤ) + 1 + blockExcess T hc M j)) =
      ∑ j, ((c j : ℤ) + 1) + ∑ j, blockExcess T hc M j := Finset.sum_add_distrib
  change genus (dat T hc M (mDegAt degree J) (mDegAt_add T hc f J hJ)).sourceGraph = _
  have hT' : (Multiset.card (rTarget T hc M).edges : ℤ) - Fintype.card (rTarget T hc M).V = -1 := by
    linarith
  rw [hT'] at hS
  linarith

/-- **The dimension count** of the restriction (condition (D3)). -/
theorem tDataAt_saturated :
    ((rTarget T hc (f.member 0)).edges.card : ℤ) + typeExcess (lowerTypeAt J) =
      2 * genus (tDataAt T hc f J hJ).sourceGraph + 2 * (mDegAt degree J) - 5 := by
  set M := f.member 0
  have hSat := M.fullDim.saturated
  rw [card_edges_target T M] at hSat
  have hE := card_rTarget_edges T hc M
  rw [hE, genus_tDataAt]
  have hmD := mDegAt_add T hc f J hJ
  have hsum := sum_J T hc f J hJ
  have hType : typeExcess (lowerTypeAt J) =
      ∑ j, ((c j : ℤ) - 2 * (J j : ℕ)) := by
    unfold typeExcess
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h2 := two_mul_lowerNat T hc f j
    have h3 := one_le_sPath T hc (f.member 0) j 0
    have h2' : 2 * (J j : ℕ) ≤ c j + 1 := by rw [hJ j]; omega
    change ((c j + 1 - 2 * (J j : ℕ) : ℕ) : ℤ) - 1 = (c j : ℤ) - 2 * ((J j : ℕ) : ℤ)
    push_cast [h2']
    ring
  rw [hType]
  have h3 : (∑ j, ((3 * c j + 2 : ℕ) : ℤ)) = 3 * ∑ j, (c j : ℤ) + 2 * k := by
    push_cast
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h4 : (∑ j, ((c j : ℤ) + 1)) = ∑ j, (c j : ℤ) + k := by
    rw [Finset.sum_add_distrib]; simp
  have h5 : (∑ j, ((c j : ℤ) - 2 * (J j : ℕ))) =
      ∑ j, (c j : ℤ) - 2 * ((∑ j, (J j : ℕ) : ℕ) : ℤ) := by
    push_cast
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  push_cast at hSat
  rw [show (∑ j, (3 * (c j : ℤ) + 2)) = 3 * ∑ j, (c j : ℤ) + 2 * k by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring] at hSat
  rw [h4, h5, hsum]
  have hmD' : mDegAt degree J + nShed T hc M = degree := mDegAt_add T hc f J hJ
  have hm' : ((mDegAt degree J : ℕ) : ℤ) = degree - nShed T hc M := by omega
  rw [hm']
  linarith

/-- **The restriction of a frame, as a typed frame**. -/
def typedFrameAt : TypedFrame core mark (lowerTypeAt J) (mDegAt degree J) where
  target := rTarget T hc (f.member 0)
  data := tDataAt T hc f J hJ
  markSource := markSrc T hc (f.member 0) (mDegAt degree J) (mDegAt_add T hc f J hJ)
  fullDim :=
    { valid := dat_valid T hc (f.member 0) _ _
      targetConnected := rTarget_connected T hc (f.member 0)
      targetGenus := rTarget_genus T hc (f.member 0)
      saturated := tDataAt_saturated T hc f J hJ
      labelling := labelling T hc (f.member 0) _ _
      det_ne_zero := det_labelling_ne_zero T hc (f.member 0) _ _
      trivalent := fun X ↦ (nonDanglingValency_dat_le T hc (f.member 0) _ _ X).trans
        ((f.member 0).fullDim.trivalent _)
      markValency := fun X hX ↦ by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hX
        exact nonDanglingValency_markSrc T hc (f.member 0) _ _ j
      pathEnds := dat_pathEnds T hc (f.member 0) _ _ }
  ident :=
    { vertex := vertexEquiv T hc (f.member 0) _ _
      row := rowEquiv T hc (f.member 0) _ _
      incidence := markedIncidenceCount_eq T hc (f.member 0) _ _
      vertex_mark := fun j ↦ vertexEquiv_markSrc T hc (f.member 0) _ _ j _ }
  typed j := by
    constructor
    · rw [localRamification_markSrc]
      have h0 := MarkedCount.markRamification_nonneg (f.member 0).fullDim.valid
        (uSource T (f.member 0) j)
      have h1 := lowerTypeAt_eq T hc f J hJ j
      push_cast [← h1]
      omega
    · have h1 := lowerTypeAt_eq T hc f J hJ j
      have h2 := sPath_le_blockCard_markSrc T hc (f.member 0) (mDegAt degree J) (mDegAt_add T hc f J hJ) j
      change _ ≤ markIndex (dat T hc (f.member 0) (mDegAt degree J) (mDegAt_add T hc f J hJ))
        (markSrc T hc (f.member 0) (mDegAt degree J) (mDegAt_add T hc f J hJ) j)
      omega

@[simp] theorem typedFrameAt_target : (typedFrameAt T hc f J hJ).target = rTarget T hc (f.member 0) := rfl
@[simp] theorem typedFrameAt_data : (typedFrameAt T hc f J hJ).data = tDataAt T hc f J hJ := rfl
@[simp] theorem typedFrameAt_markSource (j : Fin k) :
    (typedFrameAt T hc f J hJ).markSource j = markSrc T hc (f.member 0) (mDegAt degree J) (mDegAt_add T hc f J hJ) j :=
  rfl


end At

/-- The datum of the restriction, in degree `d - Σ lowerIdx`. -/
abbrev tData : GluingDatum (rTarget T hc (f.member 0)) (mDeg T hc f) :=
  tDataAt T hc f (lowerIdx T hc f) (fun _ ↦ rfl)

/-- The type of the restricted mark `j`: `aⱼ - 2 lowerIdx j`. -/
abbrev lowerTypeOf (j : Fin k) : ℕ := lowerTypeAt (lowerIdx T hc f) j

theorem lowerTypeOf_eq (j : Fin k) : lowerTypeOf T hc f j + 1 = sPath T hc (f.member 0) j 0 :=
  lowerTypeAt_eq T hc f (lowerIdx T hc f) (fun _ ↦ rfl) j

/-- **The restriction of a frame, as a typed frame**. -/
abbrev typedFrame : TypedFrame core mark (lowerTypeOf T hc f) (mDeg T hc f) :=
  typedFrameAt T hc f (lowerIdx T hc f) (fun _ ↦ rfl)

@[simp] theorem typedFrame_target : (typedFrame T hc f).target = rTarget T hc (f.member 0) := rfl
@[simp] theorem typedFrame_data : (typedFrame T hc f).data = tData T hc f := rfl
@[simp] theorem typedFrame_markSource (j : Fin k) :
    (typedFrame T hc f).markSource j = markSrc T hc (f.member 0) (mDeg T hc f) (mDeg_add T hc f) j :=
  rfl

/-! ## 3.  The multiplicity -/

/-- Membership in the ramified leaf images, unfolded. -/
theorem mem_ramifiedLeafImages {types : Fin k → ℕ} {d' : ℕ} {κ : TypedFrame core mark types d'}
    {x : κ.target.V} :
    x ∈ κ.ramifiedLeafImages ↔
      (∃ j, 0 < types j ∧ (κ.markSource j).1.1 = x) ∧ Count.IsLeafVertex κ.target x := by
  classical
  unfold TypedFrame.ramifiedLeafImages
  constructor
  · intro hx
    obtain ⟨hImg, hLeaf⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hImg
    exact ⟨⟨j, (Finset.mem_filter.mp hj).2, rfl⟩, hLeaf⟩
  · rintro ⟨⟨j, hj, rfl⟩, hLeaf⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩, hLeaf⟩

/-- The target vertex of the restricted mark `j`. -/
def xR (j : Fin k) : (rTarget T hc (f.member 0)).V :=
  (markSrc T hc (f.member 0) (mDeg T hc f) (mDeg_add T hc f) j).1.1

theorem vIncl_xR (j : Fin k) : vIncl (xR T hc f j) = xMark T (f.member 0) j :=
  congrArg (fun X : (f.member 0).data.SourceVertex ↦ X.1.1)
    (cSV_markSrc T hc (f.member 0) (mDeg T hc f) (mDeg_add T hc f) j)

/-- The image of a mark is a leaf of `T'` exactly when `φ` folds at it. -/
theorem isLeaf_xR_iff (j : Fin k) :
    Count.IsLeafVertex (rTarget T hc (f.member 0)) (xR T hc f j) ↔ j ∈ folds T (f.member 0) := by
  classical
  rw [mem_folds]
  unfold Count.IsLeafVertex
  have hR := card_incidentEdges_restrict (Keep := Keep T (f.member 0))
    (hKeep := Keep_nonempty T hc (f.member 0)) (xR T hc f j)
  rw [vIncl_xR] at hR
  have hK := card_kept_at T hc (f.member 0) (xMark_mem_Keep T hc (f.member 0) j)
  rw [show (if xMark T (f.member 0) j ∈ Set.range (xMark T (f.member 0)) then 1 else 0) = 1 by
    simp] at hK
  change (GluingDatum.incidentEdges (xR T hc f j)).card = 1 ↔ _
  omega

/-- **The ramified leaf images are the folds.** -/
theorem card_ramifiedLeafImages_typedFrame :
    (typedFrame T hc f).ramifiedLeafImages.card = (folds T (f.member 0)).card := by
  classical
  refine (Finset.card_bij (fun j _ ↦ xR T hc f j) ?_ ?_ ?_).symm
  · intro j hj
    refine mem_ramifiedLeafImages.mpr ⟨⟨j, ?_, rfl⟩, (isLeaf_xR_iff T hc f j).mpr hj⟩
    have h1 := lowerTypeOf_eq T hc f j
    have h2 := two_le_sPath_of_divalent T hc (f.member 0) j ((mem_folds T (f.member 0)).mp hj)
    omega
  · intro i _ j _ h
    apply xMark_injective T hc (f.member 0)
    rw [← vIncl_xR T hc f i, ← vIncl_xR T hc f j]
    exact congrArg vIncl h
  · intro x hx
    obtain ⟨⟨j, -, rfl⟩, hLeaf⟩ := mem_ramifiedLeafImages.mp hx
    exact ⟨j, (isLeaf_xR_iff T hc f j).mp hLeaf, rfl⟩

/-- The tail factor: `∏ (den · |weight|) = 2^{Σⱼ (c j + 1)}`. -/
theorem prod_tailFactor :
    ∏ q, (((tailWeight T hc (f.member 0) q).den : ℚ) * |tailWeight T hc (f.member 0) q|) =
      2 ^ ∑ j, (c j + 1) := by
  rw [Fintype.prod_sigma, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [tailWeight_den_mul_abs]
  simp

/-- **The tail factor is `1`**: `|Mult(ψ; marks)| = |Mult_H(φ)|`. -/
theorem typedAbsMult_typedFrame : (typedFrame T hc f).typedAbsMult = f.absMult := by
  set M := f.member 0 with hMdef
  have hD := denominatorProduct_labelling T hc M (mDeg T hc f) (mDeg_add T hc f)
  have hA := abs_det_labelling T hc M (mDeg T hc f) (mDeg_add T hc f)
  have hL := leafCount_target_eq T hc M
  have hL' := leafCount_rTarget_eq T hc M
  have hR := card_ramifiedLeafImages_typedFrame T hc f
  have hP := prod_tailFactor T hc f
  rw [← hMdef] at hR hP
  have hP' : (∏ q, ((tailWeight T hc M q).den : ℚ)) * |∏ q, tailWeight T hc M q| =
      2 ^ ∑ j, (c j + 1) := by
    rw [Finset.abs_prod, ← Finset.prod_mul_distrib]; exact hP
  have hDn : (∏ q, ((tailWeight T hc M q).den : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ ↦ by exact_mod_cast (tailWeight T hc M q).den_nz
  have hW : |∏ q, tailWeight T hc M q| ≠ 0 :=
    abs_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun q _ ↦ tailWeight_ne_zero T hc M q)
  have hStar : (typedFrame T hc f).leafCountStar = (otherLeaves T M).card := by
    unfold TypedFrame.leafCountStar
    rw [hR]
    change Count.leafCount (rTarget T hc M) - _ = _
    omega
  unfold TypedFrame.typedAbsMult TypedFrame.typedSignedMult
  rw [hStar]
  change _ = |Count.signedMult M.fullDim.labelling.presentation|
  unfold Count.signedMult
  change |(Count.denominatorProduct (labelling T hc M (mDeg T hc f) (mDeg_add T hc f)).presentation
      : ℚ) / 2 ^ (otherLeaves T M).card *
      (GluingDatum.LengthMatrixPresentation.matrix
        (labelling T hc M (mDeg T hc f) (mDeg_add T hc f)).presentation).det| = _
  rw [hD, hL]
  simp only [abs_mul, abs_div, Nat.abs_cast, abs_pow, abs_two]
  rw [hA, pow_add, ← hP']
  push_cast
  field_simp

/-! ## 4.  The coordinates -/

theorem tailWeight_pos (q : Σ j, CatSlot (c j)) : 0 < tailWeight T hc (f.member 0) q := by
  rcases q with ⟨j, i | i | i⟩
  · simp only [tailWeight]
    have : (1 : ℚ) ≤ sPath T hc (f.member 0) j i := by
      exact_mod_cast one_le_sPath T hc (f.member 0) j i
    positivity
  · simp [tailWeight]
  · simp [tailWeight]

theorem exists_inr_of_not_col (e : Fin T.P) (he : ∀ i, colIncl T hc (f.member 0) i ≠ e) :
    ∃ q, (colBlocks T hc (f.member 0)).symm e = Sum.inr q := by
  rcases h : (colBlocks T hc (f.member 0)).symm e with i | q
  · exfalso
    refine he i ?_
    rw [← (colBlocks T hc (f.member 0)).apply_symm_apply e, h]
    rfl
  · exact ⟨q, rfl⟩

/-- The tail slot read off a non-core column. -/
def slotOfCol (e : Fin T.P) : Fin T.P :=
  Sum.elim (fun _ ↦ e) (fun q ↦ T.tailSlot q.1 q.2) ((colBlocks T hc (f.member 0)).symm e)

/-- The weight of a non-core column: `1 / tailWeight`. -/
def weightOfCol (e : Fin T.P) : ℚ :=
  Sum.elim (fun _ ↦ 1) (fun q ↦ 1 / tailWeight T hc (f.member 0) q)
    ((colBlocks T hc (f.member 0)).symm e)

theorem slot_typedFrame (row : Fin p) : (typedFrame T hc f).slot row = row := by
  change (rowEquiv T hc (f.member 0) _ _) ((rowEquiv T hc (f.member 0) _ _).symm row) = row
  exact Equiv.apply_symm_apply _ _

/-- **The coordinates of the restriction**. -/
theorem coordsAt_typedFrame (y : Fin p → ℚ) (yH : Fin T.P → ℚ)
    (hy : ∀ i, yH (T.coreSlot i) = y i) :
    (∀ i, f.coordsAt yH (colIncl T hc (f.member 0) i) = (typedFrame T hc f).coordsAt y i) ∧
      ∀ e, (∀ i, colIncl T hc (f.member 0) i ≠ e) →
        f.coordsAt yH e = weightOfCol T hc f e * yH (slotOfCol T hc f e) := by
  have hz := f.mulVec_coordsAt yH
  obtain ⟨hCore, hTail⟩ := coords_blocks T hc (f.member 0) (mDeg T hc f) (mDeg_add T hc f) yH
    (f.coordsAt yH) hz
  refine ⟨fun i ↦ ?_, fun e he ↦ ?_⟩
  · have hS := (typedFrame T hc f).coordsAt_eq_of_mulVec y
      (fun i ↦ f.coordsAt yH (colIncl T hc (f.member 0) i)) (by
        rw [show (fun row ↦ y ((typedFrame T hc f).slot row)) = fun i ↦ yH (T.coreSlot i) by
          funext row; rw [slot_typedFrame, hy]]
        exact hCore)
    rw [hS]
  · obtain ⟨q, hq⟩ := exists_inr_of_not_col T hc f e he
    have he' : e = (f.member 0).fullDim.labelling.targetEdge.symm
        (tEdge T hc (f.member 0) q.1 q.2) := by
      rw [← (colBlocks T hc (f.member 0)).apply_symm_apply e, hq]; rfl
    have h1 := hTail q
    rw [← he'] at h1
    unfold weightOfCol slotOfCol
    rw [hq]
    simp only [Sum.elim_inr]
    rw [← h1]
    have := (tailWeight_pos T hc f q).ne'
    field_simp

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
