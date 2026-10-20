module

public import DraismaVargasMarkedCount.MarkedCountGeneral.Regrowth
public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrRestrictRegrow
public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrRegrowRestrict

@[expose] public section

/-!
# The decomposition and the tail count

**The decomposition theorem, on classes** (`tailedClassEquiv`): restriction and regrowth are
inverse,

  `FrameClass T.H d ≃ Σ_J (TypedFrameClass core mark (lowerType c J) (d - shed J) × SlopeData c J)`,

request-free, for one tail, two tails, or any number (all tails at once), with tail
factor `1` (`mult_tailedClassEquiv`), and openness at `y_H` matching openness at its core part,
for every positive tail lengths (`openAt_tailedClassEquiv_iff`). Hence **the tail count**
(`openMultCount_tailed`, with `card_slopeData` from the slope count of module `Ballot`):

  `openMultCount H y_H d = Σ_J (∏ⱼ M_{Jⱼ}(aⱼ)) · typedCount core mark (aⱼ - 2Jⱼ)ⱼ y (d - Σ Jⱼ)`,

which is the left side of the triangular system that determines the typed counts (module
`MarkedCountGeneral.MarkedCount`); and genericity passes from the lower typed frames to `H`
(`general_tailed_of_general`, the direction of the genericity statement that the marked count
uses).

## The inverse laws

`restrictTailed_regrowTailed` (module `CorrRestrictRegrow`) and `regrowTailed_restrictTailed`
(modules `CorrFrameChain`, `CorrFrameTarget`, `CorrRegrowRestrict`). Everything else is proved
from them and from the lemmas of the restriction and the regrowth (modules `Restriction`,
`Regrowth`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}

/-! ## 1.  The inverse laws -/

/-- **Restriction after regrowth is the identity** (one half of the decomposition theorem).
`CatRegrow.restrictTailed_regrowTailed_eq` (module
`CorrRestrictRegrow`): in the regrowth, the tails restriction finds are the attached ones
(`CatRegrow.xSpine_regrow`, `xBulb_regrow`, `xLeaf_regrow`), so the kept vertices are the old ones;
the lone path edges are the block edges, so the slopes are `s` (`|P_i| = s_i`) and the lower index
is `J`; the lone sheets are the new sheets; and the remaining datum is `κ`'s with the new sheets
put back and deleted again (`CatRegrow.resIso`). -/
theorem restrictTailed_regrowTailed (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) (J : LowerIndex c)
    (κ : TypedFrame core mark (lowerType c J) (degree - shed J)) (s : SlopeData c J) :
    (restrictTailed T hc (regrowTailed T hc hd J κ s)).toClass = ⟨J, TypedFrameClass.mk κ, s⟩ :=
  CatRegrow.restrictTailed_regrowTailed_eq T hc hd J κ s

/-- **Regrowth after restriction is the identity** (the decomposition theorem: the fibre over the
tail is determined by the core map). `CatRegrow.regrowTailed_restrictTailed_iso` (module
`CorrRegrowRestrict`): `f` is the regrowth of its own tail chains over its restriction
(`FrameChain.frameIso`: the blocks `P_i^φ` form an add/drop chain, by the rigidity of the tail, a
sheet entering at an ascent being the shed sheet of the ascent), and two regrowths with the same
marks and slopes are isomorphic (`CatRegrow.chainIso`), over the identity of the core. -/
theorem regrowTailed_restrictTailed (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) (f : Frame T.H degree) :
    Nonempty (FrameIso (regrowTailed T hc hd (restrictTailed T hc f).1
      (restrictTailed T hc f).2.1 (restrictTailed T hc f).2.2) f) :=
  CatRegrow.regrowTailed_restrictTailed_iso T hc hd f

/-! ## 2.  The bijection on classes -/

/-- **The decomposition theorem, on classes**: restriction, with inverse regrowth. -/
noncomputable def tailedClassEquiv (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) : FrameClass T.H degree ≃ LowerClass core mark c degree where
  toFun := Quotient.lift (fun f ↦ (restrictTailed T hc f).toClass)
    fun _ _ h ↦ h.elim fun iso ↦ restrictTailed_respects T hc iso
  invFun z := Quot.lift (fun κ ↦ FrameClass.mk (regrowTailed T hc hd z.1 κ z.2.2))
    (fun _ _ h ↦ h.elim fun iso ↦
      FrameClass.mk_eq_mk_iff.mpr (regrowTailed_respects T hc hd z.1 iso z.2.2)) z.2.1
  left_inv x := Quotient.inductionOn x fun f ↦
    FrameClass.mk_eq_mk_iff.mpr (regrowTailed_restrictTailed T hc hd f)
  right_inv z := by
    obtain ⟨J, x, s⟩ := z
    induction x using Quot.ind with
    | mk κ => exact restrictTailed_regrowTailed T hc hd J κ s

@[simp] theorem tailedClassEquiv_mk (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) (f : Frame T.H degree) :
    tailedClassEquiv T hc hd (FrameClass.mk f) = (restrictTailed T hc f).toClass := rfl

/-- **The tail factor is `1`**, on classes (the decomposition theorem). -/
theorem mult_tailedClassEquiv (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) (x : FrameClass T.H degree) :
    (tailedClassEquiv T hc hd x).mult = x.absMult :=
  Quotient.inductionOn x fun f ↦ typedAbsMult_restrictTailed T hc f

/-- **Openness matches**, for every positive tail lengths (no tail needs to be long). -/
theorem openAt_tailedClassEquiv_iff (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) {y : Fin p → ℚ} {yH : Fin T.P → ℚ}
    (hCore : ∀ i, yH (T.coreSlot i) = y i) (hTail : ∀ j s, 0 < yH (T.tailSlot j s))
    (x : FrameClass T.H degree) :
    (tailedClassEquiv T hc hd x).OpenAt y ↔ x.OpenAt yH := by
  induction x using Quotient.inductionOn with
  | h f =>
    obtain ⟨col, slotOf, weight, hCover, hCoords⟩ := coordsAt_restrictTailed T hc f
    obtain ⟨hCol, hOther⟩ := hCoords y yH hCore
    change (∀ i, 0 < (restrictTailed T hc f).2.1.coordsAt y i) ↔ ∀ e, 0 < f.coordsAt yH e
    constructor
    · intro h e
      by_cases he : ∃ i, col i = e
      · obtain ⟨i, rfl⟩ := he
        rw [hCol]
        exact h i
      · push Not at he
        obtain ⟨hw, j, s, hs⟩ := hCover e he
        rw [hOther e he, hs]
        exact mul_pos hw (hTail j s)
    · intro h i
      rw [← hCol]
      exact h _

/-! ## 3.  Genericity -/

/-- **Genericity of the tailed core, forward direction** (the direction the marked count uses): if
no lower typed frame has a zero coordinate at `y`, no frame of `H` has one at `y_H`, for any nonzero
tail lengths. -/
theorem general_tailed_of_general (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    {y : Fin p → ℚ} {yH : Fin T.P → ℚ} (hCore : ∀ i, yH (T.coreSlot i) = y i)
    (hTail : ∀ j s, yH (T.tailSlot j s) ≠ 0)
    (hGeneral : ∀ (J : LowerIndex c) (κ : TypedFrame core mark (lowerType c J) (degree - shed J))
      (col : Fin p), κ.coordsAt y col ≠ 0) :
    ∀ (f : Frame T.H degree) (col : Fin T.P), f.coordsAt yH col ≠ 0 := by
  intro f e
  obtain ⟨col, slotOf, weight, hCover, hCoords⟩ := coordsAt_restrictTailed T hc f
  obtain ⟨hCol, hOther⟩ := hCoords y yH hCore
  by_cases he : ∃ i, col i = e
  · obtain ⟨i, rfl⟩ := he
    rw [hCol]
    exact hGeneral _ _ i
  · push Not at he
    obtain ⟨hw, j, s, hs⟩ := hCover e he
    rw [hOther e he, hs]
    exact mul_ne_zero hw.ne' (hTail j s)

/-! ## 4.  The tail count -/

/-- A finite sum over `Σ i, A i × B i` of a function of `A` is `Σᵢ #B i · Σ_{A i}`. -/
theorem finsum_sigma_prod {ι : Type*} [Fintype ι] {A : ι → Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] (F : ∀ i, A i → ℚ) [Finite (Σ i, A i × B i)] :
    ∑ᶠ z : (Σ i, A i × B i), F z.1 z.2.1 =
      ∑ i, (Fintype.card (B i) : ℚ) * ∑ᶠ a : A i, F i a := by
  classical
  have hFin : ∀ i, Finite (A i × B i) := fun i ↦
    Finite.of_injective (fun z : A i × B i ↦ (⟨i, z⟩ : Σ i, A i × B i))
      fun _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2
  let _ : ∀ i, Fintype (A i × B i) := fun i ↦ Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases isEmpty_or_nonempty (B i) with hB | hB
  · rw [Fintype.card_eq_zero, Nat.cast_zero, zero_mul]
    exact Finset.sum_eq_zero fun z _ ↦ (hB.false z.2).elim
  · obtain ⟨b₀⟩ := hB
    have : Finite (A i) := Finite.of_injective (fun a ↦ (a, b₀)) fun _ _ h ↦ (Prod.mk.inj h).1
    let _ : Fintype (A i) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype]
    have hUniv : (Finset.univ : Finset (A i × B i)) = Finset.univ ×ˢ Finset.univ := by
      ext z; simp
    rw [hUniv, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    change ∑ _b : B i, F i a = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The tail count** (the decomposition theorem, expanded as in the marked count): the weighted
count `openMultCount` on `H` at a request with core part `y` and positive tails is the
ballot-weighted sum of the lower typed counts at `y`. -/
theorem openMultCount_tailed (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) {y : Fin p → ℚ} {yH : Fin T.P → ℚ}
    (hCore : ∀ i, yH (T.coreSlot i) = y i) (hTail : ∀ j s, 0 < yH (T.tailSlot j s)) :
    (IntegerCount.openMultCount T.H yH degree : ℚ) =
      ∑ J : LowerIndex c, (Fintype.card (SlopeData c J) : ℚ) *
        typedCount core mark (lowerType c J) y (degree - shed J) := by
  classical
  rw [IntegerCount.openMultCount_cast_eq_frameSum]
  let e₁ : {x : FrameClass T.H degree // x.OpenAt yH} ≃
      {z : LowerClass core mark c degree // z.OpenAt y} :=
    (tailedClassEquiv T hc hd).subtypeEquiv fun x ↦
      (openAt_tailedClassEquiv_iff T hc hd hCore hTail x).symm
  let e₂ : {z : LowerClass core mark c degree // z.OpenAt y} ≃
      Σ J : LowerIndex c, TypedFibre core mark (lowerType c J) y (degree - shed J) ×
        SlopeData c J :=
    { toFun := fun z ↦ ⟨z.1.1, ⟨z.1.2.1, z.2⟩, z.1.2.2⟩
      invFun := fun w ↦ ⟨⟨w.1, w.2.1.1, w.2.2⟩, w.2.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hFinH : Finite (FrameClass T.H degree) :=
    Finite.of_equiv _ (CrossCoreTransport.fibreEquiv T.H degree yH).symm
  have : Finite (Σ J : LowerIndex c, TypedFibre core mark (lowerType c J) y (degree - shed J) ×
      SlopeData c J) :=
    Finite.of_equiv _ (e₁.trans e₂)
  rw [← finsum_comp_equiv (e₁.trans e₂).symm]
  have hTerm : ∀ w : (Σ J : LowerIndex c,
      TypedFibre core mark (lowerType c J) y (degree - shed J) × SlopeData c J),
      ((e₁.trans e₂).symm w).1.absMult = w.2.1.1.typedAbsMult := by
    intro w
    rw [← mult_tailedClassEquiv T hc hd]
    have h : (tailedClassEquiv T hc hd) ((e₁.trans e₂).symm w).1 = ⟨w.1, w.2.1.1, w.2.2⟩ := by
      change (tailedClassEquiv T hc hd) ((tailedClassEquiv T hc hd).symm ⟨w.1, w.2.1.1, w.2.2⟩) = _
      exact Equiv.apply_symm_apply _ _
    rw [h]
    rfl
  rw [finsum_congr hTerm]
  exact finsum_sigma_prod (fun J (a : TypedFibre core mark (lowerType c J) y (degree - shed J)) ↦
    a.1.typedAbsMult)

/-- **The tail weights are ballot numbers** (the slope count at every mark). -/
theorem card_slopeData (J : LowerIndex c) :
    (Fintype.card (SlopeData c J) : ℤ) = ∏ j, ballot (c j + 1) (J j) := by
  rw [Fintype.card_pi]
  push_cast
  refine Finset.prod_congr rfl fun j _ ↦ card_slopeSeq (by omega) ?_
  have := (J j).isLt
  omega

/-- The marked fibre of every lower type is finite: it is a factor of a finite type. -/
theorem finite_typedFibre (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) (y : Fin p → ℚ) (J : LowerIndex c)
    (hs : Nonempty (SlopeData c J)) :
    Finite (TypedFibre core mark (lowerType c J) y (degree - shed J)) := by
  have hFinH : Finite (FrameClass T.H degree) :=
    Finite.of_equiv _ (CrossCoreTransport.fibreEquiv T.H degree (T.request y)).symm
  have : Finite (LowerClass core mark c degree) := Finite.of_equiv _ (tailedClassEquiv T hc hd)
  obtain ⟨s⟩ := hs
  exact Finite.of_injective (β := LowerClass core mark c degree) (fun x ↦ ⟨J, x.1, s⟩)
    fun x x' h ↦ Subtype.ext (Prod.mk.inj (eq_of_heq (Sigma.mk.inj_iff.mp h).2)).1

end DraismaVargas.Count.MarkedCountGeneral
