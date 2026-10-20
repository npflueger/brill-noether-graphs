module

public import DraismaVargasCount.CountSchedule
public import DraismaVargasCount.CoreRelabelInvariance
public import DraismaVargasCount.CrossCoreTransport
public import Mathlib.Algebra.BigOperators.Ring.Nat

@[expose] public section

/-!
# The weighted count and its link

This module replaces the tracked quantity of the mod-2 count: `GeometricFibre.openOddCount`
counts the open classes of odd multiplicity, and the integer count tracks instead

  `openMultCount core y degree = ∑ᶠ c : {c // c.Open}, c.multNat`,

the sum of `|Mult|` over the open classes of the geometric fibre (Vargas, Part II,
arXiv:2609.09109, the fibre count `fiber-count`). The neutral link object of the walk,
`CountTransportLink.CountLink` (equal parity), is replaced by `IntLink` (equal weighted count),
which is an equivalence relation on sites for the same trivial reason.

## What is proved here

* `openMultCount`, `IntLink`, `intLink_refl/symm/trans`.
* `openMultCount_eq_of_equiv`, `intLink_of_equiv`: an equivalence of the open classes that
  preserves `multNat` preserves the count.  This is the integer twin of
  `CountTransportLink.countLink_of_oddOpenEquiv`.
* `multNat_fibreEquiv`, `openMultCount_eq_of_no_wall`: the request-fibre identification
  `GeometricSegmentWalls.fibreEquiv` does not move `multNat`, so the weighted count is constant
  on a wall-free interval of a segment (twin of
  `GeometricSegmentWalls.openOddCount_eq_of_no_wall`).
* `openMultCount_relabel`: relabelling invariance (twin of `CoreRelabel.openOddCount_relabel`).
* `openMultCount_eq_card_of_multNat_eq_one`: if every open class has multiplicity one, the
  weighted count is the number of open classes.
* `even_openMultCount_iff`, `openMultCount_mod_two`: **the weighted count has the parity of the
  open odd count.**  This is the sanity check that the integer count refines the mod-2 one.
* `openMultCount_cast_eq_frameSum`: the weighted count read on the request-free model
  `CrossCoreTransport.FrameClass`, as a rational sum of `absMult`; this is the form the
  type-change step uses.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

variable {n p degree : ℕ}

/-! ## 1.  The weighted count and the link -/

/-- **The weighted count**: the sum of `multNat = |Mult|` over the open classes of the
geometric fibre.  The fibre is finite (`GeometricFibre.instFinite`), so the `finsum` is a
finite sum. -/
noncomputable def openMultCount (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : ℕ :=
  ∑ᶠ c : {c : GeometricFibre core y degree // c.Open}, c.1.multNat

/-- **The integer link**: equal weighted counts at the two sites.  It replaces
`CountTransportLink.CountLink` (equal parity of `openOddCount`). -/
def IntLink (degree : ℕ) {n p n' p' : ℕ} (core : Core n p) (y : Fin p → ℚ)
    (core' : Core n' p') (y' : Fin p' → ℚ) : Prop :=
  openMultCount core y degree = openMultCount core' y' degree

theorem intLink_refl (degree : ℕ) (core : Core n p) (y : Fin p → ℚ) :
    IntLink degree core y core y := rfl

theorem intLink_symm {n' p' : ℕ} {core : Core n p} {core' : Core n' p'}
    {y : Fin p → ℚ} {y' : Fin p' → ℚ} (h : IntLink degree core y core' y') :
    IntLink degree core' y' core y := h.symm

theorem intLink_trans {n' p' n'' p'' : ℕ} {core : Core n p} {core' : Core n' p'}
    {core'' : Core n'' p''} {y : Fin p → ℚ} {y' : Fin p' → ℚ} {y'' : Fin p'' → ℚ}
    (h : IntLink degree core y core' y') (h' : IntLink degree core' y' core'' y'') :
    IntLink degree core y core'' y'' := h.trans h'

/-- An equivalence of the open classes preserving `multNat` preserves the weighted count. -/
theorem openMultCount_eq_of_equiv {n' p' : ℕ} {core : Core n p} {core' : Core n' p'}
    {y : Fin p → ℚ} {y' : Fin p' → ℚ}
    (e : {c : GeometricFibre core y degree // c.Open} ≃
      {c : GeometricFibre core' y' degree // c.Open})
    (hmult : ∀ c, (e c).1.multNat = c.1.multNat) :
    openMultCount core y degree = openMultCount core' y' degree := by
  unfold openMultCount
  rw [← finsum_comp_equiv e]
  exact finsum_congr fun c ↦ (hmult c).symm

/-- **The integer twin of `CountTransportLink.countLink_of_oddOpenEquiv`**: an equivalence of
the two fibres matching openness and `multNat` is an integer link. -/
theorem intLink_of_equiv {n' p' : ℕ} {core : Core n p} {core' : Core n' p'}
    {y : Fin p → ℚ} {y' : Fin p' → ℚ}
    (e : GeometricFibre core y degree ≃ GeometricFibre core' y' degree)
    (hopen : ∀ c, (e c).Open ↔ c.Open) (hmult : ∀ c, (e c).multNat = c.multNat) :
    IntLink degree core y core' y' :=
  openMultCount_eq_of_equiv (e.subtypeEquiv fun c ↦ (hopen c).symm) fun c ↦ hmult c.1

/-! ## 2.  Constancy between walls -/

/-- The request-fibre identification does not move the multiplicity: it keeps the frame. -/
theorem multNat_fibreEquiv (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (c : GeometricFibre core y degree) :
    (GeometricSegmentWalls.fibreEquiv core degree y y' c).multNat = c.multNat := by
  obtain ⟨member, rfl⟩ := GeometricFibre.cls_surjective c
  rw [GeometricSegmentWalls.fibreEquiv_cls, GeometricFibre.multNat_cls,
    GeometricFibre.multNat_cls]
  rfl

/-- **The weighted count is constant on a wall-free interval of a segment**, the integer twin
of `GeometricSegmentWalls.openOddCount_eq_of_no_wall`. -/
theorem openMultCount_eq_of_no_wall (core : Core n p) (degree : ℕ)
    (y₀ y₁ : Fin p → ℚ) (u v : ℚ)
    (hno : ∀ (k : Frame core degree) (col : Fin p) (t : ℚ), min u v ≤ t → t ≤ max u v →
      ¬ k.IsWallParam y₀ y₁ col t) :
    openMultCount core (RationalAffineWall.segment y₀ y₁ u) degree =
      openMultCount core (RationalAffineWall.segment y₀ y₁ v) degree :=
  intLink_of_equiv
    (GeometricSegmentWalls.fibreEquiv core degree (RationalAffineWall.segment y₀ y₁ u)
      (RationalAffineWall.segment y₀ y₁ v))
    (GeometricSegmentWalls.open_fibreEquiv_iff_of_no_wall core degree y₀ y₁ u v hno)
    (multNat_fibreEquiv core degree _ _)

/-! ## 3.  Relabelling invariance -/

/-- **The weighted count is a relabelling invariant**, the integer twin of
`CoreRelabel.openOddCount_relabel`. -/
theorem openMultCount_relabel {c c' : Core n p} (d : CoreRelabel.Relabel c c')
    {y y' : Fin p → ℚ} (hy : ∀ e, y' (d.slot e) = y e) (degree : ℕ) :
    openMultCount c y degree = openMultCount c' y' degree :=
  intLink_of_equiv (CoreRelabel.relabelEquiv d hy) (CoreRelabel.relabelCls_open d hy)
    fun x ↦ by
      induction x using Quotient.inductionOn with
      | h m => rfl

/-! ## 4.  Multiplicity one -/

/-- If every open class has multiplicity one, the weighted count is the number of open
classes. -/
theorem openMultCount_eq_card_of_multNat_eq_one {core : Core n p} {y : Fin p → ℚ}
    (h : ∀ c : GeometricFibre core y degree, c.Open → c.multNat = 1) :
    openMultCount core y degree = Nat.card {c : GeometricFibre core y degree // c.Open} := by
  classical
  have _ : Fintype {c : GeometricFibre core y degree // c.Open} := Fintype.ofFinite _
  unfold openMultCount
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun c _ ↦ h c.1 c.2,
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Nat.card_eq_fintype_card]

/-! ## 5.  The weighted count refines the open odd count -/

/-- **The weighted count and the open odd count have the same parity**: a sum of naturals is
even exactly when an even number of its terms are odd. -/
theorem even_openMultCount_iff (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Even (openMultCount core y degree) ↔ Even (GeometricFibre.openOddCount core y degree) := by
  classical
  have _ : Fintype {c : GeometricFibre core y degree // c.Open} := Fintype.ofFinite _
  unfold openMultCount
  rw [finsum_eq_sum_of_fintype, Finset.even_sum_iff_even_card_odd]
  have hcard : (Finset.univ.filter fun c : {c : GeometricFibre core y degree // c.Open} ↦
      Odd c.1.multNat).card = GeometricFibre.openOddCount core y degree := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, GeometricFibre.openOddCount]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun c : GeometricFibre core y degree ↦ c.Open) (fun c ↦ Odd c.multNat))
  rw [hcard]

/-- **The weighted count mod two is the open odd count mod two.** -/
theorem openMultCount_mod_two (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    openMultCount core y degree % 2 = GeometricFibre.openOddCount core y degree % 2 := by
  have h := even_openMultCount_iff core y degree
  rcases Nat.even_or_odd (openMultCount core y degree) with he | ho
  · rw [Nat.even_iff.mp he, Nat.even_iff.mp (h.mp he)]
  · have ho' : Odd (GeometricFibre.openOddCount core y degree) :=
      Nat.not_even_iff_odd.mp fun he' ↦ (Nat.not_even_iff_odd.mpr ho) (h.mpr he')
    rw [Nat.odd_iff.mp ho, Nat.odd_iff.mp ho']

/-! ## 6.  The request-free model -/

/-- The multiplicity of a class of the request-free model is the multiplicity of its class in
the geometric fibre. -/
theorem absMult_frameClass_eq (core : Core n p) (degree : ℕ) (y : Fin p → ℚ)
    (x : CrossCoreTransport.FrameClass core degree) :
    x.absMult = ((CrossCoreTransport.fibreEquiv core degree y x).multNat : ℚ) := by
  rw [← GeometricFibre.absMult_eq_multNat]
  induction x using Quotient.inductionOn with
  | h k => rfl

/-- **The weighted count on the request-free model**: as a rational number it is the sum of
`absMult` over the frame classes open at the request.  The type-change step is stated on
`CrossCoreTransport.FrameClass`, so this is where it reads the count. -/
theorem openMultCount_cast_eq_frameSum (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    (openMultCount core y degree : ℚ) =
      ∑ᶠ x : {x : CrossCoreTransport.FrameClass core degree // x.OpenAt y}, x.1.absMult := by
  classical
  have _ : Fintype {c : GeometricFibre core y degree // c.Open} := Fintype.ofFinite _
  have _ : Fintype {x : CrossCoreTransport.FrameClass core degree // x.OpenAt y} :=
    Fintype.ofFinite _
  unfold openMultCount
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum]
  refine (Fintype.sum_equiv ((CrossCoreTransport.fibreEquiv core degree y).subtypeEquiv
    fun x ↦ (CrossCoreTransport.open_fibreEquiv core degree y x).symm) _ _ fun x ↦ ?_).symm
  exact absMult_frameClass_eq core degree y x.1

end DraismaVargas.Count.IntegerCount
