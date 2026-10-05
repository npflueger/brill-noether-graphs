module

public import DraismaVargasCount.FacetCommonMultiplicity

@[expose] public section

/-!
# The census consumers of the type-change step

**Source.**  Vargas, Part II (arXiv:2609.09109), the wall-crossing proposition
`proposition-walking-through-II` at a non-trivalent limit, with the number of members of each
type per labelled limit counted in the valency-four, valency-three and valency-two cases of
the section on changing combinatorial type (`subsec-case-v4`, `subsec-case-v3`,
`subsec-case-v2`).  Builds on `Count/FacetCommonMultiplicity.lean`.

This module turns equal counts per labelled metric limit into the parity statement across a
type change.  `typeChangeSupplyPositive_of_metricCensus` is how step 3 of the genus-six
assembly (`Assembly.typeChanges_genusSix`) is proved, fed by
`CensusAssembly.stepCensus_of_supplies`.

## What is proved

* **§1, the census reduction.**  `facetParity_iff_census`: given the common multiplicity
  `hmult` (`FacetCommonMultiplicity`), `FacetMachine.FacetParity` is **equivalent** to "at
  every coarse facet limit carrying an odd class, the all-class count on the two sides is
  even" (`facetParity_of_census` is the `←` half).  An odd class at a limit makes every class
  there odd (`isOdd_left_of_oddLimit`, `isOdd_right_of_oddLimit`), so the odd fibres are the
  whole fibres; otherwise both odd fibres are empty.  `facetParity_iff_census_at` discharges
  `hmult` at a facet datum.
* **§2, the sum lemma.**  `specializesLeftEquivSigma` / `specializesRightEquivSigma`: the
  classes (satisfying any `P`) at a coarse limit are the disjoint union, over the metric facet
  limits above it, of the classes at each; counted, `card_specializesLeft_eq_finsum` /
  `card_specializesRight_eq_finsum`, using `finite_metricFacetLimit` (there are finitely many
  metric facet limits).
* **§3, the metric consumers.**  `facetParity_of_metric_injective_index`: the metric form of
  `FacetParityPilot.facetParity_of_injective_index` (odd fibres per metric limit, one index
  type, injective, equal ranges; no `hmult` needed).  `facetParity_of_metric_equiv` and
  `facetParity_of_metricIndex`: the same on **whole** fibres, oddness then supplied by `hmult`.
  The named per-limit target **`MetricCensus`** (index per metric limit, any `ι : Type`) with
  `metricCensus_iff` (a bijection of the whole fibres at every metric limit), its consumer
  `facetParity_of_metricCensus`, and inhabitation `metricCensus_self`.
* **§4, the composite consumer.**  `facetParity_of_metricIndex_at` /
  `facetParity_of_metricCensus_at`: `FacetParity` at a facet datum from equal counts per
  labelled metric limit through an index, `hmult` discharged.
  `typeChangeSupplyPositive_of_metricCensus` (one facet datum per step, through
  `FacetParityPilot.typeChangeSupplyPositive_of_exists_facetParity`) and its universal form
  `typeChangeSupplyPositive_of_forall_metricCensus`.
* **§5, the genus-six caterpillar step.**  `cat_obligation_of_metricCensus`; the binder half of
  the step consumer's antecedent is inhabited at `cat_step` (an `example`); `MetricCensus` is
  inhabited at the genus-six caterpillar core paired with itself (an `example`).

## `MetricCensus`

* It is consumed by `facetParity_of_metricCensus` and
  `typeChangeSupplyPositive_of_metricCensus`, it is inhabited at every reflexive pair
  (`metricCensus_self`), and `metricCensus_iff` states it as a bijection of whole fibres.
* It asks for equal counts, not for at most one class on each side: it allows the
  valency-four limits with two members of each type (`N = 2`).  In Lean, the non-emptiness
  half at odd metric limits is `ColumnReceiptExport.exists_odd_mSpecializesRight/Left` (at a
  facet-generic facet datum of a move, degree at least three).
* At genus six it holds at every resolved datum: `CensusAssembly.metricCensus_of_resolved`,
  from the valency-two and valency-four clauses `ValencyTwoPairing.v2ClauseSupply` and
  `ValencyFourRealisation.v4ClauseSupply_genusSix`, the valency-three clause being
  `CensusAssembly.v3Clause_of_resolved`.

## What is not proved here

* **`MetricCensus` is not proved here**; see above for where it is proved at genus six.
  `FacetParity` and `TypeChangeSupplyPositive` are proved here only from it.
* The census hypothesis of `facetParity_of_census` is not proved here.
* `hl'` (the slot is a non-loop of the far core) is carried by the datum-level forms; it is
  free at the datum `FacetCommonMultiplicity.exists_facetDatum_nonloop` builds.
* New `Prop`: `MetricCensus` (see above).  `hmult` is stated inline, never named.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.FacetCensus

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.SimpleWallSupply (TypeChangeSupplyPositive)
open DraismaVargas.Count.FacetMachine
open DraismaVargas.Count.FacetCommonMultiplicity
open DraismaVargas.Count.ValencyThreeGeneral
  (MetricFacetLimit MSpecializesLeft MSpecializesRight exists_metricL exists_metricR)

variable {n p degree : ℕ}

/-! ## 1.  The census at a coarse facet limit -/

section Coarse

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

/-- At a coarse limit carrying an odd class, every class specialising to it is odd (first
side). -/
theorem isOdd_left_of_oddLimit
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    {l : FacetLimit c c' y₀ degree}
    (hodd : (∃ x : FrameClass c degree, x.IsOdd ∧ SpecializesLeft x l) ∨
      ∃ x' : FrameClass c' degree, x'.IsOdd ∧ SpecializesRight x' l)
    {x : FrameClass c degree} (hx : SpecializesLeft x l) : x.IsOdd := by
  rcases hodd with ⟨x₀, h₀, hs₀⟩ | ⟨x₀, h₀, hs₀⟩
  · exact (isOdd_iff_of_absMult_eq (absMult_eq_of_specializesLeft_of_common hmult hx hs₀)).mpr h₀
  · exact (isOdd_iff_of_absMult_eq (absMult_eq_of_specializes_of_common hmult hx hs₀)).mpr h₀

/-- The same on the second side. -/
theorem isOdd_right_of_oddLimit
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    {l : FacetLimit c c' y₀ degree}
    (hodd : (∃ x : FrameClass c degree, x.IsOdd ∧ SpecializesLeft x l) ∨
      ∃ x' : FrameClass c' degree, x'.IsOdd ∧ SpecializesRight x' l)
    {x : FrameClass c' degree} (hx : SpecializesRight x l) : x.IsOdd := by
  rcases hodd with ⟨x₀, h₀, hs₀⟩ | ⟨x₀, h₀, hs₀⟩
  · exact (isOdd_iff_of_absMult_eq (absMult_eq_of_specializes_of_common hmult hs₀ hx)).mp h₀
  · exact (isOdd_iff_of_absMult_eq (absMult_eq_of_specializesRight_of_common hmult hx hs₀)).mpr h₀

/-- Per coarse limit: with a common multiplicity, the odd count is the all-class count when
the limit carries an odd class, and zero otherwise. -/
theorem even_odd_iff_census
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    (l : FacetLimit c c' y₀ degree) :
    Even (Nat.card {x : FrameClass c degree // x.IsOdd ∧ SpecializesLeft x l} +
        Nat.card {x : FrameClass c' degree // x.IsOdd ∧ SpecializesRight x l}) ↔
      (((∃ x : FrameClass c degree, x.IsOdd ∧ SpecializesLeft x l) ∨
          ∃ x' : FrameClass c' degree, x'.IsOdd ∧ SpecializesRight x' l) →
        Even (Nat.card {x : FrameClass c degree // SpecializesLeft x l} +
          Nat.card {x' : FrameClass c' degree // SpecializesRight x' l})) := by
  by_cases hodd : (∃ x : FrameClass c degree, x.IsOdd ∧ SpecializesLeft x l) ∨
      ∃ x' : FrameClass c' degree, x'.IsOdd ∧ SpecializesRight x' l
  · have hL : Nat.card {x : FrameClass c degree // x.IsOdd ∧ SpecializesLeft x l} =
        Nat.card {x : FrameClass c degree // SpecializesLeft x l} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x ↦
        ⟨fun h ↦ h.2, fun h ↦ ⟨isOdd_left_of_oddLimit hmult hodd h, h⟩⟩)
    have hR : Nat.card {x : FrameClass c' degree // x.IsOdd ∧ SpecializesRight x l} =
        Nat.card {x : FrameClass c' degree // SpecializesRight x l} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x ↦
        ⟨fun h ↦ h.2, fun h ↦ ⟨isOdd_right_of_oddLimit hmult hodd h, h⟩⟩)
    rw [hL, hR]
    exact ⟨fun h _ ↦ h, fun h ↦ h hodd⟩
  · have hL : IsEmpty {x : FrameClass c degree // x.IsOdd ∧ SpecializesLeft x l} :=
      ⟨fun x ↦ hodd (Or.inl ⟨x.1, x.2⟩)⟩
    have hR : IsEmpty {x : FrameClass c' degree // x.IsOdd ∧ SpecializesRight x l} :=
      ⟨fun x ↦ hodd (Or.inr ⟨x.1, x.2⟩)⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]
    exact ⟨fun _ h ↦ absurd h hodd, fun _ ↦ ⟨0, rfl⟩⟩

/-- **The census reduction, as an interface.** -/
theorem facetParity_iff_census
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b) :
    FacetParity c c' degree y₀ ↔
      ∀ l : FacetLimit c c' y₀ degree,
        ((∃ x : FrameClass c degree, x.IsOdd ∧ SpecializesLeft x l) ∨
            ∃ x' : FrameClass c' degree, x'.IsOdd ∧ SpecializesRight x' l) →
          Even (Nat.card {x : FrameClass c degree // SpecializesLeft x l} +
            Nat.card {x' : FrameClass c' degree // SpecializesRight x' l}) :=
  forall_congr' fun l ↦ even_odd_iff_census hmult l

/-- **The census consumer.** -/
theorem facetParity_of_census
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    (hcensus : ∀ l : FacetLimit c c' y₀ degree,
      ((∃ x : FrameClass c degree, x.IsOdd ∧ SpecializesLeft x l) ∨
          ∃ x' : FrameClass c' degree, x'.IsOdd ∧ SpecializesRight x' l) →
        Even (Nat.card {x : FrameClass c degree // SpecializesLeft x l} +
          Nat.card {x' : FrameClass c' degree // SpecializesRight x' l})) :
    FacetParity c c' degree y₀ :=
  (facetParity_iff_census hmult).mpr hcensus

end Coarse

/-! ## 2.  A coarse limit is the disjoint union of its metric limits -/

section Sum

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

theorem specializesLeft_of_mSpecializes {x : FrameClass c degree}
    {m : MetricFacetLimit c c' y₀ degree} {l : FacetLimit c c' y₀ degree} (hm : m.toCoarse = l)
    (h : MSpecializesLeft x m) : SpecializesLeft x l := by
  subst hm; exact h.specializesLeft

theorem specializesRight_of_mSpecializes {x : FrameClass c' degree}
    {m : MetricFacetLimit c c' y₀ degree} {l : FacetLimit c c' y₀ degree} (hm : m.toCoarse = l)
    (h : MSpecializesRight x m) : SpecializesRight x l := by
  subst hm; exact h.specializesRight

/-- **The sum lemma, first side.** -/
noncomputable def specializesLeftEquivSigma (P : FrameClass c degree → Prop)
    (l : FacetLimit c c' y₀ degree) :
    {x : FrameClass c degree // P x ∧ SpecializesLeft x l} ≃
      Σ m : {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l},
        {x : FrameClass c degree // P x ∧ MSpecializesLeft x m.1} where
  toFun x := ⟨⟨(exists_metricL x.2.2).choose, (exists_metricL x.2.2).choose_spec.1⟩,
    ⟨x.1, x.2.1, (exists_metricL x.2.2).choose_spec.2⟩⟩
  invFun y := ⟨y.2.1, y.2.2.1, specializesLeft_of_mSpecializes y.1.2 y.2.2.2⟩
  left_inv _ := rfl
  right_inv y := by
    refine Sigma.subtype_ext (Subtype.ext ?_) rfl
    exact (exists_metricL (specializesLeft_of_mSpecializes y.1.2 y.2.2.2)).choose_spec.2.unique
      y.2.2.2

/-- **The sum lemma, second side.** -/
noncomputable def specializesRightEquivSigma (P : FrameClass c' degree → Prop)
    (l : FacetLimit c c' y₀ degree) :
    {x : FrameClass c' degree // P x ∧ SpecializesRight x l} ≃
      Σ m : {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l},
        {x : FrameClass c' degree // P x ∧ MSpecializesRight x m.1} where
  toFun x := ⟨⟨(exists_metricR x.2.2).choose, (exists_metricR x.2.2).choose_spec.1⟩,
    ⟨x.1, x.2.1, (exists_metricR x.2.2).choose_spec.2⟩⟩
  invFun y := ⟨y.2.1, y.2.2.1, specializesRight_of_mSpecializes y.1.2 y.2.2.2⟩
  left_inv _ := rfl
  right_inv y := by
    refine Sigma.subtype_ext (Subtype.ext ?_) rfl
    exact (exists_metricR (specializesRight_of_mSpecializes y.1.2 y.2.2.2)).choose_spec.2.unique
      y.2.2.2

/-- **The metric facet limits are finitely many**: each is the metric limit of some class,
and a class has at most one metric limit (`MSpecializesLeft.unique`). -/
theorem finite_metricFacetLimit : Finite (MetricFacetLimit c c' y₀ degree) := by
  classical
  let f : {x : FrameClass c degree // ∃ m, MSpecializesLeft x m} ⊕
      {x : FrameClass c' degree // ∃ m, MSpecializesRight x m} →
        MetricFacetLimit c c' y₀ degree
    | Sum.inl x => x.2.choose
    | Sum.inr x => x.2.choose
  refine Finite.of_surjective f fun m ↦ ?_
  induction m using Quotient.ind with
  | _ a =>
    rcases a with w | w
    · have h : MSpecializesLeft (c' := c') (FrameClass.mk w.frame)
          (MetricFacetLimit.ofLeft w) := ⟨w, rfl, rfl⟩
      exact ⟨Sum.inl ⟨_, _, h⟩, (Exists.choose_spec (⟨_, h⟩ : ∃ m, MSpecializesLeft
        (c' := c') (FrameClass.mk w.frame) m)).unique h⟩
    · have h : MSpecializesRight (c := c) (FrameClass.mk w.frame)
          (MetricFacetLimit.ofRight w) := ⟨w, rfl, rfl⟩
      exact ⟨Sum.inr ⟨_, _, h⟩, (Exists.choose_spec (⟨_, h⟩ : ∃ m, MSpecializesRight
        (c := c) (FrameClass.mk w.frame) m)).unique h⟩

/-- **The sum lemma, counted** (first side): the classes at a coarse limit are the sum over
its metric limits. -/
theorem card_specializesLeft_eq_finsum (P : FrameClass c degree → Prop)
    (l : FacetLimit c c' y₀ degree) :
    Nat.card {x : FrameClass c degree // P x ∧ SpecializesLeft x l} =
      ∑ᶠ m : {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l},
        Nat.card {x : FrameClass c degree // P x ∧ MSpecializesLeft x m.1} := by
  classical
  have : Finite (MetricFacetLimit c c' y₀ degree) := finite_metricFacetLimit
  have : Fintype {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l} := Fintype.ofFinite _
  rw [Nat.card_congr (specializesLeftEquivSigma P l), Nat.card_sigma, finsum_eq_sum_of_fintype]

/-- The same on the second side. -/
theorem card_specializesRight_eq_finsum (P : FrameClass c' degree → Prop)
    (l : FacetLimit c c' y₀ degree) :
    Nat.card {x : FrameClass c' degree // P x ∧ SpecializesRight x l} =
      ∑ᶠ m : {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l},
        Nat.card {x : FrameClass c' degree // P x ∧ MSpecializesRight x m.1} := by
  classical
  have : Finite (MetricFacetLimit c c' y₀ degree) := finite_metricFacetLimit
  have : Fintype {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l} := Fintype.ofFinite _
  rw [Nat.card_congr (specializesRightEquivSigma P l), Nat.card_sigma, finsum_eq_sum_of_fintype]

end Sum

/-! ## 3.  Equal counts per metric limit through an index -/

section Metric

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

/-- The bijection an injective index with equal ranges induces. -/
noncomputable def equivOfIndex {α β ι : Type*} (τL : α → ι) (τR : β → ι)
    (hL : Function.Injective τL) (hR : Function.Injective τR)
    (hrange : Set.range τL = Set.range τR) : α ≃ β :=
  (Equiv.ofInjective τL hL).trans ((Set.equivOfEq hrange).trans (Equiv.ofInjective τR hR).symm)

/-- **The metric form of `FacetParityPilot.facetParity_of_injective_index`**: the odd classes
at each metric limit are labelled injectively by one index type on both sides, with equal
ranges.  No common multiplicity is needed. -/
theorem facetParity_of_metric_injective_index {ι : Type*}
    (τL : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c degree // x.IsOdd ∧ MSpecializesLeft x m} → ι)
    (τR : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c' degree // x.IsOdd ∧ MSpecializesRight x m} → ι)
    (hL : ∀ m, Function.Injective (τL m)) (hR : ∀ m, Function.Injective (τR m))
    (hrange : ∀ m, Set.range (τL m) = Set.range (τR m)) :
    FacetParity c c' degree y₀ :=
  facetParity_of_card_eq fun l ↦ Nat.card_congr
    ((specializesLeftEquivSigma FrameClass.IsOdd l).trans
      ((Equiv.sigmaCongrRight fun m : {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l} ↦
        equivOfIndex (τL m.1) (τR m.1) (hL m.1) (hR m.1) (hrange m.1)).trans (specializesRightEquivSigma FrameClass.IsOdd l).symm))

/-- The whole fibre at a coarse limit, as a `P`-fibre with `P = True`. -/
def trueEquivLeft (l : FacetLimit c c' y₀ degree) :
    {x : FrameClass c degree // SpecializesLeft x l} ≃
      {x : FrameClass c degree // True ∧ SpecializesLeft x l} :=
  Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨trivial, h⟩, fun h ↦ h.2⟩

def trueEquivRight (l : FacetLimit c c' y₀ degree) :
    {x : FrameClass c' degree // SpecializesRight x l} ≃
      {x : FrameClass c' degree // True ∧ SpecializesRight x l} :=
  Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨trivial, h⟩, fun h ↦ h.2⟩

/-- **Equal counts per metric limit, all classes, with the common multiplicity.**  A bijection
of the whole fibres at every metric limit gives `FacetParity`: the common multiplicity makes
every bijection preserve oddness. -/
theorem facetParity_of_metric_equiv
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    (e : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c degree // MSpecializesLeft x m} ≃
        {x : FrameClass c' degree // MSpecializesRight x m}) :
    FacetParity c c' degree y₀ := by
  let eT : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c degree // True ∧ MSpecializesLeft x m} ≃
        {x : FrameClass c' degree // True ∧ MSpecializesRight x m} := fun m ↦
    ((Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨trivial, h⟩⟩).trans (e m)).trans
      (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨trivial, h⟩, fun h ↦ h.2⟩)
  refine FacetParityPilot.facetParity_of_equiv_isOdd
    (fun l ↦ (trueEquivLeft l).trans ((specializesLeftEquivSigma (fun _ ↦ True) l).trans
      ((Equiv.sigmaCongrRight fun m : {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l} ↦
        eT m.1).trans
        ((specializesRightEquivSigma (fun _ ↦ True) l).symm.trans (trueEquivRight l).symm))))
    fun l x ↦ ?_
  set x' := ((trueEquivLeft l).trans ((specializesLeftEquivSigma (fun _ ↦ True) l).trans
      ((Equiv.sigmaCongrRight fun m : {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l} ↦
        eT m.1).trans
        ((specializesRightEquivSigma (fun _ ↦ True) l).symm.trans (trueEquivRight l).symm)))) x
  exact (isOdd_iff_of_absMult_eq (absMult_eq_of_specializes_of_common hmult x.2 x'.2)).symm

/-- **The per-limit target, index form**: an injective index on the whole fibres at every
metric limit, with equal ranges, plus the common multiplicity, gives `FacetParity`. -/
theorem facetParity_of_metricIndex {ι : Type*}
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    (τL : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c degree // MSpecializesLeft x m} → ι)
    (τR : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c' degree // MSpecializesRight x m} → ι)
    (hL : ∀ m, Function.Injective (τL m)) (hR : ∀ m, Function.Injective (τR m))
    (hrange : ∀ m, Set.range (τL m) = Set.range (τR m)) :
    FacetParity c c' degree y₀ :=
  facetParity_of_metric_equiv hmult fun m ↦ equivOfIndex (τL m) (τR m) (hL m) (hR m) (hrange m)

/-- **Equal counts per labelled metric limit, through an index** -- the per-limit target of
the census route.  At every metric facet limit `m`, the classes of `c` and of `c'`
specialising to `m` are labelled injectively by one index type, with the same labels used.
The index may depend on `m`: `K` at a valency-four limit, `Unit` at valency two and three.

It is equivalent to a bijection of the two whole fibres at every metric facet limit
(`metricCensus_iff`), is consumed by `facetParity_of_metricCensus`, and holds at every
reflexive pair (`metricCensus_self`). -/
def MetricCensus (c c' : Core n p) (degree : ℕ) (y₀ : Fin p → ℚ) : Prop :=
  ∀ m : MetricFacetLimit c c' y₀ degree,
    ∃ (ι : Type) (τL : {x : FrameClass c degree // MSpecializesLeft x m} → ι)
      (τR : {x : FrameClass c' degree // MSpecializesRight x m} → ι),
      Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR

/-- **`MetricCensus` as a bijection**: `MetricCensus` is a bijection of the whole fibres at
every metric facet limit. -/
theorem metricCensus_iff :
    MetricCensus c c' degree y₀ ↔
      ∀ m : MetricFacetLimit c c' y₀ degree,
        Nonempty ({x : FrameClass c degree // MSpecializesLeft x m} ≃
          {x : FrameClass c' degree // MSpecializesRight x m}) := by
  refine forall_congr' fun m ↦ ⟨?_, ?_⟩
  · rintro ⟨ι, τL, τR, hL, hR, hrange⟩
    exact ⟨equivOfIndex τL τR hL hR hrange⟩
  · rintro ⟨e⟩
    refine ⟨Fin (Nat.card {x : FrameClass c degree // MSpecializesLeft x m}),
      Finite.equivFin _, e.symm.trans (Finite.equivFin _),
      (Finite.equivFin _).injective, (e.symm.trans (Finite.equivFin _)).injective, ?_⟩
    rw [Equiv.range_eq_univ, Equiv.range_eq_univ]

/-- **The composite consumer**: the common multiplicity and equal counts per labelled metric
limit give `FacetParity`. -/
theorem facetParity_of_metricCensus
    (hmult : ∀ a b : FacetRegrowth c c' y₀ degree, FacetRegrowth.SameLimit a b →
      regrowthMult a = regrowthMult b)
    (h : MetricCensus c c' degree y₀) : FacetParity c c' degree y₀ :=
  facetParity_of_metric_equiv hmult fun m ↦ (metricCensus_iff.mp h m).some

/-- Over one core the two sides of a metric facet limit agree. -/
theorem ofLeft_eq_ofRight_self (w : Regrowth c y₀ degree) :
    MetricFacetLimit.ofLeft (c' := c) w = MetricFacetLimit.ofRight (c := c) w :=
  Quotient.sound ⟨GeometricDatumIso.refl _, fun _ ↦ ⟨rfl, rfl⟩⟩

/-- **Inhabitation**: `MetricCensus` holds at every reflexive pair. -/
theorem metricCensus_self : MetricCensus c c degree y₀ :=
  metricCensus_iff.mpr fun _ ↦ ⟨Equiv.subtypeEquivRight fun _ ↦
    ⟨fun ⟨w, hx, hm⟩ ↦ ⟨w, hx, (ofLeft_eq_ofRight_self w).symm.trans hm⟩,
      fun ⟨w, hx, hm⟩ ↦ ⟨w, hx, (ofLeft_eq_ofRight_self w).trans hm⟩⟩⟩

end Metric

/-! ## 4.  At a facet datum and at a step -/

section Step

variable {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **Equal counts per labelled metric limit, at a facet datum**, through an index.  The
common multiplicity is discharged (`FacetCommonMultiplicity`). -/
theorem facetParity_of_metricIndex_at {ι : Type*} (hd : FacetDatum c c' degree e₀ y₀ ε)
    (hl' : c'.tail e₀ ≠ c'.head e₀)
    (τL : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c degree // MSpecializesLeft x m} → ι)
    (τR : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c' degree // MSpecializesRight x m} → ι)
    (hL : ∀ m, Function.Injective (τL m)) (hR : ∀ m, Function.Injective (τR m))
    (hrange : ∀ m, Set.range (τL m) = Set.range (τR m)) :
    FacetParity c c' degree y₀ :=
  facetParity_of_metricIndex (commonMult_of_facetDatum hd hl') τL τR hL hR hrange

/-- The same with `MetricCensus`. -/
theorem facetParity_of_metricCensus_at (hd : FacetDatum c c' degree e₀ y₀ ε)
    (hl' : c'.tail e₀ ≠ c'.head e₀) (h : MetricCensus c c' degree y₀) :
    FacetParity c c' degree y₀ :=
  facetParity_of_metricCensus (commonMult_of_facetDatum hd hl') h

/-- The census reduction at a facet datum, with the common multiplicity discharged. -/
theorem facetParity_iff_census_at (hd : FacetDatum c c' degree e₀ y₀ ε)
    (hl' : c'.tail e₀ ≠ c'.head e₀) :
    FacetParity c c' degree y₀ ↔
      ∀ l : FacetLimit c c' y₀ degree,
        ((∃ x : FrameClass c degree, x.IsOdd ∧ SpecializesLeft x l) ∨
            ∃ x' : FrameClass c' degree, x'.IsOdd ∧ SpecializesRight x' l) →
          Even (Nat.card {x : FrameClass c degree // SpecializesLeft x l} +
            Nat.card {x' : FrameClass c' degree // SpecializesRight x' l}) :=
  facetParity_iff_census (commonMult_of_facetDatum hd hl')

/-- **The composite consumer at the step level**: `SimpleWallSupply.TypeChangeSupplyPositive`
from `MetricCensus` at one facet datum per step whose slot is a non-loop of the far core
(the extra binder is free: `FacetCommonMultiplicity.exists_facetDatum_nonloop`). -/
theorem typeChangeSupplyPositive_of_metricCensus
    (h : ∀ c c' : CubicCore n p, Step c c' →
      ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core c'.core degree e₀ y₀ ε ∧
        c'.core.tail e₀ ≠ c'.core.head e₀ ∧ MetricCensus c.core c'.core degree y₀) :
    TypeChangeSupplyPositive degree n p :=
  FacetParityPilot.typeChangeSupplyPositive_of_exists_facetParity fun c c' hs ↦ by
    obtain ⟨e₀, y₀, ε, hd, hl', hc⟩ := h c c' hs
    exact ⟨e₀, y₀, ε, hd, facetParity_of_metricCensus_at hd hl' hc⟩

/-- The universal form implies the existential one. -/
theorem typeChangeSupplyPositive_of_forall_metricCensus
    (h : ∀ c c' : CubicCore n p, Step c c' →
      ∀ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core c'.core degree e₀ y₀ ε →
        c'.core.tail e₀ ≠ c'.core.head e₀ → MetricCensus c.core c'.core degree y₀) :
    TypeChangeSupplyPositive degree n p :=
  typeChangeSupplyPositive_of_metricCensus fun c c' hs ↦ by
    obtain ⟨e₀, y₀, ε, hd, hl'⟩ := exists_facetDatum_nonloop hs degree
    exact ⟨e₀, y₀, ε, hd, hl', h c c' hs e₀ y₀ ε hd hl'⟩

end Step

/-! ## 5.  The genus-six caterpillar step -/

section GenusSix

open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)

/-- The per-step obligation of `TypeChangeSupplyPositive 4 10 15` at `cat_step`, from
`MetricCensus` at a facet datum with a non-loop far slot. -/
theorem cat_obligation_of_metricCensus {e₀ : Fin (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ}
    {ε : ℚ} (hd : FacetDatum catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε)
    (hl' : catLoopCore.core.tail e₀ ≠ catLoopCore.core.head e₀)
    (h : MetricCensus catCubicCore.core catLoopCore.core (2 + 2) y₀) :
    ∃ y y' : Fin (6 * 2 + 3) → ℚ, SimpleWallSupply.PositiveGeneral catCubicCore.core (2 + 2) y ∧
      SimpleWallSupply.PositiveGeneral catLoopCore.core (2 + 2) y' ∧
        CountTransportLink.CountLink (2 + 2) catCubicCore.core y catLoopCore.core y' :=
  FacetParityPilot.cat_obligation_of_facetParity_at hd (facetParity_of_metricCensus_at hd hl' h)

/-- The binder half of the step consumer's antecedent is inhabited at `cat_step`: a facet
datum whose slot is a non-loop of `catLoopCore`. -/
example : ∃ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
    FacetDatum catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε ∧
      catLoopCore.core.tail e₀ ≠ catLoopCore.core.head e₀ :=
  exists_facetDatum_nonloop cat_step (2 + 2)

/-- `MetricCensus` is inhabited at a concrete genus-six instance (the reflexive pair at the
caterpillar core). -/
example (y₀ : Fin (6 * 2 + 3) → ℚ) :
    MetricCensus catCubicCore.core catCubicCore.core (2 + 2) y₀ :=
  metricCensus_self

end GenusSix

end DraismaVargas.Count.FacetCensus
