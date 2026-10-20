module

public import DraismaVargasCount.IntegerCount.Transport
public import DraismaVargasCount.CensusAssembly
public import DraismaVargasCount.ValencyTwoPairing
public import DraismaVargasCount.ValencyFourRealisation

@[expose] public section

/-!
# The integer crossing of a type change

The integer twin of the type-change step of the parity proof:
`FacetMachine.FacetParity` → `FacetMachine.countLink_of_facetParity` →
`FacetCensus.typeChangeSupplyPositive_of_metricCensus` → `EvenGenusParity.typeChanges`.

`FacetParity c c' degree y₀` asks, at each facet limit `l`, that the **odd** classes on the two
sides specialising to `l` be even in number.  Its integer twin `FacetSum` asks that **all**
classes on the two sides specialising to `l` carry the same total multiplicity.  It follows,
exactly as `FacetParity` does, from the exact census `FacetCensus.MetricCensus` (a bijection of
the two whole fibres at every metric facet limit, `FacetCensus.metricCensus_iff`) and the common
multiplicity at a facet datum (`FacetCommonMultiplicity.commonMult_of_facetDatum`): the coarse
bijection of `FacetCensus.facetParity_of_metric_equiv` preserves `absMult`.

## Contents

* `FacetSum` (definition).
* `facetSum_of_metricCensus` (proved): `MetricCensus` and the common multiplicity give
  `FacetSum`.
* `intLink_of_facetSum` (proved): `FacetSum` at a facet datum gives an integer link between the
  two facet requests.
* `typeChangeSupplySum_of_metricCensus`, `typeChanges` (proved from it): the integer
  `TypeChangeSupplySum`, from the same census supply `CensusAssembly.stepCensus_of_supplies` the
  parity proof uses.  Nothing about the census changes.
-/

namespace DraismaVargas.Count.IntegerCount

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.FacetMachine
open DraismaVargas.Count.FacetCommonMultiplicity
open DraismaVargas.Count.FacetCensus
open DraismaVargas.Count.ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight)

variable {n p degree : ℕ}

/-! ## 1.  The per-limit sum -/

/-- **The per-limit sum at a type-change facet**: at every facet limit, the classes of the two
cores specialising to it carry the same total multiplicity.  The integer twin of
`FacetMachine.FacetParity`. -/
def FacetSum (c c' : Core n p) (degree : ℕ) (y₀ : Fin p → ℚ) : Prop :=
  ∀ l : FacetLimit c c' y₀ degree,
    ∑ᶠ x : {x : FrameClass c degree // SpecializesLeft x l}, x.1.absMult =
      ∑ᶠ x : {x : FrameClass c' degree // SpecializesRight x l}, x.1.absMult

/-- **`MetricCensus` and the common multiplicity give the per-limit sum.**  The coarse bijection
is the one `FacetCensus.facetParity_of_metric_equiv` builds from the metric bijections; the
common multiplicity makes it preserve `absMult`. -/
theorem facetSum_of_metricCensus {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}
    (hd : FacetDatum c c' degree e₀ y₀ ε) (hl' : c'.tail e₀ ≠ c'.head e₀)
    (h : MetricCensus c c' degree y₀) : FacetSum c c' degree y₀ := by
  have hmult := commonMult_of_facetDatum hd hl'
  intro l
  let eT : ∀ m : MetricFacetLimit c c' y₀ degree,
      {x : FrameClass c degree // True ∧ MSpecializesLeft x m} ≃
        {x : FrameClass c' degree // True ∧ MSpecializesRight x m} := fun m ↦
    ((Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨trivial, h⟩⟩).trans
      (metricCensus_iff.mp h m).some).trans
      (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ ⟨trivial, h⟩, fun h ↦ h.2⟩)
  let e : {x : FrameClass c degree // SpecializesLeft x l} ≃
      {x : FrameClass c' degree // SpecializesRight x l} :=
    (trueEquivLeft l).trans ((specializesLeftEquivSigma (fun _ ↦ True) l).trans
      ((Equiv.sigmaCongrRight fun m : {m : MetricFacetLimit c c' y₀ degree // m.toCoarse = l} ↦
        eT m.1).trans
        ((specializesRightEquivSigma (fun _ ↦ True) l).symm.trans (trueEquivRight l).symm)))
  rw [← finsum_comp_equiv e.symm]
  refine finsum_congr fun x ↦ ?_
  exact absMult_eq_of_specializes_of_common hmult (e.symm x).2 x.2

/-! ## 2.  The link -/

/-- **The integer link from the per-limit sum, at one facet datum.**  The integer twin of
`FacetMachine.countLink_of_facetParity`.

At a facet datum the classes open at the facet request are exactly the classes specialising to
some facet limit, each to exactly one (`FacetMachine.exists_specializesLeft`,
`openAt_of_specializesLeft`, `SpecializesLeft.unique`, and the same on the right).  So both
weighted counts, cast to `ℚ` (`openMultCount_cast_eq_frameSum`), are sums over the finitely many
limits hit on either side (`Finset.sum_fiberwise_of_maps_to`) of the two sides of `FacetSum`. -/
theorem intLink_of_facetSum {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}
    (hd : FacetDatum c c' degree e₀ y₀ ε) (h : FacetSum c c' degree y₀) :
    IntLink degree c (facetRequest e₀ y₀ ε) c' (facetRequest e₀ y₀ ε) := by
  classical
  -- the specialisation maps, on all open classes (not only the odd ones)
  let fL : {x : FrameClass c degree // x.OpenAt (facetRequest e₀ y₀ ε)} →
      FacetLimit c c' y₀ degree := fun a ↦
    Classical.choose (exists_specializesLeft (c' := c') hd.point hd.general hd.stable a.1 a.2)
  let fR : {x : FrameClass c' degree // x.OpenAt (facetRequest e₀ y₀ ε)} →
      FacetLimit c c' y₀ degree := fun b ↦
    Classical.choose (exists_specializesRight (c := c) hd.point hd.general' hd.stable' b.1 b.2)
  have hL : ∀ a l, fL a = l ↔ SpecializesLeft a.1 l := fun a l ↦ by
    have hspec : SpecializesLeft a.1 (fL a) := Classical.choose_spec
      (exists_specializesLeft (c' := c') hd.point hd.general hd.stable a.1 a.2)
    exact ⟨fun h ↦ h ▸ hspec, fun h ↦ hspec.unique h⟩
  have hR : ∀ b l, fR b = l ↔ SpecializesRight b.1 l := fun b l ↦ by
    have hspec : SpecializesRight b.1 (fR b) := Classical.choose_spec
      (exists_specializesRight (c := c) hd.point hd.general' hd.stable' b.1 b.2)
    exact ⟨fun h ↦ h ▸ hspec, fun h ↦ hspec.unique h⟩
  -- the fibre of a specialisation map over `l` is the set of classes specialising to `l`
  let eL : ∀ l, {a // fL a = l} ≃ {x : FrameClass c degree // SpecializesLeft x l} := fun l ↦
    { toFun := fun a ↦ ⟨a.1.1, (hL a.1 l).mp a.2⟩
      invFun := fun x ↦ ⟨⟨x.1, openAt_of_specializesLeft hd.point hd.general hd.stable hd.pos
          x.2⟩, (hL _ l).mpr x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let eR : ∀ l, {b // fR b = l} ≃ {x : FrameClass c' degree // SpecializesRight x l} := fun l ↦
    { toFun := fun b ↦ ⟨b.1.1, (hR b.1 l).mp b.2⟩
      invFun := fun x ↦ ⟨⟨x.1, openAt_of_specializesRight hd.point hd.general' hd.stable'
          hd.pos x.2⟩, (hR _ l).mpr x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have _ : Fintype (FrameClass c degree) := Fintype.ofFinite _
  have _ : Fintype (FrameClass c' degree) := Fintype.ofFinite _
  -- the finitely many limits hit on either side
  let T : Finset (FacetLimit c c' y₀ degree) :=
    Finset.univ.image fL ∪ Finset.univ.image fR
  unfold IntLink
  apply Nat.cast_injective (R := ℚ)
  rw [openMultCount_cast_eq_frameSum, openMultCount_cast_eq_frameSum,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := T) (g := fL)
      (fun a _ ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))),
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := T) (g := fR)
      (fun b _ ↦ Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ b)))]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Finset.sum_subtype (p := fun a ↦ fL a = l) _ (fun a ↦ by simp),
    Finset.sum_subtype (p := fun b ↦ fR b = l) _ (fun b ↦ by simp),
    Fintype.sum_equiv (eL l) (fun a ↦ a.1.1.absMult) (fun x ↦ x.1.absMult) (fun _ ↦ rfl),
    Fintype.sum_equiv (eR l) (fun b ↦ b.1.1.absMult) (fun x ↦ x.1.absMult) (fun _ ↦ rfl),
    ← finsum_eq_sum_of_fintype, ← finsum_eq_sum_of_fintype]
  exact h l

/-! ## 3.  The type changes -/

/-- **`TypeChangeSupplySum` from `MetricCensus` at one facet datum per step.**  The integer twin
of `FacetCensus.typeChangeSupplyPositive_of_metricCensus`, with the same hypothesis. -/
theorem typeChangeSupplySum_of_metricCensus
    (h : ∀ c c' : CubicCore n p, Step c c' →
      ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core c'.core degree e₀ y₀ ε ∧
        c'.core.tail e₀ ≠ c'.core.head e₀ ∧ MetricCensus c.core c'.core degree y₀) :
    TypeChangeSupplySum degree n p := by
  intro c c' hstep
  obtain ⟨e₀, y₀, ε, hd, hl', hc⟩ := h c c' hstep
  exact ⟨_, _, hd.positiveGeneral_left, hd.positiveGeneral_right,
    intLink_of_facetSum hd (facetSum_of_metricCensus hd hl' hc)⟩

/-- **The type changes, integer form, in degree and size at least three.**  The integer twin of
`EvenGenusParity.typeChanges`, from the same census supply. -/
theorem typeChanges {degree n p : ℕ} (hDegree : 3 ≤ degree) (hn : 3 ≤ n) :
    TypeChangeSupplySum degree n p :=
  typeChangeSupplySum_of_metricCensus fun _ _ hStep ↦
    CensusAssembly.stepCensus_of_supplies (ValencyTwoPairing.v2ClauseSupply hDegree hn)
      (CensusAssembly.v4ClauseSupply_of_inputs
        (ValencyFourRealisation.v4InputsSupply hDegree hn))
      hDegree hn hStep

end DraismaVargas.Count.IntegerCount
