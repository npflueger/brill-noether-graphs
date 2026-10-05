module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquivFinal

@[expose] public section

/-!
# Injectivity of the retained-row map at a four-valent `K = 0` wall

Source: Vargas, Part II, Section 5.1 (rigidity above `w_0`) and Lemma
`lm:change-comb-type` (the wall matrix as the common minor `A_{\varphi_0}`).

`NonTrivalentValencyFourRowEquivFinal` proves `newSourceEdge_absorbed`,
`rowMap_surjective` and the row equivalence `rowEquiv`, each under the explicit
hypothesis
`hRetInj : Function.Injective (NonTrivalentValencyFourRowDictionary.retainedRow ...)`.
This module discharges that hypothesis.

## What is proved

* **The reverse row map on occurrences (Sections 2--4).**  `rowOfEdge` sends a
  retained occurrence of the candidate to the wall row of the occurrence it
  retains, and a surviving new occurrence to `newRow` of its sheet: the row of
  the unique surviving fine-side occurrence of its fine class when there is
  one, and otherwise the row of the unique surviving retaining-side occurrence
  of its wall block.  `pickWith` is the unique-choice combinator with a fallback
  that makes this well defined without any receipt; on a new occurrence over the
  anchor block -- the bridge -- its value is left unconstrained, which is
  harmless because only the retained branch is used below.

* **The block census (Sections 1 and 5).**  `block_card_le_three`,
  `block_row_eq_of_only_two`, `anchor_endpoint_valency_ne_two` and
  `fine_endpoint_second` are the four counting facts about one wall block:
  a non-anchor block has at most three survivors; two survivors that exhaust a
  block are consecutive in the wall datum; no endpoint above the anchor block
  is divalent; and a fine-side survivor is never alone at its fine endpoint.
  The four configurations of a divalent endpoint are then decided by
  `newRow_eq_ret_of_pair`, `newRow_eq_two_new`, `block_row_eq_two_ret`,
  `block_row_eq_two_fine` and `newRow_eq_fine_of_pair`.  The load-bearing one is
  two retained survivors at a fine endpoint: they are the block's only fine-side
  survivors, so every new occurrence of the block is the dangling one of their
  fine class, and a retaining-side survivor would be alone at the retaining
  endpoint -- impossible at surviving valency one.  Hence the block is divalent
  in the wall datum and the two survivors are already consecutive there.

* **`rowOfEdge_eq_of_consecutive` and `retainedRow_injective'` (Sections 6--7).**
  The source vertices of the candidate are enumerated as in
  `LimitChainCore.SelectedData.rowOfEdge_eq_of_consecutive`: away from the wall both partners
  are retained and the surviving valencies agree, and the two vertices above the
  wall are the endpoint vertices of the crossing.  `Quot.lift rowOfEdge` is then
  `rowDescend`, and `rowDescend_retainedRow` makes it a literal left inverse of
  `retainedRow`, so `retainedRow` is injective.

* **The corollaries at an actual wall (Section 8).**
  `retainedRow_injective_of_single_row`, `rowEquiv_of_single_row`,
  `rowEquiv_of_single_row_retainedRow`, `chartLabelling_of_single_row` and
  `matrix_chartLabelling_eq_incoming_of_single_row` are
  `NonTrivalentValencyFourRowEquivFinal`'s Section 6 statements with `hRetInj`
  discharged by the two censuses `gauged_starInjective_of_single_row` and
  `gauged_valency_of_single_row` supplied there.

## Hypotheses

No hypothesis about the candidate is needed.  In the abstract Section 7 form
the two standing censuses are explicit hypotheses, exactly the ones
`NonTrivalentValencyFourRowEquivFinal.rowEquiv` takes:

* `hInj`: target-direction injectivity `NonDanglingStarInjective` at every
  non-anchor block of the gauged wall datum;
* `hValency`: surviving valency at most three at every non-anchor block of the
  gauged wall datum.

At an actual four-valent wall (Section 8) both are discharged, and the
hypotheses of `retainedRow_injective_of_single_row`,
`rowEquiv_of_single_row`, `chartLabelling_of_single_row` and
`matrix_chartLabelling_eq_incoming_of_single_row` are exactly those of
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row` together
with the wall metric (`hCompat`, `hPosCoord`, `hFacetZero` for the last two).

## Used by

The boundary dispatcher for Part II case `{v4-nd4}` and the
nonsingularity/exit package built on `NonTrivalentLinkMatrix`, whose
`AgreeOffColumn` input is
`matrix_chartLabelling_eq_incoming_of_single_row`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourRetainedInjective

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.NonTrivalentValencyFourBackground
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows
open DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary
open DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquiv
open DraismaVargas.LocalCases.NonTrivalentValencyFourDescent
open DraismaVargas.LocalCases.NonTrivalentValencyFourRowDictionary

/-! ## 0. Unique choice with a fallback -/

noncomputable def pickWith {α β : Type*} (m : α → β) (P Q : α → Prop) :
    Option β := by
  classical
  exact if hP : ∃ a, P a ∧ ∀ b, P b → b = a then some (m hP.choose)
    else if hQ : ∃ a, Q a ∧ ∀ b, Q b → b = a then some (m hQ.choose)
    else none

theorem pickWith_left {α β : Type*} (m : α → β) (P Q : α → Prop) {a : α}
    (ha : P a) (hUnique : ∀ b, P b → b = a) : pickWith m P Q = some (m a) := by
  classical
  have hP : ∃ c, P c ∧ ∀ b, P b → b = c := ⟨a, ha, hUnique⟩
  rw [pickWith, dite_eq_left hP]
  exact congrArg (fun c ↦ some (m c)) (hUnique _ hP.choose_spec.1)

theorem pickWith_right {α β : Type*} (m : α → β) (P Q : α → Prop)
    (hP : ¬ ∃ c, P c ∧ ∀ b, P b → b = c) {a : α}
    (ha : Q a) (hUnique : ∀ b, Q b → b = a) : pickWith m P Q = some (m a) := by
  classical
  have hQ : ∃ c, Q c ∧ ∀ b, Q b → b = c := ⟨a, ha, hUnique⟩
  rw [pickWith, dite_eq_right hP, dite_eq_left hQ]
  exact congrArg (fun c ↦ some (m c)) (hUnique _ hQ.choose_spec.1)


/-- At a surviving valency-two vertex, two distinct incident survivors exhaust
the surviving star. -/
theorem eq_of_pair_at_valency_two {target : CFGraph} {degree : ℕ}
    (datum : GluingDatum target degree) {v : datum.SourceVertex}
    {a b : datum.SourceEdge} (hNe : a ≠ b)
    (haS : ¬ IsDangling datum a) (hbS : ¬ IsDangling datum b)
    (haI : Incident datum a v) (hbI : Incident datum b v)
    (hVal : nonDanglingValency datum v = 2)
    {f : datum.SourceEdge} (hfS : ¬ IsDangling datum f)
    (hfI : Incident datum f v) : f = a ∨ f = b := by
  classical
  have hSub : ({a, b} : Finset datum.SourceEdge) ⊆ nonDanglingIncident datum v := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨haS, haI⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨hbS, hbI⟩
  have hCard : ({a, b} : Finset datum.SourceEdge).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hNe), Finset.card_singleton]
  have hEq := Finset.eq_of_subset_of_card_le hSub
    (by rw [card_nonDanglingIncident, hVal, hCard])
  have hMem : f ∈ ({a, b} : Finset datum.SourceEdge) := by
    rw [hEq]
    exact (mem_nonDanglingIncident _ _ _).mpr ⟨hfS, hfI⟩
  simpa using hMem

/-! ## 1.  The surviving census of one non-anchor wall block -/

section Block

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : WallBlock data wall}
  (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)
  (profile : OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hValid : data.Valid)

local notation "cand" =>
  (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
    hRamification profile hConnected hGenus hValid)
local notation "gauged" => (gaugedData source pairing hNoGlue hRamification)
local notation "coarse" =>
  (GluingDatum.vertexPartition
    (gaugedData source pairing hNoGlue hRamification) wall)
local notation "blockRes" =>
  (W4Assembly.blockwiseResolution
    (gaugedData source pairing hNoGlue hRamification) star profile.pattern
    pairing)

/-- Membership in the surviving star of a wall block, spelled out. -/
theorem mem_block_star_iff (x : Fin degree) (f : (gauged).SourceEdge) :
    f ∈ nonDanglingIncident (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall x)) ↔
      ¬ IsDangling (gauged) f ∧ f.1.1 ∈ GluingDatum.incidentEdges wall ∧
        (coarse).Rel x f.1.2 := by
  rw [mem_nonDanglingIncident, incident_wallBlock_sourceVertex_iff,
    WallBlock.ofSheet_eq_iff_rel]
  constructor
  · rintro ⟨hSurv, hAt, hRel⟩
    exact ⟨hSurv, hAt, ((coarse).rel_repr_right x).trans hRel⟩
  · rintro ⟨hSurv, hAt, hRel⟩
    exact ⟨hSurv, hAt, ((coarse).rel_repr_left x).trans hRel⟩

/-- **At most three survivors at a non-anchor wall block.** -/
theorem block_card_le_three
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    {x : Fin degree} (hb : ¬ (coarse).Rel anchor.1 x)
    (s : Finset (gauged).SourceEdge)
    (hs : ∀ f ∈ s, ¬ IsDangling (gauged) f ∧
      f.1.1 ∈ GluingDatum.incidentEdges wall ∧ (coarse).Rel x f.1.2) :
    s.card ≤ 3 := by
  classical
  have hSub : s ⊆ nonDanglingIncident (gauged)
      (WallBlock.sourceVertex (gauged) wall
        (WallBlock.ofSheet (gauged) wall x)) := by
    intro f hf
    exact (mem_block_star_iff source pairing hNoGlue hRamification x f).mpr
      (hs f hf)
  have hCard := Finset.card_le_card hSub
  rw [card_nonDanglingIncident] at hCard
  exact hCard.trans (hValency x hb)

/-- **Two survivors that exhaust a wall block carry the same wall row.** -/
theorem block_row_eq_of_only_two
    {x : Fin degree}
    {a b : NonDanglingEdge (gauged)} (hNe : a ≠ b)
    (haAt : a.1.1.1 ∈ GluingDatum.incidentEdges wall)
    (haRel : (coarse).Rel x a.1.1.2)
    (hbAt : b.1.1.1 ∈ GluingDatum.incidentEdges wall)
    (hbRel : (coarse).Rel x b.1.1.2)
    (hAll : ∀ z : (gauged).SourceEdge, ¬ IsDangling (gauged) z →
      z.1.1 ∈ GluingDatum.incidentEdges wall → (coarse).Rel x z.1.2 →
      z = a.1 ∨ z = b.1) :
    a.stablePath = b.stablePath := by
  classical
  have hNeVal : a.1 ≠ b.1 := fun h ↦ hNe (Subtype.ext h)
  have hIa : a.1 ∈ nonDanglingIncident (gauged)
      (WallBlock.sourceVertex (gauged) wall
        (WallBlock.ofSheet (gauged) wall x)) :=
    (mem_block_star_iff source pairing hNoGlue hRamification x a.1).mpr
      ⟨a.2, haAt, haRel⟩
  have hIb : b.1 ∈ nonDanglingIncident (gauged)
      (WallBlock.sourceVertex (gauged) wall
        (WallBlock.ofSheet (gauged) wall x)) :=
    (mem_block_star_iff source pairing hNoGlue hRamification x b.1).mpr
      ⟨b.2, hbAt, hbRel⟩
  have hSubset : nonDanglingIncident (gauged)
      (WallBlock.sourceVertex (gauged) wall
        (WallBlock.ofSheet (gauged) wall x)) ⊆ {a.1, b.1} := by
    intro f hf
    obtain ⟨hSurv, hAt, hRel⟩ :=
      (mem_block_star_iff source pairing hNoGlue hRamification x f).mp hf
    rcases hAll f hSurv hAt hRel with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hSupset : ({a.1, b.1} : Finset (gauged).SourceEdge) ⊆
      nonDanglingIncident (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall x)) := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hIa
    · exact hIb
  have hEq := Finset.Subset.antisymm hSubset hSupset
  have hValency2 : nonDanglingValency (gauged)
      (WallBlock.sourceVertex (gauged) wall
        (WallBlock.ofSheet (gauged) wall x)) = 2 := by
    rw [← card_nonDanglingIncident, hEq,
      Finset.card_insert_of_notMem (by simpa using hNeVal), Finset.card_singleton]
  refine stablePath_eq_of_consecutive ⟨hNe, _, ?_, ?_, hValency2⟩
  · exact ((mem_nonDanglingIncident _ _ _).mp hIa).2
  · exact ((mem_nonDanglingIncident _ _ _).mp hIb).2

/-- **No endpoint above the anchor block is divalent.**  On the non-smaller
side the endpoint partition is the whole wall block, so the endpoint is the
anchor's own trivalent endpoint; on the smaller side the sheet is either
`finePartition`-related to the selected representative -- again trivalent -- or
its fine block is a singleton, and then only the bridge survives there. -/
theorem anchor_endpoint_valency_ne_two (sideValue : Bool) {sheet : Fin degree}
    (hAnchor : (coarse).Rel anchor.1 sheet) :
    nonDanglingValency (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid sideValue sheet) ≠ 2 := by
  classical
  intro hTwo
  have hRepRel : (coarse).Rel anchor.1 (selectedRepresentative source pairing) :=
    (gauged_rel_iff source pairing hNoGlue hRamification _ _).mpr
      (source.sheet_wall_rel _)
  by_cases hSide : sideValue = smallerSide source pairing
  · by_cases hFine : (finePartition source pairing hNoGlue hRamification).Rel
        (selectedRepresentative source pairing) sheet
    · have hEq := endpointVertex_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid sideValue hAnchor
        (b := selectedRepresentative source pairing)
        (by rw [hSide, endpointForSide_smaller]; exact hFine.symm)
      rw [hEq, nonDanglingValency_endpointVertex source pairing hNoGlue
        hRamification profile hConnected hGenus hValid sideValue] at hTwo
      omega
    · have hWallData : (data.vertexPartition wall).Rel anchor.1 sheet :=
        (gauged_rel_iff source pairing hNoGlue hRamification _ _).mp hAnchor
      rcases finePartition_rel_or_singleton source pairing hNoGlue hRamification
        sheet hWallData with h | hSingleton
      · exact hFine h
      · have hSub := nonDanglingIncident_singleton_subset source pairing hNoGlue
          hRamification profile hConnected hGenus hValid hAnchor hSingleton hFine
        have hCard := Finset.card_le_card hSub
        rw [card_nonDanglingIncident, Finset.card_singleton, ← hSide, hTwo]
          at hCard
        omega
  · have hSide' : sideValue = !smallerSide source pairing :=
      bool_eq_not_of_ne hSide
    have hEq := endpointVertex_eq source pairing hNoGlue hRamification profile
      hConnected hGenus hValid sideValue hAnchor
      (b := selectedRepresentative source pairing)
      (by rw [hSide', endpointForSide_not_smaller]
          exact hAnchor.symm.trans hRepRel)
    rw [hEq, nonDanglingValency_endpointVertex source pairing hNoGlue
      hRamification profile hConnected hGenus hValid sideValue] at hTwo
    omega

/-- **A fine-side survivor is never alone at its fine endpoint.**  Either the
new occurrence of its fine class survives, or the fine class carries a second
fine-side survivor: a surviving valency of one is impossible. -/
theorem fine_endpoint_second {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x)
    {z : (gauged).SourceEdge} (hzS : ¬ IsDangling (gauged) z)
    (hzAt : z.1.1 ∈ GluingDatum.incidentEdges wall)
    (hzSide : star.right pairing z.1.1 =
      !retSide source pairing hNoGlue hRamification profile ((coarse).repr x))
    (hzRel : (blockRes ((coarse).repr x)).newEdge.Rel x z.1.2) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge x) ∨
      ∃ w : (gauged).SourceEdge, ¬ IsDangling (gauged) w ∧
        w.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing w.1.1 =
          !retSide source pairing hNoGlue hRamification profile
            ((coarse).repr x) ∧
        (blockRes ((coarse).repr x)).newEdge.Rel x w.1.2 ∧ w ≠ z := by
  classical
  have hIncZ : Incident (cand).datum ((cand).oldSourceEdge z)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) x) := by
    have h := retainedEdge_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid z.1.1 hzAt _ hzSide z.1.2
    rw [GluingDatum.sourceEdge_self,
      endpointVertex_fine_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb hzRel] at h
    exact h
  have hSurvZ : ¬ IsDangling (cand).datum ((cand).oldSourceEdge z) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ hzS
  have hMemZ : (cand).oldSourceEdge z ∈
      nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid
          (!retSide source pairing hNoGlue hRamification profile
            ((coarse).repr x)) x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hSurvZ, hIncZ⟩
  have hNeOne := NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    ((cand).datum_valid
      (gaugedData_valid source pairing hNoGlue hRamification hValid)).1
    (endpointVertex source pairing hNoGlue hRamification profile hConnected
      hGenus hValid
      (!retSide source pairing hNoGlue hRamification profile
        ((coarse).repr x)) x)
  have hPos : 0 < (nonDanglingIncident (cand).datum
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) x)).card :=
    Finset.card_pos.mpr ⟨_, hMemZ⟩
  have hGt : 1 < (nonDanglingIncident (cand).datum
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) x)).card := by
    rw [card_nonDanglingIncident] at hPos ⊢
    omega
  obtain ⟨f, hf, hfNe⟩ :=
    Finset.exists_mem_ne hGt ((cand).oldSourceEdge z)
  obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  rcases nonDanglingIncident_fine_cases source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hb hfS hfI with
    hNew | ⟨w, hwS, hwAt, hwSide, hwRel, rfl⟩
  · left
    rw [← hNew]
    exact hfS
  · exact Or.inr ⟨w, hwS, hwAt, hwSide, hwRel,
      fun h ↦ hfNe (congrArg (cand).oldSourceEdge h)⟩

/-! ## 2.  The candidate-to-wall row assignment -/

/-- A surviving occurrence of the wall block of `x`, on the fine side of the
prescribed pairing and in the fine class of `x`. -/
def FineSurvAt (x : Fin degree) (f : NonDanglingEdge (gauged)) : Prop :=
  f.1.1.1 ∈ GluingDatum.incidentEdges wall ∧
    star.right pairing f.1.1.1 =
      !retSide source pairing hNoGlue hRamification profile ((coarse).repr x) ∧
    (blockRes ((coarse).repr x)).newEdge.Rel x f.1.1.2

/-- A surviving occurrence of the wall block of `x` on the retaining side. -/
def RetSurvAt (x : Fin degree) (r : NonDanglingEdge (gauged)) : Prop :=
  r.1.1.1 ∈ GluingDatum.incidentEdges wall ∧
    star.right pairing r.1.1.1 =
      retSide source pairing hNoGlue hRamification profile ((coarse).repr x) ∧
    (coarse).Rel x r.1.1.2

/-- **The wall row a surviving new occurrence is absorbed into**: the row of
the unique fine-side survivor of its fine class when there is one, and
otherwise the row of the unique retaining-side survivor of its block. -/
noncomputable def newRow (x : Fin degree) : Option (StablePath (gauged)) :=
  pickWith NonDanglingEdge.stablePath
    (FineSurvAt source pairing hNoGlue hRamification profile x)
    (RetSurvAt source pairing hNoGlue hRamification profile x)

theorem newRow_fine {x : Fin degree} {f : NonDanglingEdge (gauged)}
    (hf : FineSurvAt source pairing hNoGlue hRamification profile x f)
    (hUnique : ∀ g,
      FineSurvAt source pairing hNoGlue hRamification profile x g → g = f) :
    newRow source pairing hNoGlue hRamification profile x = some f.stablePath :=
  pickWith_left _ _ _ hf hUnique

theorem newRow_ret {x : Fin degree} {r : NonDanglingEdge (gauged)}
    (hNotUnique : ¬ ∃ f,
      FineSurvAt source pairing hNoGlue hRamification profile x f ∧
        ∀ g, FineSurvAt source pairing hNoGlue hRamification profile x g → g = f)
    (hr : RetSurvAt source pairing hNoGlue hRamification profile x r)
    (hUnique : ∀ g,
      RetSurvAt source pairing hNoGlue hRamification profile x g → g = r) :
    newRow source pairing hNoGlue hRamification profile x = some r.stablePath :=
  pickWith_right _ _ _ hNotUnique hr hUnique

/-- The assignment only depends on the fine class. -/
theorem newRow_congr {x y : Fin degree}
    (hRel : (blockRes ((coarse).repr x)).newEdge.Rel x y) :
    newRow source pairing hNoGlue hRamification profile x =
      newRow source pairing hNoGlue hRamification profile y := by
  have hCoarse : (coarse).Rel x y :=
    (blockRes_newEdge_refines source pairing hNoGlue hRamification profile
      ((coarse).repr x)).rel hRel
  have hRepr : (coarse).repr x = (coarse).repr y := hCoarse
  rw [hRepr] at hRel
  have hFine : FineSurvAt source pairing hNoGlue hRamification profile x =
      FineSurvAt source pairing hNoGlue hRamification profile y := by
    funext f
    apply propext
    simp only [FineSurvAt, hRepr]
    exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
      ⟨fun h ↦ hRel.symm.trans h, fun h ↦ hRel.trans h⟩
  have hRet : RetSurvAt source pairing hNoGlue hRamification profile x =
      RetSurvAt source pairing hNoGlue hRamification profile y := by
    funext r
    apply propext
    simp only [RetSurvAt, hRepr]
    exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
      ⟨fun h ↦ hCoarse.symm.trans h, fun h ↦ hCoarse.trans h⟩
  simp only [newRow, hFine, hRet]

/-- **The row assignment on surviving occurrences of the candidate**: a
retained occurrence keeps its wall row, and a new occurrence takes the row of
its absorbing survivor -- `none` exactly for the bridge over the anchor. -/
noncomputable def rowOfEdge (e : NonDanglingEdge (cand).datum) :
    Option (StablePath (gauged)) := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge (gauged),
      ResolutionAwayFromWall.retainedEdge (cand)
          (gaugedData_valid source pairing hNoGlue hRamification hValid).1 old =
        e then
    some (Classical.choose hOld).stablePath
  else newRow source pairing hNoGlue hRamification profile e.1.1.2

@[simp] theorem rowOfEdge_retained (old : NonDanglingEdge (gauged)) :
    rowOfEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid
        (ResolutionAwayFromWall.retainedEdge (cand)
          (gaugedData_valid source pairing hNoGlue hRamification hValid).1
          old) =
      some old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge (gauged),
      ResolutionAwayFromWall.retainedEdge (cand)
          (gaugedData_valid source pairing hNoGlue hRamification hValid).1
          other =
        ResolutionAwayFromWall.retainedEdge (cand)
          (gaugedData_valid source pairing hNoGlue hRamification hValid).1 old :=
    ⟨old, rfl⟩
  rw [rowOfEdge, dite_eq_left hOld]
  exact congrArg (fun c : NonDanglingEdge (gauged) ↦ some c.stablePath)
    (ResolutionAwayFromWall.retainedEdge_injective _ _
      (Classical.choose_spec hOld))

theorem rowOfEdge_newSourceEdge {s : Fin degree}
    (hs : ¬ IsDangling (cand).datum ((cand).newSourceEdge s))
    (hb : ¬ (coarse).Rel anchor.1 s) :
    rowOfEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid ⟨(cand).newSourceEdge s, hs⟩ =
      newRow source pairing hNoGlue hRamification profile s := by
  classical
  have hNot : ¬ ∃ old : NonDanglingEdge (gauged),
      ResolutionAwayFromWall.retainedEdge (cand)
          (gaugedData_valid source pairing hNoGlue hRamification hValid).1 old =
        (⟨(cand).newSourceEdge s, hs⟩ : NonDanglingEdge (cand).datum) := by
    rintro ⟨old, hEq⟩
    exact new_ne_old source pairing hNoGlue hRamification profile hConnected
      hGenus hValid s old.1 (congrArg Subtype.val hEq)
  have hEq : rowOfEdge source pairing hNoGlue hRamification profile hConnected
      hGenus hValid ⟨(cand).newSourceEdge s, hs⟩ =
      newRow source pairing hNoGlue hRamification profile
        ((cand).newSourceEdge s).1.2 := dite_eq_right hNot
  rw [hEq]
  refine (newRow_congr source pairing hNoGlue hRamification profile ?_).symm
  rw [← candidate_newEdge_rel_block source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hb,
    BalancedGlobal.Candidate.newSourceEdge_sheet]
  exact (LocalResolution.paste ((gauged).vertexPartition wall)
    (cand).resolution (cand).contracts).newEdge.rel_repr_right s

/-! ## 3.  Constancy of the row assignment away from the wall -/

/-- Away from the wall both partners are retained and the surviving valency is
the wall datum's. -/
theorem rowOfEdge_eq_away (vertex : (gauged).SourceVertex)
    (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge (cand).datum)
    (hFirst : Incident (cand).datum first.1
      (ResolutionAwayFromWall.retainedVertex (cand) vertex))
    (hSecond : Incident (cand).datum second.1
      (ResolutionAwayFromWall.retainedVertex (cand) vertex))
    (hVal : nonDanglingValency (cand).datum
      (ResolutionAwayFromWall.retainedVertex (cand) vertex) = 2) :
    rowOfEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid first =
      rowOfEdge source pairing hNoGlue hRamification profile hConnected hGenus
        hValid second := by
  classical
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand)
    (gaugedData_valid source pairing hNoGlue hRamification hValid)
    (candidate_sourceGenus source pairing hNoGlue hRamification profile
      hConnected hGenus hValid) first with ⟨a, rfl⟩ | ⟨sa, hsa, rfl⟩
  · rcases ResolutionAwayFromWall.nonDanglingEdge_cases (cand)
      (gaugedData_valid source pairing hNoGlue hRamification hValid)
      (candidate_sourceGenus source pairing hNoGlue hRamification profile
        hConnected hGenus hValid) second with ⟨b, rfl⟩ | ⟨sb, hsb, rfl⟩
    · rw [rowOfEdge_retained, rowOfEdge_retained]
      by_cases hEq : a = b
      · rw [hEq]
      · refine congrArg some (stablePath_eq_of_consecutive ⟨hEq, vertex, ?_, ?_, ?_⟩)
        · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) vertex
            hAway a.1).mp hFirst
        · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff (cand) vertex
            hAway b.1).mp hSecond
        · exact (ResolutionAwayFromWall.nonDanglingValency_retainedVertex (cand)
            (gaugedData_valid source pairing hNoGlue hRamification hValid)
            (candidate_sourceGenus source pairing hNoGlue hRamification profile
              hConnected hGenus hValid) vertex hAway).symm.trans hVal
    · exact absurd hSecond (ResolutionAwayFromWall.not_incident_newSourceEdge
        (cand) vertex hAway sb)
  · exact absurd hFirst (ResolutionAwayFromWall.not_incident_newSourceEdge
      (cand) vertex hAway sa)

/-! ## 4.  Abbreviations and the elementary incidences at a wall endpoint -/

local notation "epv" =>
  (endpointVertex source pairing hNoGlue hRamification profile hConnected hGenus
    hValid)
local notation "rside" => (retSide source pairing hNoGlue hRamification profile)
local notation "rowe" =>
  (rowOfEdge source pairing hNoGlue hRamification profile hConnected hGenus
    hValid)
local notation "nrow" => (newRow source pairing hNoGlue hRamification profile)

/-- Two occurrences of one wall block assigned to opposite sides differ. -/
theorem side_ne {u v : (gauged).SourceEdge} {s : Bool}
    (hu : star.right pairing u.1.1 = s)
    (hv : star.right pairing v.1.1 = !s) : u ≠ v := by
  intro h
  rw [h, hv] at hu
  simp at hu

/-- A surviving occurrence of the gauged wall datum survives in the
candidate. -/
theorem old_survives {old : (gauged).SourceEdge}
    (hData : ¬ IsDangling (gauged) old) :
    ¬ IsDangling (cand).datum ((cand).oldSourceEdge old) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _
    (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ hData

/-- The row assignment on a retained occurrence, in `oldSourceEdge` form. -/
theorem rowOfEdge_old {old : (gauged).SourceEdge}
    (hSurvives : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old))
    (hData : ¬ IsDangling (gauged) old) :
    rowe ⟨(cand).oldSourceEdge old, hSurvives⟩ =
      some (NonDanglingEdge.stablePath
        (⟨old, hData⟩ : NonDanglingEdge (gauged))) :=
  rowOfEdge_retained source pairing hNoGlue hRamification profile hConnected
    hGenus hValid ⟨old, hData⟩

/-- The row assignment on a surviving occurrence that is a retained one. -/
theorem rowOfEdge_of_old_eq {e : NonDanglingEdge (cand).datum}
    {old : (gauged).SourceEdge} (hOldS : ¬ IsDangling (gauged) old)
    (hEq : e.1 = (cand).oldSourceEdge old) :
    rowe e =
      some (NonDanglingEdge.stablePath
        (⟨old, hOldS⟩ : NonDanglingEdge (gauged))) := by
  have hSurv : ¬ IsDangling (cand).datum ((cand).oldSourceEdge old) :=
    old_survives source pairing hNoGlue hRamification profile hConnected hGenus
      hValid hOldS
  refine Eq.trans (congrArg (rowe)
    (Subtype.ext hEq : e = (⟨(cand).oldSourceEdge old, hSurv⟩ :
      NonDanglingEdge (cand).datum))) ?_
  exact rowOfEdge_old source pairing hNoGlue hRamification profile hConnected
    hGenus hValid hSurv hOldS

/-- The row assignment on a surviving occurrence that is a new one. -/
theorem rowOfEdge_of_new_eq {e : NonDanglingEdge (cand).datum} {s : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 s) (hEq : e.1 = (cand).newSourceEdge s) :
    rowe e = nrow s := by
  have hSurv : ¬ IsDangling (cand).datum ((cand).newSourceEdge s) := by
    rw [← hEq]
    exact e.2
  refine Eq.trans (congrArg (rowe)
    (Subtype.ext hEq : e = (⟨(cand).newSourceEdge s, hSurv⟩ :
      NonDanglingEdge (cand).datum))) ?_
  exact rowOfEdge_newSourceEdge source pairing hNoGlue hRamification profile
    hConnected hGenus hValid hSurv hb

/-- A retaining-side survivor of a non-anchor block meets the retaining
endpoint of its block. -/
theorem incident_ret_endpoint {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) {r : (gauged).SourceEdge}
    (hrAt : r.1.1 ∈ GluingDatum.incidentEdges wall)
    (hrSide : star.right pairing r.1.1 = rside ((coarse).repr x))
    (hrRel : (coarse).Rel x r.1.2) :
    Incident (cand).datum ((cand).oldSourceEdge r)
      (epv (rside ((coarse).repr x)) x) := by
  have h := retainedEdge_incident source pairing hNoGlue hRamification profile
    hConnected hGenus hValid r.1.1 hrAt _ hrSide r.1.2
  rw [GluingDatum.sourceEdge_self,
    endpointVertex_ret_eq source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hb hrRel] at h
  exact h

/-- A fine-side survivor in the fine class of a non-anchor block meets the fine
endpoint of that class. -/
theorem incident_fine_endpoint {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) {w : (gauged).SourceEdge}
    (hwAt : w.1.1 ∈ GluingDatum.incidentEdges wall)
    (hwSide : star.right pairing w.1.1 = !rside ((coarse).repr x))
    (hwRel : (blockRes ((coarse).repr x)).newEdge.Rel x w.1.2) :
    Incident (cand).datum ((cand).oldSourceEdge w)
      (epv (!rside ((coarse).repr x)) x) := by
  have h := retainedEdge_incident source pairing hNoGlue hRamification profile
    hConnected hGenus hValid w.1.1 hwAt _ hwSide w.1.2
  rw [GluingDatum.sourceEdge_self,
    endpointVertex_fine_eq source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hb hwRel] at h
  exact h

/-- The new occurrence of a sheet of a non-anchor block meets the retaining
endpoint of that block. -/
theorem incident_new_ret_endpoint {x y : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) (hRel : (coarse).Rel x y) :
    Incident (cand).datum ((cand).newSourceEdge y)
      (epv (rside ((coarse).repr x)) x) := by
  have h := bridgeEdge_incident source pairing hNoGlue hRamification profile
    hConnected hGenus hValid (rside ((coarse).repr x)) y
  rw [endpointVertex_ret_eq source pairing hNoGlue hRamification profile
    hConnected hGenus hValid hb hRel] at h
  exact h

/-- Sheets of one fine class of a non-anchor block carry the same new
occurrence. -/
theorem newSourceEdge_fine_eq {x y : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x)
    (hRel : (blockRes ((coarse).repr x)).newEdge.Rel x y) :
    (cand).newSourceEdge y = (cand).newSourceEdge x :=
  (newSourceEdge_eq_of_rel source pairing hNoGlue hRamification profile
    hConnected hGenus hValid
    ((candidate_newEdge_rel_block source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hb y).mpr hRel)).symm

/-- The fine partition of a non-anchor block refines the wall partition. -/
theorem coarse_of_fine {x y : Fin degree}
    (hRel : (blockRes ((coarse).repr x)).newEdge.Rel x y) : (coarse).Rel x y :=
  (blockRes_newEdge_refines source pairing hNoGlue hRamification profile
    ((coarse).repr x)).rel hRel

/-- The retaining endpoint of a non-anchor block does not depend on which sheet
of the block names it. -/
theorem ret_endpoint_eq {x y : Fin degree} (hb : ¬ (coarse).Rel anchor.1 x)
    (hRel : (coarse).Rel x y) :
    epv (rside ((coarse).repr y)) y = epv (rside ((coarse).repr x)) x := by
  have hRepr : (coarse).repr y = (coarse).repr x := hRel.symm
  rw [hRepr]
  exact endpointVertex_ret_eq source pairing hNoGlue hRamification profile
    hConnected hGenus hValid hb hRel

/-! ## 5.  The census of a non-anchor wall block at a divalent endpoint -/

/-- **A new occurrence sharing its retaining endpoint with one retained
survivor.**  If the retaining endpoint of the non-anchor block of `y` carries
exactly the retained occurrence of `r` and the new occurrence of `y`, then the
new occurrence is absorbed into `r`'s wall row.  Either `y`'s fine class carries
a second fine-side survivor -- and then `r` is the block's unique retaining-side
survivor -- or `z` is alone there and `z` and `r` exhaust the block. -/
theorem newRow_eq_ret_of_pair
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    {y : Fin degree} (hb : ¬ (coarse).Rel anchor.1 y)
    {r z : (gauged).SourceEdge} (hrS : ¬ IsDangling (gauged) r)
    (hrAt : r.1.1 ∈ GluingDatum.incidentEdges wall)
    (hrSide : star.right pairing r.1.1 = rside ((coarse).repr y))
    (hrRel : (coarse).Rel y r.1.2)
    (hzS : ¬ IsDangling (gauged) z)
    (hzAt : z.1.1 ∈ GluingDatum.incidentEdges wall)
    (hzSide : star.right pairing z.1.1 = !rside ((coarse).repr y))
    (hzRel : (blockRes ((coarse).repr y)).newEdge.Rel y z.1.2)
    (hPair : ∀ g : (cand).datum.SourceEdge, ¬ IsDangling (cand).datum g →
      Incident (cand).datum g (epv (rside ((coarse).repr y)) y) →
      g = (cand).oldSourceEdge r ∨ g = (cand).newSourceEdge y) :
    nrow y =
      some (NonDanglingEdge.stablePath
        (⟨r, hrS⟩ : NonDanglingEdge (gauged))) := by
  classical
  have hRetUnique : ∀ u : (gauged).SourceEdge, ¬ IsDangling (gauged) u →
      u.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing u.1.1 = rside ((coarse).repr y) →
      (coarse).Rel y u.1.2 → u = r := by
    intro u huS huAt huSide huRel
    rcases hPair ((cand).oldSourceEdge u)
      (old_survives source pairing hNoGlue hRamification profile hConnected
        hGenus hValid huS)
      (incident_ret_endpoint source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb huAt huSide huRel) with h | h
    · exact ResolutionCut.oldSourceEdge_injective (cand) h
    · exact absurd h (new_ne_old source pairing hNoGlue hRamification profile
        hConnected hGenus hValid y u)
  by_cases hUniqFine : ∀ u : (gauged).SourceEdge, ¬ IsDangling (gauged) u →
      u.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing u.1.1 = !rside ((coarse).repr y) →
      (blockRes ((coarse).repr y)).newEdge.Rel y u.1.2 → u = z
  · have hRow : nrow y =
        some (NonDanglingEdge.stablePath
          (⟨z, hzS⟩ : NonDanglingEdge (gauged))) := by
      refine newRow_fine source pairing hNoGlue hRamification profile
        ⟨hzAt, hzSide, hzRel⟩ ?_
      intro g hg
      obtain ⟨hgAt, hgSide, hgRel⟩ := hg
      exact Subtype.ext (hUniqFine g.1 g.2 hgAt hgSide hgRel)
    rw [hRow]
    refine congrArg some (block_row_eq_of_only_two source pairing hNoGlue
      hRamification (a := (⟨z, hzS⟩ : NonDanglingEdge (gauged)))
      (b := (⟨r, hrS⟩ : NonDanglingEdge (gauged)))
      (fun h ↦ side_ne source pairing hNoGlue hRamification hrSide hzSide
        (congrArg Subtype.val h).symm)
      hzAt
      (coarse_of_fine source pairing hNoGlue hRamification profile hzRel)
      hrAt hrRel ?_)
    intro u huS huAt huRel
    by_cases huSide : star.right pairing u.1.1 = rside ((coarse).repr y)
    · exact Or.inr (hRetUnique u huS huAt huSide huRel)
    · have huSide' : star.right pairing u.1.1 = !rside ((coarse).repr y) :=
        bool_eq_not_of_ne huSide
      by_cases huFine : (blockRes ((coarse).repr y)).newEdge.Rel y u.1.2
      · exact Or.inl (hUniqFine u huS huAt huSide' huFine)
      · exfalso
        have hbU : ¬ (coarse).Rel anchor.1 u.1.2 := fun h ↦ hb (h.trans huRel.symm)
        have hReprU : (coarse).repr u.1.2 = (coarse).repr y := huRel.symm
        by_cases hNewU : IsDangling (cand).datum ((cand).newSourceEdge u.1.2)
        · rcases fine_endpoint_second source pairing hNoGlue hRamification
            profile hConnected hGenus hValid hbU huS huAt
            (by rw [hReprU]; exact huSide') rfl with
            hSurv | ⟨u', hu'S, hu'At, hu'Side, hu'Rel, hu'Ne⟩
          · exact hSurv hNewU
          · have hu'Coarse : (coarse).Rel y u'.1.2 :=
              huRel.trans (coarse_of_fine source pairing hNoGlue hRamification
                profile hu'Rel)
            rw [hReprU] at hu'Side hu'Rel
            have hzr : z ≠ r :=
              Ne.symm (side_ne source pairing hNoGlue hRamification hrSide hzSide)
            have hzu : z ≠ u := fun h ↦ huFine (h ▸ hzRel)
            have hzu' : z ≠ u' := by
              intro h
              exact huFine (hzRel.trans (by rw [h]; exact hu'Rel.symm))
            have hru : r ≠ u :=
              side_ne source pairing hNoGlue hRamification hrSide huSide'
            have hru' : r ≠ u' :=
              side_ne source pairing hNoGlue hRamification hrSide hu'Side
            have huu' : u ≠ u' := Ne.symm hu'Ne
            have hMem : ∀ g ∈ ({z, r, u, u'} : Finset (gauged).SourceEdge),
                ¬ IsDangling (gauged) g ∧
                  g.1.1 ∈ GluingDatum.incidentEdges wall ∧
                  (coarse).Rel y g.1.2 := by
              intro g hg
              simp only [Finset.mem_insert, Finset.mem_singleton] at hg
              rcases hg with rfl | rfl | rfl | rfl
              · exact ⟨hzS, hzAt, coarse_of_fine source pairing hNoGlue
                  hRamification profile hzRel⟩
              · exact ⟨hrS, hrAt, hrRel⟩
              · exact ⟨huS, huAt, huRel⟩
              · exact ⟨hu'S, hu'At, hu'Coarse⟩
            have hCard := block_card_le_three source pairing hNoGlue hRamification
              hValency hb ({z, r, u, u'} : Finset (gauged).SourceEdge) hMem
            rw [Finset.card_insert_of_notMem (by simp [hzr, hzu, hzu']),
              Finset.card_insert_of_notMem (by simp [hru, hru']),
              Finset.card_insert_of_notMem (by simp [huu']),
              Finset.card_singleton] at hCard
            omega
        · rcases hPair ((cand).newSourceEdge u.1.2) hNewU
            (incident_new_ret_endpoint source pairing hNoGlue hRamification
              profile hConnected hGenus hValid hb huRel) with h | h
          · exact new_ne_old source pairing hNoGlue hRamification profile
              hConnected hGenus hValid u.1.2 r h.symm
          · exact huFine ((candidate_newEdge_rel_block source pairing hNoGlue
              hRamification profile hConnected hGenus hValid hb u.1.2).mp
              (newSourceEdge_rel_of_eq source pairing hNoGlue hRamification
                profile hConnected hGenus hValid h.symm))
  · push Not at hUniqFine
    obtain ⟨z', hz'S, hz'At, hz'Side, hz'Rel, hz'Ne⟩ := hUniqFine
    refine newRow_ret source pairing hNoGlue hRamification profile ?_
      ⟨hrAt, hrSide, hrRel⟩ ?_
    · rintro ⟨c, -, hUniq⟩
      apply hz'Ne
      have h₁ := hUniq ⟨z', hz'S⟩ ⟨hz'At, hz'Side, hz'Rel⟩
      have h₂ := hUniq ⟨z, hzS⟩ ⟨hzAt, hzSide, hzRel⟩
      exact congrArg (fun w : NonDanglingEdge (gauged) ↦ w.1) (h₁.trans h₂.symm)
    · intro g hg
      obtain ⟨hgAt, hgSide, hgRel⟩ := hg
      exact Subtype.ext (hRetUnique g.1 g.2 hgAt hgSide hgRel)

/-- **Two surviving new occurrences at one retaining endpoint.**  They pin down
the two fine-side survivors of the block, which are then its only survivors, and
each is alone in its own fine class. -/
theorem newRow_eq_two_new
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    {x : Fin degree} (hb : ¬ (coarse).Rel anchor.1 x)
    {z₁ z₂ : (gauged).SourceEdge} (hz₁S : ¬ IsDangling (gauged) z₁)
    (hz₁At : z₁.1.1 ∈ GluingDatum.incidentEdges wall)
    (hz₁Side : star.right pairing z₁.1.1 = !rside ((coarse).repr x))
    (hz₁Rel : (coarse).Rel x z₁.1.2)
    (hz₂S : ¬ IsDangling (gauged) z₂)
    (hz₂At : z₂.1.1 ∈ GluingDatum.incidentEdges wall)
    (hz₂Side : star.right pairing z₂.1.1 = !rside ((coarse).repr x))
    (hz₂Rel : (coarse).Rel x z₂.1.2)
    (hNeNew : (cand).newSourceEdge z₁.1.2 ≠ (cand).newSourceEdge z₂.1.2)
    (hPair : ∀ g : (cand).datum.SourceEdge, ¬ IsDangling (cand).datum g →
      Incident (cand).datum g (epv (rside ((coarse).repr x)) x) →
      g = (cand).newSourceEdge z₁.1.2 ∨ g = (cand).newSourceEdge z₂.1.2) :
    nrow z₁.1.2 = nrow z₂.1.2 := by
  classical
  have hNe : z₁ ≠ z₂ := fun h ↦ hNeNew
    (congrArg (fun u : (gauged).SourceEdge ↦ (cand).newSourceEdge u.1.2) h)
  have hNoRet : ∀ u : (gauged).SourceEdge, ¬ IsDangling (gauged) u →
      u.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing u.1.1 = rside ((coarse).repr x) →
      (coarse).Rel x u.1.2 → False := by
    intro u huS huAt huSide huRel
    rcases hPair ((cand).oldSourceEdge u)
      (old_survives source pairing hNoGlue hRamification profile hConnected
        hGenus hValid huS)
      (incident_ret_endpoint source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb huAt huSide huRel) with h | h
    · exact new_ne_old source pairing hNoGlue hRamification profile hConnected
        hGenus hValid z₁.1.2 u h
    · exact new_ne_old source pairing hNoGlue hRamification profile hConnected
        hGenus hValid z₂.1.2 u h
  have hAll : ∀ u : (gauged).SourceEdge, ¬ IsDangling (gauged) u →
      u.1.1 ∈ GluingDatum.incidentEdges wall → (coarse).Rel x u.1.2 →
      u = z₁ ∨ u = z₂ := by
    intro u huS huAt huRel
    by_cases huSide : star.right pairing u.1.1 = rside ((coarse).repr x)
    · exact (hNoRet u huS huAt huSide huRel).elim
    · have huSide' : star.right pairing u.1.1 = !rside ((coarse).repr x) :=
        bool_eq_not_of_ne huSide
      rcases NonTrivalentValencyFourRowEquivFinal.eq_of_three_on_side source
        pairing hNoGlue hRamification (hInj x hb) z₁ z₂ u hz₁S hz₂S huS hz₁At
        hz₂At huAt hz₁Rel hz₂Rel huRel hz₁Side hz₂Side huSide' with h | h | h
      · exact absurd h hNe
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  have hRowEq : NonDanglingEdge.stablePath
        (⟨z₁, hz₁S⟩ : NonDanglingEdge (gauged)) =
      NonDanglingEdge.stablePath (⟨z₂, hz₂S⟩ : NonDanglingEdge (gauged)) :=
    block_row_eq_of_only_two source pairing hNoGlue hRamification
      (a := (⟨z₁, hz₁S⟩ : NonDanglingEdge (gauged)))
      (b := (⟨z₂, hz₂S⟩ : NonDanglingEdge (gauged)))
      (fun h ↦ hNe (congrArg (fun w : NonDanglingEdge (gauged) ↦ w.1) h))
      hz₁At hz₁Rel hz₂At hz₂Rel hAll
  have hb₁ : ¬ (coarse).Rel anchor.1 z₁.1.2 := fun h ↦ hb (h.trans hz₁Rel.symm)
  have hb₂ : ¬ (coarse).Rel anchor.1 z₂.1.2 := fun h ↦ hb (h.trans hz₂Rel.symm)
  have hRepr₁ : (coarse).repr z₁.1.2 = (coarse).repr x := hz₁Rel.symm
  have hRepr₂ : (coarse).repr z₂.1.2 = (coarse).repr x := hz₂Rel.symm
  have hRow₁ : nrow z₁.1.2 =
      some (NonDanglingEdge.stablePath
        (⟨z₁, hz₁S⟩ : NonDanglingEdge (gauged))) := by
    refine newRow_fine source pairing hNoGlue hRamification profile
      ⟨hz₁At, by rw [hRepr₁]; exact hz₁Side, rfl⟩ ?_
    intro g hg
    obtain ⟨hgAt, -, hgRel⟩ := hg
    have hgCoarse : (coarse).Rel x g.1.1.2 :=
      hz₁Rel.trans (coarse_of_fine source pairing hNoGlue hRamification profile
        hgRel)
    rcases hAll g.1 g.2 hgAt hgCoarse with h | h
    · exact Subtype.ext h
    · exact absurd (newSourceEdge_fine_eq source pairing hNoGlue hRamification
        profile hConnected hGenus hValid hb₁ (by rw [← h]; exact hgRel)).symm
        hNeNew
  have hRow₂ : nrow z₂.1.2 =
      some (NonDanglingEdge.stablePath
        (⟨z₂, hz₂S⟩ : NonDanglingEdge (gauged))) := by
    refine newRow_fine source pairing hNoGlue hRamification profile
      ⟨hz₂At, by rw [hRepr₂]; exact hz₂Side, rfl⟩ ?_
    intro g hg
    obtain ⟨hgAt, -, hgRel⟩ := hg
    have hgCoarse : (coarse).Rel x g.1.1.2 :=
      hz₂Rel.trans (coarse_of_fine source pairing hNoGlue hRamification profile
        hgRel)
    rcases hAll g.1 g.2 hgAt hgCoarse with h | h
    · exact absurd (newSourceEdge_fine_eq source pairing hNoGlue hRamification
        profile hConnected hGenus hValid hb₂ (by rw [← h]; exact hgRel))
        hNeNew
    · exact Subtype.ext h
  rw [hRow₁, hRow₂, hRowEq]

/-- **Two retained survivors at one retaining endpoint.**  They are then the
block's only survivors: a fine-side survivor would be alone in its fine class,
so its new occurrence would survive and sit at the same endpoint. -/
theorem block_row_eq_two_ret
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    {x : Fin degree} (hb : ¬ (coarse).Rel anchor.1 x)
    {r₁ r₂ : (gauged).SourceEdge} (hr₁S : ¬ IsDangling (gauged) r₁)
    (hr₁At : r₁.1.1 ∈ GluingDatum.incidentEdges wall)
    (hr₁Side : star.right pairing r₁.1.1 = rside ((coarse).repr x))
    (hr₁Rel : (coarse).Rel x r₁.1.2)
    (hr₂S : ¬ IsDangling (gauged) r₂)
    (hr₂At : r₂.1.1 ∈ GluingDatum.incidentEdges wall)
    (hr₂Side : star.right pairing r₂.1.1 = rside ((coarse).repr x))
    (hr₂Rel : (coarse).Rel x r₂.1.2) (hNe : r₁ ≠ r₂)
    (hPair : ∀ g : (cand).datum.SourceEdge, ¬ IsDangling (cand).datum g →
      Incident (cand).datum g (epv (rside ((coarse).repr x)) x) →
      g = (cand).oldSourceEdge r₁ ∨ g = (cand).oldSourceEdge r₂) :
    NonDanglingEdge.stablePath (⟨r₁, hr₁S⟩ : NonDanglingEdge (gauged)) =
      NonDanglingEdge.stablePath (⟨r₂, hr₂S⟩ : NonDanglingEdge (gauged)) := by
  classical
  refine block_row_eq_of_only_two source pairing hNoGlue hRamification
    (a := (⟨r₁, hr₁S⟩ : NonDanglingEdge (gauged)))
    (b := (⟨r₂, hr₂S⟩ : NonDanglingEdge (gauged)))
    (fun h ↦ hNe (congrArg (fun w : NonDanglingEdge (gauged) ↦ w.1) h))
    hr₁At hr₁Rel hr₂At hr₂Rel ?_
  intro u huS huAt huRel
  by_cases huSide : star.right pairing u.1.1 = rside ((coarse).repr x)
  · rcases hPair ((cand).oldSourceEdge u)
      (old_survives source pairing hNoGlue hRamification profile hConnected
        hGenus hValid huS)
      (incident_ret_endpoint source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb huAt huSide huRel) with h | h
    · exact Or.inl (ResolutionCut.oldSourceEdge_injective (cand) h)
    · exact Or.inr (ResolutionCut.oldSourceEdge_injective (cand) h)
  · exfalso
    have huSide' : star.right pairing u.1.1 = !rside ((coarse).repr x) :=
      bool_eq_not_of_ne huSide
    have hbU : ¬ (coarse).Rel anchor.1 u.1.2 := fun h ↦ hb (h.trans huRel.symm)
    have hReprU : (coarse).repr u.1.2 = (coarse).repr x := huRel.symm
    have hUniq : ∀ u' : (gauged).SourceEdge, ¬ IsDangling (gauged) u' →
        u'.1.1 ∈ GluingDatum.incidentEdges wall →
        star.right pairing u'.1.1 = !rside ((coarse).repr u.1.2) →
        (blockRes ((coarse).repr u.1.2)).newEdge.Rel u.1.2 u'.1.2 → u' = u := by
      intro u' hu'S hu'At hu'Side hu'Rel
      by_contra hu'Ne
      have hu'Coarse : (coarse).Rel x u'.1.2 :=
        huRel.trans (coarse_of_fine source pairing hNoGlue hRamification profile
          hu'Rel)
      rw [hReprU] at hu'Side
      have hr₁u : r₁ ≠ u :=
        side_ne source pairing hNoGlue hRamification hr₁Side huSide'
      have hr₁u' : r₁ ≠ u' :=
        side_ne source pairing hNoGlue hRamification hr₁Side hu'Side
      have hr₂u : r₂ ≠ u :=
        side_ne source pairing hNoGlue hRamification hr₂Side huSide'
      have hr₂u' : r₂ ≠ u' :=
        side_ne source pairing hNoGlue hRamification hr₂Side hu'Side
      have huu' : u ≠ u' := fun h ↦ hu'Ne h.symm
      have hMem : ∀ g ∈ ({r₁, r₂, u, u'} : Finset (gauged).SourceEdge),
          ¬ IsDangling (gauged) g ∧
            g.1.1 ∈ GluingDatum.incidentEdges wall ∧ (coarse).Rel x g.1.2 := by
        intro g hg
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact ⟨hr₁S, hr₁At, hr₁Rel⟩
        · exact ⟨hr₂S, hr₂At, hr₂Rel⟩
        · exact ⟨huS, huAt, huRel⟩
        · exact ⟨hu'S, hu'At, hu'Coarse⟩
      have hCard := block_card_le_three source pairing hNoGlue hRamification
        hValency hb ({r₁, r₂, u, u'} : Finset (gauged).SourceEdge) hMem
      rw [Finset.card_insert_of_notMem (by simp [hNe, hr₁u, hr₁u']),
        Finset.card_insert_of_notMem (by simp [hr₂u, hr₂u']),
        Finset.card_insert_of_notMem (by simp [huu']),
        Finset.card_singleton] at hCard
      omega
    have hNewSurv := (newSourceEdge_survives_of_unique_fine_survivor source
      pairing hNoGlue hRamification profile hConnected hGenus hValid hbU huS
      huAt (by rw [hReprU]; exact huSide') rfl hUniq).1
    rcases hPair ((cand).newSourceEdge u.1.2) hNewSurv
      (incident_new_ret_endpoint source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb huRel) with h | h
    · exact new_ne_old source pairing hNoGlue hRamification profile hConnected
        hGenus hValid u.1.2 r₁ h.symm
    · exact new_ne_old source pairing hNoGlue hRamification profile hConnected
        hGenus hValid u.1.2 r₂ h.symm

/-- **Two retained survivors at one fine endpoint.**  This is the load-bearing
sub-case.  They are the block's only fine-side survivors, so every new
occurrence of the block is the dangling one of their fine class; a
retaining-side survivor would then be alone at the retaining endpoint, which is
impossible.  Hence the block is divalent and the two are consecutive in the
wall datum. -/
theorem block_row_eq_two_fine
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    {x : Fin degree} (hb : ¬ (coarse).Rel anchor.1 x)
    {w₁ w₂ : (gauged).SourceEdge} (hw₁S : ¬ IsDangling (gauged) w₁)
    (hw₁At : w₁.1.1 ∈ GluingDatum.incidentEdges wall)
    (hw₁Side : star.right pairing w₁.1.1 = !rside ((coarse).repr x))
    (hw₁Rel : (blockRes ((coarse).repr x)).newEdge.Rel x w₁.1.2)
    (hw₂S : ¬ IsDangling (gauged) w₂)
    (hw₂At : w₂.1.1 ∈ GluingDatum.incidentEdges wall)
    (hw₂Side : star.right pairing w₂.1.1 = !rside ((coarse).repr x))
    (hw₂Rel : (blockRes ((coarse).repr x)).newEdge.Rel x w₂.1.2) (hNe : w₁ ≠ w₂)
    (hPair : ∀ g : (cand).datum.SourceEdge, ¬ IsDangling (cand).datum g →
      Incident (cand).datum g (epv (!rside ((coarse).repr x)) x) →
      g = (cand).oldSourceEdge w₁ ∨ g = (cand).oldSourceEdge w₂) :
    NonDanglingEdge.stablePath (⟨w₁, hw₁S⟩ : NonDanglingEdge (gauged)) =
      NonDanglingEdge.stablePath (⟨w₂, hw₂S⟩ : NonDanglingEdge (gauged)) := by
  classical
  have hw₁Coarse : (coarse).Rel x w₁.1.2 :=
    coarse_of_fine source pairing hNoGlue hRamification profile hw₁Rel
  have hw₂Coarse : (coarse).Rel x w₂.1.2 :=
    coarse_of_fine source pairing hNoGlue hRamification profile hw₂Rel
  have hNewDangling : IsDangling (cand).datum ((cand).newSourceEdge x) := by
    by_contra hSurv
    rcases hPair ((cand).newSourceEdge x) hSurv
      (bridgeEdge_incident source pairing hNoGlue hRamification profile
        hConnected hGenus hValid (!rside ((coarse).repr x)) x) with h | h
    · exact new_ne_old source pairing hNoGlue hRamification profile hConnected
        hGenus hValid x w₁ h.symm
    · exact new_ne_old source pairing hNoGlue hRamification profile hConnected
        hGenus hValid x w₂ h.symm
  have hFineAll : ∀ u : (gauged).SourceEdge, ¬ IsDangling (gauged) u →
      u.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing u.1.1 = !rside ((coarse).repr x) →
      (coarse).Rel x u.1.2 → u = w₁ ∨ u = w₂ := by
    intro u huS huAt huSide huRel
    rcases NonTrivalentValencyFourRowEquivFinal.eq_of_three_on_side source
      pairing hNoGlue hRamification (hInj x hb) w₁ w₂ u hw₁S hw₂S huS hw₁At
      hw₂At huAt hw₁Coarse hw₂Coarse huRel hw₁Side hw₂Side huSide with h | h | h
    · exact absurd h hNe
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  refine block_row_eq_of_only_two source pairing hNoGlue hRamification
    (a := (⟨w₁, hw₁S⟩ : NonDanglingEdge (gauged)))
    (b := (⟨w₂, hw₂S⟩ : NonDanglingEdge (gauged)))
    (fun h ↦ hNe (congrArg (fun v : NonDanglingEdge (gauged) ↦ v.1) h))
    hw₁At hw₁Coarse hw₂At hw₂Coarse ?_
  intro u huS huAt huRel
  by_cases huSide : star.right pairing u.1.1 = !rside ((coarse).repr x)
  · exact hFineAll u huS huAt huSide huRel
  · exfalso
    have huSide' : star.right pairing u.1.1 = rside ((coarse).repr x) := by
      have hNot := bool_eq_not_of_ne huSide
      simpa using hNot
    have hRetUniq : ∀ u' : (gauged).SourceEdge, ¬ IsDangling (gauged) u' →
        u'.1.1 ∈ GluingDatum.incidentEdges wall →
        star.right pairing u'.1.1 = rside ((coarse).repr x) →
        (coarse).Rel x u'.1.2 → u' = u := by
      intro u' hu'S hu'At hu'Side hu'Rel
      by_contra hu'Ne
      have hw₁u : w₁ ≠ u :=
        Ne.symm (side_ne source pairing hNoGlue hRamification huSide' hw₁Side)
      have hw₁u' : w₁ ≠ u' :=
        Ne.symm (side_ne source pairing hNoGlue hRamification hu'Side hw₁Side)
      have hw₂u : w₂ ≠ u :=
        Ne.symm (side_ne source pairing hNoGlue hRamification huSide' hw₂Side)
      have hw₂u' : w₂ ≠ u' :=
        Ne.symm (side_ne source pairing hNoGlue hRamification hu'Side hw₂Side)
      have huu' : u ≠ u' := fun h ↦ hu'Ne h.symm
      have hMem : ∀ g ∈ ({w₁, w₂, u, u'} : Finset (gauged).SourceEdge),
          ¬ IsDangling (gauged) g ∧
            g.1.1 ∈ GluingDatum.incidentEdges wall ∧ (coarse).Rel x g.1.2 := by
        intro g hg
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact ⟨hw₁S, hw₁At, hw₁Coarse⟩
        · exact ⟨hw₂S, hw₂At, hw₂Coarse⟩
        · exact ⟨huS, huAt, huRel⟩
        · exact ⟨hu'S, hu'At, hu'Rel⟩
      have hCard := block_card_le_three source pairing hNoGlue hRamification
        hValency hb ({w₁, w₂, u, u'} : Finset (gauged).SourceEdge) hMem
      rw [Finset.card_insert_of_notMem (by simp [hNe, hw₁u, hw₁u']),
        Finset.card_insert_of_notMem (by simp [hw₂u, hw₂u']),
        Finset.card_insert_of_notMem (by simp [huu']),
        Finset.card_singleton] at hCard
      omega
    have hSubset : nonDanglingIncident (cand).datum
        (epv (rside ((coarse).repr x)) x) ⊆ {(cand).oldSourceEdge u} := by
      intro g hg
      obtain ⟨hgS, hgI⟩ := (mem_nonDanglingIncident _ _ _).mp hg
      rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue
        hRamification profile hConnected hGenus hValid hb hgS hgI with
        ⟨u', hu'S, hu'At, hu'Side, hu'Rel, rfl⟩ |
        ⟨u', hu'S, hu'At, hu'Side, hu'Rel, rfl⟩
      · rw [hRetUniq u' hu'S hu'At hu'Side hu'Rel]
        exact Finset.mem_singleton_self _
      · exfalso
        have hEqNew : (cand).newSourceEdge u'.1.2 = (cand).newSourceEdge x := by
          rcases hFineAll u' hu'S hu'At hu'Side hu'Rel with h | h
          · rw [h]
            exact newSourceEdge_fine_eq source pairing hNoGlue hRamification
              profile hConnected hGenus hValid hb hw₁Rel
          · rw [h]
            exact newSourceEdge_fine_eq source pairing hNoGlue hRamification
              profile hConnected hGenus hValid hb hw₂Rel
        rw [hEqNew] at hgS
        exact hgS hNewDangling
    exact old_survives source pairing hNoGlue hRamification profile hConnected
      hGenus hValid huS
      (isDangling_of_subset_singleton source pairing hNoGlue hRamification
        profile hConnected hGenus hValid hSubset
        (incident_ret_endpoint source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hb huAt huSide' huRel))

/-- **A retained survivor sharing its fine endpoint with the new occurrence.**
The retained survivor is then the only survivor of its fine class, so the new
occurrence is absorbed into its wall row. -/
theorem newRow_eq_fine_of_pair {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) {w : (gauged).SourceEdge}
    (hwS : ¬ IsDangling (gauged) w)
    (hwAt : w.1.1 ∈ GluingDatum.incidentEdges wall)
    (hwSide : star.right pairing w.1.1 = !rside ((coarse).repr x))
    (hwRel : (blockRes ((coarse).repr x)).newEdge.Rel x w.1.2)
    (hPair : ∀ g : (cand).datum.SourceEdge, ¬ IsDangling (cand).datum g →
      Incident (cand).datum g (epv (!rside ((coarse).repr x)) x) →
      g = (cand).oldSourceEdge w ∨ g = (cand).newSourceEdge x) :
    nrow x =
      some (NonDanglingEdge.stablePath
        (⟨w, hwS⟩ : NonDanglingEdge (gauged))) := by
  refine newRow_fine source pairing hNoGlue hRamification profile
    ⟨hwAt, hwSide, hwRel⟩ ?_
  intro g hg
  obtain ⟨hgAt, hgSide, hgRel⟩ := hg
  rcases hPair ((cand).oldSourceEdge g.1)
    (old_survives source pairing hNoGlue hRamification profile hConnected hGenus
      hValid g.2)
    (incident_fine_endpoint source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hb hgAt hgSide hgRel) with h | h
  · exact Subtype.ext (ResolutionCut.oldSourceEdge_injective (cand) h)
  · exact absurd h (new_ne_old source pairing hNoGlue hRamification profile
      hConnected hGenus hValid x g.1)

/-! ## 6.  Constancy of the row assignment at the two wall endpoints -/

/-- **Constancy at the retaining endpoint of a non-anchor block.** -/
theorem rowOfEdge_eq_ret
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    {x : Fin degree} (hb : ¬ (coarse).Rel anchor.1 x)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 (epv (rside ((coarse).repr x)) x))
    (hF : Incident (cand).datum f.1 (epv (rside ((coarse).repr x)) x))
    (hVal : nonDanglingValency (cand).datum
      (epv (rside ((coarse).repr x)) x) = 2) :
    rowe e = rowe f := by
  classical
  have hNeVal : e.1 ≠ f.1 := fun h ↦ hNe (Subtype.ext h)
  have hPair : ∀ g : (cand).datum.SourceEdge, ¬ IsDangling (cand).datum g →
      Incident (cand).datum g (epv (rside ((coarse).repr x)) x) →
      g = e.1 ∨ g = f.1 :=
    fun g hgS hgI ↦ eq_of_pair_at_valency_two (cand).datum hNeVal e.2 f.2 hE hF
      hVal hgS hgI
  rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hb e.2 hE with
    ⟨r₁, hr₁S, hr₁At, hr₁Side, hr₁Rel, hEeq⟩ |
    ⟨z₁, hz₁S, hz₁At, hz₁Side, hz₁Rel, hEeq⟩
  · rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue
      hRamification profile hConnected hGenus hValid hb f.2 hF with
      ⟨r₂, hr₂S, hr₂At, hr₂Side, hr₂Rel, hFeq⟩ |
      ⟨z₂, hz₂S, hz₂At, hz₂Side, hz₂Rel, hFeq⟩
    · rw [rowOfEdge_of_old_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hr₁S hEeq,
        rowOfEdge_of_old_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hr₂S hFeq]
      refine congrArg some (block_row_eq_two_ret source pairing hNoGlue
        hRamification profile hConnected hGenus hValid hValency hb hr₁S hr₁At
        hr₁Side hr₁Rel hr₂S hr₂At hr₂Side hr₂Rel ?_ ?_)
      · intro h
        apply hNeVal
        rw [hEeq, hFeq, h]
      · intro g hgS hgI
        rcases hPair g hgS hgI with h | h
        · exact Or.inl (h.trans hEeq)
        · exact Or.inr (h.trans hFeq)
    · have hby : ¬ (coarse).Rel anchor.1 z₂.1.2 :=
        fun h ↦ hb (h.trans hz₂Rel.symm)
      have hRepr : (coarse).repr z₂.1.2 = (coarse).repr x := hz₂Rel.symm
      rw [rowOfEdge_of_old_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hr₁S hEeq,
        rowOfEdge_of_new_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hby hFeq]
      refine (newRow_eq_ret_of_pair source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hValency hby hr₁S hr₁At
        (by rw [hRepr]; exact hr₁Side) (hz₂Rel.symm.trans hr₁Rel) hz₂S hz₂At
        (by rw [hRepr]; exact hz₂Side) rfl ?_).symm
      intro g hgS hgI
      rw [ret_endpoint_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb hz₂Rel] at hgI
      rcases hPair g hgS hgI with h | h
      · exact Or.inl (h.trans hEeq)
      · exact Or.inr (h.trans hFeq)
  · rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue
      hRamification profile hConnected hGenus hValid hb f.2 hF with
      ⟨r₂, hr₂S, hr₂At, hr₂Side, hr₂Rel, hFeq⟩ |
      ⟨z₂, hz₂S, hz₂At, hz₂Side, hz₂Rel, hFeq⟩
    · have hby : ¬ (coarse).Rel anchor.1 z₁.1.2 :=
        fun h ↦ hb (h.trans hz₁Rel.symm)
      have hRepr : (coarse).repr z₁.1.2 = (coarse).repr x := hz₁Rel.symm
      rw [rowOfEdge_of_new_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hby hEeq,
        rowOfEdge_of_old_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hr₂S hFeq]
      refine newRow_eq_ret_of_pair source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hValency hby hr₂S hr₂At
        (by rw [hRepr]; exact hr₂Side) (hz₁Rel.symm.trans hr₂Rel) hz₁S hz₁At
        (by rw [hRepr]; exact hz₁Side) rfl ?_
      intro g hgS hgI
      rw [ret_endpoint_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb hz₁Rel] at hgI
      rcases hPair g hgS hgI with h | h
      · exact Or.inr (h.trans hEeq)
      · exact Or.inl (h.trans hFeq)
    · have hb₁ : ¬ (coarse).Rel anchor.1 z₁.1.2 :=
        fun h ↦ hb (h.trans hz₁Rel.symm)
      have hb₂ : ¬ (coarse).Rel anchor.1 z₂.1.2 :=
        fun h ↦ hb (h.trans hz₂Rel.symm)
      rw [rowOfEdge_of_new_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hb₁ hEeq,
        rowOfEdge_of_new_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hb₂ hFeq]
      refine newRow_eq_two_new source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hInj hb hz₁S hz₁At hz₁Side hz₁Rel hz₂S hz₂At
        hz₂Side hz₂Rel ?_ ?_
      · rw [← hEeq, ← hFeq]
        exact hNeVal
      · intro g hgS hgI
        rcases hPair g hgS hgI with h | h
        · exact Or.inl (h.trans hEeq)
        · exact Or.inr (h.trans hFeq)

/-- **Constancy at the fine endpoint of a non-anchor block.** -/
theorem rowOfEdge_eq_fine
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    {x : Fin degree} (hb : ¬ (coarse).Rel anchor.1 x)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 (epv (!rside ((coarse).repr x)) x))
    (hF : Incident (cand).datum f.1 (epv (!rside ((coarse).repr x)) x))
    (hVal : nonDanglingValency (cand).datum
      (epv (!rside ((coarse).repr x)) x) = 2) :
    rowe e = rowe f := by
  classical
  have hNeVal : e.1 ≠ f.1 := fun h ↦ hNe (Subtype.ext h)
  have hPair : ∀ g : (cand).datum.SourceEdge, ¬ IsDangling (cand).datum g →
      Incident (cand).datum g (epv (!rside ((coarse).repr x)) x) →
      g = e.1 ∨ g = f.1 :=
    fun g hgS hgI ↦ eq_of_pair_at_valency_two (cand).datum hNeVal e.2 f.2 hE hF
      hVal hgS hgI
  rcases nonDanglingIncident_fine_cases source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hb e.2 hE with
    hEeq | ⟨w₁, hw₁S, hw₁At, hw₁Side, hw₁Rel, hEeq⟩
  · rcases nonDanglingIncident_fine_cases source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hb f.2 hF with
      hFeq | ⟨w₂, hw₂S, hw₂At, hw₂Side, hw₂Rel, hFeq⟩
    · exact absurd (hEeq.trans hFeq.symm) hNeVal
    · rw [rowOfEdge_of_new_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hb hEeq,
        rowOfEdge_of_old_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hw₂S hFeq]
      refine newRow_eq_fine_of_pair source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb hw₂S hw₂At hw₂Side hw₂Rel ?_
      intro g hgS hgI
      rcases hPair g hgS hgI with h | h
      · exact Or.inr (h.trans hEeq)
      · exact Or.inl (h.trans hFeq)
  · rcases nonDanglingIncident_fine_cases source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hb f.2 hF with
      hFeq | ⟨w₂, hw₂S, hw₂At, hw₂Side, hw₂Rel, hFeq⟩
    · rw [rowOfEdge_of_old_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hw₁S hEeq,
        rowOfEdge_of_new_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hb hFeq]
      refine (newRow_eq_fine_of_pair source pairing hNoGlue hRamification
        profile hConnected hGenus hValid hb hw₁S hw₁At hw₁Side hw₁Rel ?_).symm
      intro g hgS hgI
      rcases hPair g hgS hgI with h | h
      · exact Or.inl (h.trans hEeq)
      · exact Or.inr (h.trans hFeq)
    · rw [rowOfEdge_of_old_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hw₁S hEeq,
        rowOfEdge_of_old_eq source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hw₂S hFeq]
      refine congrArg some (block_row_eq_two_fine source pairing hNoGlue
        hRamification profile hConnected hGenus hValid hInj hValency hb hw₁S
        hw₁At hw₁Side hw₁Rel hw₂S hw₂At hw₂Side hw₂Rel ?_ ?_)
      · intro h
        apply hNeVal
        rw [hEeq, hFeq, h]
      · intro g hgS hgI
        rcases hPair g hgS hgI with h | h
        · exact Or.inl (h.trans hEeq)
        · exact Or.inr (h.trans hFeq)

/-- **Constancy at every source vertex above the wall.**  At an anchor endpoint
the surviving valency is never two, so the case is vacuous; at a non-anchor
block the two endpoint censuses decide it. -/
theorem rowOfEdge_eq_wall
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    (sideValue : Bool) {v : (cand).datum.SourceVertex} (t : Fin degree)
    (hv : epv sideValue t = v)
    {e f : NonDanglingEdge (cand).datum} (hNe : e ≠ f)
    (hE : Incident (cand).datum e.1 v) (hF : Incident (cand).datum f.1 v)
    (hVal : nonDanglingValency (cand).datum v = 2) :
    rowe e = rowe f := by
  classical
  subst hv
  by_cases hA : (coarse).Rel anchor.1 t
  · exact absurd hVal (anchor_endpoint_valency_ne_two source pairing hNoGlue
      hRamification profile hConnected hGenus hValid sideValue hA)
  · by_cases hSide : sideValue = rside ((coarse).repr t)
    · subst hSide
      exact rowOfEdge_eq_ret source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hInj hValency hA hNe hE hF hVal
    · have hSide' : sideValue = !rside ((coarse).repr t) :=
        bool_eq_not_of_ne hSide
      subst hSide'
      exact rowOfEdge_eq_fine source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hInj hValency hA hNe hE hF hVal

/-! ## 7.  The reverse row map on stable rows, and injectivity -/

/-- **The row assignment is constant on consecutive pairs.**  The source
vertices of the candidate are enumerated as in
`LimitChainCore.SelectedData.rowOfEdge_eq_of_consecutive`: an old vertex away from the wall
is a retained vertex, and the two vertices above the wall are the endpoint
vertices of the crossing. -/
theorem rowOfEdge_eq_of_consecutive
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    {e f : NonDanglingEdge (cand).datum}
    (h : Consecutive (cand).datum e f) : rowe e = rowe f := by
  obtain ⟨hNe, v, hE, hF, hVal⟩ := h
  cases hTarget : v.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · rw [hAt] at hTarget
        exact rowOfEdge_eq_wall source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hInj hValency false v.1.2
          (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩)
          hNe hE hF hVal
      · obtain ⟨old, hOldTarget, hOldVertex⟩ :=
          ResolutionAwayFromWall.exists_retainedVertex_of_target (cand) v place
            hAt hTarget
        have hOldAway : old.1.1 ≠ wall := fun hEq ↦ hAt (hOldTarget.symm.trans hEq)
        subst hOldVertex
        exact rowOfEdge_eq_away source pairing hNoGlue hRamification profile
          hConnected hGenus hValid old hOldAway e f hE hF hVal
  | inr point =>
      cases point
      exact rowOfEdge_eq_wall source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hInj hValency true v.1.2
        (((cand).datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩)
        hNe hE hF hVal

/-- **The reverse row map on stable rows of the candidate.** -/
noncomputable def rowDescend
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3) :
    StablePath (cand).datum → Option (StablePath (gauged)) :=
  Quot.lift (rowe)
    (fun _ _ h ↦ rowOfEdge_eq_of_consecutive source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hInj hValency h)

@[simp] theorem rowDescend_mk
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    (e : NonDanglingEdge (cand).datum) :
    rowDescend source pairing hNoGlue hRamification profile hConnected hGenus
        hValid hInj hValency e.stablePath = rowe e := rfl

/-- **The reverse map is a literal left inverse of the retained-row map.** -/
theorem rowDescend_retainedRow
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3)
    (r : StablePath (gauged)) :
    rowDescend source pairing hNoGlue hRamification profile hConnected hGenus
        hValid hInj hValency
        (NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
          hRamification profile hConnected hGenus hValid r) = some r := by
  induction r using Quot.inductionOn with
  | h e =>
      exact rowOfEdge_retained source pairing hNoGlue hRamification profile
        hConnected hGenus hValid e

/-- **Injectivity of the retained-row map of the `K = 0` candidate.**  This
completes the row dictionary: the hypotheses are exactly the two censuses
`hInj` and `hValency` that `NonTrivalentValencyFourRowEquivFinal.rowEquiv`
carries, and nothing else about the candidate is assumed. -/
theorem retainedRow_injective'
    (hInj : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      NonDanglingStarInjective (gauged) star (WallBlock.ofSheet (gauged) wall y))
    (hValency : ∀ y : Fin degree, ¬ (coarse).Rel anchor.1 y →
      nonDanglingValency (gauged)
        (WallBlock.sourceVertex (gauged) wall
          (WallBlock.ofSheet (gauged) wall y)) ≤ 3) :
    Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow source pairing hNoGlue
        hRamification profile hConnected hGenus hValid) := by
  intro r₁ r₂ hEq
  have h₁ := rowDescend_retainedRow source pairing hNoGlue hRamification profile
    hConnected hGenus hValid hInj hValency r₁
  have h₂ := rowDescend_retainedRow source pairing hNoGlue hRamification profile
    hConnected hGenus hValid hInj hValency r₂
  rw [hEq, h₂] at h₁
  exact (Option.some_injective _ h₁).symm

end Block

/-! ## 8.  The unconditional corollaries at an actual four-valent wall -/

section ActualWall

open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.StablePathFacetContraction

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (cover : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation cover coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (wallStar : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
  (hForest : ContractionForest cover a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (anchorBlock : WallBlock (contractDatum cover hc hab hOne) ⟨a, hab⟩)
  (hAnchor : nonDanglingValency (contractDatum cover hc hab hOne)
    (WallBlock.sourceVertex (contractDatum cover hc hab hOne) ⟨a, hab⟩
      anchorBlock) = 4)
  (pairing : Fin 3)

local notation "wSrc" =>
  (NonTrivalentUniqueFourValent.wallFourBranchAnchor cover fd hc hab hOne
    wallStar hForest anchorBlock hAnchor)
local notation "wNG" =>
  (NonTrivalentUniqueFourValent.wall_noGlue cover fd hc hab hOne hForest)
local notation "wRam" =>
  (NonTrivalentUniqueFourValent.wall_ramification cover fd hc hab hOne wallStar
    hForest anchorBlock)
local notation "wProf" =>
  (NonTrivalentUniqueFourValent.ordinaryBlockProfile_of_single_row cover fd hc
    hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock
    hAnchor)
local notation "wConn" =>
  (NonTrivalentUniqueFourValent.wall_target_connected cover fd hab hOne)
local notation "wGen" =>
  (NonTrivalentUniqueFourValent.wall_target_genus cover fd hab hOne)
local notation "wVal" =>
  (NonTrivalentUniqueFourValent.wall_valid cover fd hc hab hOne hForest)

/-- **The retained-row map is injective at an actual four-valent wall.**  The
hypotheses are exactly those of
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row` together
with the wall metric; nothing about the candidate is assumed. -/
theorem retainedRow_injective_of_single_row :
    Function.Injective
      (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam
        wProf wConn wGen wVal) :=
  retainedRow_injective' wSrc pairing wNG wRam wProf wConn wGen wVal
    (fun y _ ↦
      NonTrivalentValencyFourRowEquivFinal.gauged_starInjective_of_single_row
        cover fd hc hab hOne wallStar hForest anchorBlock hAnchor pairing y)
    (fun y hy ↦
      NonTrivalentValencyFourRowEquivFinal.gauged_valency_of_single_row cover fd
        hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
        anchorBlock hAnchor pairing y hy)

/-- **The row equivalence of the `K = 0` candidate at an actual four-valent
wall, unconditionally.** -/
noncomputable def rowEquiv_of_single_row :
    StablePath (NonTrivalentValencyFourBackground.candidate wSrc pairing wNG wRam
        wProf wConn wGen wVal).datum ≃
      Option (StablePath (gaugedData wSrc pairing wNG wRam)) :=
  NonTrivalentValencyFourRowEquivFinal.rowEquiv_of_single_row cover fd hc hab
    hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock hAnchor
    pairing
    (retainedRow_injective_of_single_row cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing)

/-- The row equivalence sends each retained row to its wall row. -/
theorem rowEquiv_of_single_row_retainedRow
    (r : StablePath (gaugedData wSrc pairing wNG wRam)) :
    rowEquiv_of_single_row cover fd hc hab hOne wallStar hForest coordinates
        facet hRows hZeroCoord anchorBlock hAnchor pairing
        (NonTrivalentValencyFourRowDictionary.retainedRow wSrc pairing wNG wRam
          wProf wConn wGen wVal r) =
      some r :=
  NonTrivalentValencyFourRowEquivFinal.rowEquiv_of_single_row_retainedRow cover
    fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
    anchorBlock hAnchor pairing
    (retainedRow_injective_of_single_row cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing) r

variable (hCompat : DanglingCompatible cover hc hab hOne)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

/-- **The outgoing honest chart at an actual four-valent wall,
unconditionally.** -/
noncomputable def chartLabelling_of_single_row
    (chart : Option {column : coordinate //
      column ≠ fd.labelling.targetEdge.symm contracted} ≃ coordinate) :
    StableLengthMatrixLabelling
      (NonTrivalentValencyFourBackground.candidate wSrc pairing wNG wRam wProf
        wConn wGen wVal).datum coordinate :=
  NonTrivalentValencyFourRowEquivFinal.chartLabelling_of_single_row cover fd hc
    hab hOne wallStar hForest coordinates facet hRows hZeroCoord anchorBlock
    hAnchor pairing hCompat hPosCoord hFacetZero
    (retainedRow_injective_of_single_row cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing)
    chart

/-- **The common minor `A_{φ₀}` at an actual four-valent wall, entry by entry,
unconditionally.**  The outgoing honest matrix agrees with the incoming
full-dimensional cover's off the contracted column; no hypothesis about the
candidate is needed. -/
theorem matrix_chartLabelling_eq_incoming_of_single_row
    (chart : Option {column : coordinate //
      column ≠ fd.labelling.targetEdge.symm contracted} ≃ coordinate)
    (p : StablePath (contractDatum cover hc hab hOne))
    (column : {column : coordinate //
      column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (chartLabelling_of_single_row cover fd hc hab hOne wallStar hForest
          coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing hCompat
          hPosCoord hFacetZero chart).presentation
        (chart (some (wallRowIndex cover fd hc hab hOne hCompat hForest
          (noContractedReturn_of_fourStar cover fd hc hab hOne wallStar)
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero p)))
        (chart (some column)) =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row
          (incomingRow cover fd hc hab hOne hCompat hForest p))
        column.1 :=
  NonTrivalentValencyFourRowEquivFinal.matrix_chartLabelling_eq_incoming_of_single_row
    cover fd hc hab hOne wallStar hForest coordinates facet hRows hZeroCoord
    anchorBlock hAnchor pairing hCompat hPosCoord hFacetZero
    (retainedRow_injective_of_single_row cover fd hc hab hOne wallStar hForest
      coordinates facet hRows hZeroCoord anchorBlock hAnchor pairing)
    chart p column

end ActualWall

end DraismaVargas.LocalCases.NonTrivalentValencyFourRetainedInjective
