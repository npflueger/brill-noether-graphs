import DraismaVargasCount.TypeChangePositiveProbe
import DraismaVargasCount.OpenAtPositivity
import DraismaVargasCount.GeometricLimitTransport

/-!
# The facet machine: a type-change step from the per-limit parity

**Source.**  Vargas, Part II (arXiv:2609.09109), the wall-crossing proposition
`proposition-walking-through-II` at a **non-trivalent** limit, with `prop-signed-mult`(2);
and Draisma--Vargas Part I (arXiv:1909.12924), `lemma-yinM-iff-zPositive`, the ε-ball
mechanism, here centred on a point of the facet `{y e₀ = 0}` of the positive orthant.  This
module reduces the parity of the count across a Whitehead step (step 3 of the genus-six
assembly) to a per-limit parity at the facet the two chambers share.

## What the machine does

A Whitehead step `c → c'` contracts one slot `e₀`; the two cores agree once its ends
are identified (`TypeChangePositiveProbe.exists_shared_contraction_core`).  The two
chambers meet along the facet `{y e₀ = 0}`.  The machine:

* **Genericity and stabilisation.**  It picks a facet point `y₀` (`y₀ e₀ = 0`, positive
  elsewhere) that is *general on the facet* for both cores (`exists_facetPoint_general`:
  finite avoidance of the coordinate walls restricted to the facet), and a radius `ε` at
  which the request `facetRequest e₀ y₀ ε = y₀ + ε·δ_{e₀}` is stable for both cores
  (`exists_facetStable`).  The **same** request vector is used on both sides: a
  Whitehead step keeps the slot labels, so nothing has to be transported.
* **Specialisation.**  It shows that the frames open at `y₀ + ε·δ_{e₀}` are **exactly** the
  frames that degenerate at `y₀` in exactly one coordinate (`openAt_facetRequest_iff`),
  i.e. the `WallStar.Regrowth`s at the facet point, and that the coordinate lost is the
  column supporting the row labelled by `e₀` (`bridgeRow_of_degenerateAt`).
* **The facet limits.**  It puts the regrowths over **both** cores into one quotient,
  `FacetLimit`: a regrowth's limit is a gluing datum, which mentions no core, so limits over
  `c` and over `c'` are compared directly by `GeometricDatumIso`.
* **The link.**  It reads the per-limit parity `FacetParity` (the named hypothesis) through
  `CrossCoreParity.countLink_of_fibrewiseParity` with `L := FacetLimit`, giving
  `CountLink` between two positive general requests: the per-step obligation of
  `SimpleWallSupply.TypeChangeSupplyPositive` (`typeChangeSupplyPositive_step_of_facetParity`).

## Remarks that shaped it

* **Nothing persists across a type-change facet.**  No frame is open at a request
  with a zero slot (`OpenAtPositivity.not_openAt_of_nonpos`), so there is no facet point
  in the open cone: every member on either side specialises.  This matches the paper --
  a non-trivalent `mH₀` lies in no open full-dimensional cone.
* **Genericity lives inside the facet.**  The bridge coordinate vanishes identically
  on the facet, so "avoid every coordinate wall" is impossible there; the
  exceptional family is the *proper* restricted walls (`facetWall`).  The transfer
  from the finite normal-form family to every frame needs a frame isomorphism (a
  match of coordinate *functionals*, `exists_nf_coordFunctional`), not
  `SegmentWalls.exists_nf_coordsAt_eq`, which matches one request only.  This is
  the frame-level twin of Part I's facet genericity
  (`FacetGenericity.exists_facetGeneric`, over atlas charts), whose
  `FacetArrival`/`WallData` carry the same bridge row
  (`OuterWalk.WallData.incomingMatrix_facet_eq_zero`).
* **The limit relation must be the geometric one.**  `OpenOdd` lives on
  `CrossCoreTransport.FrameClass`, the quotient by the *geometric* frame isomorphism,
  and only `GeometricDatumIso` of limits is carried along it
  (`GeometricLimitTransport.limitIso`); with the strict `WallStar.SameLimit` the
  specialisation of a class would not be single-valued.
* **No core identification of the limit is needed.**  The machine never identifies
  a limit's stable graph with the contracted core; `FacetLimit` is the *unlabelled*
  limit.  That is coarser than the paper's labelled metric limit, which is harmless
  for parity: a coarse fibre is a disjoint union of fine fibres.
* **Universes.**  `FacetLimit : Type 1` (a `Regrowth` carries a `CFGraph.{0}`), while
  `TypeChangePositiveProbe.countLink_iff_exists_fibrewiseParity` quantifies `L : Type`;
  the universe-polymorphic producer `CrossCoreParity.countLink_of_fibrewiseParity` is what
  is used.
* **Why not `GeometricStar`.**  Its `hy : Nondegenerate y` enters only through
  `InheritedLimitRows.rows_ne_zero` (every stable row keeps positive length), which
  fails at a facet point at exactly the bridge row; it feeds the row and branch
  dictionaries of the limit's identification with the **same** core, which at a
  facet is the contracted core.  The machine uses only `WallStar.Regrowth.limit`,
  `GeometricDatumIso` and `GeometricLimitTransport.limitIso`, none of which takes `hy`.

## What is proved here

* `facetRequest`, `coordsAt_facetRequest`, `coordsAt_eq_of_vanish`,
  `col_eq_of_vanish`, `bridgeRow_support`, `bridge_entry_pos`,
  `coordsAt_slotUnit_pos` -- one frame coordinate on the facet.
* `FacetPoint`, `FacetGeneral`, `facetWall`, `exists_nf_coordFunctional`,
  `exists_facetPoint_general` -- **genericity on the facet**.
* `FacetStable`, `exists_facetStable` -- **stabilisation**.
* `degenerateAt_of_closed`, `degenerateAt_of_openAt`, `openAt_of_degenerateAt`,
  `openAt_facetRequest_iff`, `bridgeRow_of_degenerateAt` -- **specialisation and its
  converse**.
* `FacetRegrowth`, `FacetLimit`, `SpecializesLeft`, `SpecializesRight` and their
  `unique`, `exists_…`, `openAt_of_…` lemmas -- **the facet limits, and specialisation on
  classes**.
* `SharedContractionSlot`, `FacetDatum`, `exists_facetDatum`,
  `positiveGeneral_facetRequest`, `not_facetPoint_neg`,
  `FacetDatum.specializeLeft/Right` (`μ_c`, `μ_{c'}`), `FacetDatum.card_left/right`.
* `FacetParity` -- **the named hypothesis** -- with `facetParity_of_card_eq` (equal counts
  per limit suffice) and `facetParity_iff_fibrewise`.
* `countLink_of_facetParity`, `typeChangeSupplyPositive_step_of_facetParity`,
  `typeChangeSupplyPositive_of_facetParity`, `c34_genusSix_of_facetParity` -- **the link**,
  and its consumption by the propagation.
* `catLoopMove`, `catLoopCore`, `cat_step`, `cat_step_unloops`, `cat_loop_count`,
  `catLoop_loop_count`, `catFrame_degenerateAt_facet`, `catFrame_openAt_facetRequest`,
  `catFrame_isOdd`, `cat_facetParity_domain`, `cat_specializeLeft`,
  `cat_step_obligation_of_facetParity` -- **inhabitation at genus six**: an actual Whitehead
  step out of the caterpillar of loops, a facet datum, both requests positive and general,
  and a facet limit whose odd fibre on the caterpillar side is nonempty; and the composite
  applied there.

## What is not proved here

* **`FacetParity` is not proved here.**  It is the per-limit content of the valency-by-valency
  analysis of a type change (the members of each type at the three anchor valencies).
  Everything that concludes a `CountLink`, `TypeChangeSupplyPositive` or
  `CountSchedule.C34` here takes it as a hypothesis.  At a facet datum it follows from equal
  counts per labelled metric limit (`FacetCensus.facetParity_of_metricCensus_at`), which
  `CensusAssembly` proves at genus six; that is how step 3 of the assembly is discharged.
* **`FacetParity` is stated for the unlabelled limit**, not the paper's labelled
  metric limit.  It is implied by the paper's per-labelled-limit statement (sum over
  the fine limits in a coarse class, `FacetCensus` §2), but no identification of a limit's
  stable graph with the contracted core (`DegSpec.contractedCore`, `ContractionData`) is
  built here.
* **The facet limits are not shown `Valid`**, exactly as `WallStar`'s own limits are
  not; no `FibreMember` over the contracted core and no `CoreIdentification` of a
  limit is constructed.
* **No adapter to Part I's facet objects.**  Nothing here turns a facet datum and a
  regrowth at its facet point into an `OuterWalk.FacetArrival` / `WallData`, which is
  where the far-side candidates (`OuterWalk.TypeChangeLink` and the type-change
  dispatchers of the Part I library) live, and the facet point is not shown
  `FacetGenericity.FacetGeneric`.  Both are finite-avoidance conditions, so a common point
  exists, but it is not built here.
* **The inhabitation is object-level at one step.**  `cat_facetParity_domain` shows
  that at the caterpillar step one facet limit has a nonempty odd fibre on the
  caterpillar side; it says nothing about the far side, and nothing about how many
  classes specialise to that limit.
* **Strictness is not decided.**  `FacetParity → CountLink` is proved at every facet
  datum; that the converse fails somewhere is neither proved nor refuted, and no
  instance separating them is exhibited.
* The base count, the trivalent-wall hypothesis `InConeSupplySimple` and the genus bound
  are not touched; `c34_genusSix_of_facetParity` carries them as hypotheses exactly as
  `SimpleWallSupply.c34_genusSix_simple` does.
-/

namespace DraismaVargas.Count.FacetMachine

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame NFFrame)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.OpenOddRung (OpenOdd)
open DraismaVargas.Count.SimpleWallSupply (PositiveGeneral TypeChangeSupplyPositive)

variable {n p degree : ℕ}

/-! ## 1.  The facet request and one frame coordinate on the facet -/

/-- The unit request on the slot `e₀`: the direction normal to the facet `{y e₀ = 0}`. -/
def slotUnit (e₀ : Fin p) : Fin p → ℚ := Pi.single e₀ 1

/-- **The facet request** `y₀ + ε·δ_{e₀}`, written as an update because `y₀ e₀ = 0` on
the facet. -/
def facetRequest (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ) : Fin p → ℚ :=
  Function.update y₀ e₀ ε

@[simp] theorem facetRequest_self (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ) :
    facetRequest e₀ y₀ ε e₀ = ε := by
  simp [facetRequest]

theorem facetRequest_of_ne {e₀ e : Fin p} (y₀ : Fin p → ℚ) (ε : ℚ) (h : e ≠ e₀) :
    facetRequest e₀ y₀ ε e = y₀ e := by
  simp [facetRequest, h]

/-- On the facet hyperplane the facet request is `1·y₀ + ε·δ_{e₀}`. -/
theorem facetRequest_eq_comb {e₀ : Fin p} {y₀ : Fin p → ℚ} (hy₀ : y₀ e₀ = 0)
    (ε : ℚ) :
    facetRequest e₀ y₀ ε = fun s ↦ 1 * y₀ s + ε * slotUnit e₀ s := by
  funext s
  by_cases hs : s = e₀
  · subst hs
    simp [slotUnit, hy₀]
  · rw [facetRequest_of_ne y₀ ε hs, slotUnit, Pi.single_eq_of_ne hs]
    ring

/-- **Each frame coordinate is affine in `ε` along the facet normal.** -/
theorem coordsAt_facetRequest {core : Core n p} (k : Frame core degree) {e₀ : Fin p}
    {y₀ : Fin p → ℚ} (hy₀ : y₀ e₀ = 0) (ε : ℚ) (col : Fin p) :
    k.coordsAt (facetRequest e₀ y₀ ε) col =
      k.coordsAt y₀ col + ε * k.coordsAt (slotUnit e₀) col := by
  rw [facetRequest_eq_comb hy₀, PositiveOrthantWall.coordsAt_comb, one_mul]

/-- Every request splits along the facet: its projection to `{y e₀ = 0}` plus
`y e₀` times the facet normal. -/
theorem eq_comb_update (y : Fin p → ℚ) (e₀ : Fin p) :
    y = fun s ↦ 1 * Function.update y e₀ 0 s + y e₀ * slotUnit e₀ s := by
  funext s
  by_cases hs : s = e₀
  · subst hs
    simp [slotUnit]
  · rw [Function.update_of_ne hs, slotUnit, Pi.single_eq_of_ne hs]
    ring

/-- **A coordinate that vanishes on the facet hyperplane is a multiple of `y e₀`.** -/
theorem coordsAt_eq_of_vanish {core : Core n p} (k : Frame core degree) {e₀ col : Fin p}
    (hvan : ∀ y : Fin p → ℚ, y e₀ = 0 → k.coordsAt y col = 0) (y : Fin p → ℚ) :
    k.coordsAt y col = y e₀ * k.coordsAt (slotUnit e₀) col := by
  have hsplit := congrArg (fun z ↦ k.coordsAt z col) (eq_comb_update y e₀)
  rw [hsplit, PositiveOrthantWall.coordsAt_comb,
    hvan _ (Function.update_self e₀ 0 y), mul_zero, zero_add]

/-- Such a coordinate is nonzero on the facet normal: a nonsingular length matrix
has no identically vanishing coordinate (it is `1` on its own push direction). -/
theorem coordsAt_slotUnit_ne_zero {core : Core n p} (k : Frame core degree) {e₀ col : Fin p}
    (hvan : ∀ y : Fin p → ℚ, y e₀ = 0 → k.coordsAt y col = 0) :
    k.coordsAt (slotUnit e₀) col ≠ 0 := by
  intro h
  have h1 := coordsAt_eq_of_vanish k hvan (k.push col)
  rw [k.coordsAt_push col, Pi.single_eq_same, h, mul_zero] at h1
  exact one_ne_zero h1

/-- **At most one coordinate of a frame vanishes on the facet.**  Two distinct
coordinate functionals of a nonsingular frame are never both multiples of `y e₀`. -/
theorem col_eq_of_vanish {core : Core n p} (k : Frame core degree) {e₀ col col' : Fin p}
    (h : ∀ y : Fin p → ℚ, y e₀ = 0 → k.coordsAt y col = 0)
    (h' : ∀ y : Fin p → ℚ, y e₀ = 0 → k.coordsAt y col' = 0) : col = col' := by
  by_contra hne
  have h1 := coordsAt_eq_of_vanish k h (k.push col)
  have h2 := coordsAt_eq_of_vanish k h' (k.push col)
  rw [k.coordsAt_push col, Pi.single_eq_same] at h1
  rw [k.coordsAt_push col, Pi.single_eq_of_ne (Ne.symm hne)] at h2
  have hpush : k.push col e₀ ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h1
    exact one_ne_zero h1
  rcases mul_eq_zero.mp h2.symm with hz | hz
  · exact hpush hz
  · exact coordsAt_slotUnit_ne_zero k h' hz

/-- **The bridge row.**  If the coordinate `col` vanishes on the facet `{y e₀ = 0}`,
then the row of the length matrix labelled by the slot `e₀` is supported in the
column `col` alone -- the shape of `OuterWalk.TypeChangeLink.outgoingMatrix_facet_eq_zero`. -/
theorem bridgeRow_support {core : Core n p} (k : Frame core degree) {e₀ col : Fin p}
    (h : ∀ y : Fin p → ℚ, y e₀ = 0 → k.coordsAt y col = 0) (c : Fin p) (hc : c ≠ col) :
    k.matrix (k.slot.symm e₀) c = 0 := by
  have h1 := coordsAt_eq_of_vanish k h (k.push c)
  rw [k.coordsAt_push c, Pi.single_eq_of_ne (Ne.symm hc)] at h1
  rcases mul_eq_zero.mp h1.symm with hz | hz
  · exact hz
  · exact absurd hz (coordsAt_slotUnit_ne_zero k h)

/-- The one surviving entry of the bridge row is strictly positive (entries are
non-negative path sums, and a nonsingular matrix has no zero row). -/
theorem bridge_entry_pos {core : Core n p} (k : Frame core degree) {e₀ col : Fin p}
    (h : ∀ y : Fin p → ℚ, y e₀ = 0 → k.coordsAt y col = 0) :
    0 < k.matrix (k.slot.symm e₀) col := by
  obtain ⟨c, hc⟩ := PositiveOrthantWall.exists_matrix_ne_zero k (k.slot.symm e₀)
  have hcol : c = col := by
    by_contra hne
    exact hc (bridgeRow_support k h c hne)
  subst hcol
  exact lt_of_le_of_ne (StarPilot.matrix_nonneg k _ _) (Ne.symm hc)

/-- **The vanishing coordinate grows on the positive side of the facet.**  Its value
on the facet normal is the inverse of the bridge entry. -/
theorem coordsAt_slotUnit_pos {core : Core n p} (k : Frame core degree) {e₀ col : Fin p}
    (h : ∀ y : Fin p → ℚ, y e₀ = 0 → k.coordsAt y col = 0) :
    0 < k.coordsAt (slotUnit e₀) col := by
  have hreal : k.matrix.mulVec (k.coordsAt (slotUnit e₀)) (k.slot.symm e₀) = 1 := by
    rw [k.mulVec_coordsAt]
    simp [slotUnit]
  have hsum : k.matrix.mulVec (k.coordsAt (slotUnit e₀)) (k.slot.symm e₀) =
      k.matrix (k.slot.symm e₀) col * k.coordsAt (slotUnit e₀) col := by
    change (∑ c, k.matrix (k.slot.symm e₀) c * k.coordsAt (slotUnit e₀) c) = _
    refine Finset.sum_eq_single col (fun c _ hc ↦ ?_)
      (fun hcon ↦ absurd (Finset.mem_univ col) hcon)
    rw [bridgeRow_support k h c hc, zero_mul]
  rw [hsum] at hreal
  have hA := bridge_entry_pos k h
  by_contra hx
  push Not at hx
  have := mul_nonpos_of_nonneg_of_nonpos hA.le hx
  linarith

/-! ## 2.  Facet points, and genericity on the facet -/

/-- **A facet point** of the slot `e₀`: `y₀ e₀ = 0`, every other slot positive. -/
def FacetPoint (e₀ : Fin p) (y₀ : Fin p → ℚ) : Prop :=
  y₀ e₀ = 0 ∧ ∀ e, e ≠ e₀ → 0 < y₀ e

/-- **General on the facet**, for one core: every frame coordinate that vanishes at
`y₀` vanishes on the whole facet hyperplane `{y e₀ = 0}`.  It is obtained by the
finite avoidance of `SegmentWalls.exists_generic_start`, performed inside the facet
(`exists_facetPoint_general`).  By `col_eq_of_vanish` it implies that each frame
loses at most one coordinate at `y₀`: the frame-level twin of Part I's facet genericity
`FacetGenericity.FacetGeneric`, which says the same for the charts of the
universal atlas. -/
def FacetGeneral (core : Core n p) (degree : ℕ) (e₀ : Fin p) (y₀ : Fin p → ℚ) : Prop :=
  ∀ (k : Frame core degree) (col : Fin p), k.coordsAt y₀ col = 0 →
    ∀ y : Fin p → ℚ, y e₀ = 0 → k.coordsAt y col = 0

/-- One coordinate wall of a frame, restricted to the facet: its value at `z` is the
coordinate at the projection of `z` to `{y e₀ = 0}`. -/
noncomputable def facetWall {core : Core n p} (k : Frame core degree) (e₀ col : Fin p) :
    RationalAffineWall (Fin p) where
  coefficient s := if s = e₀ then 0 else (k.coordWall col).coefficient s
  constant := 0

theorem eval_facetWall {core : Core n p} (k : Frame core degree) (e₀ col : Fin p)
    (z : Fin p → ℚ) :
    (facetWall k e₀ col).eval z = k.coordsAt (Function.update z e₀ 0) col := by
  rw [← Frame.eval_coordWall]
  simp only [RationalAffineWall.eval, facetWall, Frame.coordWall, add_zero]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hs : s = e₀
  · subst hs
    simp
  · rw [if_neg hs, Function.update_of_ne hs]

/-- **Every frame coordinate is a normal-form coordinate, as a functional.**  The
match is a strict frame isomorphism, so it holds at every request at once -- which
is what "vanishes on the whole facet" needs, and more than
`SegmentWalls.exists_nf_coordsAt_eq` (one request) gives. -/
theorem exists_nf_coordFunctional {core : Core n p} (k : Frame core degree) (col : Fin p) :
    ∃ (r : NFFrame core degree) (col' : Fin p),
      ∀ y : Fin p → ℚ, (NFFrame.toFrame r).coordsAt y col' = k.coordsAt y col := by
  obtain ⟨r, hcls⟩ := SegmentWalls.exists_nfFrame (k.member fun _ ↦ 0)
  obtain ⟨fi⟩ := (SegmentWalls.isoOverCore_member_iff _ _ _).mp
    (FibreMember.cls_eq_cls_iff.mp hcls)
  refine ⟨r, fi.column.symm col, fun y ↦ ?_⟩
  have h := fi.coordsAt_column y (fi.column.symm col)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Avoiding every proper facet wall of the normal-form family is genericity on the
facet for every frame. -/
theorem facetGeneral_of_avoid (core : Core n p) (degree : ℕ) (e₀ : Fin p) (z : Fin p → ℚ)
    (havoid : ∀ (r : NFFrame core degree) (col : Fin p),
      (facetWall (NFFrame.toFrame r) e₀ col).Proper →
        (facetWall (NFFrame.toFrame r) e₀ col).eval z ≠ 0) :
    FacetGeneral core degree e₀ (Function.update z e₀ 0) := by
  intro k col hk y hy
  obtain ⟨r, col', hr⟩ := exists_nf_coordFunctional k col
  have hnp : ¬ (facetWall (NFFrame.toFrame r) e₀ col').Proper := by
    intro hprop
    apply havoid r col' hprop
    rw [eval_facetWall, hr]
    exact hk
  have hzero : (facetWall (NFFrame.toFrame r) e₀ col').eval y = 0 := by
    by_contra hy'
    exact hnp ⟨y, hy'⟩
  rw [eval_facetWall, Function.update_eq_self_iff.mpr hy.symm, hr] at hzero
  exact hzero

/-- **Genericity: a facet point general for both cores of a step exists.**  The
exceptional family is every *proper* facet wall of either core's normal-form frames
-- finite -- and the constraint is the positive orthant, so the projected point is
positive off `e₀`. -/
theorem exists_facetPoint_general (c c' : Core n p) (degree : ℕ) (e₀ : Fin p) :
    ∃ y₀ : Fin p → ℚ, FacetPoint e₀ y₀ ∧ FacetGeneral c degree e₀ y₀ ∧
      FacetGeneral c' degree e₀ y₀ := by
  classical
  let _ : Fintype (NFFrame c degree) := Fintype.ofFinite _
  let _ : Fintype (NFFrame c' degree) := Fintype.ofFinite _
  let W : (NFFrame c degree × Fin p) ⊕ (NFFrame c' degree × Fin p) →
      RationalAffineWall (Fin p) :=
    Sum.elim (fun x ↦ facetWall (NFFrame.toFrame x.1) e₀ x.2)
      (fun x ↦ facetWall (NFFrame.toFrame x.1) e₀ x.2)
  obtain ⟨z, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive
      (fun x : {x // (W x).Proper} ↦ W x.1) SegmentWalls.coordinateWall (fun _ ↦ 1)
      (fun x ↦ x.2) (by intro l; rw [SegmentWalls.eval_coordinateWall]; norm_num)
  refine ⟨Function.update z e₀ 0, ⟨Function.update_self e₀ 0 z, fun e he ↦ ?_⟩,
    ?_, ?_⟩
  · rw [Function.update_of_ne he]
    have h := hpos e
    rwa [SegmentWalls.eval_coordinateWall] at h
  · exact facetGeneral_of_avoid c degree e₀ z fun r col hprop ↦
      havoid ⟨Sum.inl (r, col), hprop⟩
  · exact facetGeneral_of_avoid c' degree e₀ z fun r col hprop ↦
      havoid ⟨Sum.inr (r, col), hprop⟩

/-! ## 3.  Stability of the facet request -/

/-- **Stability of the facet request `y₀ + ε·δ_{e₀}`** for one core: every frame
coordinate is nonzero there, and has the sign it has at `y₀` whenever that sign is
nonzero. -/
def FacetStable (core : Core n p) (degree : ℕ) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ) :
    Prop :=
  ∀ (k : Frame core degree) (col : Fin p),
    k.coordsAt (facetRequest e₀ y₀ ε) col ≠ 0 ∧
      (k.coordsAt y₀ col ≠ 0 →
        (0 < k.coordsAt (facetRequest e₀ y₀ ε) col ↔ 0 < k.coordsAt y₀ col))

/-- A finite family of positive rationals has a positive lower bound. -/
theorem exists_pos_le_of_finite {ι : Type*} [Finite ι] (f : ι → ℚ) (hf : ∀ i, 0 < f i) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i ↦ (h.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

/-- An affine function `a + ε b` keeps the sign of `a ≠ 0` while `ε |b| < |a|`. -/
theorem affine_sign {a b ε : ℚ} (hε : 0 < ε) (ha : a ≠ 0) (hsmall : ε * |b| < |a|) :
    a + ε * b ≠ 0 ∧ (0 < a + ε * b ↔ 0 < a) := by
  have h1 : ε * -|b| ≤ ε * b := mul_le_mul_of_nonneg_left (neg_abs_le b) hε.le
  have h2 : ε * b ≤ ε * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) hε.le
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · rw [abs_of_neg hneg] at hsmall
    refine ⟨fun h ↦ ?_, ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩ <;> linarith
  · rw [abs_of_pos hpos] at hsmall
    refine ⟨fun h ↦ ?_, ⟨fun _ ↦ hpos, fun _ ↦ ?_⟩⟩ <;> linarith

/-- **Stabilisation: a radius of stability exists.**  Each normal-form
coordinate is `a + ε b` along the facet normal; if `a = 0` then genericity makes
it a nonzero multiple of `ε`, and otherwise `ε < |a| / |b|` keeps its sign.  The
normal-form family is finite, so one radius serves every frame. -/
theorem exists_facetStable (core : Core n p) (degree : ℕ) {e₀ : Fin p} {y₀ : Fin p → ℚ}
    (hy₀ : y₀ e₀ = 0) (hgen : FacetGeneral core degree e₀ y₀) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧
      ∀ ε : ℚ, 0 < ε → ε ≤ ε₀ → FacetStable core degree e₀ y₀ ε := by
  classical
  let bound : NFFrame core degree × Fin p → ℚ := fun x ↦
    if (NFFrame.toFrame x.1).coordsAt y₀ x.2 ≠ 0 ∧
        (NFFrame.toFrame x.1).coordsAt (slotUnit e₀) x.2 ≠ 0 then
      |(NFFrame.toFrame x.1).coordsAt y₀ x.2| /
        |(NFFrame.toFrame x.1).coordsAt (slotUnit e₀) x.2|
    else 1
  have hbound : ∀ x, 0 < bound x := by
    intro x
    simp only [bound]
    split_ifs with h
    · exact div_pos (abs_pos.mpr h.1) (abs_pos.mpr h.2)
    · exact one_pos
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_of_finite bound hbound
  refine ⟨δ / 2, half_pos hδ, fun ε hε hεle k col ↦ ?_⟩
  obtain ⟨r, col', hr⟩ := exists_nf_coordFunctional k col
  have hb := hle (r, col')
  rw [coordsAt_facetRequest k hy₀]
  by_cases ha : k.coordsAt y₀ col = 0
  · have hb0 := coordsAt_slotUnit_ne_zero k (hgen k col ha)
    refine ⟨?_, fun h ↦ absurd ha h⟩
    rw [ha, zero_add]
    exact mul_ne_zero hε.ne' hb0
  · by_cases hb0 : k.coordsAt (slotUnit e₀) col = 0
    · rw [hb0, mul_zero, add_zero]
      exact ⟨ha, fun _ ↦ Iff.rfl⟩
    · have hab : bound (r, col') = |k.coordsAt y₀ col| / |k.coordsAt (slotUnit e₀) col| := by
        simp only [bound, hr]
        rw [if_pos ⟨ha, hb0⟩]
      rw [hab] at hb
      have hbpos : 0 < |k.coordsAt (slotUnit e₀) col| := abs_pos.mpr hb0
      have hlt : ε < |k.coordsAt y₀ col| / |k.coordsAt (slotUnit e₀) col| := by
        linarith [half_lt_self hδ]
      have hsmall := (lt_div_iff₀ hbpos).mp hlt
      exact ⟨(affine_sign hε ha hsmall).1, fun _ ↦ (affine_sign hε ha hsmall).2⟩

/-! ## 4.  Specialisation and its converse -/

section Specialisation

variable {core : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **Totality at the facet point.**  A frame whose closed cone contains a
general facet point degenerates there in **exactly one** coordinate: it is not open
at `y₀` (a request with a zero slot carries no open frame,
`OpenAtPositivity.not_openAt_of_nonpos`), and two vanishing coordinates would both
vanish on the facet, which `col_eq_of_vanish` forbids. -/
theorem degenerateAt_of_closed (hpt : FacetPoint e₀ y₀)
    (hgen : FacetGeneral core degree e₀ y₀)
    {k : Frame core degree} (hclosed : ∀ col, 0 ≤ k.coordsAt y₀ col) :
    ∃ col, k.DegenerateAt y₀ col := by
  have hnot : ¬ k.OpenAt y₀ := OpenAtPositivity.not_openAt_of_nonpos k (le_of_eq hpt.1)
  obtain ⟨col, hcol⟩ : ∃ col, k.coordsAt y₀ col = 0 := by
    by_contra hall
    push Not at hall
    exact hnot fun col ↦ lt_of_le_of_ne (hclosed col) (hall col).symm
  refine ⟨col, hcol, fun c hc ↦ lt_of_le_of_ne (hclosed c) fun h ↦ hc ?_⟩
  exact col_eq_of_vanish k (hgen k c h.symm) (hgen k col hcol)

/-- **Specialisation.**  A frame open at the facet request lies, at the facet
point, in the closure of its cone, hence (`degenerateAt_of_closed`) degenerates there in
exactly one
coordinate: it *is* a `WallStar.Regrowth` at `y₀`. -/
theorem degenerateAt_of_openAt (hpt : FacetPoint e₀ y₀)
    (hgen : FacetGeneral core degree e₀ y₀)
    (hst : FacetStable core degree e₀ y₀ ε) {k : Frame core degree}
    (hopen : k.OpenAt (facetRequest e₀ y₀ ε)) : ∃ col, k.DegenerateAt y₀ col := by
  refine degenerateAt_of_closed hpt hgen fun col ↦ ?_
  by_contra hneg
  push Not at hneg
  have h := ((hst k col).2 hneg.ne).mp (hopen col)
  linarith

/-- **The converse: every regrowth at the facet point is regrown on the positive
side.**  The vanishing coordinate is a positive multiple of `y e₀`
(`coordsAt_slotUnit_pos`), and the others keep their positive sign (stability). -/
theorem openAt_of_degenerateAt (hpt : FacetPoint e₀ y₀)
    (hgen : FacetGeneral core degree e₀ y₀) (hst : FacetStable core degree e₀ y₀ ε)
    (hε : 0 < ε) {k : Frame core degree} {col : Fin p}
    (hdeg : k.DegenerateAt y₀ col) : k.OpenAt (facetRequest e₀ y₀ ε) := by
  intro c
  by_cases hc : c = col
  · subst hc
    rw [coordsAt_facetRequest k hpt.1, hdeg.1, zero_add]
    exact mul_pos hε (coordsAt_slotUnit_pos k (hgen k c hdeg.1))
  · exact ((hst k c).2 (hdeg.2 c hc).ne').mpr (hdeg.2 c hc)

/-- **The stabilisation statement**: at every stable
radius the frames open at the facet request are exactly the regrowths at the facet
point -- a set that does not depend on `ε`. -/
theorem openAt_facetRequest_iff (hpt : FacetPoint e₀ y₀)
    (hgen : FacetGeneral core degree e₀ y₀)
    (hst : FacetStable core degree e₀ y₀ ε) (hε : 0 < ε) (k : Frame core degree) :
    k.OpenAt (facetRequest e₀ y₀ ε) ↔ ∃ col, k.DegenerateAt y₀ col :=
  ⟨degenerateAt_of_openAt hpt hgen hst,
    fun ⟨_, hdeg⟩ ↦ openAt_of_degenerateAt hpt hgen hst hε hdeg⟩

/-- **The vanishing coordinate is the bridge column.**  At a general facet point the
coordinate a regrowth loses is the unique column supporting the row labelled by the
contracted slot `e₀`, and that entry is positive. -/
theorem bridgeRow_of_degenerateAt (hgen : FacetGeneral core degree e₀ y₀)
    {k : Frame core degree} {col : Fin p} (hdeg : k.DegenerateAt y₀ col) :
    (∀ c, c ≠ col → k.matrix (k.slot.symm e₀) c = 0) ∧
      0 < k.matrix (k.slot.symm e₀) col :=
  ⟨bridgeRow_support k (hgen k col hdeg.1), bridge_entry_pos k (hgen k col hdeg.1)⟩

end Specialisation

/-! ## 5.  The facet limits: one quotient for both sides of the step -/

/-- A regrowth at the facet point, over either core of the step. -/
abbrev FacetRegrowth (c c' : Core n p) (y₀ : Fin p → ℚ) (degree : ℕ) : Type 1 :=
  Regrowth c y₀ degree ⊕ Regrowth c' y₀ degree

namespace FacetRegrowth

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

/-- The target of the limit: the frame's target with the vanishing occurrence
contracted. -/
def limitTarget : FacetRegrowth c c' y₀ degree → CFGraph.{0}
  | Sum.inl w => w.frame.limitTarget w.column
  | Sum.inr w => w.frame.limitTarget w.column

/-- **The limit datum** -- `WallStar.Regrowth.limit`, on either side.  A gluing datum
mentions no core, so the limits over the two cores live in one world. -/
noncomputable def limit : (a : FacetRegrowth c c' y₀ degree) → GluingDatum a.limitTarget degree
  | Sum.inl w => w.limit
  | Sum.inr w => w.limit

/-- **Same facet limit, across the two cores**: a geometric isomorphism of the two
limit data.  The geometric (orientation-independent) isomorphism is forced:
`CrossCoreTransport.FrameClass` quotients by the geometric frame isomorphism, and
only `GeometricDatumIso` is carried along it (`GeometricLimitTransport.limitIso`). -/
def SameLimit (a b : FacetRegrowth c c' y₀ degree) : Prop :=
  Nonempty (GeometricDatumIso a.limit b.limit)

theorem sameLimit_equivalence :
    Equivalence (SameLimit (c := c) (c' := c') (y₀ := y₀) (degree := degree)) :=
  ⟨fun _ ↦ ⟨GeometricDatumIso.refl _⟩, fun h ↦ h.elim fun i ↦ ⟨i.symm⟩,
    fun h h' ↦ h.elim fun i ↦ h'.elim fun j ↦ ⟨i.trans j⟩⟩

/-- The setoid of facet limits. -/
def setoid (c c' : Core n p) (y₀ : Fin p → ℚ) (degree : ℕ) :
    Setoid (FacetRegrowth c c' y₀ degree) :=
  ⟨SameLimit, sameLimit_equivalence⟩

end FacetRegrowth

/-- **The facet limits**: regrowths at the facet point over either
core of the step, up to geometric isomorphism of their limit data. -/
def FacetLimit (c c' : Core n p) (y₀ : Fin p → ℚ) (degree : ℕ) : Type 1 :=
  Quotient (FacetRegrowth.setoid c c' y₀ degree)

namespace FacetLimit

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

/-- The facet limit of a regrowth over the first core. -/
def ofLeft (w : Regrowth c y₀ degree) : FacetLimit c c' y₀ degree :=
  Quotient.mk _ (Sum.inl w)

/-- The facet limit of a regrowth over the second core. -/
def ofRight (w : Regrowth c' y₀ degree) : FacetLimit c c' y₀ degree :=
  Quotient.mk _ (Sum.inr w)

end FacetLimit

/-! ## 6.  Specialisation of frame classes, on the request-free model -/

section Classes

variable {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **A frame class over the first core specialises to the facet limit `l`**: some
representative frame degenerates at the facet point, and its limit is `l`. -/
def SpecializesLeft (x : FrameClass c degree) (l : FacetLimit c c' y₀ degree) : Prop :=
  ∃ w : Regrowth c y₀ degree, FrameClass.mk w.frame = x ∧ FacetLimit.ofLeft w = l

/-- The same over the second core. -/
def SpecializesRight (x : FrameClass c' degree) (l : FacetLimit c c' y₀ degree) : Prop :=
  ∃ w : Regrowth c' y₀ degree, FrameClass.mk w.frame = x ∧ FacetLimit.ofRight w = l

/-- **Specialisation is single-valued on classes**: two regrowths representing one
geometric frame class have geometrically isomorphic limits. -/
theorem SpecializesLeft.unique {x : FrameClass c degree} {l l' : FacetLimit c c' y₀ degree}
    (h : SpecializesLeft x l) (h' : SpecializesLeft x l') : l = l' := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', rfl⟩ := h'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (hw.trans hw'.symm)
  exact Quotient.sound ⟨GeometricLimitTransport.limitIso fi⟩

theorem SpecializesRight.unique {x : FrameClass c' degree} {l l' : FacetLimit c c' y₀ degree}
    (h : SpecializesRight x l) (h' : SpecializesRight x l') : l = l' := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', rfl⟩ := h'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (hw.trans hw'.symm)
  exact Quotient.sound ⟨GeometricLimitTransport.limitIso fi⟩

/-- **Every class open at the facet request specialises** (first core). -/
theorem exists_specializesLeft (hpt : FacetPoint e₀ y₀) (hgen : FacetGeneral c degree e₀ y₀)
    (hst : FacetStable c degree e₀ y₀ ε) (x : FrameClass c degree)
    (hx : x.OpenAt (facetRequest e₀ y₀ ε)) :
    ∃ l : FacetLimit c c' y₀ degree, SpecializesLeft x l := by
  obtain ⟨k, rfl⟩ := FrameClass.mk_surjective x
  obtain ⟨col, hdeg⟩ := degenerateAt_of_openAt hpt hgen hst hx
  exact ⟨FacetLimit.ofLeft ⟨k, col, hdeg⟩, ⟨k, col, hdeg⟩, rfl, rfl⟩

/-- The same over the second core. -/
theorem exists_specializesRight (hpt : FacetPoint e₀ y₀)
    (hgen : FacetGeneral c' degree e₀ y₀)
    (hst : FacetStable c' degree e₀ y₀ ε) (x : FrameClass c' degree)
    (hx : x.OpenAt (facetRequest e₀ y₀ ε)) :
    ∃ l : FacetLimit c c' y₀ degree, SpecializesRight x l := by
  obtain ⟨k, rfl⟩ := FrameClass.mk_surjective x
  obtain ⟨col, hdeg⟩ := degenerateAt_of_openAt hpt hgen hst hx
  exact ⟨FacetLimit.ofRight ⟨k, col, hdeg⟩, ⟨k, col, hdeg⟩, rfl, rfl⟩

/-- **Conversely, a class that specialises is open at the facet request** (first
core): the star of a facet limit on side `c` is exactly the set of classes that
are open just off the facet. -/
theorem openAt_of_specializesLeft (hpt : FacetPoint e₀ y₀)
    (hgen : FacetGeneral c degree e₀ y₀)
    (hst : FacetStable c degree e₀ y₀ ε) (hε : 0 < ε) {x : FrameClass c degree}
    {l : FacetLimit c c' y₀ degree} (h : SpecializesLeft x l) :
    x.OpenAt (facetRequest e₀ y₀ ε) := by
  obtain ⟨w, rfl, -⟩ := h
  exact openAt_of_degenerateAt hpt hgen hst hε w.degenerate

/-- The same over the second core. -/
theorem openAt_of_specializesRight (hpt : FacetPoint e₀ y₀)
    (hgen : FacetGeneral c' degree e₀ y₀) (hst : FacetStable c' degree e₀ y₀ ε)
    (hε : 0 < ε)
    {x : FrameClass c' degree} {l : FacetLimit c c' y₀ degree} (h : SpecializesRight x l) :
    x.OpenAt (facetRequest e₀ y₀ ε) := by
  obtain ⟨w, rfl, -⟩ := h
  exact openAt_of_degenerateAt hpt hgen hst hε w.degenerate

end Classes

/-! ## 7.  The facet datum of a Whitehead step, and the machine -/

/-- **The slot a Whitehead step contracts**: the two cores agree once the two
(distinct) ends `v₀`, `v₁` of `e₀` are identified.  This is exactly the conclusion
of `TypeChangePositiveProbe.exists_shared_contraction_core`, named at `e₀`. -/
def SharedContractionSlot (c c' : Core n p) (e₀ : Fin p) : Prop :=
  ∃ v₀ v₁ : Fin n, v₀ ≠ v₁ ∧
    ((c.tail e₀ = v₀ ∧ c.head e₀ = v₁) ∨
      (c.tail e₀ = v₁ ∧ c.head e₀ = v₀)) ∧
    (∀ e : Fin p, TypeChangePositiveProbe.contractVertex v₀ v₁ (c'.tail e) =
      TypeChangePositiveProbe.contractVertex v₀ v₁ (c.tail e)) ∧
    (∀ e : Fin p, TypeChangePositiveProbe.contractVertex v₀ v₁ (c'.head e) =
      TypeChangePositiveProbe.contractVertex v₀ v₁ (c.head e))

/-- Every Whitehead step has a shared contraction slot. -/
theorem exists_sharedContractionSlot {c c' : CubicCore n p} (h : Step c c') :
    ∃ e₀ : Fin p, SharedContractionSlot c.core c'.core e₀ := by
  obtain ⟨e₀, v₀, v₁, hne, hends, ht, hh⟩ :=
    TypeChangePositiveProbe.exists_shared_contraction_core h
  exact ⟨e₀, v₀, v₁, hne, hends, ht, hh⟩

/-- **A facet datum for a step** `c → c'`: the contracted slot `e₀`, a facet point
`y₀` general for both cores, and a radius `ε` at which the facet request is stable
for both cores.  The request `y₀ + ε·δ_{e₀}` is then used, **unchanged**, on both
sides: a Whitehead step keeps the slot labels, so no transport of `y₀` is needed.
Always inhabited (`exists_facetDatum`); it is a condition the machine produces,
not a hypothesis anyone has to discharge. -/
structure FacetDatum (c c' : Core n p) (degree : ℕ) (e₀ : Fin p) (y₀ : Fin p → ℚ)
    (ε : ℚ) : Prop where
  shared : SharedContractionSlot c c' e₀
  point : FacetPoint e₀ y₀
  general : FacetGeneral c degree e₀ y₀
  general' : FacetGeneral c' degree e₀ y₀
  pos : 0 < ε
  stable : FacetStable c degree e₀ y₀ ε
  stable' : FacetStable c' degree e₀ y₀ ε

/-- **A facet request is positive and general** for every core at which it is stable. -/
theorem positiveGeneral_facetRequest {core : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ}
    {ε : ℚ}
    (hpt : FacetPoint e₀ y₀) (hε : 0 < ε) (hst : FacetStable core degree e₀ y₀ ε) :
    PositiveGeneral core degree (facetRequest e₀ y₀ ε) := by
  refine ⟨fun i ↦ ?_, fun k col ↦ (hst k col).1⟩
  by_cases hi : i = e₀
  · subst hi
    rw [facetRequest_self]
    exact hε
  · rw [facetRequest_of_ne y₀ ε hi]
    exact hpt.2 i hi

/-- **Negation check**: negating a facet point destroys it, so no facet
datum sits at a negated request.  (Any `p ≥ 2` has a slot `e ≠ e₀`.) -/
theorem not_facetPoint_neg {e₀ e : Fin p} {y₀ : Fin p → ℚ} (hpt : FacetPoint e₀ y₀)
    (he : e ≠ e₀) : ¬ FacetPoint e₀ (fun s ↦ (-1 : ℚ) * y₀ s) := by
  rintro ⟨-, hneg⟩
  have h1 : 0 < (-1 : ℚ) * y₀ e := hneg e he
  have h2 := hpt.2 e he
  linarith

/-- **At every step a facet datum exists.** -/
theorem exists_facetDatum {c c' : CubicCore n p} (h : Step c c') (degree : ℕ) :
    ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
      FacetDatum c.core c'.core degree e₀ y₀ ε := by
  obtain ⟨e₀, hshared⟩ := exists_sharedContractionSlot h
  obtain ⟨y₀, hpt, hgen, hgen'⟩ := exists_facetPoint_general c.core c'.core degree e₀
  obtain ⟨ε₀, hε₀, hst⟩ := exists_facetStable c.core degree hpt.1 hgen
  obtain ⟨ε₁, hε₁, hst'⟩ := exists_facetStable c'.core degree hpt.1 hgen'
  have hmin : 0 < min ε₀ ε₁ := lt_min hε₀ hε₁
  exact ⟨e₀, y₀, min ε₀ ε₁, hshared, hpt, hgen, hgen', hmin,
    hst _ hmin (min_le_left _ _), hst' _ hmin (min_le_right _ _)⟩

namespace FacetDatum

variable {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}

theorem positiveGeneral_left (hd : FacetDatum c c' degree e₀ y₀ ε) :
    PositiveGeneral c degree (facetRequest e₀ y₀ ε) :=
  positiveGeneral_facetRequest hd.point hd.pos hd.stable

theorem positiveGeneral_right (hd : FacetDatum c c' degree e₀ y₀ ε) :
    PositiveGeneral c' degree (facetRequest e₀ y₀ ε) :=
  positiveGeneral_facetRequest hd.point hd.pos hd.stable'

/-- **`μ_c`: the specialisation map on the first side.**  Chosen, but canonical:
`specializeLeft_eq_iff`. -/
noncomputable def specializeLeft (hd : FacetDatum c c' degree e₀ y₀ ε)
    (a : OpenOdd c degree (facetRequest e₀ y₀ ε)) : FacetLimit c c' y₀ degree :=
  Classical.choose (exists_specializesLeft (c' := c') hd.point hd.general hd.stable a.1 a.2.1)

/-- **`μ_{c'}`: the specialisation map on the second side.** -/
noncomputable def specializeRight (hd : FacetDatum c c' degree e₀ y₀ ε)
    (b : OpenOdd c' degree (facetRequest e₀ y₀ ε)) : FacetLimit c c' y₀ degree :=
  Classical.choose (exists_specializesRight (c := c) hd.point hd.general' hd.stable' b.1 b.2.1)

theorem specializeLeft_eq_iff (hd : FacetDatum c c' degree e₀ y₀ ε)
    (a : OpenOdd c degree (facetRequest e₀ y₀ ε)) (l : FacetLimit c c' y₀ degree) :
    hd.specializeLeft a = l ↔ SpecializesLeft a.1 l := by
  have hspec : SpecializesLeft a.1 (hd.specializeLeft a) :=
    Classical.choose_spec
      (exists_specializesLeft (c' := c') hd.point hd.general hd.stable a.1 a.2.1)
  exact ⟨fun h ↦ h ▸ hspec, fun h ↦ hspec.unique h⟩

theorem specializeRight_eq_iff (hd : FacetDatum c c' degree e₀ y₀ ε)
    (b : OpenOdd c' degree (facetRequest e₀ y₀ ε)) (l : FacetLimit c c' y₀ degree) :
    hd.specializeRight b = l ↔ SpecializesRight b.1 l := by
  have hspec : SpecializesRight b.1 (hd.specializeRight b) :=
    Classical.choose_spec
      (exists_specializesRight (c := c) hd.point hd.general' hd.stable' b.1 b.2.1)
  exact ⟨fun h ↦ h ▸ hspec, fun h ↦ hspec.unique h⟩

/-- **The fibre of `μ_c` over `l` is the odd part of the star of `l` on side `c`**,
with the facet request dropped: a class specialising to `l` is automatically open
just off the facet. -/
theorem card_left (hd : FacetDatum c c' degree e₀ y₀ ε) (l : FacetLimit c c' y₀ degree) :
    Nat.card {a : OpenOdd c degree (facetRequest e₀ y₀ ε) // hd.specializeLeft a = l} =
      Nat.card {x : FrameClass c degree // x.IsOdd ∧ SpecializesLeft x l} := by
  refine Nat.card_congr
    { toFun := fun a ↦ ⟨a.1.1, a.1.2.2, (hd.specializeLeft_eq_iff a.1 l).mp a.2⟩
      invFun := fun x ↦ ⟨⟨x.1, openAt_of_specializesLeft hd.point hd.general hd.stable hd.pos
          x.2.2, x.2.1⟩, (hd.specializeLeft_eq_iff _ l).mpr x.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The same on side `c'`. -/
theorem card_right (hd : FacetDatum c c' degree e₀ y₀ ε) (l : FacetLimit c c' y₀ degree) :
    Nat.card {b : OpenOdd c' degree (facetRequest e₀ y₀ ε) // hd.specializeRight b = l} =
      Nat.card {x : FrameClass c' degree // x.IsOdd ∧ SpecializesRight x l} := by
  refine Nat.card_congr
    { toFun := fun b ↦ ⟨b.1.1, b.1.2.2, (hd.specializeRight_eq_iff b.1 l).mp b.2⟩
      invFun := fun x ↦ ⟨⟨x.1, openAt_of_specializesRight hd.point hd.general' hd.stable'
          hd.pos x.2.2, x.2.1⟩, (hd.specializeRight_eq_iff _ l).mpr x.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

end FacetDatum

/-- **The per-limit parity at a type-change facet -- the named hypothesis.**

For every facet limit `l` at the facet point `y₀`, the number of odd frame classes of
`c` specialising to `l` plus the number of odd frame classes of `c'` specialising to
`l` is even.  This is Draisma--Vargas Part II's `proposition-walking-through-II` at a
non-trivalent limit, read mod 2: by `prop-signed-mult`(2) every member of the star
of `l` has the same `Mult`, and by the valency-three and valency-two cases of Part II's
section on changing combinatorial type (`subsec-case-v3`, `subsec-case-v2`) and the
valency-four `K`-family (`subsec-case-v4`) the star meets the sides `c` and `c'` in equally
many members, so the odd parts have equal size and their sum is even.

**It is discharged from equal counts per limit** (`facetParity_of_card_eq`); at genus six
this is `FacetCensus.facetParity_of_metricCensus_at` with `CensusAssembly`.  The equal-`Mult`
half at an actual link is `NonTrivalentNonfacetDenominator.signedMult_eq_of_typeChangeLink`.

At every facet datum `FacetParity c c' degree y₀` is equivalent to the
fibrewise parity of the two specialisation maps `μ_c`, `μ_{c'}`
(`facetParity_iff_fibrewise`), which is the input of
`CrossCoreParity.countLink_of_fibrewiseParity`.  It is not the free reformulation
that `TypeChangePositiveProbe.countLink_iff_exists_fibrewiseParity` warns about: its
index type is the geometric `FacetLimit`, fixed by the facet point rather than chosen,
and at the genus-six caterpillar step one limit already has a nonempty fibre on side
`c` (`cat_facetParity_domain`).  It implies the link (`countLink_of_facetParity`);
whether that implication is strict is neither proved nor refuted here. -/
def FacetParity (c c' : Core n p) (degree : ℕ) (y₀ : Fin p → ℚ) : Prop :=
  ∀ l : FacetLimit c c' y₀ degree,
    Even (Nat.card {x : FrameClass c degree // x.IsOdd ∧ SpecializesLeft x l} +
      Nat.card {x : FrameClass c' degree // x.IsOdd ∧ SpecializesRight x l})

section Machine

variable {c c' : Core n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **Equal counts suffice**: equal counts per facet limit give the parity. -/
theorem facetParity_of_card_eq
    (h : ∀ l : FacetLimit c c' y₀ degree,
      Nat.card {x : FrameClass c degree // x.IsOdd ∧ SpecializesLeft x l} =
        Nat.card {x : FrameClass c' degree // x.IsOdd ∧ SpecializesRight x l}) :
    FacetParity c c' degree y₀ := fun l ↦ by
  rw [h l]
  exact ⟨_, rfl⟩

/-- **`FacetParity` as fibrewise parity**: at a facet datum, `FacetParity` is the fibrewise
parity of the two specialisation maps. -/
theorem facetParity_iff_fibrewise (hd : FacetDatum c c' degree e₀ y₀ ε) :
    FacetParity c c' degree y₀ ↔
      ∀ l : FacetLimit c c' y₀ degree,
        Even (Nat.card {a : OpenOdd c degree (facetRequest e₀ y₀ ε) //
            hd.specializeLeft a = l} +
          Nat.card {b : OpenOdd c' degree (facetRequest e₀ y₀ ε) //
            hd.specializeRight b = l}) := by
  refine forall_congr' fun l ↦ ?_
  rw [hd.card_left l, hd.card_right l]

/-- **The link from the per-limit parity, at one facet datum.** -/
theorem countLink_of_facetParity (hd : FacetDatum c c' degree e₀ y₀ ε)
    (hpar : FacetParity c c' degree y₀) :
    CountTransportLink.CountLink degree c (facetRequest e₀ y₀ ε) c'
      (facetRequest e₀ y₀ ε) :=
  CrossCoreParity.countLink_of_fibrewiseParity hd.specializeLeft hd.specializeRight
    ((facetParity_iff_fibrewise hd).mp hpar)

end Machine

/-- **The per-step obligation of `SimpleWallSupply.TypeChangeSupplyPositive`, from the
per-limit parity.**  The machine chooses the facet datum itself (`exists_facetDatum`):
the only input is `FacetParity` at the facet points of the step's contracted slot. -/
theorem typeChangeSupplyPositive_step_of_facetParity {c c' : CubicCore n p} (hstep : Step c c')
    (hpar : ∀ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
      FacetDatum c.core c'.core degree e₀ y₀ ε → FacetParity c.core c'.core degree y₀) :
    ∃ y y' : Fin p → ℚ, PositiveGeneral c.core degree y ∧
      PositiveGeneral c'.core degree y' ∧
        CountTransportLink.CountLink degree c.core y c'.core y' := by
  obtain ⟨e₀, y₀, ε, hd⟩ := exists_facetDatum hstep degree
  exact ⟨_, _, hd.positiveGeneral_left, hd.positiveGeneral_right,
    countLink_of_facetParity hd (hpar e₀ y₀ ε hd)⟩

/-- **`SimpleWallSupply.TypeChangeSupplyPositive` from the per-limit parity at every
step.** -/
theorem typeChangeSupplyPositive_of_facetParity
    (h : ∀ c c' : CubicCore n p, Step c c' →
      ∀ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
        FacetDatum c.core c'.core degree e₀ y₀ ε → FacetParity c.core c'.core degree y₀) :
    TypeChangeSupplyPositive degree n p :=
  fun _ _ hstep ↦ typeChangeSupplyPositive_step_of_facetParity hstep (h _ _ hstep)

/-! ## 8.  Inhabitation at genus six -/

section GenusSix

open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)
open DraismaVargas.Count.SegmentWalls (catFrame)

/-- **A Whitehead move out of the genus-six caterpillar of loops.**  The base is the
spine slot `1`, from the loop vertex `0` to the spine vertex `1`; the move carries
one dart of the loop slot `0` to vertex `1` and slot `2`'s dart at vertex `1` to
vertex `0`.  Slot `0` stops being a loop and slots `0`, `1` become parallel, so the
far core has five loops where the caterpillar has six. -/
def catLoopMove : catCubicCore.graph.MoveData where
  base := (1, false)
  left := (0, false)
  right := (2, false)
  nonloop := by decide
  left_vert := by decide
  left_ne := by decide
  right_vert := by decide
  right_ne := by decide

/-- The far side of that move. -/
def catLoopCore : CubicCore (4 * 2 + 2) (6 * 2 + 3) :=
  CoreOfDarts.CubicCore.ofGraph (catCubicCore.graph.move catLoopMove) rfl

/-- **It is an actual Whitehead step.** -/
theorem cat_step : Step catCubicCore catLoopCore :=
  ⟨catLoopMove, CoreOfDarts.CubicCore.graph_ofGraph _ _⟩

/-- The move really changes the core: slot `0` is a loop of the caterpillar and not of
the far core. -/
theorem cat_step_unloops :
    catCubicCore.core.tail 0 = catCubicCore.core.head 0 ∧
      catLoopCore.core.tail 0 ≠ catLoopCore.core.head 0 := by
  decide

/-- The caterpillar of loops has six loops. -/
theorem cat_loop_count :
    (Finset.univ.filter fun e : Fin (6 * 2 + 3) ↦
      catCubicCore.core.tail e = catCubicCore.core.head e).card = 6 := by
  decide

/-- The far core of `cat_step` has five. -/
theorem catLoop_loop_count :
    (Finset.univ.filter fun e : Fin (6 * 2 + 3) ↦
      catLoopCore.core.tail e = catLoopCore.core.head e).card = 5 := by
  decide

/-- **The caterpillar frame degenerates at every facet point of every slot**, in the
coordinate of that slot: its length matrix is diagonal with positive entries. -/
theorem catFrame_degenerateAt_facet {e₀ : Fin (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ}
    (hpt : FacetPoint e₀ y₀) : (catFrame 2).DegenerateAt y₀ e₀ := by
  refine ⟨?_, fun c hc ↦ ?_⟩
  · rw [SegmentWalls.coordsAt_catFrame_apply, hpt.1, zero_div]
  · rw [SegmentWalls.coordsAt_catFrame_apply]
    exact div_pos (hpt.2 c hc) (FibreCaterpillar.catDiag_pos 2 c)

/-- It is open at every facet request, directly (every slot of the request is
positive). -/
theorem catFrame_openAt_facetRequest {e₀ : Fin (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ}
    {ε : ℚ} (hpt : FacetPoint e₀ y₀) (hε : 0 < ε) :
    (catFrame 2).OpenAt (facetRequest e₀ y₀ ε) := by
  intro c
  rw [SegmentWalls.coordsAt_catFrame_apply]
  refine div_pos ?_ (FibreCaterpillar.catDiag_pos 2 c)
  by_cases hc : c = e₀
  · subst hc
    rw [facetRequest_self]
    exact hε
  · rw [facetRequest_of_ne y₀ ε hc]
    exact hpt.2 c hc

/-- The caterpillar class has multiplicity one, hence is odd. -/
theorem catFrame_isOdd : (FrameClass.mk (catFrame 2)).IsOdd :=
  ⟨1, odd_one, by
    rw [CrossCoreTransport.FrameClass.absMult_mk, Nat.cast_one]
    exact FibreCaterpillar.caterpillarMember_absMult 2 fun _ ↦ 1⟩

/-- **The antecedent of the machine is inhabited at a concrete genus-six step, and
`FacetParity`'s quantifier is not empty there.**  At the caterpillar step `cat_step`
there is a facet datum, and at its facet point some facet limit -- the limit of the
caterpillar frame itself -- has a **nonempty** odd fibre on the caterpillar side.  So
`FacetParity catCubicCore.core catLoopCore.core 4 y₀` ties the far side's count at
that limit to a nonzero count on the caterpillar side; it is not a statement about
an empty index. -/
theorem cat_facetParity_domain :
    ∃ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
      FacetDatum catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε ∧
        ∃ l : FacetLimit catCubicCore.core catLoopCore.core y₀ (2 + 2),
          0 < Nat.card {x : FrameClass catCubicCore.core (2 + 2) //
            x.IsOdd ∧ SpecializesLeft x l} := by
  obtain ⟨e₀, y₀, ε, hd⟩ := exists_facetDatum cat_step (2 + 2)
  let w : Regrowth catCubicCore.core y₀ (2 + 2) :=
    ⟨catFrame 2, e₀, catFrame_degenerateAt_facet hd.point⟩
  refine ⟨e₀, y₀, ε, hd, FacetLimit.ofLeft w, ?_⟩
  have : Nonempty {x : FrameClass catCubicCore.core (2 + 2) //
      x.IsOdd ∧ SpecializesLeft x (FacetLimit.ofLeft (c' := catLoopCore.core) w)} :=
    ⟨⟨FrameClass.mk (catFrame 2), catFrame_isOdd, w, rfl, rfl⟩⟩
  exact Nat.card_pos

/-- The same witness, on the request side of the machine: the caterpillar class is an
open odd class at the facet request, and `μ_c` sends it to the caterpillar's facet
limit. -/
theorem cat_specializeLeft {e₀ : Fin (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ} {ε : ℚ}
    (hd : FacetDatum catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε) :
    hd.specializeLeft ⟨FrameClass.mk (catFrame 2), catFrame_openAt_facetRequest hd.point hd.pos,
        catFrame_isOdd⟩ =
      FacetLimit.ofLeft ⟨catFrame 2, e₀, catFrame_degenerateAt_facet hd.point⟩ :=
  (hd.specializeLeft_eq_iff _ _).mpr ⟨_, rfl, rfl⟩

/-! Two `example`s: a facet point and a regrowth in the domain of
`FacetParity`'s quantifier, at the genus-six caterpillar step. -/

example {e₀ : Fin (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ} (hpt : FacetPoint e₀ y₀) :
    Nonempty (Regrowth catCubicCore.core y₀ (2 + 2)) :=
  ⟨⟨catFrame 2, e₀, catFrame_degenerateAt_facet hpt⟩⟩

example : ∃ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
    FacetDatum catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε ∧
      Nonempty (FacetLimit catCubicCore.core catLoopCore.core y₀ (2 + 2)) := by
  obtain ⟨e₀, y₀, ε, hd⟩ := exists_facetDatum cat_step (2 + 2)
  exact ⟨e₀, y₀, ε, hd,
    ⟨FacetLimit.ofLeft ⟨catFrame 2, e₀, catFrame_degenerateAt_facet hd.point⟩⟩⟩

/-- **The composite, applied at the caterpillar step**, with `FacetParity` supplied as
a hypothesis: the per-step obligation of `TypeChangeSupplyPositive 4 10 15` there. -/
theorem cat_step_obligation_of_facetParity
    (hpar : ∀ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
      FacetDatum catCubicCore.core catLoopCore.core (2 + 2) e₀ y₀ ε →
        FacetParity catCubicCore.core catLoopCore.core (2 + 2) y₀) :
    ∃ y y' : Fin (6 * 2 + 3) → ℚ, PositiveGeneral catCubicCore.core (2 + 2) y ∧
      PositiveGeneral catLoopCore.core (2 + 2) y' ∧
        CountTransportLink.CountLink (2 + 2) catCubicCore.core y catLoopCore.core y' :=
  typeChangeSupplyPositive_step_of_facetParity cat_step hpar

end GenusSix

/-! ## 9.  Integration: the count's positive assembly with the type-change half replaced -/

/-- **`CountSchedule.C34 2`, with `TypeChangeSupplyPositive` replaced by the per-limit
parity at every facet datum of every genus-six Whitehead step.**  This is
`SimpleWallSupply.c34_genusSix_simple` composed with
`typeChangeSupplyPositive_of_facetParity`: the facet machine is consumed by the
assembly, and its only input on the type-change side is `FacetParity`. -/
theorem c34_genusSix_of_facetParity
    (hcone : SimpleWallSupply.InConeSupplySimple (2 + 2) (4 * 2 + 2) (6 * 2 + 3))
    (hfacet : ∀ c c' : CubicCore (4 * 2 + 2) (6 * 2 + 3), Step c c' →
      ∀ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
        FacetDatum c.core c'.core (2 + 2) e₀ y₀ ε → FacetParity c.core c'.core (2 + 2) y₀)
    (request : Fin (6 * 2 + 3) → ℚ) (hreqpos : ∀ i, 0 < request i)
    (hbase : StepSupplyReduction.GeneralRequest (FibreCaterpillar.catCore 2) (2 + 2) request)
    (classification : CaterpillarBallot.BallotClassification 2 request) :
    CountSchedule.C34 2 :=
  SimpleWallSupply.c34_genusSix_simple hcone (typeChangeSupplyPositive_of_facetParity hfacet)
    request hreqpos hbase classification

end DraismaVargas.Count.FacetMachine
