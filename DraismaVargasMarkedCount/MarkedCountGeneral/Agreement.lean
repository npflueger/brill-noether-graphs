module

public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame
public import DraismaVargasMarkedCount.MarkedCountGeneral.NilFrame
public import DraismaVargasMarkedCount.MarkedCount.Correspondence

@[expose] public section

/-!
# Agreement with the marked count at ramification one (type 1) and with the integer count (no marks)

A typed frame has marks of types `aⱼ`, each satisfying (D4′): `r(uⱼ) ≥ aⱼ` and `m(uⱼ) ≥ aⱼ + 1`;
its multiplicity is `D det A / 2^{l*(T)}`, where `l*(T)` counts the leaves of `T` other than the
images of the ramified marks.

**Type 1 is the ramification-one count** (namespace `DraismaVargas.Count.MarkedCount`, written
`MarkedCount` below). With every type equal to `1`, a typed frame **is** a `MarkedCount.MarkedFrame`
(`typedFrameEquiv`): (D4′) at type `1` is `MarkedCount`'s `ramified` plus `m(u) ≥ 2`, which
`MarkedCount` proves from Riemann--Hurwitz (`MarkedFrame.two_le_markIndex`), and the type excess is
`0` (`typeExcess_one`), so the full-dimensionality is `MarkedCount`'s (`MarkedFullDim.castExcess`).
The isomorphisms are the same (`TypedFrameIso.toMarked`, `.ofMarked`), so are the classes
(`typedFrameClassEquiv`), the coordinates and openness (definitionally), and **so is the
multiplicity** (`typedSignedMult_ofMarkedFrame`): `MarkedCount`'s `∏ⱼ r(uⱼ) · D det A / 2^{l(T)}`
equals the typed `D det A / 2^{l*(T)}`. This is the one place where the two conventions meet, and it
is a theorem here, not a remark: at a marked frame of ramification one `r(u) ∈ {1, 2}`, and
`r(u) = 2` exactly when `φ(u)` is a leaf (a ramified mark either folds over a leaf or lies over a
divalent vertex, the local structure at a ramified mark for `a = 1`), which is read off the lollipop
regrowth (`ramificationFactor_eq_two_pow`). Hence `typedCount_one_eq_markedCount`.

**Type 0 and no marks.** A type-`0` mark is an unramified mark kept in the core.
Its count is related to the count without it by the drop lemma (module `Drop`).
With no marks at all, a typed frame is a `Frame` of the integer count
(`typedCount_nil_eq_openMultCount`, proved in module `NilFrame`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}

/-! ## 1.  Frames of type 1 are the marked frames of `MarkedCount` -/

@[simp] theorem typeExcess_one : typeExcess (fun _ : Fin k ↦ 1) = 0 := by
  simp [typeExcess]

/-- A marked frame of `MarkedCount` as a typed frame of type `1` at every mark. -/
def ofMarkedFrame (κ : MarkedFrame core mark degree) :
    TypedFrame core mark (fun _ ↦ 1) degree where
  target := κ.target
  data := κ.data
  markSource := κ.markSource
  fullDim := κ.fullDim.castExcess typeExcess_one.symm
  ident := κ.ident
  typed j := ⟨by exact_mod_cast κ.ramified j, κ.two_le_markIndex j⟩

/-- A typed frame of type `1` at every mark as a marked frame of `MarkedCount`. -/
def toMarkedFrame (κ : TypedFrame core mark (fun _ ↦ 1) degree) :
    MarkedFrame core mark degree where
  target := κ.target
  data := κ.data
  markSource := κ.markSource
  fullDim := κ.fullDim.castExcess typeExcess_one
  ident := κ.ident
  ramified j := by exact_mod_cast (κ.typed j).1

/-- **Typed frames of type `1` are the marked frames of `MarkedCount`.** -/
def typedFrameEquiv : TypedFrame core mark (fun _ ↦ 1) degree ≃ MarkedFrame core mark degree where
  toFun := toMarkedFrame
  invFun := ofMarkedFrame
  left_inv _ := rfl
  right_inv _ := rfl

/-- An isomorphism of `MarkedCount` frames is a typed isomorphism. -/
def TypedFrameIso.ofMarked {κ κ' : MarkedFrame core mark degree} (iso : MarkedFrameIso κ κ') :
    TypedFrameIso (ofMarkedFrame κ) (ofMarkedFrame κ') :=
  ⟨iso.datum, iso.mark, iso.overCore_vertex, iso.overCore_row⟩

/-- A typed isomorphism of type-`1` frames is an isomorphism of `MarkedCount` frames. -/
def TypedFrameIso.toMarked {κ κ' : TypedFrame core mark (fun _ ↦ 1) degree}
    (iso : TypedFrameIso κ κ') : MarkedFrameIso (toMarkedFrame κ) (toMarkedFrame κ') :=
  ⟨iso.datum, iso.mark, iso.overCore_vertex, iso.overCore_row⟩

/-- **The classes agree.** -/
def typedFrameClassEquiv :
    TypedFrameClass core mark (fun _ ↦ 1) degree ≃ MarkedFrameClass core mark degree :=
  Quot.congr typedFrameEquiv fun _ _ ↦
    ⟨fun h ↦ h.elim fun iso ↦ ⟨iso.toMarked⟩, fun h ↦ h.elim fun iso ↦ ⟨TypedFrameIso.ofMarked iso⟩⟩

@[simp] theorem typedFrameClassEquiv_mk (κ : TypedFrame core mark (fun _ ↦ 1) degree) :
    typedFrameClassEquiv (TypedFrameClass.mk κ) = MarkedFrameClass.mk (toMarkedFrame κ) := rfl

theorem coordsAt_ofMarkedFrame (κ : MarkedFrame core mark degree) (y : Fin p → ℚ) :
    (ofMarkedFrame κ).coordsAt y = κ.coordsAt y := rfl

theorem openAt_ofMarkedFrame (κ : MarkedFrame core mark degree) (y : Fin p → ℚ) :
    (ofMarkedFrame κ).OpenAt y ↔ κ.OpenAt y := Iff.rfl

/-! ## 2.  The multiplicities agree -/

/-- The ramification factor is an isomorphism invariant (`MarkedCount`'s `markedAbsMult_eq`, first
step). -/
theorem ramificationFactor_map {κ κ' : MarkedFrame core mark degree} (iso : MarkedFrameIso κ κ') :
    κ'.ramificationFactor = κ.ramificationFactor := by
  unfold MarkedFrame.ramificationFactor
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [← iso.mark j, iso.markRamification_map]

section Lollipop

open DraismaVargas.Count.MarkedCount.Lollipops
open DraismaVargas.Count.MarkedCount.Restrict

/-- **At a restriction, the ramified leaf images are the folds** (the local structure at a ramified
mark, at `a = 1`): `φ'(u_j)` is a leaf of `T'` iff `φ(u_j)` is divalent in `T` iff `r_φ(u_j) = 1`
iff `r_{φ'}(u_j) = 2`; distinct marks have distinct images (`xV_injective`). -/
theorem card_ramifiedLeafImages_restrictFrame (hc : IsMarkedCubic core mark)
    (f : SegmentWalls.Frame (attachLollipops core mark) degree) :
    (ofMarkedFrame (restrictFrame hc f)).ramifiedLeafImages.card =
      (Finset.univ.filter fun j ↦ markRamification (restrictFrame hc f).data
        ((restrictFrame hc f).markSource j) = 2).card := by
  classical
  set M := f.member 0
  set R := restrictFrame hc f
  have hLeaf : ∀ j, Count.IsLeafVertex R.target (R.markSource j).1.1 ↔
      (GluingDatum.incidentEdges (xV M j)).card = 2 := by
    intro j
    have hK := card_kept_at M hc (xV_mem_Keep M j)
    rw [show (if xV M j ∈ Set.range (xV M) then 1 else 0) = 1 by simp] at hK
    change (GluingDatum.incidentEdges (vRestrict (hKeep := Keep_nonempty M) (xV M j)
      (xV_mem_Keep M j))).card = 1 ↔ _
    rw [card_incidentEdges_restrict]
    change ((GluingDatum.incidentEdges (xV M j)).filter (KeptEdge (Keep M))).card = 1 ↔ _
    omega
  have hFold : ∀ j, markRamification R.data (R.markSource j) = 2 ↔
      (GluingDatum.incidentEdges (xV M j)).card = 2 := by
    intro j
    have h1 : M.data.localRamification (markV M j).1.1 ⟨(markV M j).1.2, (markV M j).2⟩ = 1 ↔
        (GluingDatum.incidentEdges (xV M j)).card = 2 := markRamification_eq_one_iff M j
    have h := localRamification_markSource M hc j
    change (rData M).localRamification (markSource M j).1.1
      ⟨(markSource M j).1.2, (markSource M j).2⟩ = 2 ↔ _
    rw [h, ← h1]
    omega
  have hInj : Function.Injective fun j ↦ (R.markSource j).1.1 := by
    intro i j h
    exact xV_injective M hc (congrArg Subtype.val h)
  unfold TypedFrame.ramifiedLeafImages
  change (((Finset.univ.filter fun j : Fin k ↦ 0 < (fun _ ↦ 1 : Fin k → ℕ) j).image
    fun j ↦ (R.markSource j).1.1).filter fun x ↦ Count.IsLeafVertex R.target x).card = _
  rw [show (Finset.univ.filter fun j : Fin k ↦ 0 < (fun _ ↦ 1 : Fin k → ℕ) j) = Finset.univ by
    ext j; simp, Finset.filter_image, Finset.card_image_of_injective _ hInj]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hLeaf j).trans (hFold j).symm

end Lollipop

/-- **The ramification factor of a `MarkedCount` frame is `2^{#ramified leaf images}`**: its
`∏ r(u)` is `2^{#folds}`. Transported from the restriction of the lollipop regrowth, which is
isomorphic to `κ` (`restrictFrame_regrowFrame`). -/
theorem ramificationFactor_eq_two_pow (hc : IsMarkedCubic core mark)
    (κ : MarkedFrame core mark degree) :
    κ.ramificationFactor = 2 ^ (ofMarkedFrame κ).ramifiedLeafImages.card := by
  obtain ⟨iso⟩ := restrictFrame_regrowFrame hc κ
  rw [ramificationFactor_map iso, ramificationFactor_restrictFrame,
    ← card_ramifiedLeafImages_restrictFrame hc,
    (TypedFrameIso.ofMarked iso).card_ramifiedLeafImages]

/-- **The typed multiplicity is `MarkedCount`'s at type `1`**, signed:
`D det A / 2^{l*} = (∏ r) D det A / 2^l`. -/
theorem typedSignedMult_ofMarkedFrame (hc : IsMarkedCubic core mark)
    (κ : MarkedFrame core mark degree) :
    (ofMarkedFrame κ).typedSignedMult = κ.markedSignedMult := by
  rw [TypedFrame.typedSignedMult_eq, MarkedFrame.markedSignedMult,
    ramificationFactor_eq_two_pow hc]
  push_cast
  rfl

theorem typedAbsMult_ofMarkedFrame (hc : IsMarkedCubic core mark)
    (κ : MarkedFrame core mark degree) :
    (ofMarkedFrame κ).typedAbsMult = κ.markedAbsMult := by
  rw [TypedFrame.typedAbsMult, typedSignedMult_ofMarkedFrame hc, MarkedFrame.markedAbsMult]

/-- **The typed count at type `1` is `MarkedCount`'s marked count.** -/
theorem typedCount_one_eq_markedCount (hc : IsMarkedCubic core mark) (y : Fin p → ℚ) :
    typedCount core mark (fun _ ↦ 1) y degree = markedCount core mark y degree := by
  let e : TypedFibre core mark (fun _ ↦ 1) y degree ≃ MarkedFibre core mark y degree :=
    typedFrameClassEquiv.subtypeEquiv fun x ↦ by
      induction x using Quot.ind with
      | mk κ => exact Iff.rfl
  unfold typedCount markedCount
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun x ↦ ?_
  obtain ⟨x, hx⟩ := x
  induction x using Quot.ind with
  | mk κ =>
    change κ.typedAbsMult = (toMarkedFrame κ).markedAbsMult
    exact typedAbsMult_ofMarkedFrame hc (toMarkedFrame κ)

/-! ## 3.  No marks: the frames of the integer count -/

/-- **With no marks, the typed count is the weighted count of the integer count**. With `k = 0` the
mark set is empty, so the marked notions are the unmarked ones (`MarkedCount`'s
`markedStablePathEmptyEquiv`, `markedBranchVertexEmptyEquiv`), `MarkedFullDim` with excess `0` is
`FullDimensionalSourcePresentation` field for field (`markValency` is vacuous, `pathEnds` is
`HasPathEnds`), `MarkedCoreIdentification` is `CoreIdentification`, `TypedFrameIso` is
`FrameIso` (through `branchVertexEquiv` and `stablePathEquiv`), no leaf is a ramified image, so
`typedSignedMult` is Part II's `signedMult`; then `IntegerCount.openMultCount_cast_eq_frameSum`.

*Proof.* `NilFrame.typedCount_nil_eq_openMultCount'`: the maps `TypedFrame.toFrame` and
`ofFrame` are inverse up to isomorphism (`ofFrame_toFrameIso`, `toFrame_ofFrameIso`), carry
isomorphisms to isomorphisms, and keep the coordinates and the multiplicity. -/
theorem typedCount_nil_eq_openMultCount (core : Core n p) (mark : Fin 0 → Fin n)
    (types : Fin 0 → ℕ) (y : Fin p → ℚ) (degree : ℕ) :
    typedCount core mark types y degree =
      (IntegerCount.openMultCount core y degree : ℚ) :=
  typedCount_nil_eq_openMultCount' core mark types y degree

end DraismaVargas.Count.MarkedCountGeneral
