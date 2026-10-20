module

public import DraismaVargasMarkedCount.MarkedCount.MarkedFrame

@[expose] public section

/-!
# The two-point ramified count, module 1: typed marked frames

A **typed marked frame** carries a type `types j : ℕ` at every mark `j`, and satisfies

* **(D4′)**: `r_φ(u_j) ≥ types j` **and** `m(u_j) ≥ types j + 1`
  (`IsTyped`). The second clause is not implied by the first once `types j ≥ 2`: at `g = 2`
  and type `2` there are 456 + 36 full-dimensional frames with `r(u) ≥ 2` and `m(u) = 2` (a
  leaf image with excess change elsewhere, or a divalent image with no excess) that realise
  generic requests but are restrictions of nothing, so it is a field, not a theorem.
  For `types j = 0` both clauses are empty, and the mark is an **unramified mark kept in the
  core**.

The multiplicity is `Mult = D det A / 2^{l*(T)}`, where `l*(T)` is the
number of leaves of the target that are **not** images of marks of positive type
(`leafCountStar`). It is *not* `∏ r(u)^a · D det A / 2^{l(T)}` (false for `a ≥ 2`: a type-`2`
fold has `r(u) = 3` and local factor `2`), and *not* the toric multiplicity of the marked cone
(false for `a ≥ 2`: on computed instances over a genus-four core, its sum over the type-`2`
members is `4`, not `N(4; 2, 0) = 3`); neither reading is used anywhere in this folder.

The dimension count `saturated` is that of the ramification-one marked count, corrected by the
type excess `Σⱼ (types j - 1)`: with `p = 3g - 3 + k` core slots and `d = (g + Σ types + 2)/2`,
`2g + 2d - 5 = p + Σⱼ (types j - 1)` (`MarkedFullDim` at the excess `typeExcess types`). For all
types `1` the excess is `0`, that of the ramification-one count (module `Agreement`).

Everything else is the marked frame of the ramification-one count: a typed frame extends its
`MarkedFrameBase` (target, datum, marks, marked full-dimensionality, and the marked core
identification `MarkedCoreIdentification`) by (D4′), and inherits from it the coordinates
(`coordsAt`, `mulVec_coordsAt`, `coordsAt_eq_of_mulVec`), openness, and the isomorphisms over the
identity of the marked core with their invariance of the coordinates and of openness
(`MarkedFrameBase.Iso.exists_column`, `openAt_iff`).

## Contents

The multiplicity and its two forms (`typedSignedMult_eq`), the invariance of the ramified leaf
images and of the multiplicity under isomorphism (`TypedFrameIso.typedAbsMult_eq`, by
`MarkedFrameBase.Iso.absMult_eq`), the classes, the fibre at a request, and the count
`typedCount`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  Local degree and (D4′) -/

/-- **`m(A)`**, the local degree (index) of the source vertex `A`: the size of its block. -/
def markIndex (data : GluingDatum target degree) (vertex : data.SourceVertex) : ℕ :=
  (data.vertexPartition vertex.1.1).blockCard vertex.1.2

/-- **(D4′)**: ramification at least `a` and local degree at least
`a + 1`. -/
def IsTyped (data : GluingDatum target degree) (vertex : data.SourceVertex) (a : ℕ) : Prop :=
  (a : ℤ) ≤ markRamification data vertex ∧ a + 1 ≤ markIndex data vertex

/-- The type excess `Σⱼ (types j - 1)`, the correction to the dimension count. -/
def typeExcess {k : ℕ} (types : Fin k → ℕ) : ℤ := ∑ j, ((types j : ℤ) - 1)

variable {n p k : ℕ}

/-! ## 2.  Typed frames -/

/-- **A typed marked frame** over the marked core (a marked member of type `types`
without the lengths): a target tree, a gluing datum, the source vertices of the marks, marked
full-dimensionality at the excess `typeExcess types`, the ramification-one marked label (marks to
marks), and (D4′) at every mark. -/
structure TypedFrame (core : Core n p) (mark : Fin k → Fin n) (types : Fin k → ℕ)
    (degree : ℕ) extends MarkedFrameBase core mark (typeExcess types) degree where
  /-- (D4′) at every mark. -/
  typed : ∀ j, IsTyped data (markSource j) (types j)

namespace TypedFrame

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

/-- **The images of the ramified marks that are leaves**: the target vertices excluded from
`l*(T)`. A mark is ramified when its type is positive. -/
noncomputable def ramifiedLeafImages (κ : TypedFrame core mark types degree) :
    Finset κ.target.V := by
  classical
  exact ((Finset.univ.filter fun j ↦ 0 < types j).image fun j ↦ (κ.markSource j).1.1).filter
    fun x ↦ Count.IsLeafVertex κ.target x

theorem ramifiedLeafImages_subset (κ : TypedFrame core mark types degree) :
    κ.ramifiedLeafImages ⊆ Count.leafVertices κ.target := by
  classical
  intro x hx
  unfold ramifiedLeafImages at hx
  rw [Count.mem_leafVertices]
  exact (Finset.mem_filter.mp hx).2

/-- **`l*(T)`**: the leaves of the target other than the images of the
ramified marks. -/
noncomputable def leafCountStar (κ : TypedFrame core mark types degree) : ℕ :=
  Count.leafCount κ.target - κ.ramifiedLeafImages.card

/-- **The signed typed multiplicity**: `Mult(ψ; marks) = D_ψ det A_ψ / 2^{l*(T)}`,
Part II's formula on the marked matrix with the images of the ramified marks not counted as
leaves. -/
noncomputable def typedSignedMult (κ : TypedFrame core mark types degree) : ℚ :=
  (Count.denominatorProduct κ.fullDim.labelling.presentation : ℚ) / 2 ^ κ.leafCountStar *
    κ.matrix.det

/-- **The typed multiplicity** `|Mult(ψ; marks)|`. -/
noncomputable def typedAbsMult (κ : TypedFrame core mark types degree) : ℚ := |κ.typedSignedMult|

/-- **The two forms of the multiplicity**: `D det A / 2^{l*} = 2^{#ramified leaf images} · D det A / 2^{l}`
(`2^{[fold]}` times Part II's formula verbatim on the marked matrix). -/
theorem typedSignedMult_eq (κ : TypedFrame core mark types degree) :
    κ.typedSignedMult =
      (2 : ℚ) ^ κ.ramifiedLeafImages.card *
        Count.signedMult κ.fullDim.labelling.presentation := by
  have hle : κ.ramifiedLeafImages.card ≤ Count.leafCount κ.target :=
    Finset.card_le_card κ.ramifiedLeafImages_subset
  unfold typedSignedMult Count.signedMult leafCountStar
  rw [show Count.leafCount κ.target =
    Count.leafCount κ.target - κ.ramifiedLeafImages.card + κ.ramifiedLeafImages.card by omega]
  rw [Nat.add_sub_cancel, pow_add]
  change _ = _ * (_ / (2 ^ (Count.leafCount κ.target - κ.ramifiedLeafImages.card) *
    2 ^ κ.ramifiedLeafImages.card) * κ.matrix.det)
  field_simp

theorem typedSignedMult_ne_zero (κ : TypedFrame core mark types degree) :
    κ.typedSignedMult ≠ 0 := by
  have hDen : ((Count.denominatorProduct κ.fullDim.labelling.presentation : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Count.denominatorProduct_pos κ.fullDim.labelling.presentation).ne'
  exact mul_ne_zero (div_ne_zero hDen (by positivity)) κ.det_ne_zero

end TypedFrame

/-! ## 3.  Isomorphism over the identity of the marked core -/

/-- **An isomorphism of typed frames over the identity of the marked core**: an isomorphism of
the underlying `MarkedFrameBase`, as for the ramification-one `MarkedFrameIso`. -/
abbrev TypedFrameIso {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
    (first second : TypedFrame core mark types degree) :=
  MarkedFrameBase.Iso first.toMarkedFrameBase second.toMarkedFrameBase

namespace TypedFrameIso

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {first second : TypedFrame core mark types degree}

/-- An isomorphism carries the ramified leaf images onto the ramified leaf images. -/
theorem card_ramifiedLeafImages (iso : TypedFrameIso first second) :
    second.ramifiedLeafImages.card = first.ramifiedLeafImages.card := by
  classical
  refine (Finset.card_bij (fun x _ ↦ iso.datum.targetVertex x) ?_ ?_ ?_).symm
  · intro x hx
    unfold TypedFrame.ramifiedLeafImages at hx ⊢
    obtain ⟨hImg, hLeaf⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hImg
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, hj, ?_⟩,
      (iso.datum.isLeafVertex_map _).mpr hLeaf⟩
    rw [← iso.mark j]
    rfl
  · exact fun _ _ _ _ h ↦ iso.datum.targetVertex.injective h
  · intro x hx
    unfold TypedFrame.ramifiedLeafImages at hx
    obtain ⟨hImg, hLeaf⟩ := Finset.mem_filter.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hImg
    refine ⟨(first.markSource j).1.1, ?_, ?_⟩
    · unfold TypedFrame.ramifiedLeafImages
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
      rw [← iso.datum.isLeafVertex_map]
      rw [← iso.mark j] at hLeaf
      exact hLeaf
    · rw [← iso.mark j]
      rfl

/-- **An isomorphism preserves the typed multiplicity.** -/
theorem typedAbsMult_eq (iso : TypedFrameIso first second) :
    first.typedAbsMult = second.typedAbsMult := by
  unfold TypedFrame.typedAbsMult
  rw [first.typedSignedMult_eq, second.typedSignedMult_eq, abs_mul, abs_mul,
    iso.card_ramifiedLeafImages]
  exact congrArg _ iso.absMult_eq.symm

end TypedFrameIso

/-! ## 4.  Classes, the typed fibre and the typed count -/

/-- **Typed frames up to isomorphism over the marked core.** -/
def TypedFrameClass (core : Core n p) (mark : Fin k → Fin n) (types : Fin k → ℕ)
    (degree : ℕ) : Type 1 :=
  Quot fun first second : TypedFrame core mark types degree ↦
    Nonempty (TypedFrameIso first second)

namespace TypedFrameClass

variable {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

/-- The class of a typed frame. -/
def mk (κ : TypedFrame core mark types degree) : TypedFrameClass core mark types degree :=
  Quot.mk _ κ

theorem mk_surjective :
    Function.Surjective (mk (core := core) (mark := mark) (types := types) (degree := degree)) :=
  Quot.mk_surjective

theorem mk_eq_mk_of_iso {κ κ' : TypedFrame core mark types degree}
    (h : Nonempty (TypedFrameIso κ κ')) : mk κ = mk κ' :=
  Quot.sound h

/-- Openness of a class at a request. -/
def OpenAt (x : TypedFrameClass core mark types degree) (y : Fin p → ℚ) : Prop :=
  Quot.lift (fun κ : TypedFrame core mark types degree ↦ κ.OpenAt y)
    (fun _ _ h ↦ h.elim fun iso ↦ propext (iso.openAt_iff y)) x

/-- The typed multiplicity of a class. -/
noncomputable def typedAbsMult (x : TypedFrameClass core mark types degree) : ℚ :=
  Quot.lift TypedFrame.typedAbsMult (fun _ _ h ↦ h.elim fun iso ↦ iso.typedAbsMult_eq) x

@[simp] theorem openAt_mk (κ : TypedFrame core mark types degree) (y : Fin p → ℚ) :
    (mk κ).OpenAt y ↔ κ.OpenAt y := Iff.rfl

@[simp] theorem typedAbsMult_mk (κ : TypedFrame core mark types degree) :
    (mk κ).typedAbsMult = κ.typedAbsMult := rfl

end TypedFrameClass

/-- **The typed fibre** at `y`: the classes of typed frames open at `y`, i.e. the marked
members of type `types`. -/
def TypedFibre (core : Core n p) (mark : Fin k → Fin n) (types : Fin k → ℕ) (y : Fin p → ℚ)
    (degree : ℕ) : Type 1 :=
  {x : TypedFrameClass core mark types degree // x.OpenAt y}

/-- **The typed count** `N_{types}`: `Σ_{ψ} |Mult(ψ; marks)|` over the typed fibre (the left
side of `typedCount_twiceMarked`). A rational number a priori; it is a `finsum`, which is honest
because the fibre is finite (`Correspondence.finite_typedFibre`). -/
noncomputable def typedCount (core : Core n p) (mark : Fin k → Fin n) (types : Fin k → ℕ)
    (y : Fin p → ℚ) (degree : ℕ) : ℚ :=
  ∑ᶠ x : TypedFibre core mark types y degree, x.1.typedAbsMult

end DraismaVargas.Count.MarkedCountGeneral
