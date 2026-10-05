module

public import DraismaVargasCount.GeometricCount
public import DraismaVargasCount.GeometricSegmentWalls

@[expose] public section

/-!
# Counting the open odd geometric fibre through an indexed family of members

**Source.**  Vargas, Part II, the proof of the main theorem (`sec-proof-main-theorems`),
where the count over the caterpillar of loops is read off the Catalan-many morphisms of
`prop-divisors-on-chain`.  This module is the *interface*
between a family of explicitly constructed fibre members and the number
`GeometricFibre.openOddCount`; the base count over the caterpillar of loops
(`CaterpillarBallotCount`, step 1 of `Assembly`) uses it to turn "here are `k`
pairwise non-isomorphic open members of odd multiplicity" into "`openOddCount = k`".

Everything here is proved for an **abstract** `{core : Core n p}` and an
abstract request: no concrete graph, no concrete divisor, and no `simp` or
`convert` on either.  Downstream uses at the caterpillar are then syntactic
applications.

## What is proved

* `GeometricFibre.OpenOdd core y degree` -- the open odd subfibre as a type,
  with `openOddCount` its `Nat.card` by `rfl`
  (`GeometricFibre.openOddCount_eq_card_openOdd`), a `Finite` instance inherited
  from `GeometricFibre.instFinite`, the constructor
  `GeometricFibre.clsOpenOdd`, and its surjectivity
  (`GeometricFibre.exists_member_of_openOdd`).
* `GeometricFibre.card_le_openOddCount` -- **the lower bound.**  An indexed
  family of members, each open and of odd multiplicity, whose *classes* are
  pairwise distinct, gives `Nat.card ι ≤ openOddCount core y degree`.  No
  finiteness of `ι` is needed (`Nat.card` of an infinite type is `0`).
* `GeometricFibre.openOddCount_le_card` -- **the upper bound.**  The same family,
  with `ι` finite and with every open odd member isomorphic to some `f i`, gives
  `openOddCount core y degree ≤ Nat.card ι`.
* `GeometricFibre.openOddCount_eq_card` -- the two together, and
  `GeometricFibre.openOddEquiv`, the underlying **bijection**
  `ι ≃ OpenOdd core y degree` of which it is the cardinality shadow.
* `GeometricFibre.openOddCount_le_oddCount` -- the open odd count never exceeds
  the odd count.  Combined with `GeometricSegmentWalls.oddCount_eq` (the odd
  count is request-independent) this bounds `openOddCount` at *every* request by
  the odd count at *any* request.
* `FibreMember.coordsMultiset` and `GeometricFibre.coordsMultiset` -- **a class
  invariant that separates members.**  A geometric isomorphism matches
  coordinate vectors along the induced permutation `GeometricMemberIso.column`
  of the slots (`GeometricMemberIso.coords_column`), so the *multiset* of
  coordinates descends to the quotient.  `cls_ne_cls_of_coordsMultiset_ne` and
  `cls_injective_of_coordsMultiset_injective` are the separation criteria this
  yields; `cls_ne_cls_of_absMult_ne` is the weaker multiplicity criterion, which
  cannot separate the ballot members over the caterpillar of loops, since they all
  have multiplicity one.
* `SegmentWalls.Frame.coordsAt_smul` and
  `GeometricFibre.openOddCount_smul` -- **the open odd count is invariant under
  positive rescaling of the request.**  `Frame.coordsAt` is
  `matrix⁻¹.mulVec (y ∘ slot)`, hence linear in `y`, so scaling the request by
  `c > 0` scales every coordinate vector by `c` and preserves openness; the
  multiplicity belongs to the frame and does not move at all.  This is a
  genuine constancy statement over the positive orthant *along rays*; it is not
  the wall-free constancy of `GeometricSegmentWalls.openOddCount_eq_of_no_wall`,
  and neither implies the other.

## What is NOT proved here (every surviving hypothesis, explicitly)

* **Nothing is counted.**  `card_le_openOddCount`, `openOddCount_le_card` and
  `openOddCount_eq_card` are *reductions*: each takes the family `f` and its
  properties as hypotheses and asserts nothing about their existence.  In
  particular this module does not construct a single member; members over the
  caterpillar of loops are constructed in `FibreCaterpillar` (`caterpillarMember`)
  and `BallotCoreIdentification` (`ballotFamily`).
* **No injectivity is established.**  `cls_injective_of_coordsMultiset_injective`
  reduces injectivity of `i ↦ cls (f i)` to injectivity of
  `i ↦ (f i).coordsMultiset`; whether the latter holds for any particular family
  is not addressed.
* **No surjectivity is established.**  The hypothesis
  `∀ member, member.Open → member.HasOddMult → ∃ i, cls (f i) = cls member` of
  `openOddCount_le_card` is exactly a classification statement (over the
  caterpillar of loops, the exhaustion half of Part II, `prop-caterpillar-ballot`)
  and is assumed here, never proved.  In genus six over the caterpillar of loops it
  is proved in `CaterpillarAllMembers`.
* `openOddCount_smul` is invariance along a ray only: it says nothing about two
  positive requests that are not positive multiples of one another.
-/

namespace DraismaVargas.Count

open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  A class invariant strong enough to separate members

`GeometricMemberIso.coords_column` says that an isomorphism over the core
matches the two coordinate vectors along a permutation of the slots.  The
multiset of coordinates is therefore an invariant of the geometric class, and
it is the invariant the base count needs: the ballot-parametrised caterpillar
members all have multiplicity one, so `absMult` cannot separate them, while
their coordinate vectors differ because the diagonal of the length matrix
records the slopes. -/

namespace FibreMember

/-- The multiset of coordinates of a member, with multiplicity, over all slots. -/
noncomputable def coordsMultiset (member : FibreMember core y degree) : Multiset ℚ :=
  (Finset.univ : Finset (Fin p)).val.map member.coords

theorem coordsMultiset_def (member : FibreMember core y degree) :
    member.coordsMultiset = (Finset.univ : Finset (Fin p)).val.map member.coords := rfl

theorem card_coordsMultiset (member : FibreMember core y degree) :
    Multiset.card member.coordsMultiset = p := by
  rw [coordsMultiset_def, Multiset.card_map]
  simp

end FibreMember

/-- **The coordinate multiset is a geometric class invariant.** -/
theorem coordsMultiset_eq_of_geometricIso {first second : FibreMember core y degree}
    (iso : GeometricMemberIso first second) :
    first.coordsMultiset = second.coordsMultiset := by
  have hfun : second.coords ∘ iso.column = first.coords := funext iso.coords_column
  have hperm : Multiset.map (⇑iso.column) (Finset.univ : Finset (Fin p)).val =
      (Finset.univ : Finset (Fin p)).val := by
    -- abstract `Fin p`, no concrete vertex type is unfolded here
    simp
  calc first.coordsMultiset
      = Multiset.map (second.coords ∘ iso.column) (Finset.univ : Finset (Fin p)).val := by
        rw [FibreMember.coordsMultiset_def, hfun]
    _ = Multiset.map second.coords
          (Multiset.map (⇑iso.column) (Finset.univ : Finset (Fin p)).val) :=
        (Multiset.map_map _ _ _).symm
    _ = second.coordsMultiset := by rw [hperm, FibreMember.coordsMultiset_def]

namespace GeometricFibre

/-- The coordinate multiset, read on the geometric quotient. -/
noncomputable def coordsMultiset (c : GeometricFibre core y degree) : Multiset ℚ :=
  Quotient.liftOn c FibreMember.coordsMultiset
    fun _ _ h ↦ h.elim fun iso ↦ coordsMultiset_eq_of_geometricIso iso

@[simp] theorem coordsMultiset_cls (member : FibreMember core y degree) :
    coordsMultiset (cls member) = member.coordsMultiset := rfl

/-- **Separation by coordinates.**  Two members whose coordinate multisets differ
are not isomorphic over the core. -/
theorem cls_ne_cls_of_coordsMultiset_ne {first second : FibreMember core y degree}
    (h : first.coordsMultiset ≠ second.coordsMultiset) : cls first ≠ cls second := by
  intro hEq
  exact h (by rw [← coordsMultiset_cls first, hEq, coordsMultiset_cls])

/-- The packaged form: a family separated by coordinate multisets is separated by
classes.  This has the shape of the injectivity statement for the ballot family over
the caterpillar of loops (distinct slope sequences give distinct classes). -/
theorem cls_injective_of_coordsMultiset_injective {ι : Type*}
    (f : ι → FibreMember core y degree)
    (h : Function.Injective fun i ↦ (f i).coordsMultiset) :
    Function.Injective fun i ↦ cls (f i) := by
  intro a b hab
  exact h (by simpa using congrArg coordsMultiset hab)

/-- **Separation by multiplicity.**  It cannot separate the ballot members over the
caterpillar of loops, which all have multiplicity one. -/
theorem cls_ne_cls_of_absMult_ne {first second : FibreMember core y degree}
    (h : first.absMult ≠ second.absMult) : cls first ≠ cls second := by
  intro hEq
  exact h (by rw [← absMult_cls first, hEq, absMult_cls])

/-! ## 2.  The open odd subfibre as a type -/

/-- The open classes of odd multiplicity, as a type.  `openOddCount` is its
`Nat.card`. -/
abbrev OpenOdd (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Type 1 :=
  {c : GeometricFibre core y degree // c.Open ∧ c.IsOdd}

theorem openOddCount_eq_card_openOdd (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    openOddCount core y degree = Nat.card (OpenOdd core y degree) := rfl

/-- The class of an open member of odd multiplicity. -/
def clsOpenOdd (member : FibreMember core y degree) (hOpen : member.Open)
    (hOdd : member.HasOddMult) : OpenOdd core y degree :=
  ⟨cls member, hOpen, (isOdd_cls_iff member).mpr hOdd⟩

@[simp] theorem clsOpenOdd_val (member : FibreMember core y degree) (hOpen : member.Open)
    (hOdd : member.HasOddMult) : (clsOpenOdd member hOpen hOdd).1 = cls member := rfl

/-- Every open odd class is the class of an open member of odd multiplicity. -/
theorem exists_member_of_openOdd (c : OpenOdd core y degree) :
    ∃ (member : FibreMember core y degree) (hOpen : member.Open) (hOdd : member.HasOddMult),
      clsOpenOdd member hOpen hOdd = c := by
  obtain ⟨c, hOpen, hOdd⟩ := c
  obtain ⟨member, rfl⟩ := cls_surjective c
  exact ⟨member, hOpen, (isOdd_cls_iff member).mp hOdd, rfl⟩

/-! ## 3.  The count through an indexed family -/

/-- **The lower bound.**  A family of open members of odd multiplicity with
pairwise distinct classes injects into the open odd subfibre. -/
theorem card_le_openOddCount {ι : Type*} (f : ι → FibreMember core y degree)
    (hOpen : ∀ i, (f i).Open) (hOdd : ∀ i, (f i).HasOddMult)
    (hInj : Function.Injective fun i ↦ cls (f i)) :
    Nat.card ι ≤ openOddCount core y degree := by
  refine Nat.card_le_card_of_injective (fun i ↦ clsOpenOdd (f i) (hOpen i) (hOdd i)) ?_
  intro a b hab
  exact hInj (congrArg Subtype.val hab)

/-- **The upper bound.**  If every open member of odd multiplicity is isomorphic
over the core to a member of the family, the family surjects onto the open odd
subfibre. -/
theorem openOddCount_le_card {ι : Type*} [Finite ι] (f : ι → FibreMember core y degree)
    (hOpen : ∀ i, (f i).Open) (hOdd : ∀ i, (f i).HasOddMult)
    (hSurj : ∀ member : FibreMember core y degree, member.Open → member.HasOddMult →
      ∃ i, cls (f i) = cls member) :
    openOddCount core y degree ≤ Nat.card ι := by
  refine Nat.card_le_card_of_surjective (fun i ↦ clsOpenOdd (f i) (hOpen i) (hOdd i)) ?_
  intro c
  obtain ⟨member, hO, hM, rfl⟩ := exists_member_of_openOdd c
  obtain ⟨i, hi⟩ := hSurj member hO hM
  exact ⟨i, Subtype.ext hi⟩

/-- **The count.**  A classifying family computes `openOddCount` exactly. -/
theorem openOddCount_eq_card {ι : Type*} [Finite ι] (f : ι → FibreMember core y degree)
    (hOpen : ∀ i, (f i).Open) (hOdd : ∀ i, (f i).HasOddMult)
    (hInj : Function.Injective fun i ↦ cls (f i))
    (hSurj : ∀ member : FibreMember core y degree, member.Open → member.HasOddMult →
      ∃ i, cls (f i) = cls member) :
    openOddCount core y degree = Nat.card ι :=
  le_antisymm (openOddCount_le_card f hOpen hOdd hSurj)
    (card_le_openOddCount f hOpen hOdd hInj)

/-- **The bijection.**  A classifying family *is* the open odd subfibre, not
merely a set of the same size.  This is the form in which a classification is best
used (as in `CaterpillarBallot.slopesEquivOpenOdd`): `openOddCount_eq_card` is its
cardinality shadow. -/
noncomputable def openOddEquiv {ι : Type*} (f : ι → FibreMember core y degree)
    (hOpen : ∀ i, (f i).Open) (hOdd : ∀ i, (f i).HasOddMult)
    (hInj : Function.Injective fun i ↦ cls (f i))
    (hSurj : ∀ member : FibreMember core y degree, member.Open → member.HasOddMult →
      ∃ i, cls (f i) = cls member) :
    ι ≃ OpenOdd core y degree :=
  Equiv.ofBijective (fun i ↦ clsOpenOdd (f i) (hOpen i) (hOdd i))
    ⟨fun a b hab ↦ hInj (congrArg Subtype.val hab), by
      intro c
      obtain ⟨member, hO, hM, rfl⟩ := exists_member_of_openOdd c
      obtain ⟨i, hi⟩ := hSurj member hO hM
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp] theorem openOddEquiv_apply {ι : Type*} (f : ι → FibreMember core y degree)
    (hOpen : ∀ i, (f i).Open) (hOdd : ∀ i, (f i).HasOddMult)
    (hInj : Function.Injective fun i ↦ cls (f i))
    (hSurj : ∀ member : FibreMember core y degree, member.Open → member.HasOddMult →
      ∃ i, cls (f i) = cls member) (i : ι) :
    (openOddEquiv f hOpen hOdd hInj hSurj i).1 = cls (f i) := rfl

/-- The open odd count never exceeds the odd count.  Since
`GeometricSegmentWalls.oddCount_eq` makes the right-hand side independent of the
request, this bounds the open odd count at every request by the odd count at any
one request. -/
theorem openOddCount_le_oddCount (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    openOddCount core y degree ≤ oddCount core y degree := by
  refine Nat.card_le_card_of_injective
    (β := {c : GeometricFibre core y degree // c.IsOdd})
    (fun c ↦ ⟨c.1, c.2.2⟩) ?_
  intro a b hab
  exact Subtype.ext
    (congrArg (fun z : {c : GeometricFibre core y degree // c.IsOdd} ↦ z.1) hab)

end GeometricFibre

/-! ## 4.  Positive rescaling of the request -/

namespace SegmentWalls
namespace Frame

/-- **The coordinate vector of a frame is linear in the request.**  This is
immediate from `Frame.coordsAt = matrix⁻¹.mulVec (y ∘ slot)`. -/
theorem coordsAt_smul (k : Frame core degree) (c : ℚ) (y : Fin p → ℚ) :
    k.coordsAt (c • y) = c • k.coordsAt y := by
  show k.matrix⁻¹.mulVec (fun row ↦ (c • y) (k.slot row)) =
    c • k.matrix⁻¹.mulVec (fun row ↦ y (k.slot row))
  rw [show (fun row ↦ (c • y) (k.slot row)) = c • (fun row ↦ y (k.slot row)) from rfl]
  exact Matrix.mulVec_smul _ c _

end Frame
end SegmentWalls

namespace GeometricFibre

/-- Openness of a member over a positively rescaled request is openness of the
member its frame gives over the original request. -/
theorem open_frameOf_member_smul_iff {c : ℚ} (hc : 0 < c) {y : Fin p → ℚ}
    (member : FibreMember core (c • y) degree) :
    member.Open ↔ ((Frame.of member).member y).Open := by
  have hscaled : member.coords = c • (Frame.of member).coordsAt y := by
    rw [← Frame.coordsAt_smul (Frame.of member) c y]
    exact (Frame.coordsAt_of member).symm
  constructor
  · intro h slot
    have := h slot
    rw [hscaled] at this
    exact (mul_pos_iff_of_pos_left hc).mp this
  · intro h slot
    rw [hscaled]
    exact (mul_pos_iff_of_pos_left hc).mpr (h slot)

/-- **The open odd count is invariant under positive rescaling of the request.**
The multiplicity belongs to the frame, and a positive scaling moves every
coordinate vector by the same positive factor. -/
theorem openOddCount_smul (core : Core n p) (degree : ℕ) {c : ℚ} (hc : 0 < c)
    (y : Fin p → ℚ) :
    openOddCount core (c • y) degree = openOddCount core y degree := by
  refine Nat.card_congr (Equiv.subtypeEquiv
    (GeometricSegmentWalls.fibreEquiv core degree (c • y) y) ?_)
  intro a
  refine and_congr ?_
    (GeometricSegmentWalls.isOdd_fibreEquiv core degree (c • y) y a).symm
  obtain ⟨member, rfl⟩ := cls_surjective a
  rw [GeometricSegmentWalls.fibreEquiv_cls, open_cls, open_cls]
  exact open_frameOf_member_smul_iff hc member

end GeometricFibre

end DraismaVargas.Count
