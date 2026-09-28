import DraismaVargasCount.StepSupplyReduction

/-!
# The cross-core member transport

**Source.**  Vargas, Part II (arXiv:2609.09109), the section on changing combinatorial type
(`sec-constructions`).

## Why this file exists

Across a Whitehead step between two cores, the parity of the count is carried by an
equivalence

```
GeometricFibre c.core y degree ≃ GeometricFibre c'.core y' degree
```

matching `Open` with `Open` and `IsOdd` with `IsOdd` -- the input of
`CountTransportLink.countLink_of_oddOpenEquiv`.  The valency-by-valency analysis of a type
change is stated over **one fixed core**, and the Part I object spanning a Whitehead move,
`LocalCases.OuterWalk.TypeChangeLink`, carries no `CoreIdentification` and concludes about
one member's multiplicity.  The cross-core `GeometricFibre` equivalence
`CoreRelabel.relabelEquiv` does not cover every step: the two ends of a step need not be
relabellings of each other (a core with a self-loop is not a relabelling of a loopless one).

This file states the cross-core object, gives it a consumer into the count, and gives it the
producer that relabellings provide.

## The organising observation

`Count.SegmentWalls.Frame core degree` is everything a `FibreMember` carries
except its coordinate vector, and `Frame.memberEquiv` is a bijection
`Frame core degree ≃ FibreMember core y degree` for **every** `y`.  Over one
core, `GeometricSegmentWalls.isoOverCore_member_iff` says two members over `y`
are isomorphic exactly when their frames are `FrameIso`.  So the geometric
fibre has a canonical **request-free** model, `FrameClass core degree`, and
`fibreEquiv` identifies it with `GeometricFibre core y degree` for every `y`.
That is the right home for a cross-core transport, because on it the
multiplicity (`FrameClass.absMult`, hence `FrameClass.IsOdd`) carries no
request at all and only openness (`FrameClass.OpenAt`) does -- which is exactly
the split recorded by `GeometricSegmentWalls.isOdd_fibreEquiv`, which holds
unconditionally.

A `Frame c degree` and a `Frame c' degree` differ **only** in the `ident` field,
and `ident`'s `incidence` equation pins the core down against the datum.  So a
cross-core transport cannot keep the gluing datum fixed unless the two cores are
incidence-isomorphic, i.e. unless a `CoreRelabel.Relabel` exists -- which is the
precise reason the relabelling route is not enough and the object below has to
move the datum.

## What is proved here

* `frameSetoid`, `FrameClass`, `FrameClass.absMult`, `FrameClass.OpenAt`,
  `FrameClass.IsOdd` -- **the request-free model of the geometric fibre**, with
  the multiplicity and the openness predicate descended to it
  (`absMult_eq_of_frameIso`, `openAt_iff_of_frameIso`).
* `fibreEquiv`, `open_fibreEquiv`, `isOdd_fibreEquiv`, `openOddCount_eq_card` --
  the identification with `GeometricFibre core y degree` at every request, and
  the open odd count read on the model.
* `Transport` -- **the object**: an equivalence of the two cores' `FrameClass`es
  preserving `absMult` and matching `OpenAt y` with `OpenAt y'`.
  `Transport.refl`, `.symm`, `.trans` make it a groupoid, so a producer may
  compose a genuine move with a relabelling.
* `Transport.oddOpenEquiv`, `Transport.open_oddOpenEquiv`,
  `Transport.isOdd_oddOpenEquiv`, `Transport.exists_oddOpenEquiv`,
  `Transport.openOddCount_eq`, `Transport.countLink` -- **the consumer**: a
  `Transport` is exactly a `countLink_of_oddOpenEquiv` input, and it gives the
  two open odd counts *equal*, not merely of equal parity.
* `FrameTransport`, `FrameTransport.classEquiv`, `FrameTransport.toTransport` --
  the frame-level presentation a geometric producer would actually build: a map
  on frames, a map back, both respecting `FrameIso`, inverse to each other up to
  `FrameIso`, and preserving `Frame.absMult`.
* `relabelFrameIso`, `relabelFrameRoundTrip`, `ofRelabel`,
  `openAt_relabelFrame`, `transportOfRelabel` -- **the producer from relabellings**:
  every `CoreRelabel.Relabel` gives a `FrameTransport`, and matched requests turn it
  into a `Transport`.
* `slotRelabel`, `slotRelabelDatum`, `transportSlotRelabel`,
  `slotRelabel_ne_self` -- **non-vacuity**, concretely: a `Transport` between two
  cores that are *not the same term*, at every degree and every request, with no
  hypothesis.
* `op_eq_of_step`, `exists_generalRequest_pair` -- the **matched-request**
  observation.  A Whitehead step keeps the slot set `Fin p` and the edge involution and
  moves only the dart-to-vertex map (`CoreOfDarts.op_graph` and
  `CoreRelabel.exists_perm_of_reaches`; `op_eq_of_step` below records it), so the
  geometry of the move is visible only when the two requests are the *same*
  vector, the shared wall being the locus where the moved slot has length zero.
  `exists_generalRequest_pair` -- a positive request general for **two** cores at
  once -- says that such matched requests exist.
* `OpenOddTransport`, `Transport.toOpenOdd`,
  `openOddCount_eq_of_openOddTransport`, `countLink_of_openOddTransport` -- the weaker
  form: an equivalence of the *open odd* classes alone already gives the link, and unlike
  the fibre form it commits one to nothing about the closed or even-multiplicity classes.
* `Transport.ofFibrewise` -- **the producer may work one wall-limit at a time**:
  a transport assembled from a common invariant of the two sides and a fibrewise
  equivalence over it.  This is the shape Draisma--Vargas' argument has, where
  the invariant is the codimension-one limit a frame specializes to at the
  shared wall.

## What is not proved here

* **No `Transport` at an actual Whitehead step is produced.**  The only producer here
  is `transportOfRelabel`, and relabelling-isomorphic endpoints do not cover every step.
  The type changes of the genus-six assembly (`Assembly.typeChanges_genusSix`, step 3) are
  carried instead by a census inside each metric limit (`FacetCensus`, `CensusAssembly`).
* **The non-vacuity witness is not at a Whitehead step.**  `transportSlotRelabel`
  inhabits `Transport` at two different `Core n p`, but those two cores are
  related by a `Relabel`, not by `CoreOfDarts.Step`, and they are not claimed to
  be cubic or connected.  Nothing here exhibits a transport across a genuine
  type change.
* **`Transport` asks for more than parity.**  `Transport.openOddCount_eq` forces the two
  open odd counts to be *equal*; the count needs only that they have the same parity.
  Part II's own wall-crossing statement (`sec-constructions`) is that the
  full-dimensional morphisms specializing to **one** codimension-one limit have
  equal multiplicities and partition equally among the *three* resolutions of
  the 4-valent vertex (Types I, II, III), which is a local, three-way statement
  about one limit, not a two-sided bijection of whole fibres.
  `Transport.ofFibrewise` is the interface at which local statements would assemble into
  the global one, and `OpenOddTransport` is the weaker form.
* **Nothing here relates `FrameClass c degree` and `FrameClass c' degree` for
  `c ≠ c'` except through a `Relabel`.**
* **No genericity of the request is used**: `Transport`, `FrameTransport` and the
  relabel producer assume nothing about `y`, `y'` beyond the matching equation where one
  is stated.
-/

namespace DraismaVargas.Count.CrossCoreTransport

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame NFFrame coordinateWall)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open DraismaVargas.Count.CoreRelabel (Relabel)
open DraismaVargas.Count.StepSupplyReduction (GeneralRequest relabelFrame coordsAt_relabelFrame)

variable {n p degree : ℕ}

/-! ## 1.  The request-free model of the geometric fibre -/

/-- Isomorphic frames carry the same multiplicity.  `Frame.absMult` reads only
the full-dimensionality receipt, so this is `GeometricMemberIso.absMult_eq` at
any request at all. -/
theorem absMult_eq_of_frameIso {core : Core n p} {k l : Frame core degree}
    (i : FrameIso k l) : k.absMult = l.absMult :=
  (i.toMemberIso (fun _ ↦ 0)).absMult_eq

/-- Isomorphic frames are open at the same requests. -/
theorem openAt_iff_of_frameIso {core : Core n p} {k l : Frame core degree}
    (i : FrameIso k l) (y : Fin p → ℚ) : k.OpenAt y ↔ l.OpenAt y :=
  ((k.openAt_iff_open y).trans (i.toMemberIso y).open_iff).trans (l.openAt_iff_open y).symm

/-- Frames over one core, up to isomorphism over that core. -/
def frameSetoid (core : Core n p) (degree : ℕ) : Setoid (Frame core degree) where
  r k l := Nonempty (FrameIso k l)
  iseqv :=
    ⟨fun k ↦ ⟨FrameIso.refl k⟩, fun h ↦ h.elim fun i ↦ ⟨i.symm⟩,
      fun h h' ↦ h.elim fun i ↦ h'.elim fun j ↦ ⟨i.trans j⟩⟩

/-- **The request-free model of the geometric fibre.** -/
def FrameClass (core : Core n p) (degree : ℕ) : Type 1 := Quotient (frameSetoid core degree)

namespace FrameClass

variable {core : Core n p}

/-- The class of a frame. -/
def mk (k : Frame core degree) : FrameClass core degree :=
  Quotient.mk (frameSetoid core degree) k

theorem mk_surjective :
    Function.Surjective (mk (core := core) (degree := degree)) := Quotient.mk_surjective

theorem mk_eq_mk_iff {k l : Frame core degree} :
    mk k = mk l ↔ Nonempty (FrameIso k l) :=
  Quotient.eq (r := frameSetoid core degree)

/-- The multiplicity of a class: request-free, because `Frame.absMult` is. -/
noncomputable def absMult (x : FrameClass core degree) : ℚ :=
  Quotient.liftOn x Frame.absMult fun _ _ h ↦ h.elim absMult_eq_of_frameIso

@[simp] theorem absMult_mk (k : Frame core degree) : (mk k).absMult = k.absMult := rfl

/-- Openness of a class at a request.  This is the *only* request-dependent
piece of the model. -/
def OpenAt (x : FrameClass core degree) (y : Fin p → ℚ) : Prop :=
  Quotient.liftOn x (fun k ↦ k.OpenAt y) fun _ _ h ↦
    h.elim fun i ↦ propext (openAt_iff_of_frameIso i y)

@[simp] theorem openAt_mk (k : Frame core degree) (y : Fin p → ℚ) :
    (mk k).OpenAt y ↔ k.OpenAt y := Iff.rfl

/-- Odd multiplicity, in the existential form `Count.Fibre` uses. -/
def IsOdd (x : FrameClass core degree) : Prop := ∃ j : ℕ, Odd j ∧ x.absMult = j

@[simp] theorem isOdd_mk (k : Frame core degree) :
    (mk k).IsOdd ↔ ∃ j : ℕ, Odd j ∧ k.absMult = j := Iff.rfl

end FrameClass

/-- **The model is the geometric fibre, at every request.** -/
noncomputable def fibreEquiv (core : Core n p) (degree : ℕ) (y : Fin p → ℚ) :
    FrameClass core degree ≃ GeometricFibre core y degree :=
  Quotient.congr (Frame.memberEquiv core degree y) fun k l ↦
    (GeometricSegmentWalls.isoOverCore_member_iff k l y).symm

@[simp] theorem fibreEquiv_mk (core : Core n p) (degree : ℕ) (y : Fin p → ℚ)
    (k : Frame core degree) :
    fibreEquiv core degree y (FrameClass.mk k) = GeometricFibre.cls (k.member y) := rfl

@[simp] theorem fibreEquiv_symm_cls (core : Core n p) (degree : ℕ) (y : Fin p → ℚ)
    (m : FibreMember core y degree) :
    (fibreEquiv core degree y).symm (GeometricFibre.cls m) = FrameClass.mk (Frame.of m) := rfl

theorem open_fibreEquiv (core : Core n p) (degree : ℕ) (y : Fin p → ℚ)
    (x : FrameClass core degree) : (fibreEquiv core degree y x).Open ↔ x.OpenAt y := by
  induction x using Quotient.inductionOn with
  | h k => exact (k.openAt_iff_open y).symm

theorem isOdd_fibreEquiv (core : Core n p) (degree : ℕ) (y : Fin p → ℚ)
    (x : FrameClass core degree) : (fibreEquiv core degree y x).IsOdd ↔ x.IsOdd := by
  induction x using Quotient.inductionOn with
  | h k => exact GeometricFibre.isOdd_cls_iff (k.member y)

/-- The open odd count, read on the request-free model. -/
theorem openOddCount_eq_card (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    GeometricFibre.openOddCount core y degree =
      Nat.card {x : FrameClass core degree // x.OpenAt y ∧ x.IsOdd} :=
  (Nat.card_congr (Equiv.subtypeEquiv (fibreEquiv core degree y) fun x ↦
    and_congr (open_fibreEquiv core degree y x).symm
      (isOdd_fibreEquiv core degree y x).symm)).symm

/-- The model is finite, being the geometric fibre. -/
instance instFinite (core : Core n p) (degree : ℕ) : Finite (FrameClass core degree) :=
  Finite.of_equiv _ (fibreEquiv core degree (fun _ ↦ 0)).symm

theorem card_frameClass (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Nat.card (FrameClass core degree) = Nat.card (GeometricFibre core y degree) :=
  Nat.card_congr (fibreEquiv core degree y)

/-! ## 2.  The object -/

/-- **The cross-core transport.**  An equivalence of the two cores' request-free
fibres that preserves the multiplicity outright and matches openness at the two
chosen requests.  The two cores are unrelated: nothing here asks for a
`Relabel`, a `CoreIso`, or any map between them. -/
structure Transport (c c' : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) where
  /-- the bijection of classes -/
  equiv : FrameClass c degree ≃ FrameClass c' degree
  /-- multiplicities are preserved -/
  absMult : ∀ x, (equiv x).absMult = x.absMult
  /-- openness is matched at the two requests -/
  open_iff : ∀ x, (equiv x).OpenAt y' ↔ x.OpenAt y

namespace Transport

variable {c c' c'' : Core n p} {y y' y'' : Fin p → ℚ}

theorem isOdd (T : Transport c c' degree y y') (x : FrameClass c degree) :
    (T.equiv x).IsOdd ↔ x.IsOdd := by
  simp only [FrameClass.IsOdd, T.absMult]

/-- The identity transport. -/
def refl (c : Core n p) (degree : ℕ) (y : Fin p → ℚ) : Transport c c degree y y where
  equiv := Equiv.refl _
  absMult _ := rfl
  open_iff _ := Iff.rfl

/-- The inverse transport. -/
def symm (T : Transport c c' degree y y') : Transport c' c degree y' y where
  equiv := T.equiv.symm
  absMult x := by
    have h := T.absMult (T.equiv.symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  open_iff x := by
    have h := T.open_iff (T.equiv.symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

/-- Transports compose, so a producer may follow a genuine move by a
relabelling. -/
def trans (T : Transport c c' degree y y') (U : Transport c' c'' degree y' y'') :
    Transport c c'' degree y y'' where
  equiv := T.equiv.trans U.equiv
  absMult x := (U.absMult (T.equiv x)).trans (T.absMult x)
  open_iff x := (U.open_iff (T.equiv x)).trans (T.open_iff x)

/-! ### The consumer -/

/-- **The equivalence of geometric fibres a transport delivers.** -/
noncomputable def oddOpenEquiv (T : Transport c c' degree y y') :
    GeometricFibre c y degree ≃ GeometricFibre c' y' degree :=
  ((fibreEquiv c degree y).symm.trans T.equiv).trans (fibreEquiv c' degree y')

theorem open_oddOpenEquiv (T : Transport c c' degree y y')
    (z : GeometricFibre c y degree) : (T.oddOpenEquiv z).Open ↔ z.Open := by
  have hx : fibreEquiv c degree y ((fibreEquiv c degree y).symm z) = z :=
    Equiv.apply_symm_apply _ _
  calc (T.oddOpenEquiv z).Open
      ↔ (T.equiv ((fibreEquiv c degree y).symm z)).OpenAt y' :=
        open_fibreEquiv c' degree y' _
    _ ↔ ((fibreEquiv c degree y).symm z).OpenAt y := T.open_iff _
    _ ↔ (fibreEquiv c degree y ((fibreEquiv c degree y).symm z)).Open :=
        (open_fibreEquiv c degree y _).symm
    _ ↔ z.Open := by rw [hx]

theorem isOdd_oddOpenEquiv (T : Transport c c' degree y y')
    (z : GeometricFibre c y degree) : (T.oddOpenEquiv z).IsOdd ↔ z.IsOdd := by
  have hx : fibreEquiv c degree y ((fibreEquiv c degree y).symm z) = z :=
    Equiv.apply_symm_apply _ _
  calc (T.oddOpenEquiv z).IsOdd
      ↔ (T.equiv ((fibreEquiv c degree y).symm z)).IsOdd := isOdd_fibreEquiv c' degree y' _
    _ ↔ ((fibreEquiv c degree y).symm z).IsOdd := T.isOdd _
    _ ↔ (fibreEquiv c degree y ((fibreEquiv c degree y).symm z)).IsOdd :=
        (isOdd_fibreEquiv c degree y _).symm
    _ ↔ z.IsOdd := by rw [hx]

/-- **The transport is exactly a `countLink_of_oddOpenEquiv` input.** -/
theorem exists_oddOpenEquiv (T : Transport c c' degree y y') :
    ∃ e : GeometricFibre c y degree ≃ GeometricFibre c' y' degree,
      (∀ z, (e z).Open ↔ z.Open) ∧ ∀ z, (e z).IsOdd ↔ z.IsOdd :=
  ⟨T.oddOpenEquiv, T.open_oddOpenEquiv, T.isOdd_oddOpenEquiv⟩

/-- **A transport forces the two open odd counts to be equal**, not merely of
equal parity.  This is the exact respect in which the object asks for more than the
count needs. -/
theorem openOddCount_eq (T : Transport c c' degree y y') :
    GeometricFibre.openOddCount c y degree = GeometricFibre.openOddCount c' y' degree :=
  Nat.card_congr (Equiv.subtypeEquiv T.oddOpenEquiv fun z ↦
    and_congr (T.open_oddOpenEquiv z).symm (T.isOdd_oddOpenEquiv z).symm)

/-- **The consumer into the link.** -/
theorem countLink (T : Transport c c' degree y y') :
    CountTransportLink.CountLink degree c y c' y' :=
  CountTransportLink.countLink_of_oddOpenEquiv T.oddOpenEquiv T.open_oddOpenEquiv
    T.isOdd_oddOpenEquiv

end Transport

/-! ## 3.  The frame-level presentation a producer would build -/

/-- **A cross-core member transport, at the level of frames.**  This is what a
geometric construction produces: an actual map on frames and a map back, each
respecting isomorphism over its own core, mutually inverse up to isomorphism,
and preserving the multiplicity.  Nothing here mentions a request. -/
structure FrameTransport (c c' : Core n p) (degree : ℕ) where
  /-- the map on frames -/
  toFun : Frame c degree → Frame c' degree
  /-- the map back -/
  invFun : Frame c' degree → Frame c degree
  /-- isomorphic frames have isomorphic images -/
  map_iso : ∀ {k l : Frame c degree}, FrameIso k l → Nonempty (FrameIso (toFun k) (toFun l))
  /-- and likewise for the map back -/
  inv_map_iso : ∀ {k l : Frame c' degree}, FrameIso k l →
    Nonempty (FrameIso (invFun k) (invFun l))
  /-- a two-sided inverse, up to isomorphism over the core -/
  left_inv : ∀ k : Frame c degree, Nonempty (FrameIso (invFun (toFun k)) k)
  /-- a two-sided inverse, up to isomorphism over the core -/
  right_inv : ∀ k : Frame c' degree, Nonempty (FrameIso (toFun (invFun k)) k)
  /-- the multiplicity is preserved -/
  absMult_toFun : ∀ k : Frame c degree, (toFun k).absMult = k.absMult

namespace FrameTransport

variable {c c' : Core n p} {y y' : Fin p → ℚ}

/-- The induced map on classes. -/
def classMap (F : FrameTransport c c' degree) :
    FrameClass c degree → FrameClass c' degree := fun x ↦
  Quotient.liftOn x (fun k ↦ FrameClass.mk (F.toFun k)) fun _ _ h ↦
    h.elim fun i ↦ FrameClass.mk_eq_mk_iff.mpr (F.map_iso i)

@[simp] theorem classMap_mk (F : FrameTransport c c' degree) (k : Frame c degree) :
    F.classMap (FrameClass.mk k) = FrameClass.mk (F.toFun k) := rfl

/-- The induced map back on classes. -/
def classInv (F : FrameTransport c c' degree) :
    FrameClass c' degree → FrameClass c degree := fun x ↦
  Quotient.liftOn x (fun k ↦ FrameClass.mk (F.invFun k)) fun _ _ h ↦
    h.elim fun i ↦ FrameClass.mk_eq_mk_iff.mpr (F.inv_map_iso i)

@[simp] theorem classInv_mk (F : FrameTransport c c' degree) (k : Frame c' degree) :
    F.classInv (FrameClass.mk k) = FrameClass.mk (F.invFun k) := rfl

/-- **The frame-level transport is a bijection of classes.** -/
def classEquiv (F : FrameTransport c c' degree) :
    FrameClass c degree ≃ FrameClass c' degree where
  toFun := F.classMap
  invFun := F.classInv
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h k => exact FrameClass.mk_eq_mk_iff.mpr (F.left_inv k)
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h k => exact FrameClass.mk_eq_mk_iff.mpr (F.right_inv k)

/-- **The frame-level transport, plus openness at a request pair, is a
`Transport`.** -/
def toTransport (F : FrameTransport c c' degree)
    (hopen : ∀ k : Frame c degree, (F.toFun k).OpenAt y' ↔ k.OpenAt y) :
    Transport c c' degree y y' where
  equiv := F.classEquiv
  absMult x := by
    induction x using Quotient.inductionOn with
    | h k => exact F.absMult_toFun k
  open_iff x := by
    induction x using Quotient.inductionOn with
    | h k => exact hopen k

end FrameTransport

/-! ## 4.  Non-vacuity: every relabelling is a transport -/

section Relabel

variable {c c' : Core n p} {y y' : Fin p → ℚ}

/-- A relabelling carries isomorphism over one core to isomorphism over the
other: the gluing datum is untouched, so the same `GeometricDatumIso` serves. -/
def relabelFrameIso (d : Relabel c c') {k l : Frame c degree} (i : FrameIso k l) :
    FrameIso (relabelFrame d k) (relabelFrame d l) where
  datum := i.datum
  overCore_vertex branch := congrArg d.vtx (i.overCore_vertex branch)
  overCore_row path := congrArg d.slot (i.overCore_row path)

/-- Relabelling and relabelling back is the identity up to isomorphism over the
core: the datum is literally unchanged and the two permutations cancel. -/
def relabelFrameRoundTrip (d : Relabel c c') (k : Frame c degree) :
    FrameIso (relabelFrame d.symm (relabelFrame d k)) k where
  datum := GeometricDatumIso.refl k.data
  overCore_vertex branch := (d.vtx.symm_apply_apply (k.ident.vertex branch)).symm
  overCore_row path := by
    show k.ident.row ((GeometricDatumIso.refl k.data).stablePathEquiv k.fullDim.valid.1 path) =
      d.slot.symm (d.slot (k.ident.row path))
    rw [GeometricDatumIso.stablePathEquiv_refl]
    exact (d.slot.symm_apply_apply (k.ident.row path)).symm

/-- **Every relabelling is a frame-level cross-core transport.** -/
def ofRelabel (d : Relabel c c') : FrameTransport c c' degree where
  toFun := relabelFrame d
  invFun := relabelFrame d.symm
  map_iso i := ⟨relabelFrameIso d i⟩
  inv_map_iso i := ⟨relabelFrameIso d.symm i⟩
  left_inv k := ⟨relabelFrameRoundTrip d k⟩
  right_inv k := ⟨relabelFrameRoundTrip d.symm k⟩
  absMult_toFun _ := rfl

/-- A relabelled frame is open at the matched request exactly when the original
is open: its coordinate vector is literally the old one. -/
theorem openAt_relabelFrame (d : Relabel c c') (k : Frame c degree)
    (hy : ∀ e, y' (d.slot e) = y e) : (relabelFrame d k).OpenAt y' ↔ k.OpenAt y := by
  simp only [Frame.OpenAt, coordsAt_relabelFrame d k hy]

/-- **Non-vacuity: a relabelling with matched requests is a `Transport`.** -/
def transportOfRelabel (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e) :
    Transport c c' degree y y' :=
  (ofRelabel d).toTransport fun k ↦ openAt_relabelFrame d k hy

end Relabel

/-! ### A concrete inhabitant at two genuinely different cores -/

section Witness

/-- A core with its slots permuted. -/
def slotRelabel (core : Core n p) (σ : Equiv.Perm (Fin p)) : Core n p where
  tail := core.tail ∘ σ.symm
  head := core.head ∘ σ.symm

/-- The relabelling datum between a core and its slot permutation. -/
def slotRelabelDatum (core : Core n p) (σ : Equiv.Perm (Fin p)) :
    Relabel core (slotRelabel core σ) where
  slot := σ
  vtx := Equiv.refl _
  incidence v e := by
    simp [coreIncidence, slotRelabel, Function.comp]

/-- **A concrete inhabitant of `Transport` at two different cores**, at every
degree and every request, with no hypothesis. -/
noncomputable def transportSlotRelabel (core : Core n p) (σ : Equiv.Perm (Fin p))
    (degree : ℕ) (y : Fin p → ℚ) :
    Transport core (slotRelabel core σ) degree y (fun e ↦ y (σ.symm e)) :=
  transportOfRelabel (slotRelabelDatum core σ) fun e ↦ by
    show y (σ.symm (σ e)) = y e
    rw [Equiv.symm_apply_apply]

/-- **The two cores really are different**, so the inhabitant above is not the
identity transport wearing a disguise. -/
theorem slotRelabel_ne_self :
    slotRelabel (⟨![0, 1], ![0, 1]⟩ : Core 2 2) (Equiv.swap 0 1) ≠
      (⟨![0, 1], ![0, 1]⟩ : Core 2 2) := by
  intro h
  have h0 := congrArg (fun c : Core 2 2 ↦ c.tail 0) h
  simp [slotRelabel] at h0

end Witness

/-! ## 5.  The matched-request refinement -/

/-- **A Whitehead step keeps the slot set.**  Both cores' dart graphs carry the
same edge involution `opposite` on `Fin p × Bool` (`CoreOfDarts.op_graph`), and
`CoreRelabel.exists_perm_of_reaches` shows a whole chain of moves changes only
`vert`.  So the two cores of a step share their slots `Fin p` on the nose, the
identity is the slot dictionary across the step, and the shared codimension-one
wall is where the moved slot's length is zero.  That is what makes a *single*
request vector, rather than an unrelated pair, the geometrically meaningful
input. -/
theorem op_eq_of_step {c c' : CubicCore n p} (_ : Step c c') :
    c.graph.op = c'.graph.op := rfl

/-- **A positive request general for two cores at once.**  This is
`SegmentWalls.exists_general_positive` run over the disjoint union of the two
cores' normal-form families, so matched requests general for both cores
exist. -/
theorem exists_generalRequest_pair (c c' : Core n p) (degree : ℕ) :
    ∃ y : Fin p → ℚ, (∀ i, 0 < y i) ∧
      GeneralRequest c degree y ∧ GeneralRequest c' degree y := by
  classical
  let _ : Fintype (NFFrame c degree) := Fintype.ofFinite _
  let _ : Fintype (NFFrame c' degree) := Fintype.ofFinite _
  obtain ⟨y, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive
      (fun x : (NFFrame c degree × Fin p) ⊕ (NFFrame c' degree × Fin p) ↦
        Sum.elim (fun z : NFFrame c degree × Fin p ↦ (NFFrame.toFrame z.1).coordWall z.2)
          (fun z : NFFrame c' degree × Fin p ↦ (NFFrame.toFrame z.1).coordWall z.2) x)
      (coordinateWall (p := p)) (fun _ ↦ 1)
      (by rintro (⟨r, col⟩ | ⟨r, col⟩) <;> exact Frame.coordWall_proper _ _)
      (by intro l; rw [SegmentWalls.eval_coordinateWall]; exact one_pos)
  have hposy : ∀ i, 0 < y i := by
    intro i
    have h := hpos i
    rwa [SegmentWalls.eval_coordinateWall] at h
  refine ⟨y, hposy, ?_, ?_⟩
  · refine SegmentWalls.coordsAt_ne_zero_of_nf y fun r col ↦ ?_
    have h := havoid (Sum.inl (r, col))
    simp only [Sum.elim_inl] at h
    rwa [Frame.eval_coordWall] at h
  · refine SegmentWalls.coordsAt_ne_zero_of_nf y fun r col ↦ ?_
    have h := havoid (Sum.inr (r, col))
    simp only [Sum.elim_inr] at h
    rwa [Frame.eval_coordWall] at h

/-! ## 6.  A weaker form: how much less than a transport suffices -/

/-- **An equivalence of the open odd classes alone.**  Strictly weaker than a
`Transport`, and still enough for the link. -/
def OpenOddTransport (c c' : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) : Type 1 :=
  {x : FrameClass c degree // x.OpenAt y ∧ x.IsOdd} ≃
    {x : FrameClass c' degree // x.OpenAt y' ∧ x.IsOdd}

variable {c c' : Core n p} {y y' : Fin p → ℚ}

/-- A transport restricts to the open odd classes. -/
def Transport.toOpenOdd (T : Transport c c' degree y y') :
    OpenOddTransport c c' degree y y' :=
  T.equiv.subtypeEquiv fun x ↦ and_congr (T.open_iff x).symm (T.isOdd x).symm

theorem openOddCount_eq_of_openOddTransport (e : OpenOddTransport c c' degree y y') :
    GeometricFibre.openOddCount c y degree = GeometricFibre.openOddCount c' y' degree := by
  rw [openOddCount_eq_card c y degree, openOddCount_eq_card c' y' degree]
  exact Nat.card_congr e

theorem countLink_of_openOddTransport (e : OpenOddTransport c c' degree y y') :
    CountTransportLink.CountLink degree c y c' y' :=
  CountTransportLink.countLink_of_openOddCount_eq (openOddCount_eq_of_openOddTransport e)

/-! ## 7.  The producer may work one wall-limit at a time -/

/-- **A transport assembled fibrewise over a common invariant.**  If both sides'
classes carry a common invariant -- in Draisma--Vargas' argument, the
codimension-one limit a frame specializes to at the shared wall -- and the two
sides match over each value of it, they match globally.  This is the interface
at which a local, one-limit-at-a-time construction becomes the global object
a type change needs. -/
def Transport.ofFibrewise {L : Type*} (μ : FrameClass c degree → L)
    (μ' : FrameClass c' degree → L)
    (e : ∀ l : L, {x : FrameClass c degree // μ x = l} ≃
      {x : FrameClass c' degree // μ' x = l})
    (habs : ∀ (l : L) (x : {x : FrameClass c degree // μ x = l}),
      ((e l) x).1.absMult = x.1.absMult)
    (hopen : ∀ (l : L) (x : {x : FrameClass c degree // μ x = l}),
      ((e l) x).1.OpenAt y' ↔ x.1.OpenAt y) :
    Transport c c' degree y y' where
  equiv := ((Equiv.sigmaFiberEquiv μ).symm.trans (Equiv.sigmaCongrRight e)).trans
    (Equiv.sigmaFiberEquiv μ')
  absMult x := habs (μ x) ⟨x, rfl⟩
  open_iff x := hopen (μ x) ⟨x, rfl⟩

end DraismaVargas.Count.CrossCoreTransport
