module

public import GenusSixExistence.BrillNoetherRank.Tripod.ClawDefs
public import GenusSixExistence.BrillNoetherRank.Tripod.Dichotomy
public import GenusSixExistence.BrillNoetherRank.Tripod.GluingClasses
public import DraismaVargasCount.Assembly

@[expose] public section

/-!
# Glued and claw members over the tripod gadget, and the parity of the claws

Prose proof: `Research/genus-six-brill-noether-rank.md`, §3.4 (Claw members, and the parity
argument), §4 (The classification at long legs), §5.5 (The bijection) and §6.3 (Admissible
requests, and the parity of the claw classes); section and statement numbers in this file refer
to that note.

A member over the gadget `Γ̃ = tripodCore core s` is a full-dimensional tropical morphism `φ`
of degree five from (a modification of) `Γ̃` to a tree `T`, identified with `Γ̃`. Write `c` for
the centre of the tripod, `T̂ = φ(G)` for the image of the G-slots, and `k₀` for the constant of
the jump rule (Lemma 4.1). At long legs (Corollary 4.10) exactly one of the following holds:

* **glued** (`k₀ = 1`): every leg leaves its mark up a leaf edge of `T` (the *arm*), runs to the
  leaf and back (§3.3). These are the Cools--Draisma tripod gluings of the
  members over `G̃` (Theorem 5.1 with §5.5);
* **claw** (`k₀ = 0`): `φ(c) ∉ φ(G)`; the three lost edges form a claw at `φ(c)` (Theorem 4.7(b)).

## The definitions, and why they are these

`k₀` itself is not defined here: it needs the Y-degree over every target point, which is not
formalized. The two classes are defined by the combinatorial characterisations that
Corollary 4.10 and §3.4 use, read off a `Frame` (so they do not depend on the request):

* `TripodFrame.IsClaw`: the target vertex under the centre is not an endpoint of any target
  edge under a non-dangling source edge of a G-slot. This is the definition of a claw member in
  §3.4, "φ(c) ∉ φ(G)".
* `TripodFrame.IsGlued`: for each mark, the non-dangling source edge of its leg at the mark lies
  over a leaf edge of the target. This is the hairpin of §3.3.

With these definitions the dichotomy (`dichotomy`) has content in both directions, and the
gluing bijection (`exists_gluing`) is onto the glued classes.

## Genericity

Every genericity hypothesis has the form of §6.3: it asks the request to avoid a finite family of
nonzero linear functionals, so that the closure (`ClosureFrame`) can add the family to its wall set.
`Admissible core s B y` is: `y > 0`; no frame of `Γ̃` (degree 5) or of `G̃` (degree 4, at
`baseRequest s y`) has a zero coordinate (§6.3 (ii), (iii)); `y` avoids every functional of the
finite family `B`; long legs ((v)). The mark condition (iv) of §6.3 is the family `B` produced by
`exists_gluing`. It is stated existentially. `Gluing.lean` takes `B = ∅`: as §6.3 says, condition
(iv) follows from (ii), since a mark over a target vertex, or coincident mark images, would make the
gluing a frame of `Γ̃` with a zero coordinate.

## What is stated

| declaration | content | prose | where |
|---|---|---|---|
| `memberIsClaw_iff_of_iso`, `memberIsGlued_iff_of_iso` | the two predicates descend to classes (transport along `iso.datum`) | routine | `ClawDefs.lean` |
| `dichotomy` | at long legs, glued ↔ not claw | Theorem 4.7, Corollary 4.10; §4.8 | `Dichotomy.lean` |
| `exists_gluing` | open classes over `G̃` ≃ open glued classes over `Γ̃`, preserving `multNat`; `B = ∅` | Theorem 5.1, §3.3; §5.5 | `Gluing.lean`, `GluingClasses.lean` |
| `openOddClawCount_odd_of_gluing`, `parityPackage` | (P5): the number of open claw classes of odd multiplicity is odd | §6.3 (P5) | here, from the above, `EvenGenusParity.evenC34_three` and `Assembly.c34_genusSix` |

The witness used by the assembly is the one at the closed actual point, `Realisation`.
-/

namespace GenusSixExistence.Tripod.Classification

open DraismaVargas.Count
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open Gadget

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}

/-! The predicates `IsClaw`, `IsGlued` (on frames, members, classes), `Admissible`, `markedSpec`
and `marksDivisor` are in `ClawDefs.lean`. -/

/-! ## 3.  The dichotomy -/

/-- **Glued or claw, at long legs** (Theorem 4.7 and Corollary 4.10; §4.8). Over a
gadget whose base `G̃` is connected and cubic of genus six, an open member of degree five at a request with long
legs is glued if and only if it is not a claw member. No genericity of `G̃` or of the marks, and
no gonality hypothesis, is needed. -/
theorem dichotomy (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (mem : FibreMember (tripodCore core s) y (3 + 2)) (hOpen : mem.Open) :
    MemberIsGlued mem ↔ ¬ MemberIsClaw mem :=
  Dichotomy.dichotomy hcubic hconn hgenus hpos hlong mem hOpen

/-- The dichotomy on classes. -/
theorem classDichotomy (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (c : GeometricFibre (tripodCore core s) y (3 + 2)) (hc : c.Open) :
    ClassIsGlued c ↔ ¬ ClassIsClaw c := by
  obtain ⟨mem, rfl⟩ := GeometricFibre.cls_surjective c
  rw [classIsGlued_cls, classIsClaw_cls]
  exact dichotomy hcubic hconn hgenus hpos hlong mem ((GeometricFibre.open_cls mem).mp hc)

/-! ## 4.  Admissible requests and the gluing bijection -/

/-- **The gluing bijection** (Theorem 5.1, §3.3, with §5.5 for surjectivity).
There is a finite family `B` of nonzero functionals (the mark condition (iv); `Gluing.lean`
shows `B = ∅` suffices) such that at every admissible request the open classes of degree four over `G̃` at the base request correspond to
the open glued classes of degree five over `Γ̃`, preserving the multiplicity. The map is the
Cools--Draisma tripod gluing. -/
theorem exists_gluing (hcubic : core.Cubic) (hconn : core.Connected)
    (hloop : ∀ i, core.tail i ≠ core.head i) (hgenus : p + 1 - n = 6) (s : MarkSlots p) :
    ∃ B : Finset (Fin (p + 1 + 1 + 1 + 3) → ℚ), (∀ w ∈ B, w ≠ 0) ∧
      ∀ y, Admissible core s B y →
        ∃ e : {c : GeometricFibre core (baseRequest s y) (2 + 2) // c.Open} ≃
            {c : GeometricFibre (tripodCore core s) y (3 + 2) // c.Open ∧ ClassIsGlued c},
          ∀ c, (e c).1.multNat = c.1.multNat :=
  Gluing.exists_gluing hcubic hconn hloop hgenus s

/-! ## 5.  (P5): the parity of the claw classes -/

/-- The number of open claw classes of odd multiplicity over the gadget. -/
noncomputable def openOddClawCount (core : Core n p) (s : MarkSlots p)
    (y : Fin (p + 1 + 1 + 1 + 3) → ℚ) : ℕ :=
  Nat.card {c : GeometricFibre (tripodCore core s) y (3 + 2) // c.Open ∧ c.IsOdd ∧ ClassIsClaw c}

/-- Splitting a finite count along a predicate. -/
theorem natCard_split {α : Type*} [Finite α] (P Q : α → Prop) :
    Nat.card {a // P a} = Nat.card {a // P a ∧ ¬ Q a} + Nat.card {a // P a ∧ Q a} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [add_comm, ← Finset.filter_filter, ← Finset.filter_filter]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-- **(P5) at one admissible request, from a multiplicity-preserving gluing bijection.** The
open odd count over `Γ̃` is even (`EvenGenusParity.evenC34_three`), the open odd count over `G̃` is odd
(`Assembly.c34_genusSix`), and the glued classes match the classes over `G̃`; so the claw
classes of odd multiplicity are odd in number (§6.3 (P5)). -/
theorem openOddClawCount_odd_of_gluing (hcubic : core.Cubic) (hconn : core.Connected)
    (hgenus : p + 1 - n = 6) {B : Finset (Fin (p + 1 + 1 + 1 + 3) → ℚ)}
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hy : Admissible core s B y)
    (e : {c : GeometricFibre core (baseRequest s y) (2 + 2) // c.Open} ≃
      {c : GeometricFibre (tripodCore core s) y (3 + 2) // c.Open ∧ ClassIsGlued c})
    (he : ∀ c, (e c).1.multNat = c.1.multNat) :
    Odd (openOddClawCount core s y) := by
  classical
  obtain ⟨hpos, hgenΓ, hgenG, -, hlong⟩ := hy
  have hEven := EvenGenusParity.evenC34_three (tripodCore core s) (tripodCore_cubic core s hcubic)
    (tripodCore_connected core s hconn) (by omega) y hpos hgenΓ
  have hOdd := Assembly.c34_genusSix core hcubic hconn (by omega) (baseRequest s y)
    (baseRequest_pos s hpos) hgenG
  have hdich := classDichotomy (s := s) hcubic hconn hgenus hpos hlong
  -- the open odd classes over `Γ̃` split into glued ones and claw ones
  have hsplit : GeometricFibre.openOddCount (tripodCore core s) y (3 + 2) =
      Nat.card {c : GeometricFibre (tripodCore core s) y (3 + 2) //
        (c.Open ∧ c.IsOdd) ∧ ¬ ClassIsClaw c} + openOddClawCount core s y := by
    rw [GeometricFibre.openOddCount, natCard_split _ ClassIsClaw, openOddClawCount]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c ↦ and_assoc)
  -- the glued ones are counted by the classes over `G̃`
  have hglued : Nat.card {c : GeometricFibre (tripodCore core s) y (3 + 2) //
      (c.Open ∧ c.IsOdd) ∧ ¬ ClassIsClaw c} =
      GeometricFibre.openOddCount core (baseRequest s y) (2 + 2) := by
    rw [GeometricFibre.openOddCount]
    symm
    refine Nat.card_congr ?_
    refine (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun c : GeometricFibre core (baseRequest s y) (2 + 2) ↦ c.Open)
      (fun c ↦ c.IsOdd)).symm.trans ?_
    refine (Equiv.subtypeEquiv (q := fun b : {c : GeometricFibre (tripodCore core s) y (3 + 2) //
      c.Open ∧ ClassIsGlued c} ↦ b.1.IsOdd) e fun a ↦ ?_).trans ?_
    · show Odd a.1.multNat ↔ Odd (e a).1.multNat
      rw [he a]
    refine (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun c : GeometricFibre (tripodCore core s) y (3 + 2) ↦ c.Open ∧ ClassIsGlued c)
      (fun c ↦ c.IsOdd)).trans ?_
    refine Equiv.subtypeEquivRight fun c ↦ ?_
    constructor
    · rintro ⟨⟨ho, hg⟩, hodd⟩
      exact ⟨⟨ho, hodd⟩, (hdich c ho).mp hg⟩
    · rintro ⟨⟨ho, hodd⟩, hnc⟩
      exact ⟨⟨ho, (hdich c ho).mpr hnc⟩, hodd⟩
  rw [hsplit, hglued] at hEven
  exact Nat.not_even_iff_odd.mp fun hb ↦
    (Nat.not_even_iff_odd.mpr hOdd) ((Nat.even_add.mp hEven).mpr hb)

/-- **The generic-point package of §6.3**: a finite family of nonzero functionals off which
every admissible request has an odd number of open claw classes of odd multiplicity. This is
the input of the closure (Theorem 6.3). -/
def ParityPackage (core : Core n p) (s : MarkSlots p) : Prop :=
  ∃ B : Finset (Fin (p + 1 + 1 + 1 + 3) → ℚ), (∀ w ∈ B, w ≠ 0) ∧
    ∀ y, Admissible core s B y → Odd (openOddClawCount core s y)

/-- **(P5)**, from `EvenGenusParity.evenC34_three`, `Assembly.c34_genusSix`, the dichotomy and
the gluing bijection. -/
theorem parityPackage (hcubic : core.Cubic) (hconn : core.Connected)
    (hloop : ∀ i, core.tail i ≠ core.head i) (hgenus : p + 1 - n = 6) (s : MarkSlots p) :
    ParityPackage core s := by
  obtain ⟨B, hB, hglue⟩ := exists_gluing hcubic hconn hloop hgenus s
  refine ⟨B, hB, fun y hy ↦ ?_⟩
  obtain ⟨e, he⟩ := hglue y hy
  exact openOddClawCount_odd_of_gluing hcubic hconn hgenus hy e he

end GenusSixExistence.Tripod.Classification
