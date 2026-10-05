module

public import DraismaVargasCount.StepSupplyGenusSix
public import DraismaVargasCount.BallotCoreIdentification
public import DraismaVargasCount.DiagonalClassificationEndgame
public import DraismaVargasCount.DiagonalRigidityObligation
public import DraismaVargasCount.DiagonalExtract
public import DraismaVargasCount.DiagonalFromSeparation
public import DraismaVargasCount.LollipopLeafRow
public import DraismaVargasCount.LollipopDivalentWitness
public import DraismaVargasCount.SimpleWallSupply

@[expose] public section

/-!
# The parity of the base count, and what the ballot classification is worth

The genus-six count (`Assembly`) starts from the base count over the caterpillar of
loops, `GeometricFibre.openOddCount (catCore 2) request (2 + 2) = 5` at a positive
request (step 1).  The propagation (step 4, `SimpleWallSupply.c34_of_base_positive`)
uses that count only through its parity at one general positive request, and its base
may be *any* connected cubic core of genus six.  This module states that input once, as
`OddBaseGenusSix`, and relates it to the ballot classification of the caterpillar fibre
and to the exhaustion package `BallotSlopes.DiagonalClassification`.  It also records two
unconditional results at genus two.

## What is proved

* `OddBaseGenusSix` -- there is a connected cubic core of genus six and a general
  request over it at which the number of open classes of odd multiplicity is odd.
* `odd_openOddCount_genusSix_of_ballotClassification` -- a ballot classification at
  genus six gives the parity.
* `odd_openOddCount_genusSix_of_le_five`, `oddBaseGenusSix_of_le_five` -- **at genus
  six the parity follows from the upper bound alone**, because the lower bound `5 ≤ …`
  holds unconditionally at a positive request
  (`BallotCoreIdentification.five_le_openOddCount_genusSix`).
* `member_surjective_of_openOddCount_le`, `ballotClassificationOfFamily`,
  `ballotClassification_of_openOddCount_le`, `nonempty_ballotClassification_iff` --
  **the converse.**  At a positive request,
  `CaterpillarBallot.BallotClassification m request` is *inhabited exactly when*
  `openOddCount (catCore m) request (m + 2) ≤ catalan (m + 1)`.  The structure
  therefore does not over-claim: it is equivalent to the bare numerical statement of
  the count, for every `m`, `m = 0` included.
* `openOddCount_eq_catalan_iff_nonempty_ballotClassification` -- the same
  equivalence with the equality on the right, using the lower bound.
* `nonempty_ballotClassification_genusSix_iff`,
  `nonempty_ballotClassification_genusTwo_iff` -- the two instances that matter:
  a ballot classification at genus six is exactly `openOddCount ≤ 5`, and at genus
  two exactly `openOddCount ≤ 1`.
* `not_odd_openOddCount_genusFour_of_ballotClassification` -- a scope check: the
  parity statement is **false at genus four** if the count holds there
  (`catalan 2 = 2`), so `OddBaseGenusSix` cannot be generalised over `m` and the
  genus-six restriction is essential, not an artefact.
* `exists_general_positive_request`, `exists_general_positive_request_genusSix` -- a
  request that is *simultaneously* general and positive exists over every caterpillar,
  and the count whose parity is asserted is at least `catalan (m + 1)` there, so
  `OddBaseGenusSix` is a claim about a specific integer at least `5`, not about an
  empty fibre.
* `oddBaseGenusSix_of_c34` -- **`OddBaseGenusSix` is necessary for the propagation.**
  It is *implied by* `CountSchedule.C34 2`, unconditionally, so any statement that
  suffices for `C34 2` implies it; in particular it follows from
  `Assembly.c34_genusSix`.
* `oddBaseGenusSix_of_ballotClassification`, `oddBaseGenusSix_of_diagonalClassification`
  (§8) -- the same from a ballot classification, or from
  `BallotSlopes.DiagonalClassification 2` at a request that is positive and general.
* `ballotDiagonalRelabelStable_genusTwo` (§9) -- **the orbit test holds at `m = 0`.**
  `DiagonalExtract` derives from the `extract` field of `DiagonalClassification` the
  member-free necessary condition `BallotDiagonalRelabelStable m`; it holds at `m = 0`,
  so this member-free route cannot contradict `DiagonalClassification 0`.
* `eq_of_not_passesAboveLeaf_genusTwo`, `leafAvoidingSeparated_genusTwo`,
  `diagonal_genusTwo`, `diagonalClassification_genusTwo_of_extract_rigid` (§10) --
  **the `diagonal` field of `DiagonalClassification 0` is proved**, unconditionally
  and for every member.  At `m = 0` every member's target has at least two leaves and
  there are only three rows, so at most one row is leaf-avoiding and
  `SpineSingleColumn.LeafAvoidingSeparated 0` is vacuous.  The `extract` field at
  `m = 0` is proved in `ExtractGenusTwo`.

## What is NOT proved here -- every hypothesis

* **`OddBaseGenusSix` is not proved in this module**, and no witness for it is
  exhibited here; it follows from `Assembly.c34_genusSix` by `oddBaseGenusSix_of_c34`.
  By `nonempty_ballotClassification_genusSix_iff` a ballot classification at genus six
  is the single inequality `openOddCount (catCore 2) request (2 + 2) ≤ 5`, which is
  proved in `CaterpillarAllMembers`.
* **`BallotSlopes.DiagonalClassification` is not inhabited here.**  §10 proves its
  `diagonal` field at `m = 0` only; its `rigid` field is not touched.
* **§9 is a negative about a refutation, not a witness.**  At `m ≥ 1` the orbit test is
  not decided here.
* Nothing here constructs a `BallotClassification`, a `DiagonalClassification`, or a
  member; the converse above takes the count as input and hands back the structure,
  which is a *restatement* of the count and not a proof of it.
* By `nonempty_ballotClassification_iff`, `BallotClassification` can fail at a positive
  request only if the upper bound of the count fails, which would contradict Vargas,
  Part II (arXiv:2609.09109), `prop-divisors-on-chain`.
* Genus six only for the statements about `OddBaseGenusSix`: `m = 2` in §1, §3, §7 and
  §8.  §4 and §6 are general in `m`; §5 is about `m = 1`; §9 and §10 are about `m = 0`.
* `openOddCount` throughout is `GeometricFibre.openOddCount`.
-/

namespace DraismaVargas.Count.BaseCountParity

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.FibreCaterpillar (catCore)
open DraismaVargas.Count.StepSupplyReduction
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  The base parity statement -/

/-- **The base input of the propagation, at genus six.**

There is a connected cubic core of genus six and a general request over it at
which the number of open classes of odd multiplicity is odd.

The core is existentially quantified because the propagation can start from any
connected cubic core of genus six (the base of `SimpleWallSupply.c34_of_base_positive`
is an arbitrary cubic core): the caterpillar is one admissible choice of base and not
a required one. -/
def OddBaseGenusSix : Prop :=
  ∃ (base : CoreOfDarts.CubicCore (4 * 2 + 2) (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ),
    GeneralRequest base.core (2 + 2) y₀ ∧
      Odd (GeometricFibre.openOddCount base.core y₀ (2 + 2))

/-! ## 3.  The parity from a ballot classification, or from the upper bound -/

/-- **A ballot classification gives the parity**: the count is `5`, which is odd. -/
theorem odd_openOddCount_genusSix_of_ballotClassification
    {request : Fin (6 * 2 + 3) → ℚ}
    (classification : CaterpillarBallot.BallotClassification 2 request) :
    Odd (GeometricFibre.openOddCount (catCore 2) request (2 + 2)) := by
  rw [CaterpillarBallot.openOddCount_genusSix_eq_five classification]
  decide

/-- **At genus six the parity follows from the upper bound alone.**  The lower
bound `5 ≤ openOddCount` holds unconditionally at a positive request
(`BallotCoreIdentification.five_le_openOddCount_genusSix`, through the
ballot family), so an upper bound of `5` pins the count and `5` is odd. -/
theorem odd_openOddCount_genusSix_of_le_five {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot)
    (hle : GeometricFibre.openOddCount (catCore 2) request (2 + 2) ≤ 5) :
    Odd (GeometricFibre.openOddCount (catCore 2) request (2 + 2)) := by
  have hfive := BallotCoreIdentification.five_le_openOddCount_genusSix hRequest
  rw [le_antisymm hle hfive]
  decide

/-- `OddBaseGenusSix` from the upper bound at a general positive request over the
caterpillar. -/
theorem oddBaseGenusSix_of_le_five {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot)
    (hgen : GeneralRequest (catCore 2) (2 + 2) request)
    (hle : GeometricFibre.openOddCount (catCore 2) request (2 + 2) ≤ 5) :
    OddBaseGenusSix :=
  ⟨StepSupplyGenusSix.catCubicCore, request, hgen,
    odd_openOddCount_genusSix_of_le_five hRequest hle⟩

/-! ## 4.  What `BallotClassification` is worth: the converse -/

/-- **The exhaustion field is free once the count is bounded above.**

Given the ballot family (`BallotCoreIdentification.ballotFamily`, which
needs only a positive request) its `catalan (m + 1)` distinct open odd classes
already inject into the open odd subfibre.  If the subfibre has at most
`catalan (m + 1)` elements the injection is a bijection, so the family
exhausts — which is `member_surjective`.

Consequence: `CaterpillarBallot.BallotClassification` is **not** a stronger
statement than the count it is used to prove, and it cannot fail while the upper
bound of the count holds. -/
theorem member_surjective_of_openOddCount_le {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (family : CaterpillarBallot.BallotFamily m request)
    (hle : GeometricFibre.openOddCount (catCore m) request (m + 2) ≤ catalan (m + 1))
    (mem : FibreMember (catCore m) request (m + 2)) (hOpen : mem.Open)
    (hOdd : mem.HasOddMult) :
    ∃ s, GeometricFibre.cls (family.member s) = GeometricFibre.cls mem := by
  have hslopes : Nat.card (Slopes (2 * (m + 1))) = catalan (m + 1) := by
    rw [Nat.card_eq_fintype_card, Slopes.card_eq_catalan]
  have hcard : Nat.card (GeometricFibre.OpenOdd (catCore m) request (m + 2)) ≤
      Nat.card (Slopes (2 * (m + 1))) := by
    rw [hslopes]
    exact hle
  have hinj : Function.Injective fun s : Slopes (2 * (m + 1)) ↦
      GeometricFibre.clsOpenOdd (family.member s) (family.member_open s)
        (family.member_hasOddMult s) :=
    fun a b hab ↦ family.member_injective (congrArg Subtype.val hab)
  obtain ⟨s, hs⟩ :=
    (hinj.bijective_of_nat_card_le hcard).2 (GeometricFibre.clsOpenOdd mem hOpen hOdd)
  exact ⟨s, congrArg Subtype.val hs⟩

/-- The packaged form: a ballot family plus the upper bound is a ballot
classification. -/
noncomputable def ballotClassificationOfFamily {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (family : CaterpillarBallot.BallotFamily m request)
    (hle : GeometricFibre.openOddCount (catCore m) request (m + 2) ≤ catalan (m + 1)) :
    CaterpillarBallot.BallotClassification m request where
  toBallotFamily := family
  member_surjective := member_surjective_of_openOddCount_le family hle

/-- **A ballot classification from the upper bound alone**, at a positive request:
the family `BallotCoreIdentification.ballotFamily` supplies everything else. -/
noncomputable def ballotClassification_of_openOddCount_le (m : ℕ)
    {request : Fin (6 * m + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot)
    (hle : GeometricFibre.openOddCount (catCore m) request (m + 2) ≤ catalan (m + 1)) :
    CaterpillarBallot.BallotClassification m request :=
  ballotClassificationOfFamily (BallotCoreIdentification.ballotFamily m hRequest) hle

/-- **`BallotClassification` is exactly the upper bound of the count.**  At a
positive request the hypothesis package is inhabited if and only if the open odd
count is at most `catalan (m + 1)` — for every `m`, `m = 0` included.

So the structure is inhabited precisely when the count it encodes is true. -/
theorem nonempty_ballotClassification_iff (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    Nonempty (CaterpillarBallot.BallotClassification m request) ↔
      GeometricFibre.openOddCount (catCore m) request (m + 2) ≤ catalan (m + 1) := by
  constructor
  · rintro ⟨classification⟩
    exact (CaterpillarBallot.openOddCount_eq_catalan classification).le
  · exact fun hle ↦ ⟨ballotClassification_of_openOddCount_le m hRequest hle⟩

/-- The same equivalence with the equality of the count on the right, the lower
bound supplying the other half. -/
theorem openOddCount_eq_catalan_iff_nonempty_ballotClassification (m : ℕ)
    {request : Fin (6 * m + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot) :
    GeometricFibre.openOddCount (catCore m) request (m + 2) = catalan (m + 1) ↔
      Nonempty (CaterpillarBallot.BallotClassification m request) := by
  rw [nonempty_ballotClassification_iff m hRequest]
  constructor
  · exact fun h ↦ h.le
  · exact fun hle ↦
      le_antisymm hle (BallotCoreIdentification.catalan_le_openOddCount m hRequest)

/-- **Genus six.**  A ballot classification is exactly `openOddCount ≤ 5`. -/
theorem nonempty_ballotClassification_genusSix_iff {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    Nonempty (CaterpillarBallot.BallotClassification 2 request) ↔
      GeometricFibre.openOddCount (catCore 2) request (2 + 2) ≤ 5 := by
  have h := nonempty_ballotClassification_iff 2 hRequest
  rwa [show catalan (2 + 1) = 5 from catalan_three] at h

/-- **Genus two.**  A ballot classification at the smallest `m` is exactly
`openOddCount ≤ 1`. -/
theorem nonempty_ballotClassification_genusTwo_iff {request : Fin (6 * 0 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    Nonempty (CaterpillarBallot.BallotClassification 0 request) ↔
      GeometricFibre.openOddCount (catCore 0) request (0 + 2) ≤ 1 := by
  have h := nonempty_ballotClassification_iff 0 hRequest
  rwa [show catalan (0 + 1) = 1 from catalan_one] at h

/-! ## 5.  The parity statement is genus-six-specific, and that is not an artefact -/

/-- **The parity statement is false at genus four if the count holds there.**
`catalan 2 = 2`, so a ballot classification at `m = 1` makes the count even.

This is the reason `OddBaseGenusSix` is stated at `m = 2` and is not quantified
over `m`: `CountSchedule.C34 m` is itself only expected at `m` with
`catalan (m + 1)` odd, and Catalan numbers are odd exactly at
`m + 1 = 2 ^ k - 1`.  A generalisation of `OddBaseGenusSix` over `m` would
contradict Part II's count at genus four. -/
theorem not_odd_openOddCount_genusFour_of_ballotClassification
    {request : Fin (6 * 1 + 3) → ℚ}
    (classification : CaterpillarBallot.BallotClassification 1 request) :
    ¬ Odd (GeometricFibre.openOddCount (catCore 1) request (1 + 2)) := by
  have heq := CaterpillarBallot.openOddCount_eq_catalan classification
  rw [show catalan (1 + 1) = 2 from catalan_two] at heq
  rw [heq]
  decide

/-! ## 6.  Non-degeneracy of `OddBaseGenusSix` -/

/-- **The binders of `OddBaseGenusSix` are jointly satisfiable, and the count it
talks about is not zero.**  A request that is at once positive and general exists
over every caterpillar (`StepSupplyReduction.exists_generalRequest`, which has no
hypothesis), and at such a request the ballot family already puts
`catalan (m + 1)` classes in the open odd subfibre.  So general and positive are
compatible, unconditionally. -/
theorem exists_general_positive_request (m : ℕ) :
    ∃ request : Fin (6 * m + 3) → ℚ, (∀ i, 0 < request i) ∧
      GeneralRequest (catCore m) (m + 2) request ∧
      catalan (m + 1) ≤ GeometricFibre.openOddCount (catCore m) request (m + 2) := by
  obtain ⟨y, hpos, hgen⟩ := exists_generalRequest (catCore m) (m + 2)
  exact ⟨y, hpos, hgen, BallotCoreIdentification.catalan_le_openOddCount m hpos⟩

/-- **Genus six.**  The integer whose parity `OddBaseGenusSix` asserts is at
least five at a request that is simultaneously general and positive. -/
theorem exists_general_positive_request_genusSix :
    ∃ request : Fin (6 * 2 + 3) → ℚ, (∀ i, 0 < request i) ∧
      GeneralRequest (catCore 2) (2 + 2) request ∧
      5 ≤ GeometricFibre.openOddCount (catCore 2) request (2 + 2) := by
  obtain ⟨y, hpos, hgen, hle⟩ := exists_general_positive_request 2
  exact ⟨y, hpos, hgen, by rwa [show catalan (2 + 1) = 5 from catalan_three] at hle⟩

/-! ## 7.  `OddBaseGenusSix` is necessary for the propagation -/

/-- **`OddBaseGenusSix` is necessary for `CountSchedule.C34 2`.**  If `C34 2` holds
at all then it holds in particular over the genus-six caterpillar of loops at the
general positive request `exists_general_positive_request_genusSix` produces, so
`OddBaseGenusSix` follows -- with no other hypothesis.  So *any* statement
sufficient for `C34 2` implies it; in particular it follows from
`Assembly.c34_genusSix`. -/
theorem oddBaseGenusSix_of_c34 (h : CountSchedule.C34 2) : OddBaseGenusSix := by
  obtain ⟨y, hpos, hgen, -⟩ := exists_general_positive_request_genusSix
  refine ⟨StepSupplyGenusSix.catCubicCore, y, hgen, ?_⟩
  exact h StepSupplyGenusSix.catCubicCore.core StepSupplyGenusSix.catCubicCore.cubic
    StepSupplyGenusSix.catCubicCore.connected (by norm_num) y hpos hgen

/-- A ballot classification gives `OddBaseGenusSix`, at any general request. -/
theorem oddBaseGenusSix_of_ballotClassification {request : Fin (6 * 2 + 3) → ℚ}
    (hgen : GeneralRequest (catCore 2) (2 + 2) request)
    (classification : CaterpillarBallot.BallotClassification 2 request) :
    OddBaseGenusSix :=
  ⟨StepSupplyGenusSix.catCubicCore, request, hgen,
    odd_openOddCount_genusSix_of_ballotClassification classification⟩

/-! ## 8.  From the exhaustion package

`BallotCoreIdentification.ballotClassification'` (in `DiagonalClassificationEndgame`)
produces a `CaterpillarBallot.BallotClassification m request` from positivity of the
request together with `BallotSlopes.DiagonalClassification m request`, every
family-side argument being proved inside it by the `ballotFamilyMember*` facts.  So
`OddBaseGenusSix` follows from `DiagonalClassification 2` at a request that is at once
positive and general, and such a request exists (§6). -/

/-- `OddBaseGenusSix` from the exhaustion package `BallotSlopes.DiagonalClassification 2`. -/
theorem oddBaseGenusSix_of_diagonalClassification
    (request : Fin (6 * 2 + 3) → ℚ) (hRequest : ∀ slot, 0 < request slot)
    (hgen : GeneralRequest (catCore 2) (2 + 2) request)
    (classification : BallotSlopes.DiagonalClassification 2 request) :
    OddBaseGenusSix :=
  oddBaseGenusSix_of_ballotClassification hgen
    (BallotCoreIdentification.ballotClassification' 2 hRequest classification)

/-! ## 9.  The orbit test holds at genus two

`DiagonalExtract` derives from the `extract` field of `DiagonalClassification` a
member-free, request-free necessary condition,
`BallotSlopes.BallotDiagonalRelabelStable m`: a failure of it would contradict
`DiagonalClassification` at that `m`.

It holds at `m = 0`, and the proof needs neither an automorphism table nor any
geometry.  `SlopeRigidity.ballotCoreDiag_relabel_eq_of_nonleaf`
reduces the test to the non-leaf slots, because a relabelling carries
self-loops to self-loops and every ballot diagonal reads `2` on a loop.  At
`m = 0` the slot type is `Fin 3`, the leaf slots are `0` and `2`, and therefore
**exactly one** non-leaf slot survives -- so the relabelling fixes it and the
two sides agree pointwise. -/

/-- At genus two the only non-leaf slot is `1`. -/
theorem val_eq_one_of_not_isLeafEdge_genusTwo {slot : Fin (6 * 0 + 3)}
    (h : ¬ DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge 0 slot) :
    slot.val = 1 := by
  have hlt := slot.isLt
  simp only [DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge, not_or] at h
  omega

/-- **The orbit test holds at genus two.**  For every slope sequence and every
incidence-preserving relabelling of `catCore 0`, the ballot diagonal is carried
to a ballot diagonal -- in fact to itself. -/
theorem ballotDiagonalRelabelStable_genusTwo :
    BallotSlopes.BallotDiagonalRelabelStable 0 := by
  intro s d
  refine ⟨s, SlopeRigidity.ballotCoreDiag_relabel_eq_of_nonleaf s s d ?_⟩
  intro slot hslot
  have hsymm : ¬ DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge 0 (d.slot.symm slot) := by
    rw [SlopeRigidity.relabel_isLeafEdge_symm_iff]
    exact hslot
  have hfix : d.slot.symm slot = slot :=
    Fin.ext ((val_eq_one_of_not_isLeafEdge_genusTwo hsymm).trans
      (val_eq_one_of_not_isLeafEdge_genusTwo hslot).symm)
  rw [hfix]

/-- **The orbit test cannot fail at genus two.**  A failure of
`BallotDiagonalRelabelStable m` would contradict `DiagonalClassification` at that
`m` (`DiagonalExtract`); by `ballotDiagonalRelabelStable_genusTwo` there is no such
failure at `m = 0`.

This is a *negative about a refutation*, not a witness for
`DiagonalClassification 0`. -/
theorem not_not_ballotDiagonalRelabelStable_genusTwo :
    ¬ ¬ BallotSlopes.BallotDiagonalRelabelStable 0 :=
  fun h ↦ h ballotDiagonalRelabelStable_genusTwo

/-! ## 10.  The `diagonal` field of `DiagonalClassification 0`

`DiagonalFromSeparation` reduces the `diagonal` field to
`SpineSingleColumn.LeafAvoidingSeparated`: *distinct leaf-avoiding rows never
meet a common column.*

**At `m = 0` this holds for free, and nothing geometric is needed.**  Three facts
compose:

* `LollipopLeafRow.genus_le_leafCount_catCore` -- the target tree of **every**
  member over `catCore m` has at least `2m + 2` leaves.  At `m = 0` that is two.
* `EdgeDenominator.passesAboveLeaf_leafRow` -- the row `h(v)` of a leaf `v`
  passes above a leaf.
* `LollipopDivalentWitness.leaf_eq_of_leafRow_eq` -- distinct leaves sit on
  distinct rows.

So at least **two** of the rows pass above a leaf.  At `m = 0` there are only
`6 * 0 + 3 = 3` rows, so **at most one** row is leaf-avoiding, and a condition
that says "any two leaf-avoiding rows coincide" is vacuously true.  The
argument uses no request, no openness, no odd multiplicity and no genericity. -/

section GenusTwoSeparation

variable {request : Fin (6 * 0 + 3) → ℚ}

/-- **At genus two at most one stable row avoids the target's leaves.**  Two
distinct leaf-avoiding rows plus the two rows forced by the two leaves would be
four rows, and at `m = 0` there are only three. -/
theorem eq_of_not_passesAboveLeaf_genusTwo
    (mem : FibreMember (catCore 0) request (0 + 2)) {r r' : Fin (6 * 0 + 3)}
    (hr : ¬ EdgeDenominator.PassesAboveLeaf mem.fullDim.labelling r)
    (hr' : ¬ EdgeDenominator.PassesAboveLeaf mem.fullDim.labelling r') :
    r = r' := by
  classical
  by_contra hne
  have key : (leafVertices mem.target).card ≤
      (Finset.univ.filter fun x : Fin (6 * 0 + 3) ↦
        EdgeDenominator.PassesAboveLeaf mem.fullDim.labelling x).card := by
    refine Finset.card_le_card_of_injOn
      (fun v ↦ if h : IsLeafVertex mem.target v then LeafFibre.leafRow mem.fullDim h else 0)
      ?_ ?_
    · intro v hv
      have hLeaf : IsLeafVertex mem.target v := (mem_leafVertices v).mp (Finset.mem_coe.mp hv)
      have hval : (if h : IsLeafVertex mem.target v then LeafFibre.leafRow mem.fullDim h else 0)
          = LeafFibre.leafRow mem.fullDim hLeaf := dite_eq_left hLeaf
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      simp only [hval]
      exact EdgeDenominator.passesAboveLeaf_leafRow mem.fullDim hLeaf
    · intro a ha b hb hab
      have hA : IsLeafVertex mem.target a := (mem_leafVertices a).mp (Finset.mem_coe.mp ha)
      have hB : IsLeafVertex mem.target b := (mem_leafVertices b).mp (Finset.mem_coe.mp hb)
      simp only [dite_eq_left hA, dite_eq_left hB] at hab
      exact LollipopDivalentWitness.leaf_eq_of_leafRow_eq mem.fullDim hA hB hab
  have hpair : ({r, r'} : Finset (Fin (6 * 0 + 3))) ⊆
      Finset.univ.filter fun x : Fin (6 * 0 + 3) ↦
        ¬ EdgeDenominator.PassesAboveLeaf mem.fullDim.labelling x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl
    · exact hr
    · exact hr'
  have h2 : 2 ≤ (Finset.univ.filter fun x : Fin (6 * 0 + 3) ↦
      ¬ EdgeDenominator.PassesAboveLeaf mem.fullDim.labelling x).card := by
    exact (Finset.card_pair hne).ge.trans (Finset.card_le_card hpair)
  have htwo : 2 * 0 + 2 ≤ leafCount mem.target :=
    LollipopLeafRow.genus_le_leafCount_catCore 0 mem
  have hleaf : leafCount mem.target = (leafVertices mem.target).card := rfl
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (6 * 0 + 3))))
    (fun x ↦ EdgeDenominator.PassesAboveLeaf mem.fullDim.labelling x)
  have huniv : (Finset.univ : Finset (Fin (6 * 0 + 3))).card = 3 := by simp
  omega

/-- **Leaf-avoiding rows are separated at genus two, for every member.**
`SpineSingleColumn.LeafAvoidingSeparated 0 mem`, with no hypothesis at all. -/
theorem leafAvoidingSeparated_genusTwo (mem : FibreMember (catCore 0) request (0 + 2)) :
    SpineSingleColumn.LeafAvoidingSeparated 0 mem :=
  fun _ _ _ hr hr' _ _ ↦ eq_of_not_passesAboveLeaf_genusTwo mem hr hr'

/-- **The `diagonal` field of `BallotSlopes.DiagonalClassification 0` is
proved.**  Every open odd class over the genus-two caterpillar has a diagonal
representative, unconditionally. -/
theorem diagonal_genusTwo (mem : FibreMember (catCore 0) request (0 + 2))
    (hOpen : mem.Open) (hOdd : mem.HasOddMult) :
    ∃ rep : FibreMember (catCore 0) request (0 + 2),
      rep.Open ∧ rep.HasOddMult ∧ rep.Diagonal ∧
        GeometricFibre.cls rep = GeometricFibre.cls mem :=
  DiagonalFromSeparation.diagonal_of_leafAvoidingSeparated
    (fun mem' _ _ ↦ leafAvoidingSeparated_genusTwo mem') mem hOpen hOdd

/-- **`DiagonalClassification 0` from its last two fields.**  The `diagonal` field
is proved; `extract` (Part II's `prop-caterpillar-ballot`(1) over diagonal members,
proved at `m = 0` in `ExtractGenusTwo`) and `rigid` (`prop-caterpillar-ballot`(2)
over diagonal members) are hypotheses. -/
theorem diagonalClassification_genusTwo_of_extract_rigid
    (extract : ∀ mem : FibreMember (catCore 0) request (0 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (0 + 1)), mem.coreDiag = BallotSlopes.ballotCoreDiag 0 s)
    (rigid : ∀ first second : FibreMember (catCore 0) request (0 + 2),
      first.Open → first.HasOddMult → first.Diagonal →
        second.Open → second.HasOddMult → second.Diagonal →
          first.coreDiag = second.coreDiag →
            GeometricFibre.cls first = GeometricFibre.cls second) :
    BallotSlopes.DiagonalClassification 0 request where
  diagonal := diagonal_genusTwo
  extract := extract
  rigid := rigid

end GenusTwoSeparation

end DraismaVargas.Count.BaseCountParity
