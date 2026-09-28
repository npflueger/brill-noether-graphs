import DraismaVargasCount.GeometricCountFamily
import DraismaVargasCount.FibreCaterpillar
import Utilities.Combinatorics.Slopes

/-!
# The base count over the caterpillar of loops, reduced to the ballot family

**Source.**  Vargas, Part II (arXiv:2609.09109), the subsection on caterpillars of loops
(`lm:combinatorial-structure-caterpillar-of-loops`, `prop-caterpillar-ballot`(1) and (2),
`lm:catalan-many`, `prop-divisors-on-chain`) and the caterpillar step of the proof of the
main theorem (`thm`).  The count here is
`GeometricFibre.openOddCount (catCore m) request (m + 2)`, never `oddCount`
(which `SegmentWalls.oddCount_eq_oddCount` proves request-independent) and never a
count over the cores of a `Spec`, which demands `core_loopless`, whereas `catCore m`
has a self-loop at slot `0`.

## The genus dictionary

`catCore m : Core (4 * m + 2) (6 * m + 3)` is the stable core of the caterpillar
of loops of genus `g = 2 * m + 2`: `4m + 2 = 2g - 2` vertices, `6m + 3 = 3g - 3`
slots, `g` self-loops.  The degree is `m + 2`, and `ρ = g - 2(g - d + 1) = 0`.
The index set of the classification is therefore `Slopes (2 * (m + 1))`, whose
argument `2 * (m + 1)` is that genus written so that
`Slopes.card_eq_catalan (m + 1)` applies on the nose; `genus_eq` below records
`2 * (m + 1) = 2 * m + 2`.  The count is `catalan (m + 1)`, which at `m = 2`
(genus six, degree four) is `catalan 3 = 5` -- Part II's five ballot sequences.

Note that `catalan (m + 1)` is **not** odd for every `m` (`catalan 2 = 2`, at
`m = 1`, genus four); the base *parity* statement the genus-six count needs is the
genus-six instance, and the general statement here is a cardinality, not a
parity.

## What is proved

* `BallotFamily m request` -- a map from slope sequences to members of the
  labelled fibre over `(catCore m, request)`, each open, each of odd
  multiplicity, with pairwise distinct geometric classes.
* `BallotClassification m request` -- that structure together with the
  surjective half: every open member of odd multiplicity is isomorphic over the
  core to one of the family.
* `slopesEquivOpenOdd`, `ballotEquivOpenOdd` -- from a `BallotClassification`,
  the **bijection** of slope (resp. ballot) sequences with the open classes of
  odd multiplicity, which is what `prop-caterpillar-ballot`(2) asserts and what
  `openOddCount_eq_catalan` is the cardinality shadow of.
* `coordsMultiset_caterpillarMember` -- the caterpillar member's coordinate multiset,
  the handle for the injectivity obligation.
* `catalan_le_openOddCount` -- from a `BallotFamily`,
  `catalan (m + 1) ≤ openOddCount (catCore m) request (m + 2)`.
* `openOddCount_eq_catalan` -- from a `BallotClassification`,
  `openOddCount (catCore m) request (m + 2) = catalan (m + 1)`.
* `five_le_openOddCount_genusSix`, `openOddCount_genusSix_eq_five` -- the two
  genus-six instances: the base count, conditional on the two packages.
* `genusTwoFamily` -- **the family structure is instantiable**: at `m = 0`
  (genus two, degree two) `Slopes 2` is a one-point type, `catalan 1 = 1`, and
  `FibreCaterpillar.caterpillarMember` is the whole family.  This is
  a non-vacuity witness for `BallotFamily`, not new numerical content: the bound
  it yields, `1 ≤ openOddCount (catCore 0) request 2`, is
  `GeometricFibre.caterpillar_openOddCount_pos`.
* `one_le_openOddCount` -- that positivity, restated as a lower bound, for
  every `m` and every positive request.
* `openOddCount_smul_request` -- the base count is unchanged by positive
  rescaling of the request (an instance of
  `GeometricFibre.openOddCount_smul`).

## What is NOT proved here (every hypothesis, explicitly)

Everything geometric.  This module builds no member other than
`FibreCaterpillar.caterpillarMember`.  `BallotFamily m request` is inhabited at every
`m` and every positive request by `BallotCoreIdentification.ballotFamily`, and a
`BallotClassification` is assembled from `BallotSlopes.DiagonalClassification` in
`DiagonalClassificationEndgame`.  The inputs, field by field:

* the family `member : Slopes (2 * (m + 1)) → FibreMember (catCore m) request
  (m + 2)` itself: the ballot-parametrized gluing datum, with the
  `m(B_i) - 2` grafted length-two dangling paths, together with its
  `FullDimensionalSourcePresentation`, `DiagonalPattern` and determinant.
* `member_hasOddMult`: `absMult = 1` for every ballot sequence
  (`BallotMultiplicity`; for the zig-zag sequence alone,
  `caterpillarMember_absMult`).
* `member_injective`: distinct slope sequences give distinct classes.  The tool
  for it is `GeometricFibre.cls_injective_of_coordsMultiset_injective`: distinct
  coordinate multisets give distinct classes, and the coordinates are the
  request divided by the diagonal of the length matrix, which records the
  slopes.
* `member_surjective`: the local structure of the caterpillar fibre (bridge
  index two, `φ(C)` a leaf, `r_φ(A) = 1`, the spine injective, `A_φ` diagonal;
  Part II's `lm:bridge-and-loop` and `lm:combinatorial-structure-caterpillar-of-loops`),
  followed by the exhaustion half of `prop-caterpillar-ballot`(1) (that the
  slopes of an actual full-dimensional morphism form a `Slopes`) and of (2)
  (that the slope sequence determines the morphism).
  `LollipopLeafRow` proves `genus_le_leafCount_catCore` for *every*
  member of the fibre -- a stable row cannot close up at a branch vertex, since
  a closed row avoiding the leaves would be a closed non-backtracking walk in a
  genus-zero target.  `CoreSlotCoords` and `BallotSlopeSeparation` give the
  injective half of the uniqueness through a core-slot invariant that needs
  no genericity.

No statement here asserts that the count is odd.
-/

namespace DraismaVargas.Count.CaterpillarBallot

open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar
open Utilities.Certificate.ExplicitPotential (Core)

/-- The genus of the caterpillar core `catCore m`, in the two spellings used
below. -/
theorem genus_eq (m : ℕ) : 2 * (m + 1) = 2 * m + 2 := by ring

/-! ## 1.  The two hypothesis packages -/

/-- **A ballot family over the caterpillar of loops.**  The ballot members and
their distinctness, packaged as a hypothesis: a member of
the labelled fibre over `(catCore m, request)` for each slope sequence of genus
`2 * (m + 1) = 2m + 2`, each in the open cone, each of odd multiplicity, with
pairwise distinct classes in the geometric quotient.

`genusTwoFamily` inhabits it at `m = 0`, and
`BallotCoreIdentification.ballotFamily` inhabits it at every `m`, given a
positive request. -/
structure BallotFamily (m : ℕ) (request : Fin (6 * m + 3) → ℚ) where
  /-- The member attached to a slope sequence. -/
  member : Slopes (2 * (m + 1)) → FibreMember (catCore m) request (m + 2)
  /-- Every member lies in the open cone. -/
  member_open : ∀ s, (member s).Open
  /-- Every member has odd multiplicity (in fact multiplicity one). -/
  member_hasOddMult : ∀ s, (member s).HasOddMult
  /-- Distinct slope sequences give non-isomorphic members. -/
  member_injective : Function.Injective fun s ↦ GeometricFibre.cls (member s)

/-- **A ballot classification.**  A `BallotFamily` that additionally exhausts the
open odd part of the fibre: every open member of odd multiplicity is a ballot member,
up to isomorphism over the core (the exhaustion half of Part II's
`prop-caterpillar-ballot`). -/
structure BallotClassification (m : ℕ) (request : Fin (6 * m + 3) → ℚ) extends
    BallotFamily m request where
  /-- Every open member of odd multiplicity is one of the family, up to
  isomorphism over the core. -/
  member_surjective : ∀ mem : FibreMember (catCore m) request (m + 2),
    mem.Open → mem.HasOddMult → ∃ s, GeometricFibre.cls (member s) = GeometricFibre.cls mem

/-! ## 2.  The count, conditional on those packages -/

/-- **The lower bound.**  A ballot family gives `catalan (m + 1)` distinct open
classes of odd multiplicity. -/
theorem catalan_le_openOddCount {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (family : BallotFamily m request) :
    catalan (m + 1) ≤ GeometricFibre.openOddCount (catCore m) request (m + 2) := by
  have hle := GeometricFibre.card_le_openOddCount family.member family.member_open
    family.member_hasOddMult family.member_injective
  rwa [Nat.card_eq_fintype_card, Slopes.card_eq_catalan] at hle

/-- **The count.**  A ballot classification computes the base count exactly. -/
theorem openOddCount_eq_catalan {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (classification : BallotClassification m request) :
    GeometricFibre.openOddCount (catCore m) request (m + 2) = catalan (m + 1) := by
  have heq := GeometricFibre.openOddCount_eq_card classification.member
    classification.member_open classification.member_hasOddMult
    classification.member_injective classification.member_surjective
  rwa [Nat.card_eq_fintype_card, Slopes.card_eq_catalan] at heq

/-- **The bijection of slope sequences with classes, conditional on its inputs.**  A
ballot classification identifies the slope sequences of genus `2m + 2` with the open
classes of odd multiplicity of the labelled fibre over `(catCore m, request)`.  This is
the statement `prop-caterpillar-ballot`(2) of Part II makes, in the form the count
uses; `openOddCount_eq_catalan` is its cardinality shadow. -/
noncomputable def slopesEquivOpenOdd {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (classification : BallotClassification m request) :
    Slopes (2 * (m + 1)) ≃ GeometricFibre.OpenOdd (catCore m) request (m + 2) :=
  GeometricFibre.openOddEquiv classification.member classification.member_open
    classification.member_hasOddMult classification.member_injective
    classification.member_surjective

/-- The same bijection read on the ballot side, through
`Slopes.equivBallot`: the open odd classes of the caterpillar fibre are the
ballot sequences of length `g = 2m + 2`, which is Part II's passage from slope
sequences to ballot sequences composed with `prop-caterpillar-ballot`(2). -/
noncomputable def ballotEquivOpenOdd {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (classification : BallotClassification m request) :
    Ballot (2 * (m + 1)) ≃ GeometricFibre.OpenOdd (catCore m) request (m + 2) :=
  (Slopes.equivBallot (g := 2 * (m + 1)) (by omega)).symm.trans
    (slopesEquivOpenOdd classification)

/-! ## 3.  Genus six: the base count -/

/-- **The base count, lower half.**  At genus six a ballot family gives five open
classes of odd multiplicity. -/
theorem five_le_openOddCount_genusSix {request : Fin (6 * 2 + 3) → ℚ}
    (family : BallotFamily 2 request) :
    5 ≤ GeometricFibre.openOddCount (catCore 2) request (2 + 2) := by
  have hle := catalan_le_openOddCount family
  rwa [show catalan (2 + 1) = 5 from catalan_three] at hle

/-- **The base count.**  At genus six a ballot classification gives the base count
`5`, `catalan 3`: Part II's five ballot sequences, each of multiplicity one. -/
theorem openOddCount_genusSix_eq_five {request : Fin (6 * 2 + 3) → ℚ}
    (classification : BallotClassification 2 request) :
    GeometricFibre.openOddCount (catCore 2) request (2 + 2) = 5 := by
  have heq := openOddCount_eq_catalan classification
  rwa [show catalan (2 + 1) = 5 from catalan_three] at heq

/-! ## 4.  What is unconditional -/

/-- The caterpillar member, as a lower bound on the base count, for every
`m` and every positive request. -/
theorem one_le_openOddCount (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    1 ≤ GeometricFibre.openOddCount (catCore m) request (m + 2) :=
  GeometricFibre.caterpillar_openOddCount_pos m hRequest

/-- The base count is unchanged by positive rescaling of the request.  This does
not make it constant on the positive orthant: it is constancy along rays. -/
theorem openOddCount_smul_request (m : ℕ) {c : ℚ} (hc : 0 < c)
    (request : Fin (6 * m + 3) → ℚ) :
    GeometricFibre.openOddCount (catCore m) (c • request) (m + 2) =
      GeometricFibre.openOddCount (catCore m) request (m + 2) :=
  GeometricFibre.openOddCount_smul (catCore m) (m + 2) hc request

/-- The coordinate multiset of the caterpillar member: the request divided
entry by entry by the diagonal of the length matrix.  This is the handle
`GeometricFibre.cls_injective_of_coordsMultiset_injective` needs, made explicit
here because the diagonal is exactly where the slopes of a ballot caterpillar
will differ (`FibreCaterpillar.catDiag_eq`: `2` on a leaf row, `1/2` on a pair
edge, `1` on a slope-one spine edge). -/
theorem coordsMultiset_caterpillarMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).coordsMultiset =
      (Finset.univ : Finset (Fin (6 * m + 3))).val.map
        (fun slot ↦ request slot / catDiag m slot) := rfl

/-! ## 5.  Non-vacuity of `BallotFamily` -/

/-- At genus two there is exactly one slope sequence: `catalan 1 = 1`. -/
theorem subsingleton_slopes_genusTwo : Subsingleton (Slopes (2 * (0 + 1))) := by
  have hcard : Fintype.card (Slopes (2 * (0 + 1))) = 1 := by
    rw [Slopes.card_eq_catalan (0 + 1)]
    exact catalan_one
  exact Fintype.card_le_one_iff_subsingleton.mp hcard.le

/-- **`BallotFamily` is instantiable.**  At `m = 0` -- genus two, degree two --
the slope sequences form a one-point type and the caterpillar member is
the whole family.  This is a non-vacuity witness for the hypothesis package, not
new numerical content. -/
noncomputable def genusTwoFamily {request : Fin (6 * 0 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) : BallotFamily 0 request where
  member := fun _ ↦ caterpillarMember 0 request
  member_open := fun _ ↦ caterpillarMember_open hRequest
  member_hasOddMult := fun _ ↦ caterpillarMember_hasOddMult 0 request
  member_injective := by
    have hsub := subsingleton_slopes_genusTwo
    intro a b _
    exact hsub.elim a b

/-- The bound `genusTwoFamily` yields, spelled out: `catalan 1 = 1`. -/
theorem one_le_openOddCount_genusTwo {request : Fin (6 * 0 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    1 ≤ GeometricFibre.openOddCount (catCore 0) request (0 + 2) := by
  have hle := catalan_le_openOddCount (genusTwoFamily hRequest)
  rwa [show catalan (0 + 1) = 1 from catalan_one] at hle

end DraismaVargas.Count.CaterpillarBallot
