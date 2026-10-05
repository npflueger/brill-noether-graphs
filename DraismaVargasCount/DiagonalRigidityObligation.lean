module

public import DraismaVargasCount.DiagonalClassification
public import DraismaVargasCount.CatFlipRealizedAut
public import DraismaVargasCount.BallotCoreIdentification

@[expose] public section

/-!
# The `rigid` field over diagonal members still carries the core-symmetry obligation

**Source.**  Vargas, Part II (arXiv:2609.09109), the uniqueness in part (2) of
`prop-caterpillar-ballot`: the slope sequence determines the morphism.  This module works
alongside `Count/SlopeRigidity.lean` and `Count/CatFlipRealizedAut.lean`.

## What this module is for

`Count.BallotSlopes.DiagonalClassification` (`Count/DiagonalClassification.lean`) restricts
its `extract` and `rigid` fields to **diagonal** members.  One might hope that this
restriction avoids the members obtained by twisting a member along a core symmetry.  It
does not: `Count.SlopeRigidity.twistMember` -- a diagonal member relabelled along a core
symmetry and re-solved -- is itself *diagonal* (`twistMember_diagonal`).  So the `rigid`
field applies to it on the nose, and everything `Count/SlopeRigidity.lean` derives from the
unrestricted rigidity `CoreDiagRigid` survives the restriction verbatim.  Restricting to
diagonal members costs the obligation nothing.

Concretely: `DiagonalClassification (m+1) request` at a positive request forces
`FibreCaterpillar.caterpillarDatum (m+1)` -- and the gluing datum of **every** ballot member
`ballotFamilyMember (m+1) request s` -- to admit a self-`GeometricDatumIso` inducing
`SlopeRigidity.endSwap`, the exchange of the two loops at the near end of the spine.  That
is the symmetry-realisation half of the uniqueness in `prop-caterpillar-ballot`(2),
unchanged by the restriction.

## A hypothesis-free form of `coreDiagRigid_iff`

`SlopeRigidity.coreDiagRigid_iff` carries the hypothesis

`hdiag : ∀ mem, mem.Open → mem.HasOddMult → mem.Diagonal`.

`Count.ColumnTwist.not_forall_diagonal_of_openOdd` shows that `hdiag` implies the open odd
fibre is empty, and at a positive request it is not
(`FibreCaterpillar.caterpillarMember_open`), so that equivalence applies to no fibre with an
open odd member.  `diagonalRigid_iff` below is the same reduction with `hdiag` *deleted* --
the diagonality that the proof needs is carried by the members the statement quantifies
over, so no hypothesis at all is required.

## What is proved

* `DiagonalRigid` -- the `rigid` field of `BallotSlopes.DiagonalClassification`
  as a standalone proposition, with `diagonalRigid_of_diagonalClassification`
  and `DiagonalRigid.of_coreDiagRigid`.
* **`realizes_of_diagonalRigid`** -- the headline: the restriction to diagonal
  members does not weaken `SlopeRigidity.realizes_of_coreDiagRigid` by one
  quantifier.  `realizes_of_diagonalRigid_of_injective` adds the genericity of Part II's
  `prop-divisors-on-chain` (pairwise distinct edge lengths) and observes it is never used;
  `not_diagonalRigid_of_not_realizes` is the contrapositive.
* `DiagonalDatumIsoSupply`, `DiagonalSymmetryRealized`, **`diagonalRigid_iff`**
  -- the reduction of `rigid` to two statements, with **no hypothesis whatsoever**.
* `realizes_endSwap_of_diagonalRigid`,
  `realizes_endSwap_of_diagonalClassification` -- the end-swap obligation on
  the zig-zag caterpillar member, at every even genus at least four.
* **`realizes_endSwap_ballotFamilyMember_of_diagonalRigid`** and
  `..._of_diagonalClassification` -- the same on every member of the
  ballot family, one per slope sequence, and
  `realizes_endSwap_ballot_genusSix_of_diagonalClassification` at genus six.
* `not_diagonalClassification_of_not_realizes_endSwap`,
  `not_diagonalClassification_of_not_realizes_endSwap_ballot` -- the
  contrapositives.
* `coreDiag_pos_of_open`, `twistMember_open_of_coreDiag_pos` -- openness of a
  twist without any relation between the symmetry and the diagonal:
  `SlopeRigidity.twistMember_open`'s `hstab` is one sufficient condition, and a
  positive core diagonal is another, which is automatic for an open diagonal
  member (`FibreMember.pos_of_open` supplies the request's positivity).
* **`ballotDiagonal_orbit_of_diagonalClassification`**,
  `ballotCoreDiag_orbit_of_diagonalClassification` -- what the *`extract`* field
  costs: over a positive request the image of `BallotSlopes.ballotCoreDiag m`
  must be a subset of `Fin (6m+3) -> Q` **stable under every incidence-preserving
  symmetry of `catCore m`**.  Unlike the `rigid` obligation this reaches every
  core symmetry, not only the diagonal-stabilising ones.
* `not_diagonalClassification_of_orbit_escape` -- one core symmetry and one slope
  sequence whose ballot diagonal it moves off the ballot set would contradict the
  classification, with no gluing datum in sight.  No such pair exists:
  `BallotOrbit.no_orbit_escape` shows that the orbit of `ballotCoreDiag m s` under
  relabellings is `{ballotCoreDiag m s, ballotCoreDiag m (reverseSlopes s)}`
  (`BallotOrbit.ballotCoreDiag_relabel_eq_self_or_reverse`).
* `endSwap_no_orbit_escape` -- the end swap fixes every ballot diagonal pointwise.
* `exists_coreIncidence_eq_two_iff`, `relabel_loop_iff`,
  `catCore_tail_eq_head_iff`, `relabel_isLeafEdge_iff`,
  `relabel_isLeafEdge_symm_iff` -- **a relabelling preserves the self-loops**,
  and at the caterpillar core the self-loops are exactly the `IsLeafEdge` slots.
* `ballotCoreDiag_relabel_eq_of_leaf`, `ballotCoreDiag_relabel_eq_of_nonleaf` --
  hence **the leaf half of the orbit test above is free**: every ballot diagonal
  reads `2` on every leaf slot, so the test reduces from all `6m+3` slots to the
  `4m+2` spine and stem slots.  `BallotOrbitStability` finishes the test with an invariant
  one notch finer: a `Relabel` preserves *loop-adjacency* (having an endpoint that carries a
  self-loop), not merely loopness, and every ballot diagonal is constant on the
  loop-adjacent slots -- the `2m` stems and the two extreme spine slots read `1/2` along
  with the loops' `2`.  That leaves the `2m-1` interior spine slots, which form a path, on
  which any relabelling acts as the identity or the reversal.

## What is not proved here

* **Every result below is a necessary condition** for `DiagonalClassification`.  No
  `DiagonalClassification` is inhabited here, for any `m`, and no `Realizes (endSwap m) _`
  is proved or refuted here for any member.  At genus six the classification holds
  (`CaterpillarAllMembers.diagonalClassification_genusSix`), so the obligations of this
  module are met there.
* **`DiagonalDatumIsoSupply` and `DiagonalSymmetryRealized` are not established here** for
  any core or request.  `diagonalRigid_iff` inhabits neither side.
* **`Aut (catCore m)` is not enumerated here.**  Above genus two the end swap is one element
  of it; this module does not construct the spine reversal, so the end-swap obligation is a
  lower bound on the symmetry-realisation half, not a reduction of it.
* **Nothing here bears on the `diagonal` field**, on the count, or on parity.
-/

namespace DraismaVargas.Count.SlopeRigidity

open DraismaVargas.Count
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.LocalCases
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {c : Core n p} {y : Fin p → ℚ}

/-! ## 1.  The `rigid` field over diagonal members, named -/

/-- **The `rigid` field of `BallotSlopes.DiagonalClassification`, over an
arbitrary core and request.**  This is `CoreDiagRigid` with both members
restricted to diagonal ones. -/
def DiagonalRigid (c : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ first second : FibreMember c y degree,
    first.Open → first.HasOddMult → first.Diagonal →
      second.Open → second.HasOddMult → second.Diagonal →
        first.coreDiag = second.coreDiag →
          GeometricFibre.cls first = GeometricFibre.cls second

/-- The `rigid` field of a `DiagonalClassification` is `DiagonalRigid` at the
caterpillar core. -/
theorem diagonalRigid_of_diagonalClassification {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (classification : BallotSlopes.DiagonalClassification m request) :
    DiagonalRigid (catCore m) request (m + 2) :=
  classification.rigid

/-- The restriction to diagonal members is a weakening. -/
theorem DiagonalRigid.of_coreDiagRigid (hrigid : CoreDiagRigid c y degree) :
    DiagonalRigid c y degree :=
  fun first second hO₁ hM₁ _ hO₂ hM₂ _ heq ↦ hrigid first second hO₁ hM₁ hO₂ hM₂ heq

/-! ## 2.  The obligation survives the restriction -/

/-- **The headline.**  `SlopeRigidity.realizes_of_coreDiagRigid` with its
hypothesis replaced by `DiagonalRigid`.

The proof is that of `realizes_of_coreDiagRigid` with two arguments inserted: `m` is
diagonal by hypothesis, and `twistMember d m h` is diagonal by `twistMember_diagonal`,
its length matrix being `m`'s own.  So restricting `rigid` to diagonal members removes
**no** instance of this obligation: `twistMember` is a twisted member, it is diagonal,
and the `rigid` field applies to it. -/
theorem realizes_of_diagonalRigid (hrigid : DiagonalRigid c y degree)
    (m : FibreMember c y degree) (hOpen : m.Open) (hOdd : m.HasOddMult) (h : m.Diagonal)
    (d : Relabel c c) (hstab : ∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot) :
    Realizes d m := by
  refine (cls_twistMember_eq_iff d m h).mp ?_
  refine hrigid m (twistMember (y' := y) d m h) hOpen hOdd h
    (twistMember_open d m h hstab hOpen) ((twistMember_hasOddMult d m h).mpr hOdd)
    (twistMember_diagonal d m h) ?_
  funext slot
  rw [twistMember_coreDiag, hstab]

/-- **Genericity still buys nothing.**  `twistMember` re-solves the realization
equation rather than transporting the coordinate vector, so the pairwise distinct edge
lengths of Part II's `prop-divisors-on-chain` are never used. -/
theorem realizes_of_diagonalRigid_of_injective (_hinj : Function.Injective y)
    (hrigid : DiagonalRigid c y degree)
    (m : FibreMember c y degree) (hOpen : m.Open) (hOdd : m.HasOddMult) (h : m.Diagonal)
    (d : Relabel c c) (hstab : ∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot) :
    Realizes d m :=
  realizes_of_diagonalRigid hrigid m hOpen hOdd h d hstab

/-- **The contrapositive.** -/
theorem not_diagonalRigid_of_not_realizes
    (m : FibreMember c y degree) (hOpen : m.Open) (hOdd : m.HasOddMult) (h : m.Diagonal)
    (d : Relabel c c) (hstab : ∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot)
    (hno : ¬ Realizes d m) : ¬ DiagonalRigid c y degree :=
  fun hrigid ↦ hno (realizes_of_diagonalRigid hrigid m hOpen hOdd h d hstab)

/-! ## 3.  The reduction, with no hypothesis -/

/-- **Datum supply, over diagonal members.**  Two open odd *diagonal* members
with the same core diagonal have abstractly isomorphic gluing data. -/
def DiagonalDatumIsoSupply (c : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ first second : FibreMember c y degree,
    first.Open → first.HasOddMult → first.Diagonal →
      second.Open → second.HasOddMult → second.Diagonal →
        first.coreDiag = second.coreDiag →
          Nonempty (GeometricDatumIso first.data second.data)

/-- **Symmetry realisation, over diagonal members.**  Every incidence-preserving core
symmetry stabilising an open odd *diagonal* member's core diagonal is realised
by a self-isomorphism of that member's gluing datum. -/
def DiagonalSymmetryRealized (c : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ m : FibreMember c y degree, m.Open → m.HasOddMult → m.Diagonal →
    ∀ d : Relabel c c, (∀ slot, m.coreDiag (d.slot.symm slot) = m.coreDiag slot) → Realizes d m

/-- **The reduction of `DiagonalRigid`, as an equivalence, with no hypothesis at
all.**

`SlopeRigidity.coreDiagRigid_iff` needs `hdiag` -- every open odd member is
diagonal -- in both directions, and `Count.ColumnTwist.not_forall_diagonal_of_openOdd`
shows that `hdiag` fails over any nonempty open odd fibre.  Here the diagonality both
directions need is carried by the members the statement quantifies over, and no
hypothesis survives. -/
theorem diagonalRigid_iff :
    DiagonalRigid c y degree ↔
      DiagonalDatumIsoSupply c y degree ∧ DiagonalSymmetryRealized c y degree := by
  constructor
  · intro hrigid
    refine ⟨?_, ?_⟩
    · intro first second hO₁ hM₁ hD₁ hO₂ hM₂ hD₂ heq
      obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp
        (hrigid first second hO₁ hM₁ hD₁ hO₂ hM₂ hD₂ heq)
      exact ⟨iso.datum⟩
    · intro m hOpen hOdd hDiag d hstab
      exact realizes_of_diagonalRigid hrigid m hOpen hOdd hDiag d hstab
  · rintro ⟨hsupply, hrealize⟩ first second hO₁ hM₁ hD₁ hO₂ hM₂ hD₂ heq
    obtain ⟨i⟩ := hsupply first second hO₁ hM₁ hD₁ hO₂ hM₂ hD₂ heq
    exact cls_eq_of_realizes_defect i
      (hrealize first hO₁ hM₁ hD₁ (defect i) (defect_stabilises_coreDiag hD₁ hD₂ i heq))

/-! ## 5.  The end swap, at every even genus at least four -/

section EndSwap

variable {m : ℕ} {request : Fin (6 * (m + 1) + 3) → ℚ}

/-- **`DiagonalRigid` forces the end swap on the caterpillar member.**
`SlopeRigidity.realizes_endSwap_of_coreDiagRigid` (in `Count/CatFlipRealizedAut.lean`) with
`CoreDiagRigid` replaced by `DiagonalRigid`. -/
theorem realizes_endSwap_of_diagonalRigid (hRequest : ∀ slot, 0 < request slot)
    (hrigid : DiagonalRigid (catCore (m + 1)) request (m + 1 + 2)) :
    Realizes (endSwap m) (caterpillarMember (m + 1) request) :=
  realizes_of_diagonalRigid hrigid (caterpillarMember (m + 1) request)
    (caterpillarMember_open hRequest) (caterpillarMember_hasOddMult (m + 1) request)
    (diagonal_caterpillarMember (m + 1) request) (endSwap m)
    (coreDiag_stable_under_endSwap m)

/-- ... and off the classification itself. -/
theorem realizes_endSwap_of_diagonalClassification (hRequest : ∀ slot, 0 < request slot)
    (classification : BallotSlopes.DiagonalClassification (m + 1) request) :
    Realizes (endSwap m) (caterpillarMember (m + 1) request) :=
  realizes_endSwap_of_diagonalRigid hRequest
    (diagonalRigid_of_diagonalClassification classification)

/-- **The contrapositive**: if no self-isomorphism induces the end swap, the classification
fails. -/
theorem not_diagonalClassification_of_not_realizes_endSwap
    (hRequest : ∀ slot, 0 < request slot)
    (hno : ¬ Realizes (endSwap m) (caterpillarMember (m + 1) request)) :
    ¬ BallotSlopes.DiagonalClassification (m + 1) request :=
  fun classification ↦ hno (realizes_endSwap_of_diagonalClassification hRequest classification)

/-! ### On every member of the ballot family, not just the zig-zag one -/

/-- The ballot member `BallotCoreIdentification.ballotFamilyMember` is diagonal. -/
theorem ballotFamilyMember_diagonal (s : Slopes (2 * (m + 1 + 1))) :
    (BallotCoreIdentification.ballotFamilyMember (m + 1) request s).Diagonal :=
  BallotSlopes.diagonal_of_matrix_eq s
    (BallotCoreIdentification.ballotFamilyMember_matrix (m + 1) request s)

/-- ... and its core diagonal is the ballot diagonal of its slope sequence. -/
theorem ballotFamilyMember_coreDiag (s : Slopes (2 * (m + 1 + 1))) :
    (BallotCoreIdentification.ballotFamilyMember (m + 1) request s).coreDiag =
      BallotSlopes.ballotCoreDiag (m + 1) s :=
  BallotSlopes.coreDiag_eq_of_matrix_eq s
    (BallotCoreIdentification.ballotFamilyMember_matrix (m + 1) request s)
    (BallotCoreIdentification.ballotFamilyMember_slotMap (m + 1) request s)

/-- The end swap stabilises it, for **every** slope sequence. -/
theorem coreDiag_stable_under_endSwap_ballot (s : Slopes (2 * (m + 1 + 1)))
    (slot : Fin (6 * (m + 1) + 3)) :
    (BallotCoreIdentification.ballotFamilyMember (m + 1) request s).coreDiag
        ((endSwap m).slot.symm slot) =
      (BallotCoreIdentification.ballotFamilyMember (m + 1) request s).coreDiag slot := by
  rw [ballotFamilyMember_coreDiag]
  exact endSwap_stabilises_ballotCoreDiag s slot

/-- **The obligation lands on every ballot member.**  For each slope sequence
`s`, `DiagonalRigid` forces the gluing datum of
`BallotCoreIdentification.ballotFamilyMember (m+1) request s` to admit a
self-isomorphism inducing the end swap.  That is `catalan (m + 2)` separate
obligations at genus `2m + 4`, not one. -/
theorem realizes_endSwap_ballotFamilyMember_of_diagonalRigid
    (hRequest : ∀ slot, 0 < request slot)
    (hrigid : DiagonalRigid (catCore (m + 1)) request (m + 1 + 2))
    (s : Slopes (2 * (m + 1 + 1))) :
    Realizes (endSwap m) (BallotCoreIdentification.ballotFamilyMember (m + 1) request s) :=
  realizes_of_diagonalRigid hrigid
    (BallotCoreIdentification.ballotFamilyMember (m + 1) request s)
    (BallotCoreIdentification.ballotFamilyMember_open (m + 1) hRequest s)
    (BallotCoreIdentification.ballotFamilyMember_hasOddMult (m + 1) request s)
    (ballotFamilyMember_diagonal s) (endSwap m) (coreDiag_stable_under_endSwap_ballot s)

/-- ... off the classification. -/
theorem realizes_endSwap_ballotFamilyMember_of_diagonalClassification
    (hRequest : ∀ slot, 0 < request slot)
    (classification : BallotSlopes.DiagonalClassification (m + 1) request)
    (s : Slopes (2 * (m + 1 + 1))) :
    Realizes (endSwap m) (BallotCoreIdentification.ballotFamilyMember (m + 1) request s) :=
  realizes_endSwap_ballotFamilyMember_of_diagonalRigid hRequest
    (diagonalRigid_of_diagonalClassification classification) s

/-- **The contrapositive, on the ballot family.** -/
theorem not_diagonalClassification_of_not_realizes_endSwap_ballot
    (hRequest : ∀ slot, 0 < request slot) (s : Slopes (2 * (m + 1 + 1)))
    (hno : ¬ Realizes (endSwap m)
      (BallotCoreIdentification.ballotFamilyMember (m + 1) request s)) :
    ¬ BallotSlopes.DiagonalClassification (m + 1) request :=
  fun classification ↦ hno
    (realizes_endSwap_ballotFamilyMember_of_diagonalClassification hRequest classification s)

end EndSwap

/-- **Genus six**, spelled out: the classification forces each of the five
ballot seeds' gluing data to realise the end swap. -/
theorem realizes_endSwap_ballot_genusSix_of_diagonalClassification
    {request : Fin (6 * 2 + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot)
    (classification : BallotSlopes.DiagonalClassification 2 request)
    (s : Slopes (2 * (2 + 1))) :
    Realizes (endSwap 1) (BallotCoreIdentification.ballotFamilyMember 2 request s) :=
  realizes_endSwap_ballotFamilyMember_of_diagonalClassification hRequest classification s

/-! ## 6.  What `extract` costs: the ballot diagonals must be an `Aut`-stable set

`realizes_of_diagonalRigid` above reaches only the core symmetries that
*stabilise* a member's core diagonal, because `rigid` compares two members with
the same one.  The `extract` field is reached by **every** core symmetry, and
that is a separate, sharper and entirely finite obligation.

The bridge is that `SlopeRigidity.twistMember_open` is stronger than it needs to
be.  Its hypothesis `hstab` is one sufficient condition for openness; another,
which needs no relation between `d` and the diagonal at all, is that the core
diagonal is *positive* -- and that is automatic for an open diagonal member
(`coreDiag_pos_of_open`, which needs no positivity hypothesis on the request
because `FibreMember.pos_of_open` derives it from openness).  So a diagonal open odd member
twists to a diagonal open odd member along **any** core symmetry, and `extract`
has to accept the moved core diagonal. -/

section Orbit

/-- **The core diagonal of an open diagonal member is positive.**
`Diagonal.coreDiag_mul_coreCoords` solves the realization equation at the slot,
and openness makes the coordinate positive.

The request needs no separate positivity hypothesis: `FibreMember.pos_of_open`
derives it from `hOpen`. -/
theorem coreDiag_pos_of_open {mem : FibreMember c y degree} (h : mem.Diagonal)
    (hOpen : mem.Open) (slot : Fin p) : 0 < mem.coreDiag slot := by
  have hprod := h.coreDiag_mul_coreCoords slot
  have hcc : 0 < mem.coreCoords slot := hOpen (mem.slotMap.symm slot)
  have hpos : 0 < y slot := mem.pos_of_open hOpen slot
  by_contra hle
  have hle' : mem.coreDiag slot ≤ 0 := not_lt.mp hle
  nlinarith

/-- **A positive core diagonal makes every twist open.**  This is
`SlopeRigidity.twistMember_open` with the stabilisation hypothesis replaced by
positivity -- and, unlike that lemma, it places no condition on `d`
whatsoever. -/
theorem twistMember_open_of_coreDiag_pos (d : Relabel c c') {y' : Fin p → ℚ}
    (mem : FibreMember c y degree) (h : mem.Diagonal)
    (hpos : ∀ slot, 0 < mem.coreDiag slot) (hy' : ∀ slot, 0 < y' slot) :
    (twistMember (y' := y') d mem h).Open := by
  intro r
  have hmat : mem.coreDiag (mem.slotMap r) = mem.matrix r r := by
    show mem.matrix _ _ = _
    rw [Equiv.symm_apply_apply]
  show 0 < y' (d.slot (mem.slotMap r)) / mem.matrix r r
  rw [← hmat]
  exact div_pos (hy' _) (hpos _)

/-- **The obligation `extract` carries, for an arbitrary core symmetry.**  Over
a positive request, the core diagonal of every open odd diagonal member, moved
by *any* incidence-preserving symmetry of the core, is again a ballot diagonal.

This is a purely combinatorial, finite condition on the pair
(`Aut (catCore m)`, the image of `BallotSlopes.ballotCoreDiag m`): it says that
image is an `Aut`-stable subset of `Fin (6m+3) → ℚ`.  Nothing about gluing data
enters. -/
theorem ballotDiagonal_orbit_of_diagonalClassification {m : ℕ}
    {request : Fin (6 * m + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot)
    (classification : BallotSlopes.DiagonalClassification m request)
    (mem : FibreMember (catCore m) request (m + 2))
    (hOpen : mem.Open) (hOdd : mem.HasOddMult) (hDiag : mem.Diagonal)
    (d : Relabel (catCore m) (catCore m)) :
    ∃ t : Slopes (2 * (m + 1)),
      (fun slot ↦ mem.coreDiag (d.slot.symm slot)) = BallotSlopes.ballotCoreDiag m t := by
  obtain ⟨t, ht⟩ := classification.extract (twistMember (y' := request) d mem hDiag)
    (twistMember_open_of_coreDiag_pos d mem hDiag
      (coreDiag_pos_of_open hDiag hOpen) hRequest)
    ((twistMember_hasOddMult d mem hDiag).mpr hOdd) (twistMember_diagonal d mem hDiag)
  refine ⟨t, ?_⟩
  rw [← ht]
  funext slot
  exact (twistMember_coreDiag d mem hDiag slot).symm

/-- **The same, on the ballot family**: the classification forces the *set* of
ballot diagonals to be closed under precomposition with every core symmetry. -/
theorem ballotCoreDiag_orbit_of_diagonalClassification {m : ℕ}
    {request : Fin (6 * m + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot)
    (classification : BallotSlopes.DiagonalClassification m request)
    (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)) :
    ∃ t : Slopes (2 * (m + 1)),
      (fun slot ↦ BallotSlopes.ballotCoreDiag m s (d.slot.symm slot)) =
        BallotSlopes.ballotCoreDiag m t := by
  have hdiag : (BallotCoreIdentification.ballotFamilyMember m request s).Diagonal :=
    BallotSlopes.diagonal_of_matrix_eq s
      (BallotCoreIdentification.ballotFamilyMember_matrix m request s)
  have hvalue : (BallotCoreIdentification.ballotFamilyMember m request s).coreDiag =
      BallotSlopes.ballotCoreDiag m s :=
    BallotSlopes.coreDiag_eq_of_matrix_eq s
      (BallotCoreIdentification.ballotFamilyMember_matrix m request s)
      (BallotCoreIdentification.ballotFamilyMember_slotMap m request s)
  obtain ⟨t, ht⟩ := ballotDiagonal_orbit_of_diagonalClassification hRequest classification
    (BallotCoreIdentification.ballotFamilyMember m request s)
    (BallotCoreIdentification.ballotFamilyMember_open m hRequest s)
    (BallotCoreIdentification.ballotFamilyMember_hasOddMult m request s) hdiag d
  exact ⟨t, by rw [← ht, hvalue]⟩

/-- **The orbit test.**  A core symmetry and a slope sequence whose ballot diagonal
it moves off the ballot set would contradict `Count.BallotSlopes.DiagonalClassification`
outright -- no gluing datum, no isomorphism, no `Realizes`: just `Aut (catCore m)` against
the explicit function `BallotSlopes.ballotCoreDiag`.  `BallotOrbit.no_orbit_escape` shows
that no such pair exists, so this records what `extract` costs rather than a way to
contradict it. -/
theorem not_diagonalClassification_of_orbit_escape {m : ℕ}
    {request : Fin (6 * m + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot)
    (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m))
    (hescape : ∀ t : Slopes (2 * (m + 1)),
      (fun slot ↦ BallotSlopes.ballotCoreDiag m s (d.slot.symm slot)) ≠
        BallotSlopes.ballotCoreDiag m t) :
    ¬ BallotSlopes.DiagonalClassification m request := by
  intro classification
  obtain ⟨t, ht⟩ := ballotCoreDiag_orbit_of_diagonalClassification hRequest classification s d
  exact hescape t ht

/-- **The end swap does not escape.**  Its four moved slots carry the values
`2, 1/s₁, 1/2, 2` and `s₁ = 2` for every slope sequence, so the ballot diagonal
is not merely carried into the set but fixed pointwise
(`SlopeRigidity.endSwap_stabilises_ballotCoreDiag`). -/
theorem endSwap_no_orbit_escape {m : ℕ} (s : Slopes (2 * (m + 1 + 1))) :
    (fun slot ↦ BallotSlopes.ballotCoreDiag (m + 1) s ((endSwap m).slot.symm slot)) =
      BallotSlopes.ballotCoreDiag (m + 1) s :=
  funext fun slot ↦ endSwap_stabilises_ballotCoreDiag s slot

end Orbit

/-! ## 7.  Half of that test is free: a relabelling preserves the loops

The orbit condition of §6 quantifies over all `6m+3` slots, but the `g = 2m+2`
leaf slots cost nothing.  `coreIncidence c v e = 2` says exactly that `e` is a
self-loop at `v`, and a `Relabel` preserves every incidence multiplicity, so it
carries loops to loops; at the caterpillar core the loops are exactly the
`IsLeafEdge` slots, on which every ballot diagonal reads `2`.

So the test reduces to the `4m+2` non-leaf slots, where the values are the stem
`1/2` and the spine `1/s_i`. -/

section Loops

/-- **A slot is a self-loop exactly when some vertex meets it twice.** -/
theorem exists_coreIncidence_eq_two_iff (c : Core n p) (e : Fin p) :
    (∃ v, coreIncidence c v e = 2) ↔ c.tail e = c.head e := by
  constructor
  · rintro ⟨v, hv⟩
    rw [coreIncidence_eq] at hv
    by_cases ht : c.tail e = v
    · by_cases hh : c.head e = v
      · rw [ht, hh]
      · rw [ite_eq_left ht, ite_eq_right hh] at hv; omega
    · rw [ite_eq_right ht] at hv
      split_ifs at hv <;> omega
  · intro h
    exact ⟨c.tail e, by rw [coreIncidence_eq, ite_eq_left rfl, ← h, ite_eq_left rfl]⟩

/-- **A relabelling carries self-loops to self-loops.**  Only the `incidence`
field is used. -/
theorem relabel_loop_iff {c c' : Core n p} (d : Relabel c c') (e : Fin p) :
    c'.tail (d.slot e) = c'.head (d.slot e) ↔ c.tail e = c.head e := by
  rw [← exists_coreIncidence_eq_two_iff, ← exists_coreIncidence_eq_two_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨d.vtx.symm w, ?_⟩
    have h := d.incidence (d.vtx.symm w) e
    rw [Equiv.apply_symm_apply] at h
    rw [← h, hw]
  · rintro ⟨v, hv⟩
    exact ⟨d.vtx v, by rw [d.incidence v e, hv]⟩

/-- **At the caterpillar core the self-loops are exactly the leaf slots.**  The
head of a non-leaf row is the target occurrence itself and its tail the parent,
and those two have different branch indices. -/
theorem catCore_tail_eq_head_iff (M : ℕ) (e : Fin (6 * M + 3)) :
    (catCore M).tail e = (catCore M).head e ↔
      DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge M e := by
  have hlt := e.isLt
  rw [Fin.ext_iff, catCore_tail_val, catCore_head_val]
  unfold catTailVal catHeadVal branchIdx
    DraismaVargas.Infrastructure.CaterpillarTree.parentIndex
    DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge
  split_ifs <;> omega

/-- **A relabelling of the caterpillar core preserves the leaf slots.** -/
theorem relabel_isLeafEdge_iff {M : ℕ} (d : Relabel (catCore M) (catCore M))
    (e : Fin (6 * M + 3)) :
    DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge M (d.slot e) ↔
      DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge M e := by
  rw [← catCore_tail_eq_head_iff, ← catCore_tail_eq_head_iff]
  exact relabel_loop_iff d e

theorem relabel_isLeafEdge_symm_iff {M : ℕ} (d : Relabel (catCore M) (catCore M))
    (e : Fin (6 * M + 3)) :
    DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge M (d.slot.symm e) ↔
      DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge M e := by
  have h := relabel_isLeafEdge_iff d (d.slot.symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- **The leaf half of the orbit test is automatic.**  Every ballot diagonal
reads `2` on every leaf slot, and a relabelling keeps leaf slots leaf slots, so
the two sides agree there for *any* pair of slope sequences. -/
theorem ballotCoreDiag_relabel_eq_of_leaf {M : ℕ} (s t : Slopes (2 * (M + 1)))
    (d : Relabel (catCore M) (catCore M)) (slot : Fin (6 * M + 3))
    (hleaf : DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge M slot) :
    BallotSlopes.ballotCoreDiag M s (d.slot.symm slot) =
      BallotSlopes.ballotCoreDiag M t slot := by
  rw [BallotSlopes.ballotCoreDiag_leaf s ((relabel_isLeafEdge_symm_iff d slot).mpr hleaf),
    BallotSlopes.ballotCoreDiag_leaf t hleaf]

/-- **The orbit test reduces to the non-leaf slots.**  The remaining obligation is over
the `4m+2` spine and stem slots only; `BallotOrbitStability` settles it. -/
theorem ballotCoreDiag_relabel_eq_of_nonleaf {M : ℕ} (s t : Slopes (2 * (M + 1)))
    (d : Relabel (catCore M) (catCore M))
    (h : ∀ slot, ¬ DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge M slot →
      BallotSlopes.ballotCoreDiag M s (d.slot.symm slot) =
        BallotSlopes.ballotCoreDiag M t slot) :
    (fun slot ↦ BallotSlopes.ballotCoreDiag M s (d.slot.symm slot)) =
      BallotSlopes.ballotCoreDiag M t := by
  funext slot
  by_cases hleaf : DraismaVargas.LocalCases.CaterpillarPruning.IsLeafEdge M slot
  · exact ballotCoreDiag_relabel_eq_of_leaf s t d slot hleaf
  · exact h slot hleaf

end Loops

end DraismaVargas.Count.SlopeRigidity
