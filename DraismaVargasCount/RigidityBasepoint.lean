module

public import DraismaVargasCount.DiagonalRigidityObligation
public import DraismaVargasCount.BaseCountParity
public import DraismaVargasCount.ExtractGenusTwo

@[expose] public section

/-!
# Rigidity through a base point

The `rigid` field of `BallotSlopes.DiagonalClassification` asks that two diagonal open members of
odd multiplicity with the same core diagonal lie in the same geometric class
(`SlopeRigidity.DiagonalRigid`).  `SlopeRigidity` and `DiagonalRigidityObligation` split it into
two residues: (A) `SlopeRigidity.DiagonalDatumIsoSupply`, two such members have abstractly
isomorphic gluing data; and (B) `SlopeRigidity.DiagonalSymmetryRealized`, a core symmetry
stabilising a member's core diagonal is realised inside that member's own gluing datum.

This module observes that residue (B) never has to be checked on any member other than a base
point.  `SlopeRigidity.cls_eq_of_realizes_defect` corrects an arbitrary `GeometricDatumIso` to an
isomorphism *over the core* as soon as the **first** member realises the defect; putting the base
point first, the member being compared with it contributes nothing.

## Main results

* §1, `FullySymmetric`, `DatumIsoBase` -- a base member realising every core symmetry, and the
  base-pointed supply of datum isomorphisms.  `cls_eq_of_datumIso`, `cls_eq_base` -- **the
  general lemma**: over a fully symmetric base, an abstract isomorphism of gluing data already is
  an equality of geometric classes.  No diagonality, no openness, no oddness, no request
  hypothesis.  `coreDiagRigid_of_base`, `diagonalRigid_of_base`, `openOddCount_eq_one_of_base`,
  `datumIsoBase_of_openOddCount_eq_one` -- consequently `rigid` holds with no core diagonal in
  sight, and the open odd count is one; conversely a count of one gives the datum isomorphisms.
  So what is left of `rigid` over a fully symmetric base is the pure datum statement

  > every open odd member's gluing datum is abstractly isomorphic to the base member's.

* §2, `not_fullySymmetric_and_datumIsoBase_of_not_coreDiagRigid` -- wherever the unrestricted
  form of `rigid` (`SlopeRigidity.CoreDiagRigid`) fails, no base point is both fully symmetric and
  a datum base.  Over the caterpillar of loops of even genus at least four, at a positive
  request, `CoreDiagRigid` fails, so the fully symmetric form of the argument is special to genus
  two.
* §3, `cls_eq_of_datumIso_of_coreDiag`, `diagonalRigid_of_bases`, `diagonalRigid_of_ballotBases`
  -- **the same move at every genus, with the stabilising condition kept.**
  `SlopeRigidity.defect_stabilises_coreDiag` means a base point only has to realise the
  symmetries fixing its *own* core diagonal, so with the `extract` field in hand `rigid` follows
  from residue (B) on the ballot members (`BallotCoreIdentification.ballotFamilyMember`) alone,
  together with residue (A) *based at* those members.  Neither residue is ever needed between two
  arbitrary members.  `ballotFamilyMember_diagonal`, `ballotFamilyMember_coreDiag` -- the ballot
  member is diagonal, with the ballot diagonal of its slope sequence as core diagonal, at every
  `m`.

`DiagonalClassificationGenusSix` builds the `rigid` field with `diagonalRigid_of_ballotBases`, and
the lemmas of §3 on the ballot members are used in `CaterpillarAllMembers` for the base count
(step 1 of `DraismaVargasCount.Assembly`).
-/

namespace DraismaVargas.Count.RigidityBasepoint

open DraismaVargas.Count
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.SlopeRigidity
open DraismaVargas.LocalCases
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {c : Core n p} {y : Fin p → ℚ}

/-! ## 1.  A base point that realises every core symmetry -/

/-- **A member realising every incidence-preserving symmetry of the core.**
This is residue (B) concentrated on a single member, with the stabilising
condition on the core diagonal dropped: the symmetry is asked for outright. -/
def FullySymmetric (base : FibreMember c y degree) : Prop :=
  ∀ d : Relabel c c, Realizes d base

/-- **The base-pointed supply of datum isomorphisms.**  Every open odd member's
gluing datum is abstractly isomorphic to the base member's.  Unlike
`SlopeRigidity.DiagonalDatumIsoSupply` there is no core diagonal in the
statement, and no diagonality hypothesis on the member. -/
def DatumIsoBase (base : FibreMember c y degree) : Prop :=
  ∀ mem : FibreMember c y degree, mem.Open → mem.HasOddMult →
    Nonempty (GeometricDatumIso base.data mem.data)

/-- **The general lemma.**  Over a fully symmetric base point an abstract
isomorphism of gluing data is already an equality of geometric classes: the
defect the isomorphism leaves on the core is realised by the base member, and
`cls_eq_of_realizes_defect` corrects it.

The base point must come *first*: `cls_eq_of_realizes_defect` asks the first
member to realise the defect, which is exactly why nothing is required of
`mem`. -/
theorem cls_eq_of_datumIso {base mem : FibreMember c y degree}
    (hsym : FullySymmetric base) (i : GeometricDatumIso base.data mem.data) :
    GeometricFibre.cls base = GeometricFibre.cls mem :=
  cls_eq_of_realizes_defect i (hsym (defect i))

/-- Every open odd member lies in the base point's class. -/
theorem cls_eq_base {base : FibreMember c y degree} (hsym : FullySymmetric base)
    (hbase : DatumIsoBase base) (mem : FibreMember c y degree)
    (hOpen : mem.Open) (hOdd : mem.HasOddMult) :
    GeometricFibre.cls mem = GeometricFibre.cls base :=
  ((hbase mem hOpen hOdd).elim fun i ↦ cls_eq_of_datumIso hsym i).symm

/-- **The unrestricted `rigid`, from a base point.**  Note that the core
diagonals play no part: any two open odd members are in the base point's class,
so the hypothesis `first.coreDiag = second.coreDiag` is discarded. -/
theorem coreDiagRigid_of_base {base : FibreMember c y degree} (hsym : FullySymmetric base)
    (hbase : DatumIsoBase base) : CoreDiagRigid c y degree :=
  fun first second hO₁ hM₁ hO₂ hM₂ _ ↦
    (cls_eq_base hsym hbase first hO₁ hM₁).trans (cls_eq_base hsym hbase second hO₂ hM₂).symm

/-- The diagonal form of `rigid` (`DiagonalRigid`), from a base point. -/
theorem diagonalRigid_of_base {base : FibreMember c y degree} (hsym : FullySymmetric base)
    (hbase : DatumIsoBase base) : DiagonalRigid c y degree :=
  DiagonalRigid.of_coreDiagRigid (coreDiagRigid_of_base hsym hbase)

/-- **And the count is one.**  A fully symmetric base point that every open odd
member's datum is isomorphic to exhausts the open odd subfibre. -/
theorem openOddCount_eq_one_of_base {base : FibreMember c y degree}
    (hsym : FullySymmetric base) (hbase : DatumIsoBase base)
    (hOpen : base.Open) (hOdd : base.HasOddMult) :
    GeometricFibre.openOddCount c y degree = 1 := by
  have h := GeometricFibre.openOddCount_eq_card (ι := Unit) (fun _ ↦ base)
    (fun _ ↦ hOpen) (fun _ ↦ hOdd) (fun a b _ ↦ Subsingleton.elim a b)
    (fun mem hO hM ↦ ⟨(), (cls_eq_base hsym hbase mem hO hM).symm⟩)
  rwa [Nat.card_unique] at h

/-- **The converse.**  If the count is one, every open odd member is in the base
point's class and in particular its datum is isomorphic to the base's.  So
`DatumIsoBase` is not stronger than the count it produces. -/
theorem datumIsoBase_of_openOddCount_eq_one {base : FibreMember c y degree}
    (hOpen : base.Open) (hOdd : base.HasOddMult)
    (hcount : GeometricFibre.openOddCount c y degree = 1) : DatumIsoBase base := by
  intro mem hO hM
  have hsub : Subsingleton (GeometricFibre.OpenOdd c y degree) :=
    (Nat.card_eq_one_iff_unique.mp hcount).1
  have hcls : GeometricFibre.cls base = GeometricFibre.cls mem :=
    congrArg Subtype.val (hsub.elim (GeometricFibre.clsOpenOdd base hOpen hOdd)
      (GeometricFibre.clsOpenOdd mem hO hM))
  exact (GeometricFibre.cls_eq_cls_iff.mp hcls).elim fun iso ↦ ⟨iso.datum⟩

/-! ## 2.  The limits of the fully symmetric base point -/

/-- Wherever the unrestricted `rigid` is false, no base point is both fully
symmetric and a datum base. -/
theorem not_fullySymmetric_and_datumIsoBase_of_not_coreDiagRigid
    (h : ¬ CoreDiagRigid c y degree) (base : FibreMember c y degree) :
    ¬ (FullySymmetric base ∧ DatumIsoBase base) :=
  fun hpair ↦ h (coreDiagRigid_of_base hpair.1 hpair.2)

/-! ## 3.  The same move at every genus, with the stabiliser kept

§1--§2 drop the stabilising condition on the core diagonal, which is what makes
`FullySymmetric` unavailable above genus two.  Keeping it costs nothing and
generalises the move: `SlopeRigidity.defect_stabilises_coreDiag` says the defect
of a datum isomorphism between two *diagonal* members with the same core
diagonal already stabilises that diagonal, so a base point only ever has to
realise the symmetries that fix its own core diagonal. -/

/-- **Residue (B) is a statement about base points.**  If a diagonal member
realises every core symmetry stabilising its own core diagonal, then every
diagonal member with the same core diagonal and an abstractly isomorphic gluing
datum is in its class.  Nothing is assumed about the second member beyond
diagonality. -/
theorem cls_eq_of_datumIso_of_coreDiag {base mem : FibreMember c y degree}
    (hbD : base.Diagonal) (hmD : mem.Diagonal)
    (hstab : ∀ d : Relabel c c,
      (∀ slot, base.coreDiag (d.slot.symm slot) = base.coreDiag slot) → Realizes d base)
    (heq : base.coreDiag = mem.coreDiag)
    (i : GeometricDatumIso base.data mem.data) :
    GeometricFibre.cls base = GeometricFibre.cls mem :=
  cls_eq_of_realizes_defect i (hstab (defect i) (defect_stabilises_coreDiag hbD hmD i heq))

/-- **The diagonal form of `rigid` from a family of base points, at every
genus.**  With the `extract` field in hand, `rigid` follows from

* one diagonal base member per slope sequence, carrying that sequence's ballot
  diagonal -- `BallotCoreIdentification.ballotFamilyMember` is such a family, by
  `ballotFamilyMember_diagonal` and `ballotFamilyMember_coreDiag` below;
* residue (B) **on those members only** -- which is the form in which
  `EndSwapRealized` discharges its instances, and which
  `SlopeRigidity.realizes_endSwap_ballotFamilyMember_of_diagonalRigid` asks for;
* residue (A) **based at those members** rather than between arbitrary pairs.

So neither residue ever has to be stated between two arbitrary members.  The
three inputs are hypotheses here. -/
theorem diagonalRigid_of_bases {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (base : Slopes (2 * (m + 1)) → FibreMember (catCore m) request (m + 2))
    (hbD : ∀ s, (base s).Diagonal)
    (hbval : ∀ s, (base s).coreDiag = BallotSlopes.ballotCoreDiag m s)
    (hstab : ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ slot, (base s).coreDiag (d.slot.symm slot) = (base s).coreDiag slot) →
        Realizes d (base s))
    (hsupply : ∀ (s : Slopes (2 * (m + 1))) (mem : FibreMember (catCore m) request (m + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag m s →
          Nonempty (GeometricDatumIso (base s).data mem.data))
    (hextract : ∀ mem : FibreMember (catCore m) request (m + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (m + 1)), mem.coreDiag = BallotSlopes.ballotCoreDiag m s) :
    DiagonalRigid (catCore m) request (m + 2) := by
  intro first second hO₁ hM₁ hD₁ hO₂ hM₂ hD₂ heq
  obtain ⟨s, hs⟩ := hextract first hO₁ hM₁ hD₁
  have hs₂ : second.coreDiag = BallotSlopes.ballotCoreDiag m s := by rw [← heq, hs]
  have h₁ : GeometricFibre.cls (base s) = GeometricFibre.cls first :=
    (hsupply s first hO₁ hM₁ hD₁ hs).elim fun i ↦
      cls_eq_of_datumIso_of_coreDiag (hbD s) hD₁ (hstab s) ((hbval s).trans hs.symm) i
  have h₂ : GeometricFibre.cls (base s) = GeometricFibre.cls second :=
    (hsupply s second hO₂ hM₂ hD₂ hs₂).elim fun i ↦
      cls_eq_of_datumIso_of_coreDiag (hbD s) hD₂ (hstab s) ((hbval s).trans hs₂.symm) i
  exact h₁.symm.trans h₂

/-- The ballot member `BallotCoreIdentification.ballotFamilyMember` is diagonal,
at **every** `m`.
`SlopeRigidity.ballotFamilyMember_diagonal` is this statement at `m + 1` only,
because that section is about the end swap. -/
theorem ballotFamilyMember_diagonal (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1))) :
    (BallotCoreIdentification.ballotFamilyMember m request s).Diagonal :=
  BallotSlopes.diagonal_of_matrix_eq s
    (BallotCoreIdentification.ballotFamilyMember_matrix m request s)

/-- ... and its core diagonal is the ballot diagonal of its slope sequence, at
every `m`. -/
theorem ballotFamilyMember_coreDiag (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1))) :
    (BallotCoreIdentification.ballotFamilyMember m request s).coreDiag =
      BallotSlopes.ballotCoreDiag m s :=
  BallotSlopes.coreDiag_eq_of_matrix_eq s
    (BallotCoreIdentification.ballotFamilyMember_matrix m request s)
    (BallotCoreIdentification.ballotFamilyMember_slotMap m request s)

/-- **The diagonal form of `rigid` over the ballot family, at every genus.**  The
two diagonality inputs of `diagonalRigid_of_bases` are discharged by the ballot
family, so what remains is exactly three things and no pair of arbitrary
members:

* `hstab` -- residue (B) **on the ballot members only**, rather than on an
  arbitrary member: every core symmetry fixing the ballot diagonal of `s` is
  realised in `BallotCoreIdentification.ballotFamilyMember m request s`.  Above
  genus two this includes the end-swap obligation (`EndSwapRealized`,
  `CatFlipRealizedAut`).
* `hsupply` -- residue (A) **based at a ballot member** rather than stated
  between two arbitrary members.
* `hextract` -- the `extract` field. -/
theorem diagonalRigid_of_ballotBases {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (hstab : ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
      (∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag m s slot) →
        Realizes d (BallotCoreIdentification.ballotFamilyMember m request s))
    (hsupply : ∀ (s : Slopes (2 * (m + 1))) (mem : FibreMember (catCore m) request (m + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag m s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember m request s).data mem.data))
    (hextract : ∀ mem : FibreMember (catCore m) request (m + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (m + 1)), mem.coreDiag = BallotSlopes.ballotCoreDiag m s) :
    DiagonalRigid (catCore m) request (m + 2) :=
  diagonalRigid_of_bases (BallotCoreIdentification.ballotFamilyMember m request)
    (ballotFamilyMember_diagonal m request) (ballotFamilyMember_coreDiag m request)
    (fun s d hd ↦ hstab s d (by
      intro slot
      have h := hd slot
      rwa [ballotFamilyMember_coreDiag] at h))
    hsupply hextract

end DraismaVargas.Count.RigidityBasepoint
