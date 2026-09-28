import DraismaVargasCount.DiagonalFromSeparation
import DraismaVargasCount.RigidityBasepoint
import DraismaVargasCount.DiagonalClassificationEndgame
import DraismaVargasCount.LoopAdjacentDiagonal

/-!
# `DiagonalClassification 2` from four geometric hypotheses

`Count/DiagonalClassificationEndgame.lean` turns
`BallotSlopes.DiagonalClassification 2 request` into the genus-six count at a
positive request.  This module assembles the classification itself from four geometric
hypotheses, none of which mentions `openOddCount`, and states the resulting count.  The
base count of the genus-six assembly does not depend on this module:
`CaterpillarAllMembers.diagonalClassification_genusSix` proves the classification at genus
six directly.  What this module offers is the upper half of the base count split into four
separate, local statements.

## The assembly

`diagonalClassification_genusSix_of_residues` assembles
`BallotSlopes.DiagonalClassification 2 request` from exactly four hypotheses,
**with no positivity hypothesis at all**:

* `hSep` -- `SpineSingleColumn.LeafAvoidingSeparated 2 mem` at every open odd
  member.  Feeds `diagonal` only; it is the global half of the injectivity of the spine
  path, in the form `Count/DiagonalFromSeparation.lean` uses.
  `diagonalClassification_genusSix_of_trivalent_residues` replaces it by
  `Count/BranchSharedDirection.lean`'s localisation to the `g - 2 = 4`
  trivalent target vertices.  It holds at every member
  (`TrivalentFibreUnique.leafAvoidingSeparated`).
* `hSpine` -- the `extract` field **restricted to the `4m + 1 = 9` non-leaf
  slots**.  Feeds `extract`, and through it `rigid`.  The `2m + 2 = 6` leaf
  slots are free at every genus by
  `ExtractGenusTwo.coreDiag_eq_ballotCoreDiag_of_isLeafEdge`, and
  `ExtractGenusTwo.diagonalExtract_iff_forall_not_isLeafEdge` says the
  restriction loses nothing.  `Count/LoopAdjacentDiagonal.lean` cuts it further, to
  the `2m - 1` **interior spine slots** -- three at genus six -- by locating the `1 / 2`
  that each self-loop supplies; that is the sharp form, `hThree` below.
* `hStab` -- every relabelling of `catCore 2` that stabilises a ballot core diagonal is
  realised, **on the five ballot members** `BallotCoreIdentification.ballotFamilyMember`.
  Feeds `rigid`.
* `hSupply` -- every open odd diagonal member whose core diagonal is that of a ballot member
  has the same gluing datum up to isomorphism, **based at those five members**.  Feeds
  `rigid`.

`hStab` and `hSupply` are the two halves of the uniqueness in part (2) of Part II's
`prop-caterpillar-ballot`, in the base-pointed form of
`RigidityBasepoint.diagonalRigid_of_ballotBases`, read at `m = 2`; the point of writing the
composite down is that the join is checked, and that `hSpine` is shared between `extract`
and `rigid` rather than being assumed twice.

## What is proved

* `diagonalClassification_of_residues`,
  `diagonalClassification_genusSix_of_residues`,
  `diagonalClassification_of_trivalent_residues`,
  `diagonalClassification_genusSix_of_trivalent_residues` -- **the assembly**, at every `m`
  and at `m = 2`, with `hSep` in its two forms.
* `not_loopAdjacent_genusSix`, `diagonalExtract_genusSix_of_three_slots`,
  **`diagonalClassification_genusSix_of_sharp_residues`** -- the assembly with
  `hSpine` cut from nine slots to three, by `Count/LoopAdjacentDiagonal.lean`.  At `m = 2`
  the non-loop-adjacent slots are exactly `4`, `7` and `10`.
* `openOddCount_genusSix_eq_five_of_sharp_residues` -- the genus-six count at a positive
  request, from the four sharp hypotheses.

Nothing in the assembly is genus-six-specific except the arithmetic that makes the three
surviving slots `4`, `7`, `10`; the general-`m` forms are stated alongside.

## Remarks

* **The hypotheses are not weaker than the count.**  At a positive request, at every
  `m`, `BallotSlopes.DiagonalClassification m request` is equivalent to
  `openOddCount (catCore m) request (m + 2) ≤ catalan (m + 1)`, and each of its fields,
  and `hStab` and `hSupply` in the base-pointed form, follows from that bound (this is not
  formalized here).  So no sufficient hypothesis is weaker than the upper bound of the
  count; what the decomposition offers is four separate, local, geometric statements.
  `hSep` is of a different kind: it is a statement about the fibres of one member's target,
  which no cardinality bound reaches.
* **`hStab` at genus six.**  `hStab` quantifies over every
  `CoreRelabel.Relabel (catCore 2) (catCore 2)` stabilising a ballot diagonal.
  `BallotOrbit.ballotCoreDiag_relabel_eq_self_or_reverse` bounds what such a relabelling
  can *do* to the diagonal, at every genus, without enumerating the relabellings, and
  `BallotSpineReversalSheetIso.hStab_genusSix` realises every relabelling in each of the two
  branches it distinguishes (from `BallotEndSwapSheetIso`'s identity branch and
  `BallotFarEndSwap`'s reduction).  `SlopeRigidity.realizes_endSwap` is a statement
  about the zig-zag member `FibreCaterpillar.caterpillarMember`, and does not by itself give
  `hStab` for the other ballot members.
* **`hThree`** says that three rational numbers read off an arbitrary diagonal open odd
  member are the reciprocals of the interior entries of *one* ballot sequence, in order.
  `Count/LoopAdjacentDiagonal.lean` settles the other twelve slots at every genus; nothing
  here is proved about these three.
-/

namespace DraismaVargas.Count.DiagonalClassificationGenusSix

open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource (nonDanglingValency)
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)

/-! ## 1.  The assembly, from four geometric hypotheses -/

section Assembly

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-- **The classification from four hypotheses, at every `m`.**

* `hSep` feeds `diagonal` and nothing else
  (`DiagonalFromSeparation.diagonal_of_leafAvoidingSeparated`);
* `hSpine` feeds `extract`, and is reused inside `rigid`
  (`ExtractGenusTwo.diagonalExtract_of_forall_not_isLeafEdge`, whose converse
  `diagonalExtract_iff_forall_not_isLeafEdge` says the restriction to the
  `4m + 1` non-leaf slots loses nothing);
* `hStab` and `hSupply` feed `rigid`
  (`RigidityBasepoint.diagonalRigid_of_ballotBases`).

No positivity of the request is used. -/
theorem diagonalClassification_of_residues
    (hSep : ∀ mem : FibreMember (catCore m) request (m + 2), mem.Open → mem.HasOddMult →
      SpineSingleColumn.LeafAvoidingSeparated m mem)
    (hSpine : ∀ mem : FibreMember (catCore m) request (m + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (m + 1)), ∀ slot : Fin (6 * m + 3), ¬ IsLeafEdge m slot →
          mem.coreDiag slot = BallotSlopes.ballotCoreDiag m s slot)
    (hStab : ∀ (s : Slopes (2 * (m + 1)))
      (d : CoreRelabel.Relabel (catCore m) (catCore m)),
      (∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag m s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s))
    (hSupply : ∀ (s : Slopes (2 * (m + 1))) (mem : FibreMember (catCore m) request (m + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag m s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember m request s).data mem.data)) :
    BallotSlopes.DiagonalClassification m request := by
  have hextract : BallotSlopes.DiagonalExtract m request :=
    ExtractGenusTwo.diagonalExtract_of_forall_not_isLeafEdge hSpine
  exact
    { diagonal := DiagonalFromSeparation.diagonal_of_leafAvoidingSeparated hSep
      extract := hextract
      rigid := RigidityBasepoint.diagonalRigid_of_ballotBases hStab hSupply hextract }

/-- **Genus six.**  The same four hypotheses at `m = 2`, with every binder written
out.

At `m = 2` the slot type is `Fin 15`; `IsLeafEdge 2` holds on the six slots
`0, 3, 6, 9, 12, 14`, so `hSpine` is a statement about the remaining **nine**
slots, and `Slopes 6` has `catalan 3 = 5` elements, so `hStab` and `hSupply`
are five obligations each. -/
theorem diagonalClassification_genusSix_of_residues {request : Fin (6 * 2 + 3) → ℚ}
    (hSep : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      SpineSingleColumn.LeafAvoidingSeparated 2 mem)
    (hSpine : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ slot : Fin (6 * 2 + 3), ¬ IsLeafEdge 2 slot →
          mem.coreDiag slot = BallotSlopes.ballotCoreDiag 2 s slot)
    (hStab : ∀ (s : Slopes (2 * (2 + 1)))
      (d : CoreRelabel.Relabel (catCore 2) (catCore 2)),
      (∀ slot, BallotSlopes.ballotCoreDiag 2 s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag 2 s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s))
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember 2 request s).data mem.data)) :
    BallotSlopes.DiagonalClassification 2 request :=
  diagonalClassification_of_residues hSep hSpine hStab hSupply

/-- **The same with `hSep` replaced by its localisation.**
`Count/BranchSharedDirection.lean` discharges the fibre-uniqueness
hypothesis above every leaf and every divalent target vertex -- `2g` of the
target's `3g - 2` vertices -- and localises what remains to the `g - 2`
trivalent ones, which at genus six is **four** vertices. -/
theorem diagonalClassification_of_trivalent_residues
    (hTrivalent : ∀ mem : FibreMember (catCore m) request (m + 2), mem.Open → mem.HasOddMult →
      ∀ X Y : mem.data.SourceVertex,
        (X.1.1 : mem.target.V) = (Y.1.1 : mem.target.V) →
          (GluingDatum.incidentEdges (X.1.1 : mem.target.V)).card = 3 →
            0 < nonDanglingValency mem.data X → 0 < nonDanglingValency mem.data Y → X = Y)
    (hSpine : ∀ mem : FibreMember (catCore m) request (m + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (m + 1)), ∀ slot : Fin (6 * m + 3), ¬ IsLeafEdge m slot →
          mem.coreDiag slot = BallotSlopes.ballotCoreDiag m s slot)
    (hStab : ∀ (s : Slopes (2 * (m + 1)))
      (d : CoreRelabel.Relabel (catCore m) (catCore m)),
      (∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag m s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s))
    (hSupply : ∀ (s : Slopes (2 * (m + 1))) (mem : FibreMember (catCore m) request (m + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag m s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember m request s).data mem.data)) :
    BallotSlopes.DiagonalClassification m request :=
  diagonalClassification_of_residues
    (fun mem hOpen hOdd ↦ BranchSharedDirection.leafAvoidingSeparated_of_trivalentFibreUnique
      mem (hTrivalent mem hOpen hOdd))
    hSpine hStab hSupply

/-- Genus six, with the trivalent localisation. -/
theorem diagonalClassification_genusSix_of_trivalent_residues
    {request : Fin (6 * 2 + 3) → ℚ}
    (hTrivalent : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      ∀ X Y : mem.data.SourceVertex,
        (X.1.1 : mem.target.V) = (Y.1.1 : mem.target.V) →
          (GluingDatum.incidentEdges (X.1.1 : mem.target.V)).card = 3 →
            0 < nonDanglingValency mem.data X → 0 < nonDanglingValency mem.data Y → X = Y)
    (hSpine : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ slot : Fin (6 * 2 + 3), ¬ IsLeafEdge 2 slot →
          mem.coreDiag slot = BallotSlopes.ballotCoreDiag 2 s slot)
    (hStab : ∀ (s : Slopes (2 * (2 + 1)))
      (d : CoreRelabel.Relabel (catCore 2) (catCore 2)),
      (∀ slot, BallotSlopes.ballotCoreDiag 2 s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag 2 s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s))
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember 2 request s).data mem.data)) :
    BallotSlopes.DiagonalClassification 2 request :=
  diagonalClassification_of_trivalent_residues hTrivalent hSpine hStab hSupply

/-! ### The sharp form of `hSpine`: three slots at genus six -/

/-- **The non-loop-adjacent slots of `catCore 2` are `4`, `7` and `10`.**  These
are the interior spine edges; the other twelve slots of `Fin 15` touch a
self-loop. -/
theorem not_loopAdjacent_genusSix (e : Fin (6 * 2 + 3)) :
    ¬ BallotOrbit.LoopAdjacent (catCore 2) e ↔ (e.val = 4 ∨ e.val = 7 ∨ e.val = 10) := by
  rw [BallotOrbit.not_loopAdjacent_catCore]
  have := e.isLt
  omega

/-- **`extract` at genus six is three rational numbers.**  By
`Count/LoopAdjacentDiagonal.lean` a diagonal member's core diagonal is already
pinned on the twelve loop-adjacent slots, and agrees there with every ballot
diagonal; what `extract` still asks is that the values at slots `4`, `7` and
`10` be `1 / s₂`, `1 / s₃`, `1 / s₄` for a single `s : Slopes 6`. -/
theorem diagonalExtract_genusSix_of_three_slots {request : Fin (6 * 2 + 3) → ℚ}
    (hThree : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ e : Fin (6 * 2 + 3),
          (e.val = 4 ∨ e.val = 7 ∨ e.val = 10) →
            mem.coreDiag e = BallotSlopes.ballotCoreDiag 2 s e) :
    BallotSlopes.DiagonalExtract 2 request :=
  LoopAdjacentDiagonal.diagonalExtract_of_forall_not_loopAdjacent
    fun mem hOpen hOdd hD ↦ by
      obtain ⟨s, hs⟩ := hThree mem hOpen hOdd hD
      exact ⟨s, fun e hAdj ↦ hs e ((not_loopAdjacent_genusSix e).mp hAdj)⟩

/-- **The sharp genus-six assembly.**  The same package as
`diagonalClassification_genusSix_of_residues`, with the nine-slot `hSpine`
replaced by the three-slot `hThree` and `hSep` by its trivalent localisation.

This is the upper half of the genus-six base count in its most local form:
**four** sentences, one about the fibres of the four trivalent vertices of an arbitrary
member's target, one about three entries of its core diagonal, and two about the gluing
data of the five ballot members.  None of them mentions `openOddCount`. -/
theorem diagonalClassification_genusSix_of_sharp_residues {request : Fin (6 * 2 + 3) → ℚ}
    (hTrivalent : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      ∀ X Y : mem.data.SourceVertex,
        (X.1.1 : mem.target.V) = (Y.1.1 : mem.target.V) →
          (GluingDatum.incidentEdges (X.1.1 : mem.target.V)).card = 3 →
            0 < nonDanglingValency mem.data X → 0 < nonDanglingValency mem.data Y → X = Y)
    (hThree : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ e : Fin (6 * 2 + 3),
          (e.val = 4 ∨ e.val = 7 ∨ e.val = 10) →
            mem.coreDiag e = BallotSlopes.ballotCoreDiag 2 s e)
    (hStab : ∀ (s : Slopes (2 * (2 + 1)))
      (d : CoreRelabel.Relabel (catCore 2) (catCore 2)),
      (∀ slot, BallotSlopes.ballotCoreDiag 2 s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag 2 s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s))
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember 2 request s).data mem.data)) :
    BallotSlopes.DiagonalClassification 2 request := by
  have hextract : BallotSlopes.DiagonalExtract 2 request :=
    diagonalExtract_genusSix_of_three_slots hThree
  exact
    { diagonal := DiagonalFromSeparation.diagonal_of_leafAvoidingSeparated
        (fun mem hOpen hOdd ↦
          BranchSharedDirection.leafAvoidingSeparated_of_trivalentFibreUnique mem
            (hTrivalent mem hOpen hOdd))
      extract := hextract
      rigid := RigidityBasepoint.diagonalRigid_of_ballotBases hStab hSupply hextract }

end Assembly

/-! ## 2.  What the four hypotheses give -/

section Consequences

/-- **The genus-six count, from the four sharp hypotheses.**  The lower bound is
`BallotCoreIdentification.five_le_openOddCount_genusSix`; the upper bound is the
classification. -/
theorem openOddCount_genusSix_eq_five_of_sharp_residues {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot)
    (hTrivalent : ∀ mem : FibreMember (catCore 2) request (2 + 2), mem.Open → mem.HasOddMult →
      ∀ X Y : mem.data.SourceVertex,
        (X.1.1 : mem.target.V) = (Y.1.1 : mem.target.V) →
          (GluingDatum.incidentEdges (X.1.1 : mem.target.V)).card = 3 →
            0 < nonDanglingValency mem.data X → 0 < nonDanglingValency mem.data Y → X = Y)
    (hThree : ∀ mem : FibreMember (catCore 2) request (2 + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ s : Slopes (2 * (2 + 1)), ∀ e : Fin (6 * 2 + 3),
          (e.val = 4 ∨ e.val = 7 ∨ e.val = 10) →
            mem.coreDiag e = BallotSlopes.ballotCoreDiag 2 s e)
    (hStab : ∀ (s : Slopes (2 * (2 + 1)))
      (d : CoreRelabel.Relabel (catCore 2) (catCore 2)),
      (∀ slot, BallotSlopes.ballotCoreDiag 2 s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag 2 s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember 2 request s))
    (hSupply : ∀ (s : Slopes (2 * (2 + 1))) (mem : FibreMember (catCore 2) request (2 + 2)),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        mem.coreDiag = BallotSlopes.ballotCoreDiag 2 s →
          Nonempty (GeometricDatumIso
            (BallotCoreIdentification.ballotFamilyMember 2 request s).data mem.data)) :
    GeometricFibre.openOddCount (catCore 2) request (2 + 2) = 5 :=
  BallotCoreIdentification.openOddCount_genusSix_eq_five' hRequest
    (diagonalClassification_genusSix_of_sharp_residues hTrivalent hThree hStab hSupply)

end Consequences

end DraismaVargas.Count.DiagonalClassificationGenusSix
