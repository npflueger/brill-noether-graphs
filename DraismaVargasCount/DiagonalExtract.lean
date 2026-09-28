import DraismaVargasCount.BallotCoreIdentification
import DraismaVargasCount.DiagonalClassification
import DraismaVargasCount.SlopeRigidity

/-!
# The `extract` field of `DiagonalClassification`: a class statement, and a necessary condition

The `extract` field of `BallotSlopes.DiagonalClassification` says that a *diagonal* open member
of odd multiplicity over the caterpillar of loops has a ballot diagonal as its core diagonal.  The
restriction to diagonal members is necessary: `ColumnTwist.not_forall_extract` refutes the
unrestricted form at every positive request, the twist of the caterpillar member by the
transposition of slots `0` and `1` reading `0` where every ballot diagonal reads `2`.

## Main results

* `DiagonalExtract` -- the `extract` field as a standalone proposition;
  `diagonalExtract_of_classification`.
* `slopes_unique_of_coreDiag` -- the slope sequence `extract` produces is unique, by
  `ballotCoreDiag_injective`.
* `diagonalExtract_of_representatives`, `diagonalExtract_iff_representatives` -- **`extract` is
  a statement about geometric classes.**  Among diagonal members the core diagonal is a class
  invariant (`SlopeRigidity.coreDiag_eq_of_geometricIso_of_diagonal`, which needs no hypothesis
  on the request), so `extract` holds as soon as *one diagonal member of each open odd class* has
  a ballot diagonal, and the restatement loses nothing.  That is the shape in which a
  classification of the open odd classes discharges `extract`.
* `BallotDiagonalRelabelStable` -- a condition with no member, no request and no genus in it:
  *the set of ballot core diagonals is stable under the slot action of the incidence-preserving
  relabellings of `catCore m`*,

      ∀ s d, ∃ t, ballotCoreDiag m s ∘ d.slot.symm = ballotCoreDiag m t.

  At a positive request `extract` implies it: `SlopeRigidity.twistMember` carries a diagonal
  member along a core relabelling `d`, the twist of a diagonal open member of odd multiplicity is
  again diagonal, open and of odd multiplicity, and its core diagonal is the old one composed
  with `d.slot.symm`.  The condition holds at every `m`
  (`BallotOrbit.ballotDiagonalRelabelStable`, in `BallotOrbitStability`, which sharpens it to:
  the orbit of a ballot diagonal is `{s, s reversed}`).

`extract` does apply to twisted members: `SlopeRigidity.twistMember` is a twist and
`twistMember_diagonal` says it is diagonal.  What the restriction to diagonal members excludes is
the *column* twist (`ColumnTwist.twistColumns`), not every twist.
-/

namespace DraismaVargas.Count.BallotSlopes

open DraismaVargas.Count
open DraismaVargas.Count.CoreRelabel
open DraismaVargas.Count.FibreCaterpillar

variable {m : ℕ} {request : Fin (6 * m + 3) → ℚ}

/-! ## 1.  The field, named -/

/-- **The `extract` field of `BallotSlopes.DiagonalClassification`, as a
standalone proposition.**  The `Diagonal` hypothesis is not cosmetic:
`ColumnTwist.not_forall_extract` refutes the statement without it at every
positive request. -/
def DiagonalExtract (m : ℕ) (request : Fin (6 * m + 3) → ℚ) : Prop :=
  ∀ mem : FibreMember (catCore m) request (m + 2),
    mem.Open → mem.HasOddMult → mem.Diagonal →
      ∃ s : Slopes (2 * (m + 1)), mem.coreDiag = ballotCoreDiag m s

theorem diagonalExtract_of_classification (classification : DiagonalClassification m request) :
    DiagonalExtract m request :=
  classification.extract

/-- The slope sequence `extract` produces is unique. -/
theorem slopes_unique_of_coreDiag {mem : FibreMember (catCore m) request (m + 2)}
    {s t : Slopes (2 * (m + 1))} (hs : mem.coreDiag = ballotCoreDiag m s)
    (ht : mem.coreDiag = ballotCoreDiag m t) : s = t :=
  ballotCoreDiag_injective m (hs.symm.trans ht)

/-! ## 2.  `extract` is a statement about geometric classes -/

/-- **`extract` from one diagonal representative per open odd class.**  Among
diagonal members the core diagonal is a geometric-class invariant, by
`SlopeRigidity.coreDiag_eq_of_geometricIso_of_diagonal` -- which carries no
hypothesis on the request.  So a classification of the
open odd classes by members with ballot diagonals discharges `extract` for every
diagonal member at once. -/
theorem diagonalExtract_of_representatives
    (h : ∀ mem : FibreMember (catCore m) request (m + 2),
      mem.Open → mem.HasOddMult → mem.Diagonal →
        ∃ rep : FibreMember (catCore m) request (m + 2),
          rep.Diagonal ∧ GeometricFibre.cls rep = GeometricFibre.cls mem ∧
            ∃ s : Slopes (2 * (m + 1)), rep.coreDiag = ballotCoreDiag m s) :
    DiagonalExtract m request := by
  intro mem hOpen hOdd hD
  obtain ⟨rep, hrD, hcls, s, hs⟩ := h mem hOpen hOdd hD
  obtain ⟨iso⟩ := GeometricFibre.cls_eq_cls_iff.mp hcls
  exact ⟨s, (SlopeRigidity.coreDiag_eq_of_geometricIso_of_diagonal hrD hD iso).symm.trans hs⟩

/-- **And the restatement loses nothing**: a member is its own representative. -/
theorem diagonalExtract_iff_representatives :
    DiagonalExtract m request ↔
      ∀ mem : FibreMember (catCore m) request (m + 2),
        mem.Open → mem.HasOddMult → mem.Diagonal →
          ∃ rep : FibreMember (catCore m) request (m + 2),
            rep.Diagonal ∧ GeometricFibre.cls rep = GeometricFibre.cls mem ∧
              ∃ s : Slopes (2 * (m + 1)), rep.coreDiag = ballotCoreDiag m s :=
  ⟨fun h mem hOpen hOdd hD ↦ ⟨mem, hD, rfl, h mem hOpen hOdd hD⟩,
    diagonalExtract_of_representatives⟩

/-! ## 3.  A member-free necessary condition -/

/-- **The ballot diagonals are stable under the core's relabellings.**  No
member, no request and no genus occurs in this statement: it is a property of
`ballotCoreDiag m` and of the incidence-preserving permutation pairs of
`catCore m` alone. -/
def BallotDiagonalRelabelStable (m : ℕ) : Prop :=
  ∀ (s : Slopes (2 * (m + 1))) (d : Relabel (catCore m) (catCore m)),
    ∃ t : Slopes (2 * (m + 1)),
      (fun slot ↦ ballotCoreDiag m s (d.slot.symm slot)) = ballotCoreDiag m t

end DraismaVargas.Count.BallotSlopes
