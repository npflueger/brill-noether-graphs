import DraismaVargasCount.GeometricFibre
import DraismaVargasCount.GeometricSegmentWalls
import DraismaVargasCount.FibreCaterpillar

/-!
# Geometric counting and the subdivision-request interface

Counting over the orientation-independent fibre `GeometricFibre`: positivity of the odd and
open odd counts, extraction of an open member of odd multiplicity from a positive count, the
caterpillar member as an inhabitant of the open odd count, and the specialisation to the
integral edge lengths of a subdivision `Spec`. The wall-free segment and star arguments
(`GeometricSegmentWalls`, `GeometricStar`) use the same fibre. The strict fibre `Fibre` has
its own count (`Count.openOddCount`); no equality or parity is transferred from that count to
this one.
-/

namespace DraismaVargas.Count.GeometricFibre

open Utilities.Certificate.ExplicitPotential (Core)
variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

theorem oddCount_pos_of_hasOddMult {member : FibreMember core y degree}
    (hOdd : member.HasOddMult) : 0 < oddCount core y degree := by
  have : Nonempty {c : GeometricFibre core y degree // c.IsOdd} :=
    ⟨⟨cls member, (isOdd_cls_iff member).mpr hOdd⟩⟩
  exact Nat.card_pos

theorem openOddCount_pos_of_open_hasOddMult {member : FibreMember core y degree}
    (hOpen : member.Open) (hOdd : member.HasOddMult) :
    0 < openOddCount core y degree := by
  have : Nonempty {c : GeometricFibre core y degree // c.Open ∧ c.IsOdd} :=
    ⟨⟨cls member, hOpen, (isOdd_cls_iff member).mpr hOdd⟩⟩
  exact Nat.card_pos

/-- A positive open odd count produces an actual open fibre member of odd multiplicity, not
merely a class of the quotient. -/
theorem exists_open_hasOddMult_of_openOddCount_pos (h : 0 < openOddCount core y degree) :
    ∃ member : FibreMember core y degree, member.Open ∧ member.HasOddMult := by
  obtain ⟨c, hOpen, hOdd⟩ := (Nat.card_pos_iff.mp h).1
  obtain ⟨member, rfl⟩ := cls_surjective c
  exact ⟨member, hOpen, (isOdd_cls_iff member).mp hOdd⟩

theorem openOddCount_pos_iff :
    0 < openOddCount core y degree ↔
      ∃ member : FibreMember core y degree, member.Open ∧ member.HasOddMult :=
  ⟨exists_open_hasOddMult_of_openOddCount_pos,
    fun ⟨_, hOpen, hOdd⟩ ↦ openOddCount_pos_of_open_hasOddMult hOpen hOdd⟩

theorem openOddCount_eq_card_filter
    [DecidablePred (fun c : GeometricFibre core y degree ↦ c.Open ∧ c.IsOdd)] :
    openOddCount core y degree =
      (Finset.univ.filter fun c : GeometricFibre core y degree ↦ c.Open ∧ c.IsOdd).card := by
  rw [openOddCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The caterpillar member (`FibreCaterpillar.caterpillarMember`) makes the open odd count over
the caterpillar of loops positive at every positive request. This is positivity only: it
neither classifies the fibre nor computes the parity of the count (the base count is step 1 of
`Assembly`). -/
theorem caterpillar_openOddCount_pos (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    0 < openOddCount (FibreCaterpillar.catCore m) request (m + 2) :=
  openOddCount_pos_of_open_hasOddMult (FibreCaterpillar.caterpillarMember_open hRequest)
    (FibreCaterpillar.caterpillarMember_hasOddMult m request)

/-- The geometric fibre over the integral edge lengths of a subdivision `spec`, the kind of
request met in the endgame. -/
abbrev SpecFibre (spec : Utilities.Certificate.SubdivisionGraph.Spec n p) (degree : ℕ) :=
  GeometricFibre spec.core (fun slot ↦ (spec.length slot : ℚ)) degree

noncomputable abbrev specOpenOddCount
    (spec : Utilities.Certificate.SubdivisionGraph.Spec n p) (degree : ℕ) : ℕ :=
  openOddCount spec.core (fun slot ↦ (spec.length slot : ℚ)) degree

theorem specOpenOddCount_pos_iff (spec : Utilities.Certificate.SubdivisionGraph.Spec n p) :
    0 < specOpenOddCount spec degree ↔
      ∃ member : SpecFibreMember spec degree, member.Open ∧ member.HasOddMult :=
  openOddCount_pos_iff

end DraismaVargas.Count.GeometricFibre
