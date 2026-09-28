import DraismaVargasCount.SheetLayerMatching
import DraismaVargasCount.BallotSpineReversalSheetIso
import DraismaVargasCount.DiagonalClassificationEndgame
import DraismaVargasCount.TrivalentFibreUnique

/-!
# Every caterpillar member is a ballot member: the base count without parity

Over a generic caterpillar of loops every full-dimensional tropical morphism to a tree comes from
a ballot sequence and has multiplicity one (Vargas, *Catalan-many tropical morphisms to trees;
Part II*, arXiv:2609.09109, `prop-divisors-on-chain`). `BallotSlopes.DiagonalClassification` asks
for this only for open classes of odd multiplicity, which is all a mod-2 count needs. This module
proves the conclusion with neither hypothesis:

* `exists_diagonal_rep`, at every `m`: every member has a diagonal representative in its class.
  This is the column twist applied to `TrivalentFibreUnique.leafAvoidingSeparated`.
* `cls_eq_ballot_of_coreDiag` and `cls_eq_ballot_of_diagonal`, at every `m` given the
  stabiliser input `hStab`: a diagonal member lies in the class of the ballot member of its
  slope sequence. The ingredients are `BallotResidues.exists_coreDiag_eq_ballotCoreDiag`,
  `SheetLayerMatching.sheetLayer_of_coreDiag_eq` and
  `RigidityBasepoint.cls_eq_of_datumIso_of_coreDiag`.
* **Genus six**, where `hStab` is `BallotSpineReversalSheetIso.hStab_genusSix`:
  * `cls_eq_ballot_genusSix`: every member of the caterpillar fibre, at every request, is in a
    ballot class;
  * `absMult_eq_one_genusSix`: it therefore has multiplicity exactly one;
  * `diagonalClassification_genusSix`: `BallotSlopes.DiagonalClassification 2` at every request;
  * `card_open_genusSix`: at a positive request there are exactly five open classes.

Together these are the **integer** base count at genus six: the sum of `|Mult|` over the open
classes of the caterpillar fibre is `5 = C₃`. The only genus-specific input is `hStab`, the
realisation of relabellings that stabilise a ballot core diagonal. At general `m` it reduces,
through `BallotStabiliserReduction.hStab_of_two_branches` and
`BallotSpineReversalSheetIso.hReversal_of_identity`, to the identity branch
(`BallotFarEndSwap.identity_branch_realized_genusSix` at `m = 2`).

The count is the first step of the genus-six assembly: `Assembly.baseCount_genusSix` restates it,
and `Assembly.c34_genusSix` propagates its parity to every cubic core of genus six.
-/

namespace DraismaVargas.Count.CaterpillarAllMembers

open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar

/-- Every caterpillar member, at every `m` and every request, has a diagonal representative in
its geometric class, with the same openness and oddness. -/
theorem exists_diagonal_rep {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (mem : FibreMember (catCore m) request (m + 2)) :
    ∃ rep : FibreMember (catCore m) request (m + 2),
      rep.Diagonal ∧ GeometricFibre.cls rep = GeometricFibre.cls mem ∧
        (rep.Open ↔ mem.Open) ∧ (rep.HasOddMult ↔ mem.HasOddMult) := by
  obtain ⟨σ, -, hσ⟩ := SpineSingleColumn.exists_rowSingleColumn_of_leafAvoiding mem
    (TrivalentFibreUnique.leafAvoidingSeparated mem)
  obtain ⟨e, hzero, _⟩ := SpineOffDiagonal.exists_perm_member_matrix_diagonal mem hσ
  exact ⟨ColumnTwist.twistColumns e mem, ColumnTwist.twistColumns_diagonal_of_monomial hzero,
    ColumnTwist.twistColumns_cls e mem, ColumnTwist.twistColumns_open_iff e mem,
    ColumnTwist.twistColumns_hasOddMult_iff e mem⟩

/-- At every `m`, given the stabiliser input, a diagonal member whose core diagonal is the
ballot diagonal of `s` lies in the class of the ballot member of `s`. -/
theorem cls_eq_ballot_of_coreDiag {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (hStab : ∀ (s : Slopes (2 * (m + 1))) (d : CoreRelabel.Relabel (catCore m) (catCore m)),
      (∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag m s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s))
    (rep : FibreMember (catCore m) request (m + 2)) (hD : rep.Diagonal)
    (s : Slopes (2 * (m + 1))) (hs : rep.coreDiag = BallotSlopes.ballotCoreDiag m s) :
    GeometricFibre.cls rep =
      GeometricFibre.cls (BallotCoreIdentification.ballotFamilyMember m request s) := by
  have hbD := RigidityBasepoint.ballotFamilyMember_diagonal m request s
  have hbval := RigidityBasepoint.ballotFamilyMember_coreDiag m request s
  obtain ⟨sheets⟩ := SheetLayerMatching.sheetLayer_of_coreDiag_eq
    (BallotCoreIdentification.ballotFamilyMember m request s) rep hbD hD (hbval.trans hs.symm)
  refine (RigidityBasepoint.cls_eq_of_datumIso_of_coreDiag hbD hD (fun d hd ↦ hStab s d ?_)
    (hbval.trans hs.symm) sheets.toIso).symm
  intro slot
  have h := hd slot
  rwa [hbval] at h

/-- At every `m`, given the stabiliser input, every diagonal member lies in a ballot class. -/
theorem cls_eq_ballot_of_diagonal {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (hStab : ∀ (s : Slopes (2 * (m + 1))) (d : CoreRelabel.Relabel (catCore m) (catCore m)),
      (∀ slot, BallotSlopes.ballotCoreDiag m s (d.slot.symm slot) =
          BallotSlopes.ballotCoreDiag m s slot) →
        SlopeRigidity.Realizes d (BallotCoreIdentification.ballotFamilyMember m request s))
    (rep : FibreMember (catCore m) request (m + 2)) (hD : rep.Diagonal) :
    ∃ s : Slopes (2 * (m + 1)), GeometricFibre.cls rep =
      GeometricFibre.cls (BallotCoreIdentification.ballotFamilyMember m request s) := by
  obtain ⟨s, hs⟩ := BallotResidues.exists_coreDiag_eq_ballotCoreDiag rep hD
  exact ⟨s, cls_eq_ballot_of_coreDiag hStab rep hD s hs⟩

/-- **Genus six, with no openness, oddness or request hypothesis**: every member of the
caterpillar fibre lies in the class of a ballot member. -/
theorem cls_eq_ballot_genusSix (request : Fin (6 * 2 + 3) → ℚ)
    (mem : FibreMember (catCore 2) request (2 + 2)) :
    ∃ s : Slopes (2 * (2 + 1)), GeometricFibre.cls mem =
      GeometricFibre.cls (BallotCoreIdentification.ballotFamilyMember 2 request s) := by
  obtain ⟨rep, hD, hcls, -, -⟩ := exists_diagonal_rep mem
  obtain ⟨s, hs⟩ := cls_eq_ballot_of_diagonal
    (BallotSpineReversalSheetIso.hStab_genusSix request) rep hD
  exact ⟨s, hcls.symm.trans hs⟩

/-- **Every member of the genus-six caterpillar fibre has multiplicity exactly one.** -/
theorem absMult_eq_one_genusSix (request : Fin (6 * 2 + 3) → ℚ)
    (mem : FibreMember (catCore 2) request (2 + 2)) : mem.absMult = 1 := by
  obtain ⟨s, hs⟩ := cls_eq_ballot_genusSix request mem
  have h := congrArg GeometricFibre.absMult hs
  simp only [GeometricFibre.absMult_cls] at h
  rw [h, BallotCoreIdentification.ballotFamilyMember_absMult]

/-- The diagonal classification `BallotSlopes.DiagonalClassification 2` at genus six, at every
request, obtained here without using oddness. -/
theorem diagonalClassification_genusSix (request : Fin (6 * 2 + 3) → ℚ) :
    BallotSlopes.DiagonalClassification 2 request where
  diagonal mem hOpen hOdd := by
    obtain ⟨rep, hD, hcls, hO, hM⟩ := exists_diagonal_rep mem
    exact ⟨rep, hO.mpr hOpen, hM.mpr hOdd, hD, hcls⟩
  extract mem _ _ hD := BallotResidues.exists_coreDiag_eq_ballotCoreDiag mem hD
  rigid first second _ _ hD₁ _ _ hD₂ heq := by
    obtain ⟨s, hs⟩ := BallotResidues.exists_coreDiag_eq_ballotCoreDiag first hD₁
    rw [cls_eq_ballot_of_coreDiag (BallotSpineReversalSheetIso.hStab_genusSix request) first hD₁
        s hs,
      cls_eq_ballot_of_coreDiag (BallotSpineReversalSheetIso.hStab_genusSix request) second hD₂
        s (heq ▸ hs)]

/-- **The integer base count at genus six.** At a positive request the caterpillar fibre has
exactly five open classes, and each has multiplicity one (`absMult_eq_one_genusSix`). So the sum
of `|Mult|` over the open classes is `5 = C₃`, with no parity anywhere. -/
theorem card_open_genusSix {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    Nat.card {c : GeometricFibre (catCore 2) request (2 + 2) // c.Open} = 5 := by
  have hOddAll : ∀ c : GeometricFibre (catCore 2) request (2 + 2), c.IsOdd := by
    intro c
    obtain ⟨mem, rfl⟩ := GeometricFibre.cls_surjective c
    exact (GeometricFibre.isOdd_cls_iff mem).mpr
      (FibreMember.hasOddMult_of_absMult_eq_one (absMult_eq_one_genusSix request mem))
  have hfive := BallotCoreIdentification.openOddCount_genusSix_eq_five' hRequest
    (diagonalClassification_genusSix request)
  rw [← hfive, GeometricFibre.openOddCount]
  exact Nat.card_congr
    { toFun := fun c ↦ ⟨c.1, c.2, hOddAll c.1⟩
      invFun := fun c ↦ ⟨c.1, c.2.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

end DraismaVargas.Count.CaterpillarAllMembers
