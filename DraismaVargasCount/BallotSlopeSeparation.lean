module

public import DraismaVargasCount.CoreSlotCoords
public import DraismaVargasCount.CaterpillarBallotCount
public import DraismaVargasCount.BallotDatum

@[expose] public section

/-!
# The slopes separate the ballot members

**Source.**  Vargas, Part II (arXiv:2609.09109), `prop-caterpillar-ballot`, in
particular its item (2): a slope sequence determines the morphism.  This module
proves the **injective half** of the statement that the slope sequence
determines the class of a member over the caterpillar of loops: it removes
`BallotFamily.member_injective` from what a ballot family has to supply,
replacing it by a property of the *length matrix* of the member -- a property
that `Count.BallotValency`'s `ballotDiagonalPattern` already half establishes
for every slope sequence.  `BallotSlopeDiagonalBridge` and
`BallotCoreIdentification` turn this into the lower bound
`catalan (m + 1) ≤ openOddCount` of the base count over the caterpillar of
loops (step 1 of `DraismaVargasCount/Assembly.lean`).

## The separating invariant

`DraismaVargasCount.CoreSlotCoords` proves that for members whose length
matrix is diagonal the coordinate vector and the diagonal, both **read on core
slots**, are invariants of the geometric class -- as functions, not merely as
multisets.  The diagonal of a ballot caterpillar is where the slopes live:
over a loop the two
folded flags each have index one and contribute `1 + 1 = 2`, over a bridge the
single surviving occurrence has index two and contributes `1/2`, and over the
spine edge `h_i` the surviving occurrence is the whole `s_i`-element block
(`Slopes.card_spineMem`) and contributes `1 / s_i`.  That is
`ballotCoreDiag` below, and it visibly determines the slope sequence, one spine
slot at a time.

This is what makes the separation work **without genericity**.  The multiset
route of `GeometricCountFamily` cannot: at `m = 2` the slope sequences
`[2,1,2,3,2]` and `[2,3,2,1,2]` have the same multiset of slopes, so over an
all-ones request their coordinate multisets agree.

## What is proved

* `ballotCoreDiag m s` -- the diagonal of the ballot length matrix read on core
  slots, as Part II describes it, with its three cases
  (`ballotCoreDiag_leaf`, `ballotCoreDiag_spine`, `ballotCoreDiag_stem`).
* `Slopes.eq_of_slopes_eq`, `Slopes.eq_of_slope_eq` -- a slope sequence is
  determined by its list, hence by its extended slope function.
* **`ballotCoreDiag_injective (m) : Function.Injective (ballotCoreDiag m)`** --
  the combinatorial content of the separation: reading the diagonal at the
  spine slot `3i - 2` recovers `s_i` for `1 ≤ i ≤ 2m + 1`, and
  `slope_zero`/`slope_of_ge` pin the extension outside that range.
* **`catDiag_eq_ballotCoreDiag_zig (m) : catDiag m = ballotCoreDiag m (zig m)`**
  -- the consistency anchor.  The diagonal of the zig-zag caterpillar
  (`Caterpillar.matrix_diag_cat`, via `catDiag_eq`) *is* the formula above at
  the zig-zag slope sequence, for every `m`, so the new invariant agrees with
  the caterpillar's own.
* `member_injective_of_coreDiag` -- **the reduction.**  A family of members over
  `(catCore m, request)` that is diagonal and whose `coreDiag` is
  `ballotCoreDiag m s` has pairwise distinct classes, over any request that
  vanishes nowhere.
* `ballotFamilyOfDiagonal` -- a `BallotFamily` constructor that **does not ask
  for `member_injective`**, and `catalan_le_openOddCount_of_diagonal`,
  `five_le_openOddCount_genusSix_of_diagonal`: the lower bound `catalan (m+1)`
  and its genus-six instance `5`, from the members, their openness, odd
  multiplicity and diagonal alone.
* `genusTwoFamilyOfDiagonal` -- **non-vacuity of the constructor, with no
  hypothesis beyond positivity of the request**: at `m = 0` the
  caterpillar member satisfies all five of its arguments, the `coreDiag` one
  because `Slopes 2` is a one-point type and the consistency anchor applies.
* `slopesUpDown`, `slopesDownUp`, `slopesUpDown_ne_slopesDownUp`,
  `slopes_multiset_eq`, `ballotCoreDiag_multiset_eq`, `coordsMultiset_collision`
  -- **the negative, with its witnesses bounded.**  `[2,1,2,3,2]` and
  `[2,3,2,1,2]` are checked in Lean to be genuine, genuinely distinct elements
  of `Slopes (2 * (2 + 1))` with equal multisets of slopes, hence equal
  coordinate multisets over the all-ones request.  So
  `cls_injective_of_coordsMultiset_injective` cannot discharge
  `member_injective` at genus six without genericity, and
  `cls_injective_of_coreDiag_injective` can, with none.

## Scope

* **No ballot member is constructed here.**  For `m ≥ 1` nothing below
  constructs a `FibreMember (catCore m) request (m + 2)` at a general slope
  sequence; the members are built in `BallotCoreIdentification`, and
  `Count.BallotValency.ballotFullDim` is a *presentation*, not a member.  Every
  statement past `ballotCoreDiag_injective` therefore takes the family as a
  hypothesis.
* **The `coreDiag` hypothesis is assumed here.**  `hvalue : ∀ s,
  (member s).coreDiag = ballotCoreDiag m s` is a hypothesis of this module.
  For members that carry the ballot length matrix and label their rows by the
  core slots it is `BallotSlopes.coreDiag_eq_of_matrix_eq`, through the
  entry-by-entry diagonal of `(ballotLabelling m s).presentation`
  (`BallotDiagonal.bMatrix_diag`).  What is proved here is the `m = 0` case
  and the zig-zag case of it (`catDiag_eq_ballotCoreDiag_zig`).
* **`member_open` and `member_hasOddMult`** appear below only as hypotheses of
  the constructor.
* **Nothing here is a surjectivity statement.**  `member_surjective` -- the
  structure of an arbitrary member over the caterpillar and the exhaustion
  half of the ballot classification -- is not addressed, so no *equality* of
  counts follows from anything below, only the lower bound.
* The request hypothesis is `∀ slot, request slot ≠ 0`, weaker than positivity
  and used only to divide; no genericity (pairwise distinct lengths) is assumed
  anywhere.
-/

namespace DraismaVargas.Count

open DraismaVargas.LocalCases.CaterpillarDatum (IsPairEdge)
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)

/-! ## 1.  A slope sequence is determined by its slopes -/

namespace Slopes

variable {g : ℕ}

/-- **A slope sequence is determined by its extended slope function.**  The
extension reads the list at `i - 1`, so the values at `i = 1, …, g - 1` recover
every entry. -/
theorem eq_of_slope_eq {s t : Slopes g} (h : ∀ i, s.slope i = t.slope i) : s = t := by
  refine eq_of_slopes_eq (List.ext_getElem ?_ ?_)
  · rw [s.length_eq, t.length_eq]
  · intro i hi hi'
    have hval := h (i + 1)
    rw [slope_eq_getElem s (by simpa using hi), slope_eq_getElem t (by simpa using hi')] at hval
    simpa using hval

end Slopes

/-! ## 2.  The diagonal of a ballot caterpillar, read on core slots -/

namespace BallotSlopes

open DraismaVargas.Count.FibreCaterpillar
open DraismaVargas.Count.BallotDatum (zig zig_slope_mid)
open Utilities.Certificate.ExplicitPotential (Core)

/-- **The diagonal of the ballot length matrix, read on core slots.**  Over a
loop the two folded flags have index one each and contribute `2`; over the spine
edge `h_i` the surviving occurrence is the `s_i`-element block and contributes
`1 / s_i`; over a bridge the surviving occurrence is the pair and contributes
`1/2`.  At the zig-zag sequence this is `catDiag`
(`catDiag_eq_ballotCoreDiag_zig`). -/
noncomputable def ballotCoreDiag (m : ℕ) (s : Slopes (2 * (m + 1)))
    (slot : Fin (6 * m + 3)) : ℚ :=
  if IsLeafEdge m slot then 2
  else if slot.val % 3 = 1 then 1 / (s.slope ((slot.val + 2) / 3) : ℚ)
  else 1 / 2

variable {m : ℕ} {slot : Fin (6 * m + 3)}

theorem ballotCoreDiag_leaf (s : Slopes (2 * (m + 1))) (hleaf : IsLeafEdge m slot) :
    ballotCoreDiag m s slot = 2 := by
  rw [ballotCoreDiag, ite_eq_left hleaf]

theorem not_isLeafEdge_of_spine (hspine : slot.val % 3 = 1) : ¬ IsLeafEdge m slot := by
  rintro (h | h)
  · omega
  · omega

theorem ballotCoreDiag_spine (s : Slopes (2 * (m + 1))) (hspine : slot.val % 3 = 1) :
    ballotCoreDiag m s slot = 1 / (s.slope ((slot.val + 2) / 3) : ℚ) := by
  rw [ballotCoreDiag, ite_eq_right (not_isLeafEdge_of_spine hspine), ite_eq_left hspine]

theorem ballotCoreDiag_stem (s : Slopes (2 * (m + 1))) (hmod : slot.val % 3 = 2)
    (hlast : slot.val ≠ 6 * m + 2) : ballotCoreDiag m s slot = 1 / 2 := by
  rw [ballotCoreDiag, ite_eq_right (by rintro (h | h) <;> omega), ite_eq_right (by omega)]

/-! ## 3.  The slopes are separated -/

/-- **The combinatorial content of the separation.**  Distinct slope sequences have
distinct diagonals: the spine slot `3i - 2` reads `1 / s_i`. -/
theorem ballotCoreDiag_injective (m : ℕ) :
    Function.Injective (ballotCoreDiag m) := by
  intro s t h
  have hmid : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * m + 1 → s.slope i = t.slope i := by
    intro i h1 h2
    have hlt : 3 * i - 2 < 6 * m + 3 := by omega
    have hmod : (⟨3 * i - 2, hlt⟩ : Fin (6 * m + 3)).val % 3 = 1 := by
      show (3 * i - 2) % 3 = 1
      omega
    have hidx : ((⟨3 * i - 2, hlt⟩ : Fin (6 * m + 3)).val + 2) / 3 = i := by
      show (3 * i - 2 + 2) / 3 = i
      omega
    have hval := congrFun h (⟨3 * i - 2, hlt⟩ : Fin (6 * m + 3))
    rw [ballotCoreDiag_spine s hmod, ballotCoreDiag_spine t hmod, hidx, one_div,
      one_div] at hval
    exact_mod_cast inv_injective hval
  refine Slopes.eq_of_slope_eq fun i ↦ ?_
  rcases Nat.lt_or_ge i 1 with h0 | h1
  · rw [show i = 0 by omega, Slopes.slope_zero, Slopes.slope_zero]
    exact hmid 1 le_rfl (by omega)
  · rcases Nat.lt_or_ge (2 * m + 1) i with h2 | h2
    · rw [Slopes.slope_of_ge s (by omega), Slopes.slope_of_ge t (by omega)]
    · exact hmid i h1 h2

/-! ## 4.  The consistency anchor: the zig-zag caterpillar -/

/-- **The zig-zag diagonal `catDiag` is the ballot diagonal at the zig-zag slope
sequence**, for every `m`.  `catDiag_eq` gives `2` on a leaf row, `1/2` on a
pair edge and `1` on a slope-one spine edge; `zig_slope_mid` gives
`s_i = if i % 2 = 0 then 1 else 2`, and a spine slot `3i - 2` is a pair edge
exactly when `i` is odd. -/
theorem catDiag_eq_ballotCoreDiag_zig (m : ℕ) :
    catDiag m = ballotCoreDiag m (zig m) := by
  funext slot
  have hlt := slot.isLt
  rw [catDiag_eq, ballotCoreDiag]
  by_cases hleaf : IsLeafEdge m slot
  · rw [ite_eq_left hleaf, ite_eq_left hleaf]
  · rw [ite_eq_right hleaf, ite_eq_right hleaf]
    have hnot : slot.val % 3 ≠ 0 ∧ slot.val ≠ 6 * m + 2 := by
      constructor
      · intro h; exact hleaf (Or.inl h)
      · intro h; exact hleaf (Or.inr h)
    by_cases hspine : slot.val % 3 = 1
    · rw [ite_eq_left hspine]
      have h1 : 1 ≤ (slot.val + 2) / 3 := by omega
      have h2 : (slot.val + 2) / 3 ≤ 2 * m + 1 := by omega
      rw [zig_slope_mid m h1 h2]
      by_cases hpar : (slot.val + 2) / 3 % 2 = 0
      · rw [ite_eq_left hpar, ite_eq_right (show ¬ IsPairEdge m slot.val by
          rintro (h | h) <;> omega)]
        norm_num
      · rw [ite_eq_right hpar, ite_eq_left (show IsPairEdge m slot.val from Or.inl (by omega))]
        norm_num
    · rw [ite_eq_right hspine, ite_eq_left (show IsPairEdge m slot.val from
        Or.inr ⟨by omega, hnot.2⟩)]

/-- The caterpillar member's diagonal, read on core slots, is the ballot
diagonal at the zig-zag sequence. -/
theorem coreDiag_caterpillarMember_eq_zig (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    (caterpillarMember m request).coreDiag = ballotCoreDiag m (zig m) := by
  rw [coreDiag_caterpillarMember, catDiag_eq_ballotCoreDiag_zig]

/-! ## 5.  The injective half of the ballot classification -/

open DraismaVargas.Count.CaterpillarBallot (BallotFamily)

/-- **The reduction.**  A family of diagonal members whose diagonals are the
ballot diagonals has pairwise distinct geometric classes.  This is
`BallotFamily.member_injective`, derived rather than assumed. -/
theorem member_injective_of_coreDiag {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (member : Slopes (2 * (m + 1)) → FibreMember (catCore m) request (m + 2))
    (hdiag : ∀ s, (member s).Diagonal)
    (hvalue : ∀ s, (member s).coreDiag = ballotCoreDiag m s)
    (hrequest : ∀ slot, request slot ≠ 0) :
    Function.Injective fun s ↦ GeometricFibre.cls (member s) := by
  refine GeometricFibre.cls_injective_of_coreDiag_injective member hdiag hrequest ?_
  intro a b hab
  refine ballotCoreDiag_injective m ?_
  show ballotCoreDiag m a = ballotCoreDiag m b
  rw [← hvalue a, ← hvalue b]
  exact hab

/-- **A `BallotFamily` without the injectivity obligation.**  Compare
`CaterpillarBallot.BallotFamily`: its fourth field is supplied here
from diagonality and the value of the diagonal. -/
noncomputable def ballotFamilyOfDiagonal {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (member : Slopes (2 * (m + 1)) → FibreMember (catCore m) request (m + 2))
    (hOpen : ∀ s, (member s).Open) (hOdd : ∀ s, (member s).HasOddMult)
    (hdiag : ∀ s, (member s).Diagonal)
    (hvalue : ∀ s, (member s).coreDiag = ballotCoreDiag m s)
    (hrequest : ∀ slot, request slot ≠ 0) :
    BallotFamily m request where
  member := member
  member_open := hOpen
  member_hasOddMult := hOdd
  member_injective := member_injective_of_coreDiag member hdiag hvalue hrequest

/-- **The lower bound, with injectivity discharged.**  `catalan (m + 1)` open
classes of odd multiplicity, from the members, their openness, odd
multiplicity and diagonal alone. -/
theorem catalan_le_openOddCount_of_diagonal {m : ℕ} {request : Fin (6 * m + 3) → ℚ}
    (member : Slopes (2 * (m + 1)) → FibreMember (catCore m) request (m + 2))
    (hOpen : ∀ s, (member s).Open) (hOdd : ∀ s, (member s).HasOddMult)
    (hdiag : ∀ s, (member s).Diagonal)
    (hvalue : ∀ s, (member s).coreDiag = ballotCoreDiag m s)
    (hrequest : ∀ slot, request slot ≠ 0) :
    catalan (m + 1) ≤ GeometricFibre.openOddCount (catCore m) request (m + 2) :=
  CaterpillarBallot.catalan_le_openOddCount
    (ballotFamilyOfDiagonal member hOpen hOdd hdiag hvalue hrequest)

/-- **Genus six, end to end.**  Five open classes of odd multiplicity over the
caterpillar of loops of genus six, from the five ballot members alone -- no
injectivity obligation, no genericity of the request. -/
theorem five_le_openOddCount_genusSix_of_diagonal {request : Fin (6 * 2 + 3) → ℚ}
    (member : Slopes (2 * (2 + 1)) → FibreMember (catCore 2) request (2 + 2))
    (hOpen : ∀ s, (member s).Open) (hOdd : ∀ s, (member s).HasOddMult)
    (hdiag : ∀ s, (member s).Diagonal)
    (hvalue : ∀ s, (member s).coreDiag = ballotCoreDiag 2 s)
    (hrequest : ∀ slot, request slot ≠ 0) :
    5 ≤ GeometricFibre.openOddCount (catCore 2) request (2 + 2) :=
  CaterpillarBallot.five_le_openOddCount_genusSix
    (ballotFamilyOfDiagonal member hOpen hOdd hdiag hvalue hrequest)

/-! ## 6.  Non-vacuity of the constructor -/

/-- **`ballotFamilyOfDiagonal` is instantiable, unconditionally.**  At `m = 0`
the caterpillar member meets all five of its arguments: it is diagonal by
`CaterpillarRows.diagonalPattern`, and its diagonal is the ballot diagonal
because `Slopes 2` is a one-point type and `catDiag_eq_ballotCoreDiag_zig`
applies.  This exercises the whole chain on a genuine member. -/
noncomputable def genusTwoFamilyOfDiagonal {request : Fin (6 * 0 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) : BallotFamily 0 request :=
  ballotFamilyOfDiagonal (fun _ ↦ caterpillarMember 0 request)
    (fun _ ↦ caterpillarMember_open hRequest)
    (fun _ ↦ caterpillarMember_hasOddMult 0 request)
    (fun _ ↦ diagonal_caterpillarMember 0 request)
    (fun s ↦ by
      rw [coreDiag_caterpillarMember_eq_zig,
        show zig 0 = s from CaterpillarBallot.subsingleton_slopes_genusTwo.elim _ _])
    (fun slot ↦ (hRequest slot).ne')

/-- The bound that witness yields: `catalan 1 = 1`. -/
theorem one_le_openOddCount_genusTwo_of_diagonal {request : Fin (6 * 0 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    1 ≤ GeometricFibre.openOddCount (catCore 0) request (0 + 2) := by
  have hle := CaterpillarBallot.catalan_le_openOddCount (genusTwoFamilyOfDiagonal hRequest)
  rwa [show catalan (0 + 1) = 1 from catalan_one] at hle

/-! ## 7.  Why the coordinate *multiset* is not enough, checked in Lean

The witnesses of the negative, and the check that they really carry the
hypotheses they must carry to be witnesses: two genuine elements of
`Slopes (2 * (2 + 1))`, genuinely distinct, with genuinely equal multisets of
slopes -- hence, over the all-ones request, equal *coordinate multisets*.  So
`GeometricFibre.cls_injective_of_coordsMultiset_injective` provably cannot
discharge `BallotFamily.member_injective` at genus six without a genericity
hypothesis on the request, while
`GeometricFibre.cls_injective_of_coreDiag_injective` discharges it with none. -/

/-- The slope sequence `(2,1,2,3,2)` at `g = 6`: down, up, up, down. -/
noncomputable def slopesUpDown : Slopes (2 * (2 + 1)) where
  slopes := [2, 1, 2, 3, 2]
  length_eq := rfl
  head_eq := by decide
  getLast_eq := by decide
  one_le := by decide
  step := by decide

/-- Its mirror `(2,3,2,1,2)`: up, down, down, up. -/
noncomputable def slopesDownUp : Slopes (2 * (2 + 1)) where
  slopes := [2, 3, 2, 1, 2]
  length_eq := rfl
  head_eq := by decide
  getLast_eq := by decide
  one_le := by decide
  step := by decide

/-- The two witnesses are distinct slope sequences. -/
theorem slopesUpDown_ne_slopesDownUp : slopesUpDown ≠ slopesDownUp := by
  intro h
  exact absurd (congrArg Slopes.slopes h) (by decide)

/-- But they have the same multiset of slopes. -/
theorem slopes_multiset_eq :
    (slopesUpDown.slopes : Multiset ℕ) = (slopesDownUp.slopes : Multiset ℕ) := by
  decide

/-- Hence the same multiset of core diagonals: the two sequences differ only by
swapping the values at two spine slots. -/
theorem ballotCoreDiag_multiset_eq :
    (Finset.univ : Finset (Fin (6 * 2 + 3))).val.map (ballotCoreDiag 2 slopesUpDown) =
      (Finset.univ : Finset (Fin (6 * 2 + 3))).val.map (ballotCoreDiag 2 slopesDownUp) := by
  decide +kernel

/-- Hence, over the all-ones request, the same multiset of coordinates. -/
theorem allOnes_coreCoords_multiset_eq :
    (Finset.univ : Finset (Fin (6 * 2 + 3))).val.map
        (fun slot ↦ (1 : ℚ) / ballotCoreDiag 2 slopesUpDown slot) =
      (Finset.univ : Finset (Fin (6 * 2 + 3))).val.map
        (fun slot ↦ (1 : ℚ) / ballotCoreDiag 2 slopesDownUp slot) := by
  have hmap : ∀ s : Slopes (2 * (2 + 1)),
      (Finset.univ : Finset (Fin (6 * 2 + 3))).val.map
          (fun slot ↦ (1 : ℚ) / ballotCoreDiag 2 s slot) =
        Multiset.map (fun q : ℚ ↦ 1 / q)
          ((Finset.univ : Finset (Fin (6 * 2 + 3))).val.map (ballotCoreDiag 2 s)) :=
    fun s ↦ (Multiset.map_map _ _ _).symm
  rw [hmap, hmap, ballotCoreDiag_multiset_eq]

/-- **The precise negative.**  Any two members of the genus-six all-ones fibre
carrying the ballot diagonals of these two distinct slope sequences have *equal*
coordinate multisets.  `cls_injective_of_coordsMultiset_injective` therefore
cannot separate them; `cls_injective_of_coreDiag_injective` does, because
`ballotCoreDiag_injective` separates the diagonals as functions on core slots. -/
theorem coordsMultiset_collision
    (first second : FibreMember (catCore 2) (fun _ ↦ (1 : ℚ)) (2 + 2))
    (h₁ : first.Diagonal) (h₂ : second.Diagonal)
    (hd₁ : first.coreDiag = ballotCoreDiag 2 slopesUpDown)
    (hd₂ : second.coreDiag = ballotCoreDiag 2 slopesDownUp) :
    first.coordsMultiset = second.coordsMultiset := by
  have hA : first.coreCoords =
      fun slot ↦ (1 : ℚ) / ballotCoreDiag 2 slopesUpDown slot := by
    funext slot
    rw [h₁.coreCoords_eq_div slot, hd₁]
  have hB : second.coreCoords =
      fun slot ↦ (1 : ℚ) / ballotCoreDiag 2 slopesDownUp slot := by
    funext slot
    rw [h₂.coreCoords_eq_div slot, hd₂]
  rw [FibreMember.coordsMultiset_eq_map_coreCoords,
    FibreMember.coordsMultiset_eq_map_coreCoords, hA, hB]
  exact allOnes_coreCoords_multiset_eq

end BallotSlopes

end DraismaVargas.Count
