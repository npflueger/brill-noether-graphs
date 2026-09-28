import DraismaVargasCount.BallotDiagonal
import DraismaVargasCount.FibreCaterpillar

/-!
# Multiplicity one for every ballot caterpillar

**Source.**  Vargas, Part II (arXiv:2609.09109), the step of the proof of the main theorem
(`thm`) that computes the multiplicity of a morphism over the caterpillar of loops.  This
module proves `absMult (fullDim m s) = 1` for every `m` and every slope sequence
`s : Slopes (2 * (m + 1))`, not only for the zig-zag sequence.

For the zig-zag datum alone this is `FibreCaterpillar.caterpillarMember_absMult` (through
`Caterpillar.fdAbsMult_caterpillar`).  The inputs here are
`Count.signedMult_of_diagonalPattern`, the diagonal index pattern
`BallotValency.ballotDiagonalPattern` at a general slope sequence, and the diagonal computed
in `Count.BallotDiagonal`.

## The route, in one line

`Count.signedMult_of_diagonalPattern` turns a `DiagonalPattern` into
`Mult = (∏ᵢ num A(i,i)) / 2 ^ l(T)`.  `BallotDiagonal.bProd_num_matrix_diag`
evaluates the numerator product as `2 ^ (2m+2)` for **every** slope sequence,
and `Caterpillar.leafCount_catTree` says `l(T) = 2m+2`.  They cancel.

## Comparison with Part II

This differs from the corresponding step of Part II as follows.  That step computes the
multiplicity from the two intermediate values `det A_φ = 1` and `D_φ = 2^{l(T)}`.  In the
encoding used here both intermediate values are different when `m ≠ 1`, and neither is used
or proved: only the numerators of the diagonal entries are counted.  The conclusion
`|Mult| = 1` is the same.

## What is proved

* `signedMult_ballot`, `absMult_ballot` -- `Mult = 1` and `|Mult| = 1` on
  `(ballotLabelling m s).presentation`, for every `m` and every `s`.
* `fdAbsMult_ballotFullDim` -- `fdAbsMult (ballotFullDim m s) = 1`.
* `fdAbsMult_ballotFullDim_genusSix` -- its genus-six instance, over all five
  slope sequences at once.
* `bDiag`, `bDiag_pos`, `ballotCoords`, `ballotRealizes` -- the realization
  equation as an explicit diagonal solve, exactly as
  `FibreCaterpillar.catRealizes` does it for the zig-zag datum.  This belongs to the
  construction of the members rather than to the multiplicity; it is recorded here because
  it reduces what a member needs beyond the presentation to the `CoreIdentification` alone
  (see "What is not proved").
* `ballotMemberOf` -- the bridge to `Count.Fibre`.  It is a `FibreMember` whose
  `data` and `fullDim` fields are **pinned** to `ballotDatum m s` and
  `ballotFullDim m s` (both visible in its own type: the `realizes` argument is
  stated against `(ballotFullDim m s).labelling`, and `ballotMemberOf_data` /
  `ballotMemberOf_fullDim` read the two fields back by `rfl`).  Its remaining inputs
  -- the identification with `catCore m`, the coordinates and the solve -- are
  arguments, not assumptions hidden in a docstring.
* `ballotMemberOf_absMult`, `ballotMemberOf_hasOddMult` and the corresponding
  `ballotMember_*` -- **multiplicity one, hence odd multiplicity**, for every
  such member, every `m` and every `s`.  `ballotMember_open` records that the
  diagonal solve is in the open cone at a positive request.

## What is not proved here

* **No map from slope sequences to members.**  What is proved *in this file* is
  multiplicity one for the ballot *presentation*, and for any member built on it.  The map
  `member : Slopes (2*(m+1)) → FibreMember …` is
  `BallotCoreIdentification.ballotFamilyMember`, and `BallotCoreIdentification.ballotFamily`
  inhabits `Count.CaterpillarBallot.BallotFamily` at every `m` and every positive request,
  discharging its field `member_hasOddMult` with the `ballotMember_hasOddMult` theorem below.
* **The result applies to a member only if it is built with
  `BallotValency.ballotFullDim m s`.**  A different full-dimensional presentation over the
  same datum is not covered by anything below.  This is why `ballotMemberOf` pins the field
  in its type rather than taking a presentation as an argument.
* **No `CoreIdentification` is constructed.**  `ballotMemberOf` and
  `ballotMember` take `ident : CoreIdentification (catCore m) (ballotDatum m s)`
  as an argument; it is constructed for every `m` and `s` in `BallotCoreIdentification`
  (`ballotIdent`).  `FibreCaterpillar.catIdent` supplies it at the zig-zag, for
  `caterpillarDatum m`.
* **No exhaustion, no uniqueness, no count.**  Nothing below mentions exhaustion,
  uniqueness, `GeometricFibre.cls`, `openOddCount` or `catalan`.
* **Integrality is not used.**  Oddness is obtained from the *value* `1` via
  `FibreMember.hasOddMult_of_absMult_eq_one`, exactly as in the zig-zag case;
  `Count.Integrality` is not invoked.
* **No genericity hypothesis is used or supplied.**  Part II's count
  (`prop-divisors-on-chain`) assumes pairwise distinct edge lengths; that belongs to the
  uniqueness half and no statement below mentions it.  In particular `ballotMember_open`
  assumes only positivity of the request, which is strictly weaker.
-/

namespace DraismaVargas.Count.BallotMultiplicity

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.BallotFullDimensional
open DraismaVargas.Count.BallotValency
open DraismaVargas.Count.FibreCaterpillar (catCore)
open Utilities.Certificate.ExplicitPotential (Core)

variable {m : ℕ}

/-! ## 1.  The multiplicity of the ballot presentation -/

/-- **`Mult φ = 1` for every ballot caterpillar.**  The diagonal numerators
multiply to `2 ^ (2m+2)` (`BallotDiagonal.bProd_num_matrix_diag`, uniform in
the slope sequence) and the target has `2m+2` leaves
(`Caterpillar.leafCount_catTree`). -/
theorem signedMult_ballot (m : ℕ) (s : Slopes (2 * (m + 1))) :
    signedMult (ballotLabelling m s).presentation = 1 := by
  rw [signedMult_of_diagonalPattern (ballotDiagonalPattern m s),
    BallotDiagonal.bProd_num_matrix_diag s, Caterpillar.leafCount_catTree]
  exact div_self (by positivity)

theorem absMult_ballot (m : ℕ) (s : Slopes (2 * (m + 1))) :
    absMult (ballotLabelling m s).presentation = 1 := by
  rw [absMult, signedMult_ballot, abs_one]

/-- **Multiplicity one**: `absMult (fullDim m s) = 1` for every `m` and every slope
sequence. -/
theorem fdAbsMult_ballotFullDim (m : ℕ) (s : Slopes (2 * (m + 1))) :
    fdAbsMult (ballotFullDim m s) = 1 := absMult_ballot m s

/-- **Genus six**: all five ballot seeds have multiplicity one. -/
theorem fdAbsMult_ballotFullDim_genusSix (s : Slopes 6) :
    fdAbsMult (ballotFullDim 2 s) = 1 := fdAbsMult_ballotFullDim 2 s

/-- Consistency with the zig-zag caterpillar: at the zig-zag the value above and
`Caterpillar.fdAbsMult_caterpillar` agree.  The two presentations are
terms of different (defeq-after-`ballotDatum_zig`) types, so this is stated as
the agreement of their values, not as a transport. -/
theorem absMult_ballot_zig (m : ℕ) :
    absMult (ballotLabelling m (zig m)).presentation = 1 ∧
      fdAbsMult (CaterpillarRows.fullDim m) = 1 :=
  ⟨absMult_ballot m (zig m), Caterpillar.fdAbsMult_caterpillar m⟩

/-! ## 2.  The realization equation as an explicit diagonal solve

This section belongs to the construction of the members rather than to the multiplicity.
It is here because it is two lines given `BallotValency.ballotDiagonalPattern`, and because
it reduces what a member needs beyond the presentation to the `CoreIdentification` alone. -/

/-- The diagonal entry of the ballot length matrix on the row `slot`.
`BallotDiagonal.bMatrix_diag` evaluates it: `2` on a leaf row, `1 / s_i` on the
spine row `h_i`, `1/2` on a stem. -/
noncomputable def bDiag (m : ℕ) (s : Slopes (2 * (m + 1)))
    (slot : Fin (6 * m + 3)) : ℚ :=
  matrix (ballotLabelling m s).presentation slot slot

theorem bDiag_eq (m : ℕ) (s : Slopes (2 * (m + 1))) (slot : Fin (6 * m + 3)) :
    bDiag m s slot =
      if IsLeafEdge m slot then 2
      else if slot.val % 3 = 1 then 1 / (s.slope ((slot.val + 2) / 3) : ℚ)
      else 1 / 2 :=
  BallotDiagonal.bMatrix_diag s slot

theorem bDiag_pos (m : ℕ) (s : Slopes (2 * (m + 1))) (slot : Fin (6 * m + 3)) :
    0 < bDiag m s slot :=
  (ballotDiagonalPattern m s).matrix_diag_pos slot

theorem bDiag_ne_zero (m : ℕ) (s : Slopes (2 * (m + 1)))
    (slot : Fin (6 * m + 3)) : bDiag m s slot ≠ 0 := (bDiag_pos m s slot).ne'

/-- **The coordinate vector**: the ballot length matrix is diagonal, so the
realization equation is solved entry by entry. -/
noncomputable def ballotCoords (m : ℕ) (s : Slopes (2 * (m + 1)))
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (request : Fin (6 * m + 3) → ℚ) (slot : Fin (6 * m + 3)) : ℚ :=
  request (ident.row ((ballotLabelling m s).row.symm slot)) / bDiag m s slot

theorem ballotCoords_pos {m : ℕ} {s : Slopes (2 * (m + 1))}
    {ident : CoreIdentification (catCore m) (ballotDatum m s)}
    {request : Fin (6 * m + 3) → ℚ} (hRequest : ∀ slot, 0 < request slot)
    (slot : Fin (6 * m + 3)) : 0 < ballotCoords m s ident request slot :=
  div_pos (hRequest _) (bDiag_pos m s slot)

/-- **The realization equation, as an explicit diagonal solve.** -/
theorem ballotRealizes (m : ℕ) (s : Slopes (2 * (m + 1)))
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (request : Fin (6 * m + 3) → ℚ) :
    (matrix (ballotFullDim m s).labelling.presentation).mulVec
        (ballotCoords m s ident request) =
      fun row ↦ request (ident.row ((ballotFullDim m s).labelling.row.symm row)) := by
  funext row
  rw [ballotFullDim_labelling, (ballotDiagonalPattern m s).matrix_eq_diagonal,
    Matrix.mulVec_diagonal]
  show bDiag m s row * ballotCoords m s ident request row = _
  rw [ballotCoords, mul_div_cancel₀ _ (bDiag_ne_zero m s row)]

/-! ## 3.  The bridge to `Count.Fibre` -/

/-- **A member of the labelled fibre built on the ballot presentation.**  The
`data` and `fullDim` fields are pinned: they are `ballotDatum m s` and
`ballotFullDim m s`, and `ballotFullDim m s` appears in the type of the
`realizes` argument, so a reader can see from the signature alone which
presentation the multiplicity statements below are about.  The remaining
inputs -- the identification with `catCore m`, the coordinates and the solve --
are arguments. -/
noncomputable def ballotMemberOf (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (coords : Fin (6 * m + 3) → ℚ)
    (realizes : (matrix (ballotFullDim m s).labelling.presentation).mulVec coords =
      fun row ↦ request (ident.row ((ballotFullDim m s).labelling.row.symm row))) :
    FibreMember (catCore m) request (m + 2) where
  target := catTree m
  data := ballotDatum m s
  fullDim := ballotFullDim m s
  ident := ident
  coords := coords
  realizes := realizes

@[simp] theorem ballotMemberOf_data (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (coords : Fin (6 * m + 3) → ℚ) (realizes : _) :
    (ballotMemberOf m s request ident coords realizes).data = ballotDatum m s := rfl

@[simp] theorem ballotMemberOf_fullDim (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (coords : Fin (6 * m + 3) → ℚ) (realizes : _) :
    (ballotMemberOf m s request ident coords realizes).fullDim = ballotFullDim m s := rfl

@[simp] theorem ballotMemberOf_coords (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (coords : Fin (6 * m + 3) → ℚ) (realizes : _) :
    (ballotMemberOf m s request ident coords realizes).coords = coords := rfl

/-- **Multiplicity one, at the member level.** -/
theorem ballotMemberOf_absMult (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (coords : Fin (6 * m + 3) → ℚ) (realizes : _) :
    (ballotMemberOf m s request ident coords realizes).absMult = 1 :=
  fdAbsMult_ballotFullDim m s

/-- **Odd multiplicity at the member level, in the form `BallotFamily.member_hasOddMult`
consumes.**  The map `Slopes (2*(m+1)) → FibreMember …` that field is stated for is
`BallotCoreIdentification.ballotFamilyMember`. -/
theorem ballotMemberOf_hasOddMult (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (coords : Fin (6 * m + 3) → ℚ) (realizes : _) :
    (ballotMemberOf m s request ident coords realizes).HasOddMult :=
  FibreMember.hasOddMult_of_absMult_eq_one
    (ballotMemberOf_absMult m s request ident coords realizes)

/-- The member carried by the diagonal solve of §2: only the `CoreIdentification`
is an argument. -/
noncomputable def ballotMember (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s)) :
    FibreMember (catCore m) request (m + 2) :=
  ballotMemberOf m s request ident (ballotCoords m s ident request)
    (ballotRealizes m s ident request)

@[simp] theorem ballotMember_coords (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s)) :
    (ballotMember m s request ident).coords = ballotCoords m s ident request := rfl

theorem ballotMember_absMult (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s)) :
    (ballotMember m s request ident).absMult = 1 :=
  ballotMemberOf_absMult m s request ident _ _

theorem ballotMember_hasOddMult (m : ℕ) (s : Slopes (2 * (m + 1)))
    (request : Fin (6 * m + 3) → ℚ)
    (ident : CoreIdentification (catCore m) (ballotDatum m s)) :
    (ballotMember m s request ident).HasOddMult :=
  ballotMemberOf_hasOddMult m s request ident _ _

/-- The diagonal solve lies in the open cone at a positive request.  This is
`BallotFamily.member_open`'s content for this member. -/
theorem ballotMember_open {m : ℕ} {s : Slopes (2 * (m + 1))}
    {request : Fin (6 * m + 3) → ℚ}
    (ident : CoreIdentification (catCore m) (ballotDatum m s))
    (hRequest : ∀ slot, 0 < request slot) :
    (ballotMember m s request ident).Open :=
  fun slot ↦ ballotCoords_pos hRequest slot

/-! ## 4.  Concrete values -/

/-- **The general spine entry really is `1 / s_i`.**  At genus six and the
slope sequence `[2, 3, 4, 3, 2]` the spine row over target occurrence `7` is
`h_3`, whose slope is `4`, so its diagonal entry is `1/4` -- neither `1` nor
`1/2`, the only two values the zig-zag ever takes. -/
example : matrix (ballotLabelling 2 Slopes.six).presentation 7 7 = 1 / 4 := by
  rw [BallotDiagonal.bMatrix_diag]
  norm_num [IsLeafEdge, Slopes.slope, Slopes.six]

/-- A leaf row of the same member still has entry `2`. -/
example : matrix (ballotLabelling 2 Slopes.six).presentation 0 0 = 2 := by
  rw [BallotDiagonal.bMatrix_diag]
  norm_num [IsLeafEdge]

/-- And the multiplicity is one all the same. -/
example : fdAbsMult (ballotFullDim 2 Slopes.six) = 1 :=
  fdAbsMult_ballotFullDim 2 Slopes.six

end DraismaVargas.Count.BallotMultiplicity
