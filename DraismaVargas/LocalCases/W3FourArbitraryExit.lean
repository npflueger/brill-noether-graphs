import DraismaVargas.LocalCases.W3FourIncomingMatching
import DraismaVargas.LocalCases.W3FourRegrownColumnSeam
import DraismaVargas.LocalCases.FiniteAtlasMarch

/-!
# Equation (2)'s matrices and outgoing velocity, for an arbitrary incoming `w3Four` cover

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w3-r1-nd3-t2-(a=k₄)}`, Figure 28 and
Equation (2).  Part I works with isomorphism classes of gluing data; for a fixed
gluing datum value, Equation (2)'s four members do not all live over one datum
(see below).

`W3FourIncomingMatching.exists_member_normalization` proves that an incoming
`w3Four` cover *is* a named Figure 28 member over its own wall datum together
with a normalization receipt; `W3FourRegrownColumnSeam.MemberCertificates`
carries Equation (2)'s four honest members with their stable-incidence
dictionaries.  This file supplies the linear algebra the original-coordinate
exit of this case runs on:

* `memberMatrix` -- Equation (2)'s four derived length matrices, in the
  family's own column order `Option target.edges`;
* `outgoingVelocity`, `outgoingVelocity_system` -- the canonical outgoing chart
  velocity at a nonsingular member, the unique solution of the outgoing linear
  system whose right-hand side is the incoming one; it discharges the exit's
  `hSystems` hypothesis at any nonsingular member.

## The coordinate order

Figure 28's family is presented at **one fixed** labelling --
`W3FourLimitRows.limitRowsOfInput`, the limit's own stable rows with columns
`Option (contract target hab hOne).edges` and wall column `none` -- so an exit
stated against the incoming cover's own length matrix needs the identification
of column orders (`hOrder`, that the incoming cover's contracted column is the
family's wall column `none`) and of the presented matrix of the identified
member with the incoming cover's own (`hHonest`).  `W3FourHonestReceipts`
restates Equation (2)'s family at an **arbitrary**
`W4StableSource.StableLengthMatrixLabelling` of one member -- the analogue of
`W3Nd3CommonBalance.labelling` / `squareMatrix` / `columnEquiv` / `wallColumn`
-- which removes `hOrder` at the source.  The stable-graph half,
`StableGraphIncidence.Equivalence` between any two members, Figure 28 already
has (`W3FourRegrownColumnSeam.MemberCertificates.certificate`).

A starting nonsingular member is **not** a hypothesis:
`FullDimensionalSourcePresentation.det_ne_zero` is the incoming cover's own
nonsingularity, and `hHonest` transports it to the family's presented matrix at
the identified index, which is exactly Equation (2)'s gate.

## The gauge copy: where it enters, and where it does not

`W3FourIncomingCensus` and `W3FourIncomingMatching` work over the incoming
cover's own wall datum `contractDatum data hc hab hOne`, and so does the
identification of the incoming cover: `W3FourIncomingCensus.exists_positionMember`
supplies the `t₄` member over that datum whichever way the Position I /
Position II.b dichotomy falls, so **the identification never leaves it**, and no
`WallTransport` and no branch swap occurs there.

The branch swap enters only on the *outgoing* side, inside Equation (2): its
four members do not live over one datum value, and
`W3FourRegrownColumnSeam.exists_memberCertificates` builds `M⁽¹⁾` and `M⁽²⁾` on
branch-swapped copies, rebasing them by `W3FourDisjointness.BranchGauge.valid`.
That is strictly less than in Figure 29's case, where the *incoming*
identification itself may be forced onto a copy.

## What is not claimed

No requested `Spec`, no terminal refinement, no metric-length dictionary: the
cleared pencil of the exit is on the outgoing member's literal source
subdivision, exactly as in nd2, nd3, M11 and Figure 29.  The outgoing member is
not certified distinct from the incoming one: Equation (2)'s exit
(`W3FourHonestBalance.HonestFigure28.exists_valid_positive_exit_with_pencil`)
returns strict opposition of determinant signs, which forces distinctness of
the *matrices* but is not stated as an index inequality.  No FourStar theorem is
applied to this ThreeStar case.
-/

namespace DraismaVargas.LocalCases.W3FourArbitraryExit

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open TargetExpansion
open W3Nd2IncomingTargetPlacement (divalentOccurrence)
open W3FourClosure (FourStarGeometry)
open W3FourIncomingCensus (WallMember)
open W3FourIncomingMatching (exists_member_normalization)
open W3FourRegrownColumnSeam (MemberCertificates)
open W3ShiftIncomingMatching (SelectedCensus)

noncomputable local instance {target : CFGraph} : DecidableEq target.edges :=
  Classical.decEq _

/-! ## §2  Equation (2)'s matrices and the canonical outgoing chart velocity -/

section Velocity

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {geometry : FourStarGeometry data wall}

/-- Equation (2)'s four derived length matrices, in the family's own column
order `Option target.edges`. -/
noncomputable def memberMatrix (certified : MemberCertificates data wall geometry)
    (index : Fin 4) : Matrix (Option target.edges) (Option target.edges) ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix
    (certified.receipts.gaugeFamily.presentation index)

/-- The canonical outgoing chart velocity at a nonsingular member: the unique
solution of the outgoing linear system whose right-hand side is the incoming
one.  This is `W3Nd3ArbitraryExit.outgoingVelocity` for Figure 28's family. -/
noncomputable def outgoingVelocity (certified : MemberCertificates data wall geometry)
    (incoming : Fin 4) (incomingVelocity : Option target.edges → ℚ) (outgoing : Fin 4) :
    Option target.edges → ℚ :=
  FiniteAtlasMarch.chartCoordinates (memberMatrix certified outgoing)
    ((memberMatrix certified incoming).mulVec incomingVelocity)

/-- It discharges the exit's `hSystems` hypothesis at any nonsingular member. -/
theorem outgoingVelocity_system (certified : MemberCertificates data wall geometry)
    (incoming : Fin 4) (incomingVelocity : Option target.edges → ℚ) (outgoing : Fin 4)
    (hDet : (memberMatrix certified outgoing).det ≠ 0) :
    (memberMatrix certified incoming).mulVec incomingVelocity =
      (memberMatrix certified outgoing).mulVec
        (outgoingVelocity certified incoming incomingVelocity outgoing) :=
  (FiniteAtlasMarch.mulVec_chartCoordinates _ hDet _).symm

end Velocity

end DraismaVargas.LocalCases.W3FourArbitraryExit
