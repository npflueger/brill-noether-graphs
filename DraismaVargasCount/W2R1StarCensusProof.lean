import DraismaVargasCount.W3Nd2StarCensusProof
import DraismaVargasCount.W2R1UnitBalance
import DraismaVargas.LocalCases.W2R1GraphTracking

/-!
# The W2R1 star census, Stages 1 and 3, and Stage 2 reduced to transports

Sources: Draisma–Vargas Part I, Case `{w2-r1}`, sub-cases `{w2-r1-nd3}` (Figure 37) and
`{w2-r1-nd2}` (Figure 38), **Equation (10)**; Vargas, Part II, the star of a wall and the
balancing condition `prop-signed-mult`.  The census machinery is
`DraismaVargasCount.StarCensusEngine`; the file follows the pattern of
`DraismaVargasCount.W3Nd2StarCensusProof`, `DraismaVargasCount.W3Nd3StarCensusProof` and
`DraismaVargasCount.M11StarCensusProof`.  It concerns the star of a W2R1 wall: it proves
that the two members of Equation (10) are distinct classes of the star with the
multiplicities of Equation (10) (Stages 1 and 3), and reduces the statement that they
exhaust the star (Stage 2) to transports.

## The result, in one paragraph

`RegrowthWallInput.FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2R1` is reduced to the single
statement `W2R1StarExhaustion` (`familyStarParity_w2R1_of_exhaustion`), which is *equivalent*
to the census `W2R1StarCensus` (`w2R1StarExhaustion_iff`).  **(a) and (c) are proved at
every core, degree, positive request and Equation (10) presentation, with no hypothesis.**
The family is a miniature of the W3Nd2 family (`W3Nd2StarCensusProof`): Equation (10) has
two members with *derived* unit weights
(`W2R1CommonBalance.equation_ten_weights_normalized`), the incoming one is nonsingular, so
both are (`nonsingular`); both are wall-anchored; and they are distinct classes because a
frame isomorphism would equate their regrown columns, making the two square matrices equal
and Equation (10) `det A₀ + det A₁ = 0` singular (`not_rel_01`).  Both members expand the
divalent wall into divalent/divalent ends, so the engine's valency invariant cannot
separate them; the regrown column does, without being computed.

## What is proved

* **Stage 1 (a).**  `graphData_branchSquare` -- the branch square of **any** two-block
  limit-chain member (`LocalCases.LimitChainTwoBlock.GraphData`), family-free;
  `branchSquare` at Figures 37/38's members; `member`: position `q` of Equation (10) as a
  member of the wall's star, for any full-dimensional presentation of its datum,
  wall-anchored (`M = w.limit`, `φ = refl`), through `W2R1GraphData.equivalence` and
  `W2R1RowDescent.matrix_retained`.  `nonsingular` (both positions, always), `fdAt`,
  `rep`, `multNat_rep` (class multiplicity `= |num (signedMult (lab q))|`),
  `integral_signedMult`, `sum_signedMult_eq_zero` (Equation (10) in the incoming
  presentation's labelling, `W2R1UnitBalance.sum_signedMult_eq_zero`).
* **Stage 3 (c).**  `squareMatrix_eq_of_new_eq`, `det_eq_zero_of_new_eq`,
  `squareMatrix_det_ne_zero` (over any `W2R1CommonBalance.LimitColumns`), `frameAt`,
  `not_rel_01` (unconditional), `rep_eq_of_cls_eq`, `repCls_injective`.
* **Stage 2 reduced to transports.**  `PositionTransport`, `exhausts_of_transports`, over
  the valency-free placement data of `W3Nd2StarCensusProof` (`PlacementSpec`,
  `memberResolution`, `memberNorm`, imported, not restated).
* **Assembly.**  `Exhausts`, `repCls_surjective`, `census_of_exhaustion`,
  `exhaustion_of_census`, `starParityAt_of_census`, `starParityAt_of_exhaustion` (per
  wall); `W2R1StarCensus`, `W2R1StarExhaustion`, `w2R1StarCensus_of_exhaustion`,
  `exhaustion_of_w2R1StarCensus`, `w2R1StarExhaustion_iff`, `exists_incoming` (the
  regrowth's own cover, `W2R1GraphTracking.exists_matched_tracking`),
  `familyStarParity_w2R1_of_census`, and the headline `familyStarParity_w2R1_of_exhaustion`.

## What is NOT proved here

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2R1` is not proved in this file.**  Its exact
  remaining input here is `W2R1StarExhaustion` (Stage 2 (b): every star member is a frame
  isomorph of one of the two positions).  *Interface*: equivalent to `W2R1StarCensus`
  (`w2R1StarExhaustion_iff`), neither weaker nor stronger.  **It is proved in the companion
  `DraismaVargasCount.W2R1StarExhaustionProof`** (`W2R1StarExhaustionProof.w2R1StarExhaustion`,
  headline `W2R1StarExhaustionProof.familyStarParity_w2R1`), with the transport builder
  `M11StarExhaustionProof.nonempty_transportFree_of_rel`.
* **What Stage 2 needs** (the hypothesis of `exhausts_of_transports`): for each star member
  `m` with limit isomorphism `ψ`, a placement and a `ResolutionExpansionFree.TransportFree`
  along `ψ` from `m`'s normal form onto position `0`'s or `1`'s pasted resolution.  It
  needs the wall's `W2SourceInput` and `Pair` pulled back to `m.limit` along `ψ` and Part I's
  incoming partition census (`W2R1IncomingCensus` / `W2R1IncomingMatching`) read at `m`;
  all of it is done in `DraismaVargasCount.W2R1StarExhaustionProof`.
* No regrowth tagged `w2R1` is exhibited here.
* Nothing here depends on genus six or degree four except the headline's instantiation.

## Remarks

* Equation (10) is a two-term unit-weight balance, so the separation argument of
  `W3Nd2StarCensusProof` applies verbatim: the weights are the derived `![1, 1]`
  (`W2R1CommonBalance.LimitColumns.determinant_balance`), and `not_rel_01` is that argument
  over `W2R1CommonBalance.LimitColumns`.  The only adaptation is that the two members share
  one generic construction (`W2R1SourceCandidates.Pair.candidate`), so `member`, `rep` and
  the position transport are uniform in the position instead of split into two definitions.
* Generic lemmas are imported, not restated: `ne_zero_of_add_eq_zero`, `PlacementSpec`,
  `memberResolution`, `memberNorm` from `W3Nd2StarCensusProof`; `candidate_*`, `wall_join`,
  `refl_*`, `pasted`, `num_natAbs_eq_of_abs_eq` from `M11StarCensusProof`.  New and
  family-free: `graphData_branchSquare` (every two-block limit-chain member, hence also
  every one-block one, see `W2PStarCensusProof.coreGraphData_branchSquare`).

## Consumers

`DraismaVargasCount.W2R1StarExhaustionProof` (the exhaustion and the unconditional clause,
which `StarSupplyAssembly` uses for the trivalent wall step of
`DraismaVargasCount.Assembly`); `DraismaVargasCount.W2PStarCensusProof` uses
`graphData_branchSquare`.
-/

namespace DraismaVargas.Count.W2R1StarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W2R1Target SecondEquation W2R1SourceCandidates
open W3Nd2StarCensusProof (PlacementSpec memberResolution memberNorm)

/-! ## 1.  The branch square of any two-block member -/

section Local

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {anchors : Finset (Fin degree)}

/-- **The branch square of any two-block limit-chain member**
(`LimitChainTwoBlock.GraphData`): the stable-graph equivalence sends each branch vertex
to a member source vertex whose contraction is that branch.  Three cases, read off
`GraphData.branchImage`: away from the wall (a retained vertex), at a selected block (the
member's branch vertex above the block's anchor), and over the background (the fresh
endpoint). -/
theorem graphData_branchSquare (rd : LimitChainTwoBlock.GraphData data wall anchors)
    (v : BranchVertex data) :
    data.sourceEndpoint (contractVertex target wall (rd.equivalence.vertex v).1.1.1)
        (rd.equivalence.vertex v).1.1.2 = v.1 := by
  classical
  have hRef := M11StarCensusProof.candidate_refines rd.candidate
  change data.sourceEndpoint (contractVertex target wall (rd.branchImage v.1).1.1)
      (rd.branchImage v.1).1.2 = v.1
  by_cases hAt : v.1.1.1 = wall
  · by_cases hSel : LimitChainTwoBlock.IsSelected data wall anchors v.1.1.2
    · rw [rd.branchImage_anchorOf hAt hSel]
      unfold LimitChainTwoBlock.GraphData.branchVertex
      rw [StarCensusEngine.sourceEndpoint_contract _ data _ _ (hRef _)]
      have hc : contractVertex target wall
          (LimitChainCore.wallSide target wall
            (rd.selectedSide (LimitChainTwoBlock.anchorOf data wall anchors v.1.1.2))) =
            wall := by
        unfold LimitChainCore.wallSide
        split_ifs <;> rfl
      rw [hc, NonTrivalentValencyThreeExit.sourceEndpoint_eq_of_rel
        (LimitChainTwoBlock.anchorOf_rel hSel)]
      have hSelf := data.sourceEndpoint_self v.1
      rw [hAt] at hSelf
      exact hSelf
    · rw [rd.branchImage_background hAt hSel,
        StarCensusEngine.sourceEndpoint_contract _ data _ _ (hRef _)]
      have hSelf := data.sourceEndpoint_self v.1
      rw [hAt] at hSelf
      exact hSelf
  · rw [rd.branchImage_away hAt]
    unfold ResolutionAwayFromWall.retainedVertex
    rw [StarCensusEngine.sourceEndpoint_contract _ data _ _ (hRef _)]
    exact data.sourceEndpoint_self v.1

variable {star : TwoStar target wall} (pair : Pair data star) (hValid : data.Valid)

/-- **The branch square of Equation (10)'s member `q`** (Figures 37/38). -/
theorem branchSquare (q : Fin 2) (v : BranchVertex data) :
    data.sourceEndpoint
        (contractVertex target wall ((W2R1GraphData.equivalence pair hValid q).vertex v).1.1.1)
        ((W2R1GraphData.equivalence pair hValid q).vertex v).1.1.2 = v.1 :=
  graphData_branchSquare (W2R1GraphData.graphData pair hValid q) v

end Local

/-! ## 2.  The two positions of Equation (10) as members of the wall's star (Stage 1) -/

section Positions

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (pair : Pair w.limit star) (hValid : w.limit.Valid)

/-- **Position `q` of Equation (10) is a member of the wall's star**, for any
full-dimensional presentation of its datum.  Both positions are wall-anchored
(`M = w.limit`, `φ = refl`): Figures 37 and 38 build both members over the wall's own
limit, blockwise. -/
noncomputable def member (q : Fin 2)
    (fd : FullDimensionalSourcePresentation (pair.candidate q).datum (Fin p)) :
    GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := W2R1GraphData.equivalence pair hValid q) (fd := fd)
    (hRetained := W2R1RowDescent.matrix_retained pair hValid q)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
    (hOld := M11StarCensusProof.candidate_old _) (hEdge := M11StarCensusProof.candidate_edge _)
    (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans
      (branchSquare pair hValid q v))
    (M11StarCensusProof.refl_rowSquare w _ _ (fun _ ↦ rfl))

end Positions

/-! ## 3.  Both positions are nonsingular, and are star classes -/

section Census

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (pair : Pair w.limit star) (hValid : w.limit.Valid)
  {incoming : Fin 2}
  (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum (Fin p))

/-- Equation (10)'s labelling of position `q`, induced from the incoming presentation. -/
noncomputable abbrev lab (q : Fin 2) :=
  W2R1GraphData.outgoingLabelling pair hValid incoming incomingFD q

/-- **Both positions of Equation (10) are nonsingular**: the incoming one is
(`W2R1GraphData.incomingDet_ne_zero`), and the two determinants are negatives of each
other (`W2R1CommonBalance.LimitColumns.determinant_balance`, unit weights). -/
theorem nonsingular (q : Fin 2) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (lab w pair hValid incomingFD q).presentation).det ≠ 0 := by
  have h := (W2R1LimitMatrix.limitColumns pair hValid).determinant_balance hValid
    (W2R1GraphData.initialLabelling pair hValid incoming incomingFD)
  rw [one_mul, one_mul] at h
  exact W3Nd2StarCensusProof.ne_zero_of_add_eq_zero
    (A := fun q ↦ ((W2R1LimitMatrix.limitColumns pair hValid).squareMatrix
      (W2R1GraphData.initialLabelling pair hValid incoming incomingFD) q).det) h
    (W2R1GraphData.incomingDet_ne_zero pair hValid incoming incomingFD) q

/-- The full-dimensional presentation of a position, transported from the incoming one
along the family's stable-graph equivalences. -/
noncomputable def fdAt (q : Fin 2) :
    FullDimensionalSourcePresentation (pair.candidate q).datum (Fin p) :=
  W2R1GraphData.outgoingPresentation pair hValid (W4StarParity.limitTarget_connected w)
    (W4StarParity.limitTarget_genus w) incoming q incomingFD
    (nonsingular w pair hValid incomingFD q)

/-- **The star member of a position of Equation (10).** -/
noncomputable def rep (q : Fin 2) : GeometricStar.StarMember hy w :=
  member w hy pair hValid q (fdAt w pair hValid incomingFD q)

/-- **The multiplicity of a position's star class is its term of Equation (10)**, up to
sign. -/
theorem multNat_rep (q : Fin 2) :
    (GeometricStar.Star.toFibre (rep w hy pair hValid incomingFD q).cls).multNat =
      (signedMult (lab w pair hValid incomingFD q).presentation).num.natAbs :=
  M11StarCensusProof.num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)

/-- **Every term of Equation (10) is an integer.** -/
theorem integral_signedMult (q : Fin 2) :
    ∃ value : ℤ, signedMult (lab w pair hValid incomingFD q).presentation = (value : ℚ) :=
  isIntegralMultiplicity (fdAt w pair hValid incomingFD q)

/-- **Equation (10) in the incoming presentation's labelling.** -/
theorem sum_signedMult_eq_zero :
    ∑ q : Fin 2, signedMult (lab w pair hValid incomingFD q).presentation = 0 :=
  W2R1UnitBalance.sum_signedMult_eq_zero (W2R1LimitMatrix.limitColumns pair hValid)
    (W2R1GraphData.initialLabelling pair hValid incoming incomingFD) hValid

end Census

/-! ## 4.  Separation between the two positions (Stage 3) -/

section Generic

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : TwoStar target wall} {pair : Pair data star}
  (limit : W2R1CommonBalance.LimitColumns pair)

/-- Equal regrown columns give equal square matrices, in every common labelling. -/
theorem squareMatrix_eq_of_new_eq
    (hNew : ∀ path : StablePath data, limit.commonMatrix 1 path none =
      limit.commonMatrix 0 path none)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    limit.squareMatrix initial 0 = limit.squareMatrix initial 1 := by
  funext row column
  rw [limit.squareMatrix_common, limit.squareMatrix_common]
  cases W2R1CommonBalance.LimitColumns.targetCoordinates initial column with
  | none => exact (hNew _).symm
  | some place => rw [limit.commonMatrix_retained, limit.commonMatrix_retained]

/-- …hence, by Equation (10), a singular first member. -/
theorem det_eq_zero_of_new_eq (hValid : data.Valid)
    (hNew : ∀ path : StablePath data, limit.commonMatrix 1 path none =
      limit.commonMatrix 0 path none)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    (limit.squareMatrix initial 0).det = 0 := by
  have h := limit.determinant_balance hValid initial
  rw [← squareMatrix_eq_of_new_eq limit hNew initial] at h
  linarith

/-- A full-dimensional member `0` is nonsingular in every common labelling of
Equation (10): multiplicity does not depend on the labelling. -/
theorem squareMatrix_det_ne_zero {p : ℕ}
    (fd0 : FullDimensionalSourcePresentation (pair.candidate 0).datum (Fin p)) :
    (limit.squareMatrix fd0.labelling 0).det ≠ 0 := by
  have h := absMult_labelling_indep (limit.labelling fd0.labelling 0) fd0.labelling
  have hfd := (W4StarParity.absMult_ne_zero_iff fd0.labelling.presentation).mpr fd0.det_ne_zero
  exact (W4StarParity.absMult_ne_zero_iff _).mp (h ▸ hfd)

end Generic

section Separation

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (pair : Pair w.limit star) (hValid : w.limit.Valid)

/-- The frame of position `q`. -/
noncomputable abbrev frameAt (q : Fin 2)
    (fd : FullDimensionalSourcePresentation (pair.candidate q).datum (Fin p)) :=
  StarCensusEngine.frame w hy (pair.candidate q).datum (W2R1GraphData.equivalence pair hValid q) fd

/-- **The two positions of Equation (10) are distinct star classes**, at every wall: a
frame isomorphism would equate their regrown columns
(`StarCensusEngine.frameIso_matrix_new`), and equal regrown columns make Equation (10)
singular. -/
theorem not_rel_01
    (fd0 : FullDimensionalSourcePresentation (pair.candidate 0).datum (Fin p))
    (fd1 : FullDimensionalSourcePresentation (pair.candidate 1).datum (Fin p)) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frameAt w hy pair hValid 0 fd0)
      (frameAt w hy pair hValid 1 fd1)) := by
  rintro ⟨fi⟩
  have hNew : ∀ path : StablePath w.limit,
      (W2R1LimitMatrix.limitColumns pair hValid).commonMatrix 1 path none =
        (W2R1LimitMatrix.limitColumns pair hValid).commonMatrix 0 path none := fun path ↦
    StarCensusEngine.frameIso_matrix_new
      (E := W2R1GraphData.equivalence pair hValid 0)
      (E' := W2R1GraphData.equivalence pair hValid 1)
      (W2R1RowDescent.matrix_retained pair hValid 0)
      (W2R1RowDescent.matrix_retained pair hValid 1) fi path
  exact squareMatrix_det_ne_zero (W2R1LimitMatrix.limitColumns pair hValid) fd0
    (det_eq_zero_of_new_eq _ hValid hNew fd0.labelling)

end Separation

/-! ## 5.  The census from exhaustion (Stage 2) -/

section Assembly

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (pair : Pair w.limit star) (hValid : w.limit.Valid)
  {incoming : Fin 2}
  (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum (Fin p))

/-- **The two positions are distinct star classes** (Stage 3), at every wall. -/
theorem rep_eq_of_cls_eq (q q' : Fin 2)
    (h : (rep w hy pair hValid incomingFD q).cls = (rep w hy pair hValid incomingFD q').cls) :
    q = q' := by
  fin_cases q <;> fin_cases q'
  · rfl
  · exact (not_rel_01 w hy pair hValid (fdAt w pair hValid incomingFD 0)
      (fdAt w pair hValid incomingFD 1) (Quotient.exact h)).elim
  · exact (not_rel_01 w hy pair hValid (fdAt w pair hValid incomingFD 0)
      (fdAt w pair hValid incomingFD 1) ((Quotient.exact h).elim fun fi ↦ ⟨fi.symm⟩)).elim
  · rfl

/-- The positions' classes, as a map to the star. -/
noncomputable def repCls (q : Fin 2) : GeometricStar.Star hy w :=
  (rep w hy pair hValid incomingFD q).cls

theorem repCls_injective : Function.Injective (repCls w hy pair hValid incomingFD) :=
  fun a b h ↦ rep_eq_of_cls_eq w hy pair hValid incomingFD a b h

/-- **Exhaustion at one wall** (Stage 2): every member of the star is in the
class of one of the two positions.  *Interface*: with Stages 1 and 3 it is equivalent to
the census at this wall (`census_of_exhaustion`, `exhaustion_of_census`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ q : Fin 2,
    member.cls = (rep w hy pair hValid incomingFD q).cls

theorem repCls_surjective (hExh : Exhausts w hy pair hValid incomingFD) :
    Function.Surjective (repCls w hy pair hValid incomingFD) := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨q, h⟩ := hExh member
  exact ⟨q, h.symm⟩

/-- **The W2R1 census at one wall from exhaustion.** -/
theorem census_of_exhaustion (hExh : Exhausts w hy pair hValid incomingFD) :
    ∃ e : Fin 2 ≃ GeometricStar.Star hy w,
      ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
        (signedMult (lab w pair hValid incomingFD q).presentation).num.natAbs :=
  ⟨Equiv.ofBijective _ ⟨repCls_injective w hy pair hValid incomingFD,
      repCls_surjective w hy pair hValid incomingFD hExh⟩,
    fun q ↦ multNat_rep w hy pair hValid incomingFD q⟩

/-- **Interface: the census implies exhaustion.**  An injective map between
finite sets of equal cardinality is onto. -/
theorem exhaustion_of_census (e : Fin 2 ≃ GeometricStar.Star hy w) :
    Exhausts w hy pair hValid incomingFD := by
  classical
  have hBij : Function.Bijective (repCls w hy pair hValid incomingFD) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨repCls_injective w hy pair hValid incomingFD, Fintype.card_congr e⟩
  intro member
  obtain ⟨q, hq⟩ := hBij.2 member.cls
  exact ⟨q, hq.symm⟩

/-- **The star clause from Equation (10) and the census.** -/
theorem starParityAt_of_census (e : Fin 2 ≃ GeometricStar.Star hy w)
    (hmult : ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
      (signedMult (lab w pair hValid incomingFD q).presentation).num.natAbs) :
    RegrowthWallInput.StarParityAt hy w := by
  refine StarParityFromBalance.even_card_starClass_odd_of_equiv e ?_
  have h := StarParityFromBalance.even_sum_num_natAbs_of_sum_eq_zero _
    (integral_signedMult w pair hValid incomingFD)
    (sum_signedMult_eq_zero w pair hValid incomingFD)
  simpa only [hmult] using h

/-- **Stage 2 is the whole content of the clause at a wall**: from exhaustion, the star
clause. -/
theorem starParityAt_of_exhaustion (hExh : Exhausts w hy pair hValid incomingFD) :
    RegrowthWallInput.StarParityAt hy w := by
  obtain ⟨e, hmult⟩ := census_of_exhaustion w hy pair hValid incomingFD hExh
  exact starParityAt_of_census w hy pair hValid incomingFD e hmult

end Assembly

/-! ## 5b.  Stage 2 reduced to decoupled transports

The valency-free placement data of `W3Nd2StarCensusProof` (`PlacementSpec`,
`memberResolution`, `memberNorm`), imported rather than restated: the member carries its
own placement, and both W2R1 positions are wall-anchored, so the transport is along the
member's limit isomorphism itself. -/

section Transport

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (pair : Pair w.limit star) (hValid : w.limit.Valid)
  {incoming : Fin 2}
  (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum (Fin p))

/-- **What a member must present to be received at position `q`**: a decoupled
transport, along its limit isomorphism, from its own normal form at some placement onto
the position's pasted resolution. -/
abbrev PositionTransport (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : PlacementSpec other placement) (q : Fin 2) : Type :=
  ResolutionExpansionFree.TransportFree
    (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm) (mergeVertex other) (mergeVertex w)
    placement (pair.candidate q).right (memberResolution other placement hPlacement)
    (M11StarCensusProof.pasted (pair.candidate q))

/-- **Stage 2 reduced to transports**: if every star member presents a decoupled
transport onto one of the two positions, from its own normal form at some placement, the
star is exhausted by the positions. -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w,
      ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
      ∃ hPlacement : PlacementSpec member.member placement,
      ∃ q : Fin 2, Nonempty (PositionTransport w hy pair member.member ψ placement
        hPlacement q)) :
    Exhausts w hy pair hValid incomingFD := by
  intro member
  obtain ⟨ψ, placement, hPlacement, q, ⟨t⟩⟩ := h member
  refine ⟨q, ?_⟩
  have hNV := M11WallExhaustion.sourceVertexMap_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  have hNE := M11WallExhaustion.retainedSourceEdge_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
    (E := W2R1GraphData.equivalence pair hValid q)
    (fd := fdAt w pair hValid incomingFD q)
    (hRetained := W2R1RowDescent.matrix_retained pair hValid q)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
    (hOld := M11StarCensusProof.candidate_old _)
    (hEdge := M11StarCensusProof.candidate_edge _)
    (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans
      (branchSquare pair hValid q v))
    (M11StarCensusProof.refl_rowSquare w _ _ (fun _ ↦ rfl))
    (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _ (pair.candidate q).exterior) rfl
    member ψ (memberNorm member.member placement hPlacement) hNV hNE t

end Transport

/-! ## 6.  The family clause -/

section Family

/-- **The W2R1 star census** (the `w2R1` analogue of `M11StarParityFree.M11StarCensus`):
at every `w2R1` regrowth, for every Equation (10) presentation, the two positions are the
star, class by class, with their multiplicities. -/
def W2R1StarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2R1 →
    ∀ (star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W2SourceInput w.limit star) (pair : Pair w.limit star)
      (incoming : Fin 2)
      (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum (Fin p)),
      ∃ e : Fin 2 ≃ GeometricStar.Star hy w,
        ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
          (signedMult (lab w pair input.valid incomingFD q).presentation).num.natAbs

/-- **Stage 2 (exhaustion), family-wide**: at every `w2R1` regrowth, for every Equation (10)
presentation, every star member is in the class of one of the two positions.
*Interface*: equivalent to `W2R1StarCensus` (`w2R1StarExhaustion_iff`). -/
def W2R1StarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2R1 →
    ∀ (star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W2SourceInput w.limit star) (pair : Pair w.limit star)
      (incoming : Fin 2)
      (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum (Fin p)),
      Exhausts w hy pair input.valid incomingFD

variable {degree n p : ℕ}

theorem w2R1StarCensus_of_exhaustion (hExh : W2R1StarExhaustion degree n p) :
    W2R1StarCensus degree n p :=
  fun core y hy w cls htag star input pair incoming incomingFD ↦
    census_of_exhaustion w hy pair input.valid incomingFD
      (hExh core y hy w cls htag star input pair incoming incomingFD)

theorem exhaustion_of_w2R1StarCensus (hCensus : W2R1StarCensus degree n p) :
    W2R1StarExhaustion degree n p :=
  fun core y hy w cls htag star input pair incoming incomingFD ↦
    exhaustion_of_census w hy pair input.valid incomingFD
      (hCensus core y hy w cls htag star input pair incoming incomingFD).choose

/-- **Interface**: exhaustion is equivalent to the census. -/
theorem w2R1StarExhaustion_iff :
    W2R1StarExhaustion degree n p ↔ W2R1StarCensus degree n p :=
  ⟨w2R1StarCensus_of_exhaustion, exhaustion_of_w2R1StarCensus⟩

/-- **The incoming presentation of Equation (10) at a `w2R1` regrowth**: the regrowth's
own cover, matched by Part I (`W2R1GraphTracking.exists_matched_tracking`). -/
theorem exists_incoming {core : Core n p} {y : Fin p → ℚ} (w : Regrowth core y degree)
    (hy : Nondegenerate y) {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
    (pair : Pair w.limit star) :
    ∃ (incoming : Fin 2), Nonempty (FullDimensionalSourcePresentation
      (pair.candidate incoming).datum (Fin p)) := by
  obtain ⟨incoming, fd, -, -, -, -, -⟩ :=
    W2R1GraphTracking.exists_matched_tracking w.frame.data
      (InteriorProgress.hc_column w.frame.fullDim w.column)
      (InteriorProgress.hab_column w.frame.fullDim w.column)
      (InteriorProgress.hOne_column w.frame.fullDim w.column) w.frame.fullDim
      (InheritedLimitRows.forest w hy) star pair
      (InteriorGraphTracking.Tracks.self w.frame.fullDim)
  exact ⟨incoming, ⟨fd⟩⟩

/-- **`FamilyStarParity … .w2R1` from the W2R1 star census**: Equation (10) read mod two
through the census. -/
theorem familyStarParity_w2R1_of_census (h : W2R1StarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w2R1 := by
  intro core y hy w cls htag
  obtain ⟨star, input, pair, -⟩ := RegrowthWallInput.exists_w2R1_balance w cls htag
  obtain ⟨incoming, ⟨fd⟩⟩ := exists_incoming w hy pair
  obtain ⟨e, hmult⟩ := h core y hy w cls htag star input pair incoming fd
  exact starParityAt_of_census w hy pair input.valid fd e hmult

/-- **The `w2R1` clause of `FamilyStarParity` at genus six and degree four**, modulo
Stage 2's exhaustion alone. -/
theorem familyStarParity_w2R1_of_exhaustion
    (hExh : W2R1StarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2R1 :=
  familyStarParity_w2R1_of_census (w2R1StarCensus_of_exhaustion hExh)

end Family

end DraismaVargas.Count.W2R1StarCensusProof
