module

public import DraismaVargasCount.M11StarCensusProof
public import DraismaVargas.LocalCases.W3Nd3GraphTracking

@[expose] public section

/-!
# The W3Nd3 star census, Stages 1 and 3

Sources: Draisma–Vargas Part I, Case `{w3-r1-nd3-t3}`, Figure 30 and Equation (4) (where
the text and Figure 30 of Part I differ we follow the figure); Vargas, Part II, the star of
a codimension-one wall and the balancing condition `prop-signed-mult`.  The census
machinery is `DraismaVargasCount.StarCensusEngine`, with
`DraismaVargasCount.M11StarCensusProof` as the worked instance of the same pattern.  This
file concerns the star of a W3Nd3 wall: that its two positions are distinct classes with
the multiplicities of Equation (4) (Stages 1 and 3), and the reduction of its exhaustion by
them (Stage 2) to transports.

## The result, in one paragraph

`RegrowthWallInput.FamilyStarParity (2+2) (4*2+2) (6*2+3) .w3Nd3CoarseFine` is reduced to
the single statement `W3Nd3StarExhaustion` (`familyStarParity_w3Nd3_of_exhaustion`), which
is *equivalent* to the census `W3Nd3StarCensus` (`w3Nd3StarExhaustion_iff`) and to the
count "every such star has exactly two classes" (`w3Nd3StarExhaustion_iff_cardTwo`).
Stages (a) and (c) are proved at every core, degree and positive request with **no
hypothesis at all** -- not even a no-loop condition, which M-11 needed.  On the way,
**both positions of Equation (4) are always nonsingular** (`nonsingular`), so every
`w3Nd3CoarseFine` star has at least two classes, of equal multiplicity
(`two_le_card_star_of_tag`, `multNat_rep`, `absMult_lab_eq`).

## What is proved

* **Stage 1 (a).**  `coarse_branchSquare`, `fine_branchSquare` (the anchor branch squares,
  read off the three-case branch maps `W3Nd3LimitMatrix.coarse/fineBranchVertexMap`);
  `member0` (Figure 30's coarse member `M⁽¹⁾`) and `member1` (the fine member `M⁽²⁾`) as
  members of the wall's star, both **wall-anchored** (`φ = refl`) since both Figure 30
  members live over the wall's own limit; `rep` at every nonsingular position of the
  regrowth's own Equation (4) presentation (`lab`, via
  `W3Nd3ArbitraryExit.outgoingLabelling`), with `multNat_rep` its term's `|num|`.
* **Nonsingularity.**  `nonsingular_incoming` (the incoming position carries the
  incoming presentation's labelling), `absMult_lab_eq` (the unit-weight balance
  `sum_signedMult_lab` makes the two terms equal in absolute value), hence `nonsingular`:
  **every** position is nonsingular, `nonsingularEquiv`.
* **Stage 3 (c).**  `not_rel_01`: the two positions are never frame isomorphic.  The end
  valencies of the regrown occurrence cannot separate them (both members split the
  trivalent wall `1 + 2`, `W3Nd3UnitBalance.leafCount_coarse`,
  `W3Nd3UnitBalance.leafCount_fine`), so the regrown
  column is used: a frame isomorphism between positions preserves it row by inherited row
  (`StarCensusEngine.frameIso_matrix_new`), while the crossed column identity
  `W3Nd3CommonBalance.new_columns_add_eq_old` says the two regrown columns add up to the
  old `t₃` and `t₄` columns.  Equal regrown columns would make the coarse regrown column
  the average of two of its retained columns, so its matrix would be singular,
  contradicting full dimensionality.  No distinctness of rows (loop walls included) is
  used.  `rep_eq_of_cls_eq`, `repCls_injective`, `two_le_card_star`.
* **Stage 2 reduced to transports.**  `pulledPlacement`, `PlacementSpec`,
  `PositionTransport`, `exhausts_of_transports`: if every star member presents a
  decoupled transport (`ResolutionExpansionFree.TransportFree`) from its own normal form
  (`M11WallExhaustion.datumIso`, which is valency-free, at the position's placement
  pulled back along the member's limit isomorphism) onto some position's pasted
  resolution, the star is exhausted.  `pinned` (merge pinning from equation (C) of the W3
  input) and `positionTransport_of` discharge the two free fields of that transport
  (`wall_map`, `side_map`), leaving exactly the resolution-classification fields.
* **Assembly.**  `exists_balance` (Equation (4) in the regrowth's own coordinates, the
  incoming member being the regrowth's own cover matched by Part I,
  `W3Nd3GraphTracking.exists_matched_tracking`); `Exhausts`, `census_of_exhaustion`,
  `exhaustion_of_census`, `exhausts_iff_card` (per wall); `W3Nd3StarCensus`,
  `familyStarParity_w3Nd3_of_census`, `W3Nd3StarExhaustion`,
  `w3Nd3StarCensus_of_exhaustion`, `exhaustion_of_w3Nd3StarCensus`,
  `w3Nd3StarExhaustion_iff`, `W3Nd3StarCardTwo`, `w3Nd3StarExhaustion_iff_cardTwo`,
  `familyStarParity_w3Nd3_of_exhaustion` (the headline of this file).

## What is NOT proved here

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w3Nd3CoarseFine` is not proved in this
  file.**  Its exact remaining input is `W3Nd3StarExhaustion` (Stage 2 (b)): every star
  member is a frame isomorph of one of the two positions.  *Interface*: equivalent to
  `W3Nd3StarCensus` (`w3Nd3StarExhaustion_iff`) and to `W3Nd3StarCardTwo`
  (`w3Nd3StarExhaustion_iff_cardTwo`: no third class).  It is proved in
  `DraismaVargasCount.W3Nd3StarExhaustionProof`
  (`W3Nd3StarExhaustionProof.w3Nd3StarExhaustion`,
  `W3Nd3StarExhaustionProof.familyStarParity_w3Nd3`).  No regrowth tagged
  `w3Nd3CoarseFine` is exhibited here.
* **What Stage 2 needs** (the hypothesis of `exhausts_of_transports`; here only
  `pinned`/`positionTransport_of` are supplied): for a star member `m` with limit
  isomorphism `ψ`, (i) `PlacementSpec`: `m`'s own expansion splits the three wall
  occurrences as the position's placement pulled back along `ψ` (up to exchanging
  endpoints) -- the trivalent placement census, which needs Part I's identification
  (`W3Nd3IncomingMatching.exists_member_normalization`) at `m`, hence a W3 input and an
  nd3 profile on `m.limit` transported along `ψ⁻¹`; (ii) the remaining `TransportFree`
  fields: the member's read-off resolution is the position's pasted resolution up to the
  three sheet relabellings, with the merged and endpoint compatibilities.  All of this is
  supplied in `DraismaVargasCount.W3Nd3StarExhaustionProof`.
* No new separation, balance or multiplicity input is assumed anywhere.

## Remarks

* Equation (4) has two positions, one of them incoming.  The incoming position is
  nonsingular (`nonsingular_incoming`), so by the unit-weight two-term balance **both**
  are (`nonsingular`), with equal absolute multiplicities; with the census the star is
  exactly two classes of equal multiplicity, whence even parity.
* The two positions are never isomorphic (`not_rel_01`, unconditional).  The M-11 valency
  invariant does not apply (both members split `1 + 2`); the regrown-column invariant
  does, through the crossed column identity and nonsingularity.

## Consumers

`DraismaVargasCount.W3Nd3StarExhaustionProof`, which proves `W3Nd3StarExhaustion` and so
the `w3Nd3CoarseFine` clause that `StarSupplyAssembly` uses for the trivalent wall step of
`DraismaVargasCount.Assembly`.
-/

namespace DraismaVargas.Count.W3Nd3StarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open ThirdEquation W3R1SourceProfile W3Nd3SourceCandidates W3Nd3LimitMatrix
open M11StarCensusProof (candidate_refines candidate_merge candidate_old candidate_edge
  wall_join refl_rowSquare refl_sourceVertexEquiv num_natAbs_eq_of_abs_eq pasted)

/-! ## 1.  The anchor branch squares of Figure 30's two members -/

section Local

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}

private theorem branchSquare_of_endpoint (c : BalancedGlobal.Candidate target degree data wall)
    (E : StableGraphIncidence.Equivalence data c.datum) (v : BranchVertex data)
    (place : Vertex target) (hE : (E.vertex v).1 = c.datum.sourceEndpoint place v.1.1.2)
    (hPlace : contractVertex target wall place = v.1.1.1) :
    data.sourceEndpoint (contractVertex target wall (E.vertex v).1.1.1) (E.vertex v).1.1.2 =
      v.1 := by
  rw [hE, StarCensusEngine.sourceEndpoint_contract _ data _ _ (candidate_refines c _), hPlace]
  exact data.sourceEndpoint_self v.1

variable {star : ThreeStar target wall} (input : W3SourceInput data star)
  (profile : Nd3Profile data input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)

/-- **The branch square of the coarse member.** -/
theorem coarse_branchSquare (v : BranchVertex data) :
    data.sourceEndpoint
        (contractVertex target wall
          ((coarseStableGraphEquivalence input profile hSame).vertex v).1.1.1)
        ((coarseStableGraphEquivalence input profile hSame).vertex v).1.1.2 = v.1 := by
  classical
  by_cases hAt : v.1.1.1 = wall
  · by_cases hSel : (data.vertexPartition wall).Rel input.distinguishedBlock.1 v.1.1.2
    · exact branchSquare_of_endpoint _ _ v (oldVertex target wall)
        (coarseBranchVertexMap_of_selected input profile hSame v hAt hSel) hAt.symm
    · exact branchSquare_of_endpoint _ _ v (freshVertex target)
        (coarseBranchVertexMap_of_background input profile hSame v hAt hSel) hAt.symm
  · exact branchSquare_of_endpoint _ _ v (oldVertex target v.1.1.1)
      (coarseBranchVertexMap_of_away input profile hSame v hAt) rfl

/-- **The branch square of the fine member.** -/
theorem fine_branchSquare (v : BranchVertex data) :
    data.sourceEndpoint
        (contractVertex target wall
          ((fineStableGraphEquivalence input profile hSame).vertex v).1.1.1)
        ((fineStableGraphEquivalence input profile hSame).vertex v).1.1.2 = v.1 := by
  classical
  by_cases hAt : v.1.1.1 = wall
  · by_cases hSel : (data.vertexPartition wall).Rel input.distinguishedBlock.1 v.1.1.2
    · exact branchSquare_of_endpoint _ _ v (oldVertex target wall)
        (fineBranchVertexMap_of_selected input profile hSame v hAt hSel) hAt.symm
    · exact branchSquare_of_endpoint _ _ v (freshVertex target)
        (fineBranchVertexMap_of_background input profile hSame v hAt hSel) hAt.symm
  · exact branchSquare_of_endpoint _ _ v (oldVertex target v.1.1.1)
      (fineBranchVertexMap_of_away input profile hSame v hAt) rfl

end Local

/-! ## 2.  The two positions of Equation (4) as members of the wall's star (Stage 1) -/

section Positions

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)

variable (fd0 : FullDimensionalSourcePresentation
  (coarseCandidate input profile hSame).datum (Fin p))

/-- **Position `0` (Figure 30's coarse member `M⁽¹⁾`) is a member of the wall's star**,
for any full-dimensional presentation of its datum. -/
noncomputable def member0 : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := coarseStableGraphEquivalence input profile hSame) (fd := fd0)
    (hRetained := coarse_matrix_retained input profile hSame)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := candidate_merge _ (wall_join w))
    (hOld := candidate_old _) (hEdge := candidate_edge _)
    (fun v ↦ (refl_sourceVertexEquiv w _).trans (coarse_branchSquare input profile hSame v))
    (refl_rowSquare w _ _ (fun _ ↦ rfl))

variable (fd1 : FullDimensionalSourcePresentation
  (fineCandidate input profile hSame).datum (Fin p))

/-- **Position `1` (Figure 30's fine member `M⁽²⁾`) is a member of the wall's star.** -/
noncomputable def member1 : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := fineStableGraphEquivalence input profile hSame) (fd := fd1)
    (hRetained := fine_matrix_retained input profile hSame)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := candidate_merge _ (wall_join w))
    (hOld := candidate_old _) (hEdge := candidate_edge _)
    (fun v ↦ (refl_sourceVertexEquiv w _).trans (fine_branchSquare input profile hSame v))
    (refl_rowSquare w _ _ (fun _ ↦ rfl))

end Positions

/-! ## 3.  Separation (Stage 3): the crossed column identity forbids a frame isomorphism -/

section Separation

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (fd0 : FullDimensionalSourcePresentation
    (coarseCandidate input profile hSame).datum (Fin p))
  (fd1 : FullDimensionalSourcePresentation
    (fineCandidate input profile hSame).datum (Fin p))

/-- The frame of position `0`. -/
noncomputable abbrev frame0 :=
  StarCensusEngine.frame w hy (coarseCandidate input profile hSame).datum
    (coarseStableGraphEquivalence input profile hSame) fd0

/-- The frame of position `1`. -/
noncomputable abbrev frame1 :=
  StarCensusEngine.frame w hy (fineCandidate input profile hSame).datum
    (fineStableGraphEquivalence input profile hSame) fd1

/-- An entry of a position labelling, read in the wall's coordinates. -/
private theorem labelling_matrix_apply {right : (w.frame.limitTarget w.column).edges → Bool}
    {D : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right) degree}
    (E : StableGraphIncidence.Equivalence w.limit D) (r c : Fin p) :
    GluingDatum.LengthMatrixPresentation.matrix
        (StarCensusEngine.labelling w hy D E).presentation r c =
      StableSourceMatrix.matrix D (E.row ((InheritedLimitRows.rowLabel w hy).symm r))
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right
          (W4StarParity.columnEquiv w c)) :=
  StableSourceMatrix.labelling_matrix_eq _ r c

/-- **The two positions of Equation (4) are distinct star classes**, at every wall. -/
theorem not_rel_01 :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frame0 w hy input profile hSame fd0)
      (frame1 w hy input profile hSame fd1)) := by
  classical
  rintro ⟨fi⟩
  have hdet := (frame0 w hy input profile hSame fd0).fullDim.det_ne_zero
  apply hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  have h3 : w.column ≠ (W4StarParity.columnEquiv w).symm (some profile.first.1.1.1) := by
    intro h
    have h' := congrArg (W4StarParity.columnEquiv w) h
    rw [W4StarParity.columnEquiv_wall, Equiv.apply_symm_apply] at h'
    cases h'
  have h4 : w.column ≠ (W4StarParity.columnEquiv w).symm (some (largestTarget input profile)) := by
    intro h
    have h' := congrArg (W4StarParity.columnEquiv w) h
    rw [W4StarParity.columnEquiv_wall, Equiv.apply_symm_apply] at h'
    cases h'
  refine ⟨Pi.single w.column 2 -
    Pi.single ((W4StarParity.columnEquiv w).symm (some profile.first.1.1.1)) 1 -
    Pi.single ((W4StarParity.columnEquiv w).symm (some (largestTarget input profile))) 1, ?_, ?_⟩
  · intro h
    have := congrFun h w.column
    simp [h3, h4] at this
  · funext r
    have hNew := StarCensusEngine.frameIso_matrix_new
      (E := coarseStableGraphEquivalence input profile hSame)
      (E' := fineStableGraphEquivalence input profile hSame)
      (coarse_matrix_retained input profile hSame)
      (fine_matrix_retained input profile hSame) fi ((InheritedLimitRows.rowLabel w hy).symm r)
    have hSum := W3Nd3CommonBalance.new_columns_add_eq_old input profile hSame
      ((InheritedLimitRows.rowLabel w hy).symm r)
    have e0 := labelling_matrix_apply w hy (coarseStableGraphEquivalence input profile hSame) r
      w.column
    have e3 := labelling_matrix_apply w hy (coarseStableGraphEquivalence input profile hSame) r
      ((W4StarParity.columnEquiv w).symm (some profile.first.1.1.1))
    have e4 := labelling_matrix_apply w hy (coarseStableGraphEquivalence input profile hSame) r
      ((W4StarParity.columnEquiv w).symm (some (largestTarget input profile)))
    rw [W4StarParity.columnEquiv_wall] at e0
    rw [Equiv.apply_symm_apply] at e3 e4
    set path := (InheritedLimitRows.rowLabel w hy).symm r
    set M := GluingDatum.LengthMatrixPresentation.matrix
      (StarCensusEngine.labelling w hy (coarseCandidate input profile hSame).datum
        (coarseStableGraphEquivalence input profile hSame)).presentation
    set a := StableSourceMatrix.matrix (coarseCandidate input profile hSame).datum
      (coarseStablePathEquiv input profile hSame path)
      (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
        (coarseCandidate input profile hSame).right none)
    set b := StableSourceMatrix.matrix (fineCandidate input profile hSame).datum
      (fineStablePathEquiv input profile hSame path)
      (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
        (fineCandidate input profile hSame).right none)
    have e0' : M r w.column = a := e0
    have e3' : M r ((W4StarParity.columnEquiv w).symm (some profile.first.1.1.1)) =
        StableSourceMatrix.matrix w.limit path profile.first.1.1.1 :=
      e3.trans (coarse_matrix_retained input profile hSame path _)
    have e4' : M r ((W4StarParity.columnEquiv w).symm (some (largestTarget input profile))) =
        StableSourceMatrix.matrix w.limit path (largestTarget input profile) :=
      e4.trans (coarse_matrix_retained input profile hSame path _)
    have hNew' : b = a := hNew
    change M.mulVec _ r = 0
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
      Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [e0', e3', e4']
    linarith

end Separation

/-! ## 4.  The nonsingular positions as star classes, and the census at one wall -/

section Census

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p))

/-- Equation (4)'s labelling at the position `q`, in the regrowth's own coordinates. -/
noncomputable abbrev lab (q : Fin 2) :=
  W3Nd3ArbitraryExit.outgoingLabelling input profile hSame incoming incomingFD q

/-- The nonsingular positions of Equation (4). -/
def Nonsingular (q : Fin 2) : Prop :=
  (GluingDatum.LengthMatrixPresentation.matrix
    (lab input profile hSame incoming incomingFD q).presentation).det ≠ 0

/-- **Equation (4) in the regrowth's own coordinates.** -/
theorem sum_signedMult_lab :
    ∑ q : Fin 2, signedMult (lab input profile hSame incoming incomingFD q).presentation = 0 :=
  W3Nd3UnitBalance.sum_signedMult_eq_zero input profile hSame
    (W3Nd3ArbitraryExit.initialLabelling input profile hSame incoming incomingFD)

/-- The incoming position of Equation (4) is nonsingular: it carries the incoming
presentation's own labelling (`W3Nd3ArbitraryExit.outgoingLabelling_self`). -/
theorem nonsingular_incoming : Nonsingular input profile hSame incoming incomingFD incoming :=
  W3Nd3ArbitraryExit.incomingDet_ne_zero input profile hSame incoming incomingFD

/-- The two terms of Equation (4) have equal absolute value. -/
theorem absMult_lab_eq (q q' : Fin 2) :
    absMult (lab input profile hSame incoming incomingFD q).presentation =
      absMult (lab input profile hSame incoming incomingFD q').presentation := by
  have hbal := sum_signedMult_lab input profile hSame incoming incomingFD
  rw [Fin.sum_univ_two] at hbal
  have h1 : signedMult (lab input profile hSame incoming incomingFD 1).presentation =
      -signedMult (lab input profile hSame incoming incomingFD 0).presentation := by
    linarith
  have h01 : absMult (lab input profile hSame incoming incomingFD 0).presentation =
      absMult (lab input profile hSame incoming incomingFD 1).presentation := by
    unfold absMult
    rw [h1, abs_neg]
  fin_cases q <;> fin_cases q'
  · rfl
  · exact h01
  · exact h01.symm
  · rfl

/-- **Both positions of Equation (4) are nonsingular**, at every presentation: the
incoming one carries a full-dimensional presentation, and the unit-weight balance gives
the other the same absolute multiplicity. -/
theorem nonsingular (q : Fin 2) : Nonsingular input profile hSame incoming incomingFD q := by
  unfold Nonsingular
  rw [← W4StarParity.absMult_ne_zero_iff, absMult_lab_eq input profile hSame incoming incomingFD q
    incoming, W4StarParity.absMult_ne_zero_iff]
  exact nonsingular_incoming input profile hSame incoming incomingFD

variable (w)

/-- The full-dimensional presentation of a nonsingular position. -/
noncomputable def fdAt (q : Fin 2) (hq : Nonsingular input profile hSame incoming incomingFD q) :
    FullDimensionalSourcePresentation (W3Nd3CommonBalance.candidates input profile hSame q).datum
      (Fin p) :=
  W3Nd3ArbitraryExit.outgoingPresentation input profile hSame
    (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w) incoming q
    incomingFD hq

/-- **Every term of Equation (4) is an integer.** -/
theorem integral_signedMult (q : Fin 2) :
    ∃ value : ℤ, signedMult (lab input profile hSame incoming incomingFD q).presentation =
      (value : ℚ) := by
  by_cases hq : Nonsingular input profile hSame incoming incomingFD q
  · exact isIntegralMultiplicity (fdAt w input profile hSame incoming incomingFD q hq)
  · refine ⟨0, ?_⟩
    unfold Nonsingular at hq
    rw [not_not] at hq
    unfold signedMult
    rw [hq, mul_zero, Int.cast_zero]

/-- A singular position contributes `0`. -/
theorem signedMult_eq_zero (q : Fin 2) (hq : ¬ Nonsingular input profile hSame incoming incomingFD q) :
    signedMult (lab input profile hSame incoming incomingFD q).presentation = 0 := by
  unfold Nonsingular at hq
  rw [not_not] at hq
  unfold signedMult
  rw [hq, mul_zero]

/-- **The star member of a nonsingular position of Equation (4).** -/
noncomputable def rep : (q : Fin 2) →
    Nonsingular input profile hSame incoming incomingFD q → GeometricStar.StarMember hy w
  | ⟨0, h0⟩, hq => member0 w hy input profile hSame
      (fdAt w input profile hSame incoming incomingFD ⟨0, h0⟩ hq)
  | ⟨1, h1⟩, hq => member1 w hy input profile hSame
      (fdAt w input profile hSame incoming incomingFD ⟨1, h1⟩ hq)

/-- **The multiplicity of a position's star class is its term of Equation (4)**, up to
sign. -/
theorem multNat_rep (q : Fin 2) (hq : Nonsingular input profile hSame incoming incomingFD q) :
    (GeometricStar.Star.toFibre (rep w hy input profile hSame incoming incomingFD q hq).cls).multNat =
      (signedMult (lab input profile hSame incoming incomingFD q).presentation).num.natAbs := by
  match q, hq with
  | ⟨0, _⟩, _ => exact num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)
  | ⟨1, _⟩, _ => exact num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)

/-- **Distinct nonsingular positions are distinct star classes** (Stage 3). -/
theorem rep_eq_of_cls_eq :
    ∀ (q : Fin 2) (hq : Nonsingular input profile hSame incoming incomingFD q)
      (q' : Fin 2) (hq' : Nonsingular input profile hSame incoming incomingFD q'),
      (rep w hy input profile hSame incoming incomingFD q hq).cls =
        (rep w hy input profile hSame incoming incomingFD q' hq').cls → q = q'
  | ⟨0, _⟩, _, ⟨0, _⟩, _, _ => rfl
  | ⟨1, _⟩, _, ⟨1, _⟩, _, _ => rfl
  | ⟨0, h0⟩, hq, ⟨1, h1⟩, hq', h =>
    (not_rel_01 w hy input profile hSame (fdAt w input profile hSame incoming incomingFD ⟨0, h0⟩ hq)
      (fdAt w input profile hSame incoming incomingFD ⟨1, h1⟩ hq') (Quotient.exact h)).elim
  | ⟨1, h1⟩, hq, ⟨0, h0⟩, hq', h =>
    (not_rel_01 w hy input profile hSame (fdAt w input profile hSame incoming incomingFD ⟨0, h0⟩ hq')
      (fdAt w input profile hSame incoming incomingFD ⟨1, h1⟩ hq)
      ((Quotient.exact h).elim fun fi ↦ ⟨fi.symm⟩)).elim

/-- The positions' classes, as a map from the nonsingular positions to the star. -/
noncomputable def repCls
    (q : {q : Fin 2 // Nonsingular input profile hSame incoming incomingFD q}) :
    GeometricStar.Star hy w :=
  (rep w hy input profile hSame incoming incomingFD q.1 q.2).cls

theorem repCls_injective : Function.Injective (repCls w hy input profile hSame incoming incomingFD) :=
  fun a b h ↦ Subtype.ext (rep_eq_of_cls_eq w hy input profile hSame incoming incomingFD a.1 a.2
    b.1 b.2 h)

/-- **Exhaustion at one wall** (Stage 2): every member of the star is in the
class of some nonsingular position.  *Interface*: equivalent to the census at this wall
(`census_of_exhaustion`, `exhaustion_of_census`) and to the star having exactly two
classes (`exhausts_iff_card`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ q : Fin 2,
    ∃ hq : Nonsingular input profile hSame incoming incomingFD q,
      member.cls = (rep w hy input profile hSame incoming incomingFD q hq).cls

/-- **The W3Nd3 census at one wall from exhaustion.** -/
theorem census_of_exhaustion (hExh : Exhausts w hy input profile hSame incoming incomingFD) :
    ∃ e : {q : Fin 2 // Nonsingular input profile hSame incoming incomingFD q} ≃
        GeometricStar.Star hy w,
      ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
        (signedMult (lab input profile hSame incoming incomingFD q.1).presentation).num.natAbs := by
  refine ⟨Equiv.ofBijective _ ⟨repCls_injective w hy input profile hSame incoming incomingFD, ?_⟩,
    fun q ↦ multNat_rep w hy input profile hSame incoming incomingFD q.1 q.2⟩
  refine Quotient.ind ?_
  intro member
  obtain ⟨q, hq, h⟩ := hExh member
  exact ⟨⟨q, hq⟩, h.symm⟩

/-- **Interface: the census implies exhaustion.** -/
theorem exhaustion_of_census
    (e : {q : Fin 2 // Nonsingular input profile hSame incoming incomingFD q} ≃
      GeometricStar.Star hy w) :
    Exhausts w hy input profile hSame incoming incomingFD := by
  classical
  have hBij : Function.Bijective (repCls w hy input profile hSame incoming incomingFD) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨repCls_injective w hy input profile hSame incoming incomingFD, Fintype.card_congr e⟩
  intro member
  obtain ⟨q, hq⟩ := hBij.2 member.cls
  exact ⟨q.1, q.2, hq.symm⟩

/-- The nonsingular positions are all of `Fin 2`. -/
noncomputable def nonsingularEquiv :
    {q : Fin 2 // Nonsingular input profile hSame incoming incomingFD q} ≃ Fin 2 :=
  Equiv.subtypeUnivEquiv (nonsingular input profile hSame incoming incomingFD)

/-- **The census at one wall is "the star has exactly two classes".**  Stages 1 and 3
already give two distinct classes; exhaustion is equivalent to there being no third. -/
theorem exhausts_iff_card :
    Exhausts w hy input profile hSame incoming incomingFD ↔
      Fintype.card (GeometricStar.Star hy w) = 2 := by
  classical
  constructor
  · intro hExh
    obtain ⟨e, -⟩ := census_of_exhaustion w hy input profile hSame incoming incomingFD hExh
    rw [← Fintype.card_congr e, Fintype.card_congr
      (nonsingularEquiv w input profile hSame incoming incomingFD), Fintype.card_fin]
  · intro hCard
    refine exhaustion_of_census w hy input profile hSame incoming incomingFD
      (Fintype.equivOfCardEq ?_)
    rw [Fintype.card_congr (nonsingularEquiv w input profile hSame incoming incomingFD),
      Fintype.card_fin, hCard]

include input profile hSame incomingFD in
/-- **Stages 1 and 3 give at least two classes**, unconditionally. -/
theorem two_le_card_star : 2 ≤ Fintype.card (GeometricStar.Star hy w) := by
  classical
  have h := Fintype.card_le_of_injective _
    (repCls_injective w hy input profile hSame incoming incomingFD)
  rwa [Fintype.card_congr (nonsingularEquiv w input profile hSame incoming incomingFD),
    Fintype.card_fin] at h

end Census


/-! ## 5.  Stage 2 reduced to decoupled transports onto the two wall-anchored positions -/

section Transport

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (hSame : profile.first.1.1.1 = profile.second.1.1.1)
  (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p))

/-- The placement a member is normalized onto for position `q`: the position's own
placement, pulled back along the member's limit isomorphism. -/
noncomputable def pulledPlacement (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) (q : Fin 2) :
    (other.frame.limitTarget other.column).edges → Bool :=
  fun edge ↦ (W3Nd3CommonBalance.members input profile hSame q).right
    ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetEdge edge)

/-- The member's own expansion agrees with a placement on the wall occurrences, up to
exchanging the two expanded endpoints. -/
def PlacementSpec (other : Regrowth core y degree)
    (second : (other.frame.limitTarget other.column).edges → Bool) : Prop :=
  (∀ edge ∈ GluingDatum.incidentEdges (mergeVertex other),
    IncomingTargetExpansion.right (contracted := other.frame.edgeOf other.column) rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) edge = second edge) ∨
  (∀ edge ∈ GluingDatum.incidentEdges (mergeVertex other),
    IncomingTargetExpansion.right (contracted := other.frame.edgeOf other.column) rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) edge = !(second edge))

/-- **What a member must present to be received at position `q`.** -/
def PositionTransport (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (q : Fin 2) : Type :=
  Σ' hP : PlacementSpec other (pulledPlacement w hy input profile hSame other ψ q),
    ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm) (mergeVertex other) (mergeVertex w)
      (pulledPlacement w hy input profile hSame other ψ q)
      (W3Nd3CommonBalance.members input profile hSame q).right
      (M11WallExhaustion.incomingResolution other.frame.data rfl
        (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
        (pulledPlacement w hy input profile hSame other ψ q) hP)
      (pasted (W3Nd3CommonBalance.members input profile hSame q))

include input in
/-- Merge pinning at a trivalent wall, from equation (C) of its W3 input. -/
theorem pinned : M11WallExhaustion.Pinned hy w :=
  M11WallExhaustion.pinned_of_targetExcess_eq_one input.equation_c

/-- **The position transport with its two free fields discharged**: the wall is matched by merge
pinning (`pinned`), and the side assignments agree by construction of
`pulledPlacement`.  What remains is the classification content of a transport: the
member's read-off local resolution is the position's up to the three sheet
relabellings. -/
def positionTransport_of (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (q : Fin 2) (hP : PlacementSpec other (pulledPlacement w hy input profile hSame other ψ q))
    (oldPerm freshPerm newPerm : Equiv.Perm (Fin degree))
    (old_merged : ∀ sheet : Fin degree,
      (other.limit.vertexPartition (mergeVertex other)).Rel
        (((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).vertexPerm
          (mergeVertex other)).symm (oldPerm sheet)) sheet)
    (fresh_merged : ∀ sheet : Fin degree,
      (other.limit.vertexPartition (mergeVertex other)).Rel
        (((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).vertexPerm
          (mergeVertex other)).symm (freshPerm sheet)) sheet)
    (left_relabel : (pasted (W3Nd3CommonBalance.members input profile hSame q)).left =
      (M11WallExhaustion.incomingResolution other.frame.data rfl
        (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
        (pulledPlacement w hy input profile hSame other ψ q) hP).left.relabel oldPerm)
    (right_relabel : (pasted (W3Nd3CommonBalance.members input profile hSame q)).right =
      (M11WallExhaustion.incomingResolution other.frame.data rfl
        (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
        (pulledPlacement w hy input profile hSame other ψ q) hP).right.relabel freshPerm)
    (newEdge_relabel : (pasted (W3Nd3CommonBalance.members input profile hSame q)).newEdge =
      (M11WallExhaustion.incomingResolution other.frame.data rfl
        (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
        (pulledPlacement w hy input profile hSame other ψ q) hP).newEdge.relabel newPerm)
    (newEdge_old : ∀ sheet : Fin degree,
      (M11WallExhaustion.incomingResolution other.frame.data rfl
        (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
        (pulledPlacement w hy input profile hSame other ψ q) hP).left.Rel
        (oldPerm.symm (newPerm sheet)) sheet)
    (newEdge_fresh : ∀ sheet : Fin degree,
      (M11WallExhaustion.incomingResolution other.frame.data rfl
        (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
        (pulledPlacement w hy input profile hSame other ψ q) hP).right.Rel
        (freshPerm.symm (newPerm sheet)) sheet)
    (endpoint_compatible : ∀ edge : (other.frame.limitTarget other.column).edges,
      ((edge : (other.frame.limitTarget other.column).V ×
          (other.frame.limitTarget other.column).V).1 = mergeVertex other ∨
        (edge : (other.frame.limitTarget other.column).V ×
          (other.frame.limitTarget other.column).V).2 = mergeVertex other) →
      ∀ sheet : Fin degree,
        (if pulledPlacement w hy input profile hSame other ψ q edge then
            (M11WallExhaustion.incomingResolution other.frame.data rfl
              (fst_ne_snd (other.frame.edgeOf other.column))
              (other.frame.numEdges_edgeOf other.column)
              (pulledPlacement w hy input profile hSame other ψ q) hP).right
          else (M11WallExhaustion.incomingResolution other.frame.data rfl
              (fst_ne_snd (other.frame.edgeOf other.column))
              (other.frame.numEdges_edgeOf other.column)
              (pulledPlacement w hy input profile hSame other ψ q) hP).left).Rel
          ((if pulledPlacement w hy input profile hSame other ψ q edge then freshPerm
            else oldPerm).symm
            ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm edge sheet)) sheet) :
    PositionTransport w hy input profile hSame other ψ q :=
  ⟨hP,
    { oldPerm := oldPerm
      freshPerm := freshPerm
      newPerm := newPerm
      wall_map := pinned w hy input other ψ
      side_map := fun _ ↦ rfl
      old_merged := old_merged
      fresh_merged := fresh_merged
      left_relabel := left_relabel
      right_relabel := right_relabel
      newEdge_relabel := newEdge_relabel
      newEdge_old := newEdge_old
      newEdge_fresh := newEdge_fresh
      endpoint_compatible := endpoint_compatible }⟩

/-- **Stage 2 reduced to transports**: if every star member presents a decoupled
transport onto some nonsingular position, the star is exhausted by the positions. -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w, ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ q : Fin 2, ∃ _ : Nonsingular input profile hSame incoming incomingFD q,
        Nonempty (PositionTransport w hy input profile hSame member.member ψ q)) :
    Exhausts w hy input profile hSame incoming incomingFD := by
  intro member
  obtain ⟨ψ, q, hq, ⟨⟨hP, t⟩⟩⟩ := h member
  refine ⟨q, hq, ?_⟩
  match q, hq, hP, t with
  | ⟨0, h0⟩, hq, hP, t =>
    exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
      (E := coarseStableGraphEquivalence input profile hSame)
      (fd := fdAt w input profile hSame incoming incomingFD ⟨0, h0⟩ hq)
      (hRetained := coarse_matrix_retained input profile hSame)
      (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
      (hMerge := candidate_merge _ (wall_join w)) (hOld := candidate_old _)
      (hEdge := candidate_edge _)
      (fun v ↦ (refl_sourceVertexEquiv w _).trans (coarse_branchSquare input profile hSame v))
      (refl_rowSquare w _ _ (fun _ ↦ rfl))
      (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (coarseCandidate input profile hSame).exterior) rfl member ψ
      (M11WallExhaustion.datumIso member.member.frame.data rfl
        (fst_ne_snd (member.member.frame.edgeOf member.member.column))
        (member.member.frame.numEdges_edgeOf member.member.column) _ hP
        member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus)
      (M11WallExhaustion.sourceVertexMap_datumIso member.member.frame.data rfl
        (fst_ne_snd (member.member.frame.edgeOf member.member.column))
        (member.member.frame.numEdges_edgeOf member.member.column) _ hP
        member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus)
      (M11WallExhaustion.retainedSourceEdge_datumIso member.member.frame.data rfl
        (fst_ne_snd (member.member.frame.edgeOf member.member.column))
        (member.member.frame.numEdges_edgeOf member.member.column) _ hP
        member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus) t
  | ⟨1, h1⟩, hq, hP, t =>
    exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
      (E := fineStableGraphEquivalence input profile hSame)
      (fd := fdAt w input profile hSame incoming incomingFD ⟨1, h1⟩ hq)
      (hRetained := fine_matrix_retained input profile hSame)
      (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
      (hMerge := candidate_merge _ (wall_join w)) (hOld := candidate_old _)
      (hEdge := candidate_edge _)
      (fun v ↦ (refl_sourceVertexEquiv w _).trans (fine_branchSquare input profile hSame v))
      (refl_rowSquare w _ _ (fun _ ↦ rfl))
      (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (fineCandidate input profile hSame).exterior) rfl member ψ
      (M11WallExhaustion.datumIso member.member.frame.data rfl
        (fst_ne_snd (member.member.frame.edgeOf member.member.column))
        (member.member.frame.numEdges_edgeOf member.member.column) _ hP
        member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus)
      (M11WallExhaustion.sourceVertexMap_datumIso member.member.frame.data rfl
        (fst_ne_snd (member.member.frame.edgeOf member.member.column))
        (member.member.frame.numEdges_edgeOf member.member.column) _ hP
        member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus)
      (M11WallExhaustion.retainedSourceEdge_datumIso member.member.frame.data rfl
        (fst_ne_snd (member.member.frame.edgeOf member.member.column))
        (member.member.frame.numEdges_edgeOf member.member.column) _ hP
        member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus) t

end Transport

/-! ## 6.  The family clause -/

section Family

open ClassifiedContinuation (SourceCase)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Equation (4) at every regrowth tagged `w3Nd3CoarseFine`, in the regrowth's own
coordinates**, with the incoming member the regrowth's own cover matched by Part I. -/
theorem exists_balance (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w3Nd3CoarseFine) :
    ∃ (star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W3SourceInput w.limit star)
      (profile : Nd3Profile w.limit input.distinguishedBlock)
      (hSame : profile.first.1.1.1 = profile.second.1.1.1)
      (incoming : Fin 2)
      (incomingFD : FullDimensionalSourcePresentation
        (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p)),
      ∑ q : Fin 2, signedMult (lab input profile hSame incoming incomingFD q).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w3 star input profile =>
    cases profile with
    | nd3CoarseFine profile hSame _ _ =>
      have hForest := InheritedLimitRows.forest w hy
      have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data
        (InteriorProgress.hc_column w.frame.fullDim w.column)
        (InteriorProgress.hab_column w.frame.fullDim w.column)
        (InteriorProgress.hOne_column w.frame.fullDim w.column) hForest
      obtain ⟨incoming, fd, -, -, -⟩ :=
        W3Nd3GraphTracking.exists_matched_tracking w.frame.data
          (InteriorProgress.hc_column w.frame.fullDim w.column)
          (InteriorProgress.hab_column w.frame.fullDim w.column)
          (InteriorProgress.hOne_column w.frame.fullDim w.column) w.frame.fullDim hForest hCompat
          star input profile hSame (InteriorGraphTracking.Tracks.self w.frame.fullDim)
      exact ⟨star, input, profile, hSame, incoming, fd,
        sum_signedMult_lab input profile hSame incoming fd⟩
    | four => cases htag
    | shift => cases htag
    | nd2CoarseFine => cases htag
  | w2 _ _ profile => cases profile <;> cases htag

/-- **The W3Nd3 star census.**  At every regrowth tagged `w3Nd3CoarseFine`, for every
presentation of its Equation (4) family, the star is in bijection with the family's
nonsingular positions (all of `Fin 2`, by `nonsingular`), each class carrying its
position's multiplicity.  *Interface*: equivalent to `W3Nd3StarExhaustion`. -/
def W3Nd3StarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Nd3CoarseFine →
    ∀ (star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W3SourceInput w.limit star)
      (profile : Nd3Profile w.limit input.distinguishedBlock)
      (hSame : profile.first.1.1.1 = profile.second.1.1.1)
      (incoming : Fin 2)
      (incomingFD : FullDimensionalSourcePresentation
        (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p)),
      ∃ e : {q : Fin 2 // Nonsingular input profile hSame incoming incomingFD q} ≃
          GeometricStar.Star hy w,
        ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
          (signedMult (lab input profile hSame incoming incomingFD q.1).presentation).num.natAbs

/-- **`FamilyStarParity … .w3Nd3CoarseFine` from the census**: Equation (4) at the
regrowth (`exists_balance`, with no further hypothesis) read mod two through the engine. -/
theorem familyStarParity_w3Nd3_of_census (h : W3Nd3StarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w3Nd3CoarseFine := by
  intro core y hy w cls htag
  obtain ⟨star, input, profile, hSame, incoming, fd, hbal⟩ := exists_balance w hy cls htag
  obtain ⟨e, hmult⟩ := h core y hy w cls htag star input profile hSame incoming fd
  exact StarCensusEngine.starParityAt_of_census
    (fun q ↦ signedMult (lab input profile hSame incoming fd q).presentation)
    (integral_signedMult w input profile hSame incoming fd) hbal
    (Nonsingular input profile hSame incoming fd)
    (signedMult_eq_zero w input profile hSame incoming fd) e hmult

/-- **Stage 2 (exhaustion), family-wide**: at every `w3Nd3CoarseFine` regrowth, for every
Equation (4) presentation, every star member is in the class of a position.
*Interface*: equivalent to `W3Nd3StarCensus` (`w3Nd3StarExhaustion_iff`) and to
`W3Nd3StarCardTwo` (`w3Nd3StarExhaustion_iff_cardTwo`). -/
def W3Nd3StarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Nd3CoarseFine →
    ∀ (star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W3SourceInput w.limit star)
      (profile : Nd3Profile w.limit input.distinguishedBlock)
      (hSame : profile.first.1.1.1 = profile.second.1.1.1)
      (incoming : Fin 2)
      (incomingFD : FullDimensionalSourcePresentation
        (W3Nd3CommonBalance.candidates input profile hSame incoming).datum (Fin p)),
      Exhausts w hy input profile hSame incoming incomingFD

/-- **The W3Nd3 star census from exhaustion.** -/
theorem w3Nd3StarCensus_of_exhaustion (hExh : W3Nd3StarExhaustion degree n p) :
    W3Nd3StarCensus degree n p :=
  fun core y hy w cls htag star input profile hSame incoming incomingFD ↦
    census_of_exhaustion w hy input profile hSame incoming incomingFD
      (hExh core y hy w cls htag star input profile hSame incoming incomingFD)

/-- **Interface**: the census implies exhaustion. -/
theorem exhaustion_of_w3Nd3StarCensus (hCensus : W3Nd3StarCensus degree n p) :
    W3Nd3StarExhaustion degree n p :=
  fun core y hy w cls htag star input profile hSame incoming incomingFD ↦
    exhaustion_of_census w hy input profile hSame incoming incomingFD
      (hCensus core y hy w cls htag star input profile hSame incoming incomingFD).choose

theorem w3Nd3StarExhaustion_iff :
    W3Nd3StarExhaustion degree n p ↔ W3Nd3StarCensus degree n p :=
  ⟨w3Nd3StarCensus_of_exhaustion, exhaustion_of_w3Nd3StarCensus⟩

/-- **Exhaustion, as a count**: every star at a `w3Nd3CoarseFine` regrowth has exactly
two classes.  *Interface*: equivalent to `W3Nd3StarExhaustion`
(`w3Nd3StarExhaustion_iff_cardTwo`). -/
def W3Nd3StarCardTwo (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Nd3CoarseFine → Fintype.card (GeometricStar.Star hy w) = 2

theorem w3Nd3StarExhaustion_iff_cardTwo :
    W3Nd3StarExhaustion degree n p ↔ W3Nd3StarCardTwo degree n p := by
  constructor
  · intro hExh core y hy w cls htag
    obtain ⟨star, input, profile, hSame, incoming, fd, -⟩ := exists_balance w hy cls htag
    exact (exhausts_iff_card w hy input profile hSame incoming fd).mp
      (hExh core y hy w cls htag star input profile hSame incoming fd)
  · intro hCard core y hy w cls htag star input profile hSame incoming incomingFD
    exact (exhausts_iff_card w hy input profile hSame incoming incomingFD).mpr
      (hCard core y hy w cls htag)

/-- **At least two classes at every `w3Nd3CoarseFine` regrowth**, with no hypothesis. -/
theorem two_le_card_star_of_tag (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w3Nd3CoarseFine) :
    2 ≤ Fintype.card (GeometricStar.Star hy w) := by
  obtain ⟨star, input, profile, hSame, incoming, fd, -⟩ := exists_balance w hy cls htag
  exact two_le_card_star w hy input profile hSame incoming fd

/-- **The headline**: the `w3Nd3CoarseFine` clause of `FamilyStarParity` at genus
six and degree four, modulo Stage 2's exhaustion alone. -/
theorem familyStarParity_w3Nd3_of_exhaustion
    (hExh : W3Nd3StarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Nd3CoarseFine :=
  familyStarParity_w3Nd3_of_census (w3Nd3StarCensus_of_exhaustion hExh)

end Family

end DraismaVargas.Count.W3Nd3StarCensusProof
