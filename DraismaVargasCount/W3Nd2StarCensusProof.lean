module

public import DraismaVargasCount.M11StarCensusProof
public import DraismaVargasCount.W3Nd2UnitBalance
public import DraismaVargas.LocalCases.W3Nd2GraphTracking

@[expose] public section

/-!
# The W3 nd2 star census, Stages 1 and 3, and Stage 2 reduced to transports

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w3-r1-nd2}`, Figure 31 and
Equation (5); Vargas, Part II (arXiv:2609.09109): the star of a wall and
`prop-signed-mult`.  Engine: `StarCensusEngine`; worked example: `M11StarCensusProof`.
This is the W3 nd2 case of the star parity in step 2 of `Assembly`.  The census splits
into (a) every nonsingular position is a star class (Stage 1), (b) every star class is a
position (Stage 2), and (c) distinct positions are distinct classes (Stage 3).

## The result, in one paragraph

`RegrowthWallInput.FamilyStarParity (2+2) (4*2+2) (6*2+3) .w3Nd2CoarseFine` is reduced to
the single residue `W3Nd2StarExhaustion` (Stage 2 (b): every star member is a frame
isomorph of one of Figure 31's two positions), which is *equivalent* to the census
`W3Nd2StarCensus` (`w3Nd2StarExhaustion_iff`).  **(a) and (c) are proved at every core,
degree, positive request and Equation (5) presentation, with no hypothesis.**  Two facts
make the family simpler than M-11: both positions are always nonsingular (Equation (5)
has two terms of opposite determinant and the incoming one is nonsingular), and the two
positions are always distinct classes, by an argument that needs no computation of the
regrown columns -- a frame isomorphism would make them equal, and then Equation (5)
`det A₀ + det A₁ = 0` would force `det A₀ = 0`.

## What is proved

* **Stage 1 (a).**  `coarse_branchSquare`, `fine_branchSquare` (generic datum);
  `member0`, `member1`: Figure 31's two positions as members of the wall's star, both
  wall-anchored (`M = w.limit`, `φ = refl`), for *any* full-dimensional presentation.
  `nonsingular`: both positions are nonsingular in the incoming presentation's labelling.
  `fdAt`, `rep`, `multNat_rep` (class multiplicity = `|num (signedMult (lab q))|`),
  `integral_signedMult`, `sum_signedMult_eq_zero` (Equation (5) in that labelling).
* **Stage 3 (c).**  `squareMatrix_eq_of_new_eq`, `det_eq_zero_of_new_eq` (generic datum),
  `squareMatrix_det_ne_zero`, `not_rel_01` (unconditional), `rep_eq_of_cls_eq`,
  `repCls_injective`: uniqueness and multiplicity in case (5).
* **Stage 2 reduced to transports, at any valency.**  `PlacementSpec`,
  `placementSpec_self`, `memberResolution`, `memberNorm`, `PositionTransport`,
  `exhausts_of_transports`: if every star member presents a
  `ResolutionExpansionFree.TransportFree` from its own normal form
  (`M11WallExhaustion.datumIso` at a placement of its choice) onto a position's pasted
  resolution, the star is exhausted.  Unlike `M11StarCensusProof.exhausts_of_transports`
  the placement is carried in the receipt, so nothing divalent enters.
* **No coherence dichotomy.**  `nd2Profile_eq` (and the `Subsingleton` instance): an
  `Nd2Profile` is determined by its datum and block.
* **Assembly.**  `Exhausts`, `repCls_surjective`, `census_of_exhaustion`,
  `exhaustion_of_census`, `starParityAt_of_census`, `starParityAt_of_exhaustion` (per
  wall); `W3Nd2StarCensus`, `W3Nd2StarExhaustion`, `w3Nd2StarCensus_of_exhaustion`,
  `exhaustion_of_w3Nd2StarCensus`, `w3Nd2StarExhaustion_iff`, `exists_incoming`,
  `familyStarParity_w3Nd2_of_census`, and `familyStarParity_w3Nd2_of_exhaustion`.

## What is NOT proved here (every hypothesis, explicitly)

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w3Nd2CoarseFine` is not proved here.**  Its
  exact residue is `W3Nd2StarExhaustion`.  *Interface*: equivalent to `W3Nd2StarCensus`
  (`w3Nd2StarExhaustion_iff`), so neither weaker nor stronger than the census.  It is
  proved in `W3Nd2StarExhaustionProof`.
* **No inhabitant of the antecedent is exhibited**: no concrete `w3Nd2CoarseFine`
  regrowth, `W3SourceInput` or `Nd2Profile` is constructed here.  Computer experiments
  with genus-six W3 nd2 walls are consistent with the census: every such wall seen has
  two labelled classes, one on each side, of multiplicity `1`.  Stages 1 and 3 hold at
  every wall, so a failure of the census would have to be a third star class.
* **What Stage 2 needs** (the hypothesis of `exhausts_of_transports`, not proved here):
  for each star member `m` with limit isomorphism `ψ`, a placement and a
  `ResolutionExpansionFree.TransportFree` along `ψ` onto the coarse or fine pasted
  resolution.  Its `endpoint_compatible` field is endpoint sheet rigidity, which does
  not follow from the isomorphism's data alone; the other fields need (i) the wall's
  `W3SourceInput` and `Nd2Profile` transported to `m.limit` along `ψ⁻¹`, and (ii) Part
  I's identification `W3Nd2IncomingMemberMatching.exists_member_normalization` at `m`,
  read through (i).
* Nothing here depends on genus six or degree four except the instantiation of the
  family clause.

## Tempting inferences, checked

* (i) *"The star is exactly the nonsingular positions; both have equal absolute
  multiplicity."*  **Holds, and more**: both positions are *always* nonsingular
  (`nonsingular`), so the census index is `Fin 2` itself, and equal absolute
  multiplicity is Equation (5).  Star parity then needs exactly exhaustion plus (c).
* (ii) *"Whether the two positions can be isomorphic is the (c) question."*  **Settled:
  never** (`not_rel_01`, unconditional).  The end valencies do not separate them (both
  split the trivalent wall `1 + 2`); the regrown column does, via Equation (5) rather
  than by computing it.
* (iii) *"(b) needs the same two pieces as for M-11: profile transport along a general
  limit isomorphism, and a coherence dichotomy."*  **Half holds.**  Profile transport
  is needed (Part I's identification is stated against the member's own input and
  profile).  The coherence dichotomy has **no W3 nd2 analogue**: both positions are
  wall-anchored, there is no remote position, and the profile is unique
  (`nd2Profile_eq`), so the member's own coarse position is not re-anchored by any
  branch swap.  What remains instead is endpoint sheet rigidity
  (`endpoint_compatible`), as for every non-joined resolution.  The residue is stated in
  the shape of `exhausts_of_transports`.

## Shared patterns

* `PlacementSpec`, `memberResolution`, `memberNorm` and the proof pattern of
  `exhausts_of_transports` are valency-free and family-free; `W3Nd3StarCensusProof` uses
  the same pattern.
* `M11StarCensusProof.candidate_*`, `wall_join`, `refl_rowSquare`,
  `refl_sourceVertexEquiv`, `pasted`, `num_natAbs_eq_of_abs_eq` are generic in the
  candidate; this file imports the M-11 proof only for them.
* `det_eq_zero_of_new_eq` is a two-member pattern: any two-term unit-weight balance whose
  members agree off the wall column separates its two positions the same way (W3Nd3,
  W2R1).

## Consumers

`W3Nd2StarExhaustionProof`, and through it the `w3Nd2CoarseFine` clause of the star
parity (step 2 of `Assembly`).
-/

namespace DraismaVargas.Count.W3Nd2StarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open ThirdEquation W3R1SourceProfile W3Nd2SourceCandidates W3Nd2FineCandidates

/-! ## 1.  Figure 31's two members over an arbitrary datum: the branch squares -/

section Local

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : ThreeStar target wall} (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)

/-- **The branch square of the coarse member** (Figure 31, position `0`). -/
theorem coarse_branchSquare (v : BranchVertex data) :
    data.sourceEndpoint
        (contractVertex target wall
          ((W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile).vertex v).1.1.1)
        ((W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile).vertex v).1.1.2 =
      v.1 := by
  have hRef := M11StarCensusProof.candidate_refines (coarseCandidate input profile)
  rw [W3Nd2CoarseStableGraph.coarseStableGraphEquivalence_vertex_apply]
  by_cases hAt : v.1.1.1 = wall
  · rw [W3Nd2CoarseStableGraph.coarseBranchVertexMap_of_wall input profile v hAt,
      StarCensusEngine.sourceEndpoint_contract _ data _ _ (hRef _)]
    have hSelf := data.sourceEndpoint_self v.1
    rw [hAt] at hSelf
    exact hSelf
  · rw [W3Nd2CoarseStableGraph.coarseBranchVertexMap_of_away input profile v hAt]
    change data.sourceEndpoint (contractVertex target wall
        ((coarseCandidate input profile).datum.sourceEndpoint
          (oldVertex target v.1.1.1) v.1.1.2).1.1)
        ((coarseCandidate input profile).datum.sourceEndpoint
          (oldVertex target v.1.1.1) v.1.1.2).1.2 = v.1
    rw [StarCensusEngine.sourceEndpoint_contract _ data _ _ (hRef _)]
    exact data.sourceEndpoint_self v.1

/-- **The branch square of the fine member** (Figure 31, position `1`). -/
theorem fine_branchSquare (v : BranchVertex data) :
    data.sourceEndpoint
        (contractVertex target wall
          ((W3Nd2FineStableGraph.fineStableGraphEquivalence input profile).vertex v).1.1.1)
        ((W3Nd2FineStableGraph.fineStableGraphEquivalence input profile).vertex v).1.1.2 =
      v.1 := by
  have hRef := M11StarCensusProof.candidate_refines (fineCandidate input profile)
  rw [W3Nd2FineStableGraph.fineStableGraphEquivalence_vertex_apply]
  by_cases hAt : v.1.1.1 = wall
  · rw [W3Nd2FineStableGraph.fineBranchVertexMap_of_wall input profile v hAt,
      StarCensusEngine.sourceEndpoint_contract _ data _ _ (hRef _)]
    have hSelf := data.sourceEndpoint_self v.1
    rw [hAt] at hSelf
    exact hSelf
  · rw [W3Nd2FineStableGraph.fineBranchVertexMap_of_away input profile v hAt]
    change data.sourceEndpoint (contractVertex target wall
        ((fineCandidate input profile).datum.sourceEndpoint
          (oldVertex target v.1.1.1) v.1.1.2).1.1)
        ((fineCandidate input profile).datum.sourceEndpoint
          (oldVertex target v.1.1.1) v.1.1.2).1.2 = v.1
    rw [StarCensusEngine.sourceEndpoint_contract _ data _ _ (hRef _)]
    exact data.sourceEndpoint_self v.1

end Local

/-! ## 2.  The two positions of Equation (5) as members of the wall's star (Stage 1) -/

section Positions

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)

variable (fd0 : FullDimensionalSourcePresentation (coarseCandidate input profile).datum (Fin p))

/-- **Position `0` (Figure 31's coarse member) is a member of the wall's star**, for any
full-dimensional presentation of its datum.  Wall-anchored. -/
noncomputable def member0 : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile) (fd := fd0)
    (hRetained := W3Nd2CoarseLimitMatrix.matrix_retained input profile)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
    (hOld := M11StarCensusProof.candidate_old _) (hEdge := M11StarCensusProof.candidate_edge _)
    (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans
      (coarse_branchSquare input profile v))
    (M11StarCensusProof.refl_rowSquare w _ _ (fun _ ↦ rfl))

variable (fd1 : FullDimensionalSourcePresentation (fineCandidate input profile).datum (Fin p))

/-- **Position `1` (Figure 31's fine member) is a member of the wall's star.**
Wall-anchored. -/
noncomputable def member1 : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := W3Nd2FineStableGraph.fineStableGraphEquivalence input profile) (fd := fd1)
    (hRetained := W3Nd2FineLimitMatrix.matrix_retained input profile)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
    (hOld := M11StarCensusProof.candidate_old _) (hEdge := M11StarCensusProof.candidate_edge _)
    (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans
      (fine_branchSquare input profile v))
    (M11StarCensusProof.refl_rowSquare w _ _ (fun _ ↦ rfl))

end Positions

/-! ## 3.  Both positions are nonsingular, and are star classes -/

/-- In a two-term vanishing sum, one nonzero term makes the other nonzero. -/
theorem ne_zero_of_add_eq_zero {A : Fin 2 → ℚ} (h : A 0 + A 1 = 0) {i : Fin 2} (hi : A i ≠ 0)
    (j : Fin 2) : A j ≠ 0 := by
  intro hj
  apply hi
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] at hj ⊢ <;> linarith

section Census

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)
  {incoming : Fin 2}
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p))

/-- Equation (5)'s labelling of position `q`, induced from the incoming presentation. -/
noncomputable abbrev lab (q : Fin 2) :=
  W3Nd2PositiveExit.outgoingLabelling input profile incoming incomingFD q

/-- **Both positions of Equation (5) are nonsingular**: the incoming one is
(`W3Nd2PositiveExit.incomingDet_ne_zero`), and the two determinants are negatives of each
other (`W3Nd2CommonBalance.determinant_balance`). -/
theorem nonsingular (q : Fin 2) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (lab w input profile incomingFD q).presentation).det ≠ 0 :=
  ne_zero_of_add_eq_zero (A := fun q ↦ (W3Nd2CommonBalance.squareMatrix input profile
      (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD) q).det)
    (W3Nd2CommonBalance.determinant_balance input profile _)
    (W3Nd2PositiveExit.incomingDet_ne_zero input profile incoming incomingFD) q

/-- The full-dimensional presentation of a position, transported from the incoming one
along the family's stable-graph equivalence. -/
noncomputable def fdAt (q : Fin 2) :
    FullDimensionalSourcePresentation (W3Nd2CommonBalance.candidates input profile q).datum
      (Fin p) :=
  W3Nd2PositiveExit.outgoingPresentation input profile
    (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w) incoming q
    incomingFD (nonsingular w input profile incomingFD q)

/-- **The star member of a position of Equation (5).** -/
noncomputable def rep : Fin 2 → GeometricStar.StarMember hy w
  | ⟨0, h0⟩ => member0 w hy input profile (fdAt w input profile incomingFD ⟨0, h0⟩)
  | ⟨1, h1⟩ => member1 w hy input profile (fdAt w input profile incomingFD ⟨1, h1⟩)

/-- **The multiplicity of a position's star class is its term of Equation (5)**, up to
sign. -/
theorem multNat_rep (q : Fin 2) :
    (GeometricStar.Star.toFibre (rep w hy input profile incomingFD q).cls).multNat =
      (signedMult (lab w input profile incomingFD q).presentation).num.natAbs := by
  match q with
  | ⟨0, _⟩ => exact M11StarCensusProof.num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)
  | ⟨1, _⟩ => exact M11StarCensusProof.num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)

/-- **Every term of Equation (5) is an integer.** -/
theorem integral_signedMult (q : Fin 2) :
    ∃ value : ℤ, signedMult (lab w input profile incomingFD q).presentation = (value : ℚ) :=
  isIntegralMultiplicity (fdAt w input profile incomingFD q)

/-- **Equation (5) in the incoming presentation's labelling.** -/
theorem sum_signedMult_eq_zero :
    ∑ q : Fin 2, signedMult (lab w input profile incomingFD q).presentation = 0 :=
  W3Nd2UnitBalance.sum_signedMult_eq_zero input profile
    (W3Nd2PositiveExit.initialLabelling input profile incoming incomingFD)

end Census

/-! ## 4.  Separation between the two positions (Stage 3)

The engine's separation invariants are the regrown column (`frameIso_matrix_new`) and the
valencies of its ends (`frameIso_valencies`).  The valencies do not separate here: both
members split the trivalent wall `1 + 2` (`W3Nd2UnitBalance.leafCount_coarse`,
`leafCount_fine`).  The regrown column does, and for a reason that needs no computation:
if the two regrown columns agreed on every inherited row, the two square matrices of
Equation (5) would coincide in every common labelling, so Equation (5),
`det A₀ + det A₁ = 0`, would force `det A₀ = 0`, contradicting full dimensionality. -/

section Generic

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : ThreeStar target wall} (input : W3SourceInput data star)
  (profile : Nd2Profile data input.distinguishedBlock)

/-- Equal regrown columns give equal square matrices, in every common labelling. -/
theorem squareMatrix_eq_of_new_eq
    (hNew : ∀ path : StablePath data, W3Nd2CommonBalance.commonMatrix input profile 1 path none =
      W3Nd2CommonBalance.commonMatrix input profile 0 path none)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate) :
    W3Nd2CommonBalance.squareMatrix input profile initial 0 =
      W3Nd2CommonBalance.squareMatrix input profile initial 1 := by
  funext row column
  rw [W3Nd2CommonBalance.squareMatrix_common, W3Nd2CommonBalance.squareMatrix_common]
  cases W3Nd2CommonBalance.targetCoordinates input profile initial column with
  | none => exact (hNew _).symm
  | some place =>
    rw [W3Nd2CommonBalance.commonMatrix_retained, W3Nd2CommonBalance.commonMatrix_retained]

/-- …hence, by Equation (5), a singular first member. -/
theorem det_eq_zero_of_new_eq
    (hNew : ∀ path : StablePath data, W3Nd2CommonBalance.commonMatrix input profile 1 path none =
      W3Nd2CommonBalance.commonMatrix input profile 0 path none)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : StableLengthMatrixLabelling
      (W3Nd2CommonBalance.candidates input profile 0).datum coordinate) :
    (W3Nd2CommonBalance.squareMatrix input profile initial 0).det = 0 := by
  have h := W3Nd2CommonBalance.determinant_balance input profile initial
  rw [← squareMatrix_eq_of_new_eq input profile hNew initial] at h
  linarith

end Generic

section Separation

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)
  (fd0 : FullDimensionalSourcePresentation (coarseCandidate input profile).datum (Fin p))
  (fd1 : FullDimensionalSourcePresentation (fineCandidate input profile).datum (Fin p))

/-- The frame of position `0`. -/
noncomputable abbrev frame0 :=
  StarCensusEngine.frame w hy (coarseCandidate input profile).datum
    (W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile) fd0

/-- The frame of position `1`. -/
noncomputable abbrev frame1 :=
  StarCensusEngine.frame w hy (fineCandidate input profile).datum
    (W3Nd2FineStableGraph.fineStableGraphEquivalence input profile) fd1

/-- A full-dimensional coarse member is nonsingular in every common labelling of
Equation (5): multiplicity does not depend on the labelling. -/
theorem squareMatrix_det_ne_zero :
    (W3Nd2CommonBalance.squareMatrix input profile fd0.labelling 0).det ≠ 0 := by
  have h := absMult_labelling_indep
    (W3Nd2CommonBalance.labelling input profile fd0.labelling 0) fd0.labelling
  have hfd := (W4StarParity.absMult_ne_zero_iff fd0.labelling.presentation).mpr fd0.det_ne_zero
  exact (W4StarParity.absMult_ne_zero_iff _).mp (h ▸ hfd)

/-- **The coarse and fine positions are distinct star classes**, at every wall: a frame
isomorphism would equate their regrown columns (`StarCensusEngine.frameIso_matrix_new`),
and equal regrown columns make Equation (5) singular. -/
theorem not_rel_01 :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frame0 w hy input profile fd0)
      (frame1 w hy input profile fd1)) := by
  rintro ⟨fi⟩
  have hNew : ∀ path : StablePath w.limit,
      W3Nd2CommonBalance.commonMatrix input profile 1 path none =
        W3Nd2CommonBalance.commonMatrix input profile 0 path none := fun path ↦
    StarCensusEngine.frameIso_matrix_new
      (E := W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile)
      (E' := W3Nd2FineStableGraph.fineStableGraphEquivalence input profile)
      (W3Nd2CoarseLimitMatrix.matrix_retained input profile)
      (W3Nd2FineLimitMatrix.matrix_retained input profile) fi path
  exact squareMatrix_det_ne_zero w input profile fd0
    (det_eq_zero_of_new_eq input profile hNew fd0.labelling)

end Separation

/-! ## 5.  The census from exhaustion (Stage 2 residue) -/

section Assembly

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)
  {incoming : Fin 2}
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p))

/-- **The two positions are distinct star classes** (Stage 3), at every wall. -/
theorem rep_eq_of_cls_eq : ∀ q q' : Fin 2,
    (rep w hy input profile incomingFD q).cls = (rep w hy input profile incomingFD q').cls →
      q = q'
  | ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | ⟨1, _⟩, ⟨1, _⟩, _ => rfl
  | ⟨0, h0⟩, ⟨1, h1⟩, h =>
    (not_rel_01 w hy input profile (fdAt w input profile incomingFD ⟨0, h0⟩)
      (fdAt w input profile incomingFD ⟨1, h1⟩) (Quotient.exact h)).elim
  | ⟨1, h1⟩, ⟨0, h0⟩, h =>
    (not_rel_01 w hy input profile (fdAt w input profile incomingFD ⟨0, h0⟩)
      (fdAt w input profile incomingFD ⟨1, h1⟩)
      ((Quotient.exact h).elim fun fi ↦ ⟨fi.symm⟩)).elim

/-- The positions' classes, as a map to the star. -/
noncomputable def repCls (q : Fin 2) : GeometricStar.Star hy w :=
  (rep w hy input profile incomingFD q).cls

theorem repCls_injective : Function.Injective (repCls w hy input profile incomingFD) :=
  fun a b h ↦ rep_eq_of_cls_eq w hy input profile incomingFD a b h

/-- **The exhaustion residue at one wall** (Stage 2): every member of the star is in the
class of one of the two positions.  *Interface*: with Stages 1 and 3 it is equivalent to
the census at this wall (`census_of_exhaustion`, `exhaustion_of_census`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ q : Fin 2,
    member.cls = (rep w hy input profile incomingFD q).cls

theorem repCls_surjective (hExh : Exhausts w hy input profile incomingFD) :
    Function.Surjective (repCls w hy input profile incomingFD) := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨q, h⟩ := hExh member
  exact ⟨q, h.symm⟩

/-- **The W3 nd2 census at one wall from exhaustion.** -/
theorem census_of_exhaustion (hExh : Exhausts w hy input profile incomingFD) :
    ∃ e : Fin 2 ≃ GeometricStar.Star hy w,
      ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
        (signedMult (lab w input profile incomingFD q).presentation).num.natAbs :=
  ⟨Equiv.ofBijective _ ⟨repCls_injective w hy input profile incomingFD,
      repCls_surjective w hy input profile incomingFD hExh⟩,
    fun q ↦ multNat_rep w hy input profile incomingFD q⟩

/-- **Interface: the census implies exhaustion.**  An injective map between
finite sets of equal cardinality is onto. -/
theorem exhaustion_of_census (e : Fin 2 ≃ GeometricStar.Star hy w) :
    Exhausts w hy input profile incomingFD := by
  classical
  have hBij : Function.Bijective (repCls w hy input profile incomingFD) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨repCls_injective w hy input profile incomingFD, Fintype.card_congr e⟩
  intro member
  obtain ⟨q, hq⟩ := hBij.2 member.cls
  exact ⟨q, hq.symm⟩

/-- **The star clause from Equation (5) and the census.** -/
theorem starParityAt_of_census (e : Fin 2 ≃ GeometricStar.Star hy w)
    (hmult : ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
      (signedMult (lab w input profile incomingFD q).presentation).num.natAbs) :
    RegrowthWallInput.StarParityAt hy w := by
  refine StarParityFromBalance.even_card_starClass_odd_of_equiv e ?_
  have h := StarParityFromBalance.even_sum_num_natAbs_of_sum_eq_zero _
    (integral_signedMult w input profile incomingFD)
    (sum_signedMult_eq_zero w input profile incomingFD)
  simpa only [hmult] using h

/-- **Stage 2 is the whole content of the clause at a wall**: from exhaustion, the star
clause. -/
theorem starParityAt_of_exhaustion (hExh : Exhausts w hy input profile incomingFD) :
    RegrowthWallInput.StarParityAt hy w := by
  obtain ⟨e, hmult⟩ := census_of_exhaustion w hy input profile incomingFD hExh
  exact starParityAt_of_census w hy input profile incomingFD e hmult

end Assembly

/-! ## 5b.  Stage 2 reduced to decoupled transports, at any valency

`M11StarCensusProof.exhausts_of_transports` normalizes a member through the *divalent*
placement census (`M11WallExhaustion.memberPlacement`).  The normalization itself
(`M11WallExhaustion.datumIso`, with its dictionaries `sourceVertexMap_datumIso` and
`retainedSourceEdge_datumIso`) takes **any** placement agreeing with the member's own
incoming side assignment up to the global endpoint swap (`PlacementSpec`), at any
valency; the member's own side assignment is always one (`placementSpec_self`).  So the
reduction below carries the placement as part of the receipt and applies verbatim at a
trivalent wall.  Both W3 nd2 positions are wall-anchored, so the transport is along the
member's limit isomorphism itself (composed with `refl.symm`, as the engine states it). -/

section Transport

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **A member placement**: a side assignment on the member's limit target agreeing with
the member's own incoming side assignment up to the global endpoint swap.  This is exactly
the hypothesis of `M11WallExhaustion.datumIso`; no valency enters. -/
def PlacementSpec (other : Regrowth core y degree)
    (placement : (other.frame.limitTarget other.column).edges → Bool) : Prop :=
  (∀ edge ∈ GluingDatum.incidentEdges (mergeVertex other),
    IncomingTargetExpansion.right (contracted := other.frame.edgeOf other.column) rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) edge = placement edge) ∨
  (∀ edge ∈ GluingDatum.incidentEdges (mergeVertex other),
    IncomingTargetExpansion.right (contracted := other.frame.edgeOf other.column) rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) edge = !(placement edge))

/-- Every member has a placement: its own incoming side assignment. -/
theorem placementSpec_self (other : Regrowth core y degree) :
    PlacementSpec other (IncomingTargetExpansion.right (contracted := other.frame.edgeOf other.column)
      rfl (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column)) :=
  Or.inl fun _ _ ↦ rfl

/-- The local resolution a member presents at a placement, read off its own endpoint
partitions. -/
noncomputable abbrev memberResolution (other : Regrowth core y degree)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : PlacementSpec other placement) : ResolutionM11.LocalResolution degree :=
  M11WallExhaustion.incomingResolution other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    placement hPlacement

/-- **The member's normal form**: its frame datum is the resolution expansion of its own
limit at the placement. -/
noncomputable abbrev memberNorm (other : Regrowth core y degree)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : PlacementSpec other placement) :=
  M11WallExhaustion.datumIso other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    placement hPlacement other.frame.fullDim.targetConnected other.frame.fullDim.targetGenus

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd2Profile w.limit input.distinguishedBlock)
  {incoming : Fin 2}
  (incomingFD : FullDimensionalSourcePresentation
    (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p))

/-- **The receipt a member must present to be received at position `q`**: a decoupled
transport, along its limit isomorphism, from its own normal form at some placement onto
the position's pasted resolution. -/
def PositionTransport (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : PlacementSpec other placement) : Fin 2 → Type
  | ⟨0, _⟩ => ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm) (mergeVertex other) (mergeVertex w)
      placement (coarseCandidate input profile).right
      (memberResolution other placement hPlacement)
      (M11StarCensusProof.pasted (coarseCandidate input profile))
  | ⟨1, _⟩ => ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm) (mergeVertex other) (mergeVertex w)
      placement (fineCandidate input profile).right
      (memberResolution other placement hPlacement)
      (M11StarCensusProof.pasted (fineCandidate input profile))

/-- **Stage 2 reduced to transports**: if every star member presents a decoupled
transport onto one of the two positions, from its own normal form at some placement, the
star is exhausted by the positions. -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w,
      ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
      ∃ hPlacement : PlacementSpec member.member placement,
      ∃ q : Fin 2, Nonempty (PositionTransport w hy input profile member.member ψ placement
        hPlacement q)) :
    Exhausts w hy input profile incomingFD := by
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
  match q, t with
  | ⟨0, h0⟩, t =>
    exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
      (E := W3Nd2CoarseStableGraph.coarseStableGraphEquivalence input profile)
      (fd := fdAt w input profile incomingFD ⟨0, h0⟩)
      (hRetained := W3Nd2CoarseLimitMatrix.matrix_retained input profile)
      (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
      (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
      (hOld := M11StarCensusProof.candidate_old _)
      (hEdge := M11StarCensusProof.candidate_edge _)
      (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans
        (coarse_branchSquare input profile v))
      (M11StarCensusProof.refl_rowSquare w _ _ (fun _ ↦ rfl))
      (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (coarseCandidate input profile).exterior) rfl member ψ
      (memberNorm member.member placement hPlacement) hNV hNE t
  | ⟨1, h1⟩, t =>
    exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
      (E := W3Nd2FineStableGraph.fineStableGraphEquivalence input profile)
      (fd := fdAt w input profile incomingFD ⟨1, h1⟩)
      (hRetained := W3Nd2FineLimitMatrix.matrix_retained input profile)
      (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
      (hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w))
      (hOld := M11StarCensusProof.candidate_old _)
      (hEdge := M11StarCensusProof.candidate_edge _)
      (fun v ↦ (M11StarCensusProof.refl_sourceVertexEquiv w _).trans
        (fine_branchSquare input profile v))
      (M11StarCensusProof.refl_rowSquare w _ _ (fun _ ↦ rfl))
      (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (fineCandidate input profile).exterior) rfl member ψ
      (memberNorm member.member placement hPlacement) hNV hNE t

end Transport

/-! ## 5c.  No coherence dichotomy: the Figure 31 profile is canonical

At M-11 a member's own position `0` is the wall's position `0` or `1` according to the
coherence of its limit isomorphism, because Figure 32 has two split positions exchanged
by a branch swap.  Figure 31 has no such pair: both positions are wall-anchored, they are
always distinct classes (`not_rel_01`), and the profile they are built from is determined
by the datum and the distinguished block -- the two surviving occurrences are told apart
by their indices `k - 1` and `k`. -/

/-- **An `Nd2Profile` is unique**: its two survivors are the block's only survivors, and
`small` has index one less than `large`. -/
theorem nd2Profile_eq {target : CFGraph} {degree : ℕ} {wall : target.V}
    {data : GluingDatum target degree} {block : W4Assembly.WallBlock data wall}
    (P Q : Nd2Profile data block) : P = Q := by
  have hPs : P.small ∈ survivors data block := by rw [P.surviving]; simp
  have hPl : P.large ∈ survivors data block := by rw [P.surviving]; simp
  rw [Q.surviving] at hPs hPl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hPs hPl
  have hS : P.small = Q.small := by
    rcases hPs with h | h
    · exact h
    · have h1 := P.small_index
      have h2 := Q.large_index
      rw [h] at h1
      omega
  have hL : P.large = Q.large := by
    rcases hPl with h | h
    · have h1 := P.large_index
      have h2 := Q.small_index
      rw [h] at h1
      omega
    · exact h
  cases P
  cases Q
  cases hS
  cases hL
  rfl

instance {target : CFGraph} {degree : ℕ} {wall : target.V}
    {data : GluingDatum target degree} {block : W4Assembly.WallBlock data wall} :
    Subsingleton (Nd2Profile data block) :=
  ⟨nd2Profile_eq⟩

/-! ## 6.  The family clause -/

section Family

/-- **The W3 nd2 star census** (the `w3Nd2CoarseFine` analogue of
`M11StarParityFree.M11StarCensus`): at every `w3Nd2CoarseFine` regrowth, for every
Equation (5) presentation, the two positions are the star, class by class, with their
multiplicities. -/
def W3Nd2StarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Nd2CoarseFine →
    ∀ (star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W3SourceInput w.limit star)
      (profile : Nd2Profile w.limit input.distinguishedBlock)
      (incoming : Fin 2)
      (incomingFD : FullDimensionalSourcePresentation
        (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p)),
      ∃ e : Fin 2 ≃ GeometricStar.Star hy w,
        ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
          (signedMult (lab w input profile incomingFD q).presentation).num.natAbs

/-- **Stage 2's residue, family-wide**: at every `w3Nd2CoarseFine` regrowth, for every
Equation (5) presentation, every star member is in the class of one of the two
positions.  *Interface*: equivalent to `W3Nd2StarCensus` (`w3Nd2StarExhaustion_iff`). -/
def W3Nd2StarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Nd2CoarseFine →
    ∀ (star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W3SourceInput w.limit star)
      (profile : Nd2Profile w.limit input.distinguishedBlock)
      (incoming : Fin 2)
      (incomingFD : FullDimensionalSourcePresentation
        (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p)),
      Exhausts w hy input profile incomingFD

variable {degree n p : ℕ}

theorem w3Nd2StarCensus_of_exhaustion (hExh : W3Nd2StarExhaustion degree n p) :
    W3Nd2StarCensus degree n p :=
  fun core y hy w cls htag star input profile incoming incomingFD ↦
    census_of_exhaustion w hy input profile incomingFD
      (hExh core y hy w cls htag star input profile incoming incomingFD)

theorem exhaustion_of_w3Nd2StarCensus (hCensus : W3Nd2StarCensus degree n p) :
    W3Nd2StarExhaustion degree n p :=
  fun core y hy w cls htag star input profile incoming incomingFD ↦
    exhaustion_of_census w hy input profile incomingFD
      (hCensus core y hy w cls htag star input profile incoming incomingFD).choose

/-- **Interface**: exhaustion is equivalent to the census. -/
theorem w3Nd2StarExhaustion_iff :
    W3Nd2StarExhaustion degree n p ↔ W3Nd2StarCensus degree n p :=
  ⟨w3Nd2StarCensus_of_exhaustion, exhaustion_of_w3Nd2StarCensus⟩

/-- **The incoming presentation of Equation (5) at a `w3Nd2CoarseFine` regrowth**: the
regrowth's own cover, matched by Part I (`W3Nd2GraphTracking.exists_matched_tracking`). -/
theorem exists_incoming {core : Core n p} {y : Fin p → ℚ} (w : Regrowth core y degree)
    (hy : Nondegenerate y)
    {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
    (input : W3SourceInput w.limit star)
    (profile : Nd2Profile w.limit input.distinguishedBlock) :
    ∃ (incoming : Fin 2), Nonempty (FullDimensionalSourcePresentation
      (W3Nd2CommonBalance.candidates input profile incoming).datum (Fin p)) := by
  have hForest := InheritedLimitRows.forest w hy
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data
    (InteriorProgress.hc_column w.frame.fullDim w.column)
    (InteriorProgress.hab_column w.frame.fullDim w.column)
    (InteriorProgress.hOne_column w.frame.fullDim w.column) hForest
  obtain ⟨incoming, fd, -, -, -, -, -⟩ :=
    W3Nd2GraphTracking.exists_matched_tracking w.frame.data
      (InteriorProgress.hc_column w.frame.fullDim w.column)
      (InteriorProgress.hab_column w.frame.fullDim w.column)
      (InteriorProgress.hOne_column w.frame.fullDim w.column) w.frame.fullDim hForest hCompat
      star input profile (InteriorGraphTracking.Tracks.self w.frame.fullDim)
  exact ⟨incoming, ⟨fd⟩⟩

/-- **`FamilyStarParity … .w3Nd2CoarseFine` from the W3 nd2 star census**: Equation (5)
read mod two through the census. -/
theorem familyStarParity_w3Nd2_of_census (h : W3Nd2StarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w3Nd2CoarseFine := by
  intro core y hy w cls htag
  obtain ⟨star, input, profile, -⟩ := RegrowthWallInput.exists_w3Nd2_balance w cls htag
  obtain ⟨incoming, ⟨fd⟩⟩ := exists_incoming w hy input profile
  obtain ⟨e, hmult⟩ := h core y hy w cls htag star input profile incoming fd
  exact starParityAt_of_census w hy input profile fd e hmult

/-- **The `w3Nd2CoarseFine` clause of `FamilyStarParity` at genus six and degree four**,
modulo Stage 2's exhaustion alone. -/
theorem familyStarParity_w3Nd2_of_exhaustion
    (hExh : W3Nd2StarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Nd2CoarseFine :=
  familyStarParity_w3Nd2_of_census (w3Nd2StarCensus_of_exhaustion hExh)

end Family

end DraismaVargas.Count.W3Nd2StarCensusProof
