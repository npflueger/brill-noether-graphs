import DraismaVargasCount.RegrowthWallInput
import DraismaVargasCount.GeometricMultiplicity
import DraismaVargasCount.StarParityFromBalance

/-!
# The W4 star clause at every discrete four-valent regrowth

Source: Vargas, Part II (arXiv:2609.09109): the star of a codimension-one wall and
`prop-signed-mult` (1).  The balance at a four-valent wall is Equation (1) of
Draisma--Vargas Part I (arXiv:1909.12924, case `{w4}`).  This module proves the star
clause of step 2 of `Assembly` at the discrete four-valent walls.

## The finding, in one paragraph

`W4WallExhaustion.starEquiv` takes `hDiscrete` and three `Candidate`s.  **Neither
exists in general** at a four-valent regrowth.  A four-valent wall need not be
discrete (computer experiments find such walls), and a discrete four-valent wall
need not have three candidates: a candidate at the pairing `q` is a full-dimensional
frame, so it exists only when Equation (1)'s member at `q` is **nonsingular**, and at
most of the discrete four-valent walls found in computer experiments one member is
singular and the star has two classes.  At such a wall `∀ q : Fin 3, Candidate …` is
uninhabited (`W4WallExhaustion.card_eq_three` would force three classes).  The right
statement is a *partial* one, and it is proved here with no hypothesis beyond
discreteness: **the star of a discrete four-valent regrowth is the set of pairings at
which Equation (1)'s member is nonsingular** (`card_star_eq`), each such member *is* a
star candidate (`candidate`), and the singular members contribute `0` to Equation (1)
because their determinant vanishes.  Equation (1) then gives the star clause directly
(`starParityAt_of_discrete`).

## What is proved

* §1 `candidate` -- **the balance family's member at a nonsingular pairing is a
  `W4WallExhaustion.Candidate`, generically in the regrowth.**  The full-dimensional
  presentation is the regrowth's own matched cover (`RegrowthWallInput.w4Matched`)
  moved along `W4PositiveExit.between`; the core labels are the regrowth's inherited
  ones (`identification`); the slot permutation is the identity (`frame_slot`); the
  coordinates at the wall request are the regrowth's own (`frame_coordsAt`, from
  `lab_mulVec_coordsAt`: off the wall column the member's matrix is the regrowth's,
  and the wall coordinate is `0`), so `DegenerateAt` is inherited; the two `overCore`
  squares are proved generically.  Its labelling *is* the balance's labelling
  `lab q = W4CommonBalance.labelling input (initial …) q` (`candidate_labelling`,
  `rfl`).
* §2 the **partial exhaustion engine**, wall-generic: `frameIso1` (the upward lift onto one
  candidate at the member's own pairing), `pairing_eq_of_frameIso2` (two candidates related
  by a frame isomorphism sit at the same pairing), `partialStarEquiv : {q // S q} ≃ Star`
  for any partial family covering every member's pairing, and
  `even_card_starClass_odd_partial` (the star clause from a vanishing sum over `Fin 3`
  whose missing terms are `0`).  These are `W4WallExhaustion` §§4, 6 with the total
  family `cand : ∀ q, Candidate q` replaced by a partial one; the proofs are the same.
* §3 covering: `datum_eq_expansion` (at a discrete wall the family's member *is* the
  uniform expansion), `det_ne_zero_index` (every star member's own pairing is
  nonsingular: multiplicity is an isomorphism invariant,
  `GeometricMultiplicity.absMult_eq_of_datumIso`).
* §4 `starParityAt_of_discrete` -- **`hstar` at every discrete four-valent regrowth**, for
  every core, degree and positive request, with no receipt; `card_star_eq` -- the exact
  census; `familyStarParity_w4_of_nonDiscrete`, `familyStarParity_w4_iff` and
  `familyStarParity_w4` -- the W4 family clause reduced to exactly its non-discrete part.

## What is NOT proved here (every hypothesis)

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w4` is not proved here.**  Its exact
  residue is `NonDiscreteW4StarParity`: the star clause at four-valent regrowths whose
  merged partition is **not** discrete.  `familyStarParity_w4_iff` proves the two
  equivalent, so the residue is neither weaker nor stronger than the W4 clause
  restricted to non-discrete walls.  Computer experiments find such walls (one wall
  block of size two and valency six, `r_φ = 0`, with a two-class star that
  balances), so the residue is not vacuous; it is treated in
  `W4NonDiscreteStarCensus`.  Nothing here handles it: `DiscreteW4Normalization`, on
  which `frameIso1` rests, needs discreteness, and a non-discrete wall's members are
  not uniform expansions.
* **Nothing about schedules.**  `starParityAt_of_discrete` is a statement about one
  regrowth; the quantifier over walls of a schedule is `RegrowthWallInput`'s
  `inConeSupplySimple_of_familyStarParity`, which needs all ten tags.
* **Nothing about the other nine families.**
* `hDiscrete` is not derived from anything: it is the case split of
  `familyStarParity_w4_of_nonDiscrete`.

## Three tempting inferences, checked

* (i) *"`hDiscrete` follows from four-valency (Part I's local structure; the `K = 0`
  statement of `NonTrivalentValencyFourKZero` / `W4IncomingPrunedFibre.census`)."*
  **It does not.**  At a four-valent wall equation (C) of Part I reads `ch(w) = 0`,
  which a block `A` of size two with incident block counts `(1, 1, 2, 2)` satisfies
  (`6 - 2 - 2·2 = 0`).  The two named modules are about other things (the `K = 0`
  construction at Part II's valency-four limits, and the pruned fibre over the wall).
  `W4WallExhaustion`'s own docstring records that `AuxR0SourceInput` does not imply it.
* (ii) *"The three candidates are the three pairings of `w4WallInput`'s family."*
  **Not as stated; true in the corrected form.**  Only the nonsingular pairings give
  candidates (`candidate` needs `hDet`), and at many discrete four-valent walls one
  pairing is singular.
* (iii) *"`even_card_starClass_odd_w4` with `hbal := w4_sum_signedMult_eq_zero`."*
  **Not as stated** (it needs all three candidates, and its `hbal` is on the
  candidates' presentations, not on `W4CommonBalance.labelling`); **true in the
  corrected form** `even_card_starClass_odd_partial`, where the candidates' labellings
  are literally the balance's (`rfl`) and the singular terms vanish.

## Consumers

The W4 clause of `RegrowthWallInput.FamilyStarParity` (step 2 of `Assembly`), modulo
`NonDiscreteW4StarParity`.
-/

namespace DraismaVargas.Count.W4StarParity

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction TargetExpansion
open W4TargetPairings (FourStar)
open W4StableSource FullDimensionalSource
open WallStar (Regrowth Nondegenerate)
open SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex Candidate)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  Equation (1)'s family at a regrowth, and its nonsingular members as candidates -/

section Family

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))

/-- Equation (1)'s source input at the regrowth's wall (a `Prop`). -/
abbrev input : AuxR0SourceInput w.limit star := RegrowthWallInput.w4Input w hy star

/-- The regrowth's own coordinates, read as the limit's optional occurrences. -/
noncomputable def columnEquiv : Fin p ≃ Option (w.frame.limitTarget w.column).edges :=
  w.frame.fullDim.labelling.targetEdge.trans
    (M11IncomingCoordinates.incomingColumnEquiv (contracted := w.frame.edgeOf w.column) rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)).symm

theorem columnEquiv_wall : columnEquiv w w.column = none :=
  M11IncomingCoordinates.incomingColumnEquiv_symm_contracted (contracted := w.frame.edgeOf w.column)
    rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)

theorem columnEquiv_retained (c : Fin p) (hc : c ≠ w.column) :
    columnEquiv w c = some (StarMetricCompatibility.retainedColumns w.frame w.column ⟨c, hc⟩) := by
  apply (M11IncomingCoordinates.incomingColumnEquiv (contracted := w.frame.edgeOf w.column) rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)).symm_apply_eq.mpr
  exact (InheritedLimitRows.unfoldEdge_retainedColumns w ⟨c, hc⟩).symm

/-- The initial square labelling of the zeroth member of Equation (1)'s family. -/
noncomputable def initial :
    StableLengthMatrixLabelling (W4OutgoingStableRows.member (input w hy star) 0).datum (Fin p) where
  row := (W4OutgoingStableRows.stablePathEquiv (input w hy star) 0).symm.trans
    (InheritedLimitRows.rowLabel w hy)
  targetEdge := (columnEquiv w).trans
    (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
      (W4OutgoingStableRows.member (input w hy star) 0).right)

/-- The balance's labelling at the pairing `q`. -/
noncomputable abbrev lab (q : Fin 3) :
    StableLengthMatrixLabelling (W4OutgoingStableRows.member (input w hy star) q).datum (Fin p) :=
  W4CommonBalance.labelling (input w hy star) (initial w hy star) q

theorem lab_row (q : Fin 3) :
    (lab w hy star q).row = (W4OutgoingStableRows.stablePathEquiv (input w hy star) q).symm.trans
      (InheritedLimitRows.rowLabel w hy) := by
  ext x
  simp [W4CommonBalance.labelling, W4CommonBalance.sourceCoordinates, initial]

theorem lab_targetEdge (q : Fin 3) :
    (lab w hy star q).targetEdge = (columnEquiv w).trans
      (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
        (W4OutgoingStableRows.member (input w hy star) q).right) := by
  ext x
  simp [W4CommonBalance.labelling, W4CommonBalance.targetCoordinates, initial]


theorem limitTarget_connected : graph_connected (w.frame.limitTarget w.column) :=
  graph_connected_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) w.frame.fullDim.targetConnected

theorem limitTarget_genus : genus (w.frame.limitTarget w.column) = 0 :=
  (genus_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column)).trans w.frame.fullDim.targetGenus

example (q : Fin 3) : (W4OutgoingStableRows.member (input w hy star) q).right = star.right q := rfl

/-- The member's datum at the pairing `q`, on the expanded wall target. -/
noncomputable abbrev datum (q : Fin 3) :=
  (W4OutgoingStableRows.member (input w hy star) q).datum

/-- The matrix entries of the balance's labelling off the wall column are the regrowth's
own, read through its slot permutation. -/
theorem lab_matrix_retained (q : Fin 3) (r c : Fin p) (hc : c ≠ w.column) :
    GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation r c =
      w.frame.matrix (w.frame.slot.symm r) c := by
  rw [StableSourceMatrix.labelling_matrix_eq, lab_row, lab_targetEdge]
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  rw [columnEquiv_retained w c hc, W4OutgoingStableRows.matrix_retained]
  exact InheritedLimitRows.matrix_retained w hy r ⟨c, hc⟩

/-- **The balance's labelling realizes the request at the regrowth's own coordinates.** -/
theorem lab_mulVec_coordsAt (q : Fin 3) :
    (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).mulVec
        (w.frame.coordsAt y) = y := by
  funext r
  have hw := congrFun (w.frame.mulVec_coordsAt y) (w.frame.slot.symm r)
  simp only [Equiv.apply_symm_apply] at hw
  rw [← hw]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases hc : c = w.column
  · subst hc
    rw [w.degenerate.1, mul_zero, mul_zero]
  · rw [lab_matrix_retained w hy star q r c hc]


/-- The regrowth's own inherited core identification of its limit. -/
noncomputable abbrev wallIdent : CoreIdentification core w.limit :=
  InheritedLimitIncidence.coreIdentification w hy

/-- Core labels of the member at `q`, inherited through the literal W4 incidence maps. -/
noncomputable def identification (q : Fin 3) : CoreIdentification core (datum w hy star q) where
  vertex := (W4OutgoingStableRows.equivalence (input w hy star) q).vertex.symm.trans
    (wallIdent w hy).vertex
  row := (W4OutgoingStableRows.equivalence (input w hy star) q).row.symm.trans (wallIdent w hy).row
  incidence v slot := by
    have h := (W4OutgoingStableRows.equivalence (input w hy star) q).incidence
      ((W4OutgoingStableRows.equivalence (input w hy star) q).vertex.symm v)
      ((wallIdent w hy).row.symm slot)
    have ho := (wallIdent w hy).incidence
      ((W4OutgoingStableRows.equivalence (input w hy star) q).vertex.symm v) slot
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_symm] using h.symm.trans ho

theorem identification_row (q : Fin 3) :
    (identification w hy star q).row = (lab w hy star q).row := by
  rw [lab_row]
  rfl

/-- **The member at a nonsingular pairing is full-dimensional**: the regrowth's own
matched cover (`RegrowthWallInput.w4Matched`) transported along the family's stable-graph
equivalence, with the balance's own labelling. -/
noncomputable def fullDim (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    FullDimensionalSourcePresentation (datum w hy star q) (Fin p) :=
  StableGraphFullDimensional.presentationOfEquivalence (RegrowthWallInput.w4Matched w hy star)
    (W4PositiveExit.between (input w hy star) (RegrowthWallInput.w4Incoming w star) q)
    (W4PositiveExit.candidate_valid (input w hy star) q)
    (W4PositiveExit.candidate_targetConnected (input w hy star) (limitTarget_connected w) q)
    (W4PositiveExit.candidate_targetGenus (input w hy star) (limitTarget_genus w) q)
    ((W4PositiveExit.candidate_targetEdgeCard (input w hy star) q).trans
      (W4PositiveExit.candidate_targetEdgeCard (input w hy star) _).symm)
    ((W4OutgoingStableRows.member_sourceGenus (input w hy star) q).trans
      (W4OutgoingStableRows.member_sourceGenus (input w hy star) _).symm)
    (lab w hy star q) hDet

theorem fullDim_labelling (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    (fullDim w hy star q hDet).labelling = lab w hy star q := rfl

/-- The member's frame at a nonsingular pairing. -/
noncomputable def frame (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    Frame core degree :=
  ⟨_, _, fullDim w hy star q hDet, identification w hy star q⟩

theorem frame_slot (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    (frame w hy star q hDet).slot = Equiv.refl (Fin p) := by
  apply Equiv.ext
  intro r
  change (identification w hy star q).row ((fullDim w hy star q hDet).labelling.row.symm r) = r
  rw [identification_row, fullDim_labelling, Equiv.apply_symm_apply]

/-- **The member's coordinates at the wall request are the regrowth's own.** -/
theorem frame_coordsAt (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    (frame w hy star q hDet).coordsAt y = w.frame.coordsAt y := by
  have hM : (frame w hy star q hDet).matrix =
      GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation := rfl
  have h : (fun r ↦ y ((frame w hy star q hDet).slot r)) =
      (frame w hy star q hDet).matrix.mulVec (w.frame.coordsAt y) := by
    rw [frame_slot, hM, lab_mulVec_coordsAt]
    rfl
  rw [SegmentWalls.Frame.coordsAt, h, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (frame w hy star q hDet).isUnit_det, Matrix.one_mulVec]

theorem frame_degenerate (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    (frame w hy star q hDet).DegenerateAt y w.column := by
  rw [SegmentWalls.Frame.DegenerateAt, frame_coordsAt]
  exact w.degenerate

theorem frame_edgeOf (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    (frame w hy star q hDet).edgeOf w.column =
      occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) (star.right q) none := by
  change (lab w hy star q).targetEdge w.column = _
  rw [lab_targetEdge]
  simp only [Equiv.trans_apply]
  rw [columnEquiv_wall]
  rfl


/-- The member's regrowth at a nonsingular pairing: same request, same column. -/
noncomputable def regrowth (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    Regrowth core y degree :=
  ⟨frame w hy star q hDet, w.column, frame_degenerate w hy star q hDet⟩

/-! ### The partition conditions at a discrete wall -/

theorem side_refines (q : Fin 3) (side : Bool) :
    ((datum w hy star q).vertexPartition
        (W4OutgoingSurvival.sideVertex (w.frame.limitTarget w.column) (mergeVertex w) side)).Refines
      (w.limit.vertexPartition (mergeVertex w)) := by
  rw [W4OutgoingStableRows.member_vertexPartition_side (input w hy star) q side]
  exact W4OutgoingSurvival.sidePartition_refines_wall w.limit star _ q side

variable (hDiscrete : w.limit.vertexPartition (mergeVertex w) = SheetPartition.discrete degree)

include hDiscrete in
theorem side_eq (q : Fin 3) (side : Bool) :
    (datum w hy star q).vertexPartition
        (W4OutgoingSurvival.sideVertex (w.frame.limitTarget w.column) (mergeVertex w) side) =
      w.limit.vertexPartition (mergeVertex w) := by
  rw [hDiscrete]
  apply DiscreteContraction.eq_discrete_of_refines
  rw [← hDiscrete]
  exact side_refines w hy star q side

include hDiscrete in
theorem merge (q : Fin 3) :
    SheetPartition.join
        ((datum w hy star q).vertexPartition
          (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)))
        ((datum w hy star q).vertexPartition (freshVertex (w.frame.limitTarget w.column))) =
      w.limit.vertexPartition (mergeVertex w) := by
  rw [show (datum w hy star q).vertexPartition
      (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)) = SheetPartition.discrete degree
      from (side_eq w hy star hDiscrete q false).trans hDiscrete,
    show (datum w hy star q).vertexPartition (freshVertex (w.frame.limitTarget w.column)) =
      SheetPartition.discrete degree from (side_eq w hy star hDiscrete q true).trans hDiscrete,
    W4LimitContraction.join_discrete_discrete, hDiscrete]

theorem away (q : Fin 3) (vertex : (w.frame.limitTarget w.column).V)
    (hvertex : vertex ≠ mergeVertex w) :
    (datum w hy star q).vertexPartition (oldVertex (w.frame.limitTarget w.column) vertex) =
      w.limit.vertexPartition vertex :=
  GlobalResolution.expandedVertexPartition_old_of_ne w.limit (mergeVertex w) _ _ hvertex

theorem retained (q : Fin 3) (edge : (w.frame.limitTarget w.column).edges) :
    (datum w hy star q).edgePartition
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) (star.right q)
          (some edge)) = w.limit.edgePartition edge :=
  GlobalResolution.expandedEdgePartition_old w.limit (mergeVertex w) _ _ edge

/-- **The limit of the member is the wall datum**, by the literal contraction
dictionaries. -/
noncomputable def limitIso (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    GeometricDatumIso (regrowth w hy star q hDet).limit w.limit :=
  W4LimitContraction.limitIso rfl (fst_ne_snd ((frame w hy star q hDet).edgeOf w.column))
    ((frame w hy star q hDet).numEdges_edgeOf w.column) (frame_edgeOf w hy star q hDet)
    w.limit (datum w hy star q) (merge w hy star hDiscrete q) (away w hy star q)
    (retained w hy star q)

theorem contract_sideVertex (side : Bool) :
    contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
      (W4OutgoingSurvival.sideVertex (w.frame.limitTarget w.column) (mergeVertex w) side) =
        mergeVertex w := by
  cases side <;> rfl

/-- **Lift, contract, identify is the identity on wall source vertices.** -/
theorem sourceVertex_branchImage (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0)
    (v : w.limit.SourceVertex) :
    (limitIso w hy star hDiscrete q hDet).sourceVertexEquiv
        (InheritedLimitBranches.vertexMap (regrowth w hy star q hDet)
          (W4OutgoingStableRows.branchImage (input w hy star) q v)) = v := by
  by_cases hv : v.1.1 = mergeVertex w
  · have hbranch : W4OutgoingStableRows.branchImage (input w hy star) q v =
        (datum w hy star q).sourceEndpoint
          (W4OutgoingSurvival.sideVertex (w.frame.limitTarget w.column) (mergeVertex w)
            (W4OutgoingStableRows.branchSide (input w hy star) q
              (W4Assembly.WallBlock.ofSheet w.limit (mergeVertex w) v.1.2))) v.1.2 := by
      rw [W4OutgoingStableRows.branchImage, if_pos hv]
      rfl
    have key := W4LimitContraction.sourceVertexEquiv_sourceEndpoint rfl
      (fst_ne_snd ((frame w hy star q hDet).edgeOf w.column))
      ((frame w hy star q hDet).numEdges_edgeOf w.column) (frame_edgeOf w hy star q hDet)
      w.limit (datum w hy star q) (merge w hy star hDiscrete q) (away w hy star q)
      (retained w hy star q)
      (W4OutgoingSurvival.sideVertex (w.frame.limitTarget w.column) (mergeVertex w)
        (W4OutgoingStableRows.branchSide (input w hy star) q
          (W4Assembly.WallBlock.ofSheet w.limit (mergeVertex w) v.1.2)))
      (mergeVertex w) v.1.2 (contract_sideVertex w _) (side_refines w hy star q _)
    rw [hbranch]
    refine key.trans ?_
    rw [← hv]
    exact w.limit.sourceEndpoint_self v
  · have hbranch : W4OutgoingStableRows.branchImage (input w hy star) q v =
        (datum w hy star q).sourceEndpoint (oldVertex (w.frame.limitTarget w.column) v.1.1)
          v.1.2 := by
      rw [W4OutgoingStableRows.branchImage, if_neg hv]
      rfl
    have key := W4LimitContraction.sourceVertexEquiv_sourceEndpoint rfl
      (fst_ne_snd ((frame w hy star q hDet).edgeOf w.column))
      ((frame w hy star q hDet).numEdges_edgeOf w.column) (frame_edgeOf w hy star q hDet)
      w.limit (datum w hy star q) (merge w hy star hDiscrete q) (away w hy star q)
      (retained w hy star q)
      (oldVertex (w.frame.limitTarget w.column) v.1.1) v.1.1 v.1.2 rfl
      (by rw [away w hy star q v.1.1 hv]; exact SheetPartition.Refines.refl _)
    rw [hbranch]
    exact key.trans (w.limit.sourceEndpoint_self v)


theorem branchVertexEquiv_eq (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0)
    (v : StableGraphIncidence.BranchVertex w.limit) :
    (limitIso w hy star hDiscrete q hDet).branchVertexEquiv
        (InheritedLimitRows.limit_connected (regrowth w hy star q hDet))
        (InheritedLimitBranches.branchEquiv (regrowth w hy star q hDet) hy
          (W4OutgoingStableRows.branchVertexEquiv (input w hy star) q v)) = v :=
  Subtype.ext (sourceVertex_branchImage w hy star hDiscrete q hDet v.1)

/-- **The limit isomorphism preserves the inherited branch labels.** -/
theorem overCore_vertex (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0)
    (branch : StableGraphIncidence.BranchVertex (regrowth w hy star q hDet).limit) :
    (InheritedLimitIncidence.coreIdentification w hy).vertex
        ((limitIso w hy star hDiscrete q hDet).branchVertexEquiv
          (InheritedLimitRows.limit_connected (regrowth w hy star q hDet)) branch) =
      (InheritedLimitIncidence.coreIdentification (regrowth w hy star q hDet) hy).vertex
        branch := by
  obtain ⟨old, rfl⟩ :=
    (InheritedLimitBranches.branchEquiv (regrowth w hy star q hDet) hy).surjective branch
  obtain ⟨v, rfl⟩ := (W4OutgoingStableRows.branchVertexEquiv (input w hy star) q).surjective old
  rw [branchVertexEquiv_eq w hy star hDiscrete q hDet v]
  exact (congrArg (wallIdent w hy).vertex
      ((W4OutgoingStableRows.branchVertexEquiv (input w hy star) q).symm_apply_apply v)).symm.trans
    (congrArg (identification w hy star q).vertex
      ((InheritedLimitBranches.branchEquiv (regrowth w hy star q hDet) hy).symm_apply_apply
        (W4OutgoingStableRows.branchVertexEquiv (input w hy star) q v))).symm

/-- The retained copy of a wall occurrence is the literal contraction embedding of the
corresponding limit occurrence. -/
theorem retained_eq (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0)
    (edge : NonDanglingEdge (regrowth w hy star q hDet).limit) :
    (W4OutgoingStableRows.retained (input w hy star) q
        ((limitIso w hy star hDiscrete q hDet).nonDanglingEdgeEquiv
          (InheritedLimitRows.limit_connected (regrowth w hy star q hDet)) edge)).1 =
      InheritedLimitRows.edgeEmbedding (regrowth w hy star q hDet) edge.1 := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · exact (W4LimitContraction.occurrenceEquiv_edgeEquiv rfl
      (fst_ne_snd ((frame w hy star q hDet).edgeOf w.column))
      ((frame w hy star q hDet).numEdges_edgeOf w.column) (frame_edgeOf w hy star q hDet)
      edge.1.1.1).trans
      (InheritedLimitRows.edgeEmbedding_target (regrowth w hy star q hDet) edge.1).symm
  · exact (congrArg Prod.snd (IncomingNormalizationRows.sourceEdgeEmbedding_val
      (datum w hy star q) rfl (fst_ne_snd ((frame w hy star q hDet).edgeOf w.column))
      ((frame w hy star q hDet).numEdges_edgeOf w.column) edge.1)).symm

theorem stablePathEquiv_eq (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0)
    (row : StablePath (regrowth w hy star q hDet).limit) :
    W4OutgoingStableRows.stablePathEquiv (input w hy star) q
        ((limitIso w hy star hDiscrete q hDet).stablePathEquiv
          (InheritedLimitRows.limit_connected (regrowth w hy star q hDet)) row) =
      InheritedLimitRows.rowEquiv (regrowth w hy star q hDet) hy row := by
  refine Quot.inductionOn row ?_
  intro edge
  refine Eq.trans (congrArg (W4OutgoingStableRows.stablePathEquiv (input w hy star) q)
    ((limitIso w hy star hDiscrete q hDet).stablePathEquiv_mk
      (InheritedLimitRows.limit_connected (regrowth w hy star q hDet)) edge)) ?_
  refine Eq.trans (W4OutgoingStableRows.stablePathEquiv_mk (input w hy star) q _) ?_
  refine Eq.trans ?_ (InheritedLimitRows.rowEquiv_mk (regrowth w hy star q hDet) hy edge).symm
  exact congrArg NonDanglingEdge.stablePath (Subtype.ext (retained_eq w hy star hDiscrete q hDet edge))

/-- **The limit isomorphism preserves the inherited row labels.** -/
theorem overCore_row (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0)
    (row : StablePath (regrowth w hy star q hDet).limit) :
    (InheritedLimitIncidence.coreIdentification w hy).row
        ((limitIso w hy star hDiscrete q hDet).stablePathEquiv
          (InheritedLimitRows.limit_connected (regrowth w hy star q hDet)) row) =
      (InheritedLimitIncidence.coreIdentification (regrowth w hy star q hDet) hy).row row := by
  change (wallIdent w hy).row ((limitIso w hy star hDiscrete q hDet).stablePathEquiv
      (InheritedLimitRows.limit_connected (regrowth w hy star q hDet)) row) =
    (identification w hy star q).row
      (InheritedLimitRows.rowEquiv (regrowth w hy star q hDet) hy row)
  change _ = (wallIdent w hy).row ((W4OutgoingStableRows.stablePathEquiv (input w hy star) q).symm
    (InheritedLimitRows.rowEquiv (regrowth w hy star q hDet) hy row))
  rw [← stablePathEquiv_eq w hy star hDiscrete q hDet row, Equiv.symm_apply_apply]

/-- **The balance family's member at a nonsingular pairing is a
`W4WallExhaustion.Candidate`.**  Every field is generic in the regrowth. -/
noncomputable def candidate (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    Candidate hy w hDiscrete star q where
  data := datum w hy star q
  fullDim := fullDim w hy star q hDet
  ident := identification w hy star q
  column := w.column
  degenerate := frame_degenerate w hy star q hDet
  column_eq := frame_edgeOf w hy star q hDet
  side_old := side_eq w hy star hDiscrete q false
  side_fresh := side_eq w hy star hDiscrete q true
  away := away w hy star q
  retained := retained w hy star q
  overCore_vertex := overCore_vertex w hy star hDiscrete q hDet
  overCore_row := overCore_row w hy star hDiscrete q hDet

theorem candidate_labelling (q : Fin 3)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0) :
    (candidate w hy star hDiscrete q hDet).fullDim.labelling = lab w hy star q := rfl

end Family


/-! ## 2.  The exhaustion engine with a *partial* candidate family -/

section PartialEngine

open GeometricSegmentWalls (FrameIso)
open W4WallExhaustion (index normIso transIso)

variable {hy : Nondegenerate y} {wall : Regrowth core y degree}
  (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
  (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree)
  (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall))

/-- The datum half of the upward lift onto **one** candidate at the member's own
pairing (`W4WallExhaustion.frameDatum` with the family replaced by that candidate). -/
noncomputable def frameDatum1 (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (c : Candidate hy wall hDiscrete star (index hFour star other iso)) :
    GeometricDatumIso other.frame.data c.data :=
  ((normIso hFour hDiscrete star other iso).trans (transIso hFour star other iso)).trans
    (UniformExpansionRecognition.ofEq (Candidate.data_eq c).symm)

theorem frameDatum1_sourceVertex (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (c : Candidate hy wall hDiscrete star (index hFour star other iso))
    (vertex : other.frame.data.SourceVertex) :
    ((frameDatum1 hFour hDiscrete star other iso c).sourceVertexEquiv vertex).1 =
      ((transIso hFour star other iso).sourceVertexEquiv
        ((normIso hFour hDiscrete star other iso).sourceVertexEquiv vertex)).1 :=
  UniformExpansionRecognition.ofEq_sourceVertexEquiv (Candidate.data_eq c).symm
    ((transIso hFour star other iso).sourceVertexEquiv
      ((normIso hFour hDiscrete star other iso).sourceVertexEquiv vertex))

theorem frameDatum1_sourceEdge (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (c : Candidate hy wall hDiscrete star (index hFour star other iso))
    (edge : other.frame.data.SourceEdge) :
    ((frameDatum1 hFour hDiscrete star other iso c).sourceEdgeEquiv edge).1 =
      ((transIso hFour star other iso).sourceEdgeEquiv
        ((normIso hFour hDiscrete star other iso).sourceEdgeEquiv edge)).1 :=
  UniformExpansionRecognition.ofEq_sourceEdgeEquiv (Candidate.data_eq c).symm
    ((transIso hFour star other iso).sourceEdgeEquiv
      ((normIso hFour hDiscrete star other iso).sourceEdgeEquiv edge))

theorem source_square1 (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (c : Candidate hy wall hDiscrete star (index hFour star other iso))
    (vertex : other.frame.data.SourceVertex) :
    c.datumIso.sourceVertexEquiv
        (InheritedLimitBranches.vertexMap c.regrowth
          ((frameDatum1 hFour hDiscrete star other iso c).sourceVertexEquiv vertex)) =
      iso.datum.sourceVertexEquiv (InheritedLimitBranches.vertexMap other vertex) := by
  have hMember := Candidate.member_contractSourceVertex c
    ((frameDatum1 hFour hDiscrete star other iso c).sourceVertexEquiv vertex)
  have hVal := frameDatum1_sourceVertex hFour hDiscrete star other iso c vertex
  have hNorm : InheritedLimitBranches.vertexMap other vertex =
      GeometricUniformExpansion.contractSourceVertex other.limit (mergeVertex other)
        ((W4WallExhaustion.inheritedStar other iso hFour star).right (index hFour star other iso))
        ((normIso hFour hDiscrete star other iso).sourceVertexEquiv vertex) :=
    DiscreteW4Normalization.contractSourceVertex_datumIso other.frame.data other.frame.fullDim
      rfl (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column)
      (W4WallExhaustion.inheritedStar other iso hFour star)
      (W4WallExhaustion.limit_discrete other iso hFour hDiscrete) vertex
  have hLift := GeometricUniformExpansion.contractSourceVertex_lift iso.datum
    (mergeVertex other) (mergeVertex wall) (W4WallExhaustion.map_merge other iso hFour) _ _
    (W4WallExhaustion.right_map hFour star other iso)
    ((normIso hFour hDiscrete star other iso).sourceVertexEquiv vertex)
  rw [hMember, hVal, hNorm, hLift]
  exact (UniformExpansionRecognition.contractSourceVertex_eq_sourceEndpoint wall.limit
    (mergeVertex wall) (star.right (index hFour star other iso)) _).symm

theorem edge_square1 (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (c : Candidate hy wall hDiscrete star (index hFour star other iso))
    (edge : other.limit.SourceEdge) :
    (frameDatum1 hFour hDiscrete star other iso c).sourceEdgeEquiv
        (InheritedLimitRows.edgeEmbedding other edge) =
      InheritedLimitRows.edgeEmbedding c.regrowth
        (StarFrameIso.transfer iso c.starLimitIso edge) := by
  apply Subtype.ext
  have hNorm : (normIso hFour hDiscrete star other iso).sourceEdgeEquiv
      (InheritedLimitRows.edgeEmbedding other edge) =
      GeometricUniformExpansion.retainedSourceEdge other.limit (mergeVertex other)
        ((W4WallExhaustion.inheritedStar other iso hFour star).right
          (index hFour star other iso)) edge :=
    DiscreteW4Normalization.retainedSourceEdge_datumIso other.frame.data other.frame.fullDim rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column)
      (W4WallExhaustion.inheritedStar other iso hFour star)
      (W4WallExhaustion.limit_discrete other iso hFour hDiscrete) edge
  have hLift : (transIso hFour star other iso).sourceEdgeEquiv
      (GeometricUniformExpansion.retainedSourceEdge other.limit (mergeVertex other)
        ((W4WallExhaustion.inheritedStar other iso hFour star).right
          (index hFour star other iso)) edge) =
      GeometricUniformExpansion.retainedSourceEdge wall.limit (mergeVertex wall)
        (star.right (index hFour star other iso)) (iso.datum.sourceEdgeEquiv edge) :=
    GeometricUniformExpansion.retainedSourceEdge_lift iso.datum (mergeVertex other)
      (mergeVertex wall) (W4WallExhaustion.map_merge other iso hFour) _ _
      (W4WallExhaustion.right_map hFour star other iso) edge
  have hMember := Candidate.member_edgeEmbedding_val c
    (StarFrameIso.transfer iso c.starLimitIso edge)
  have hTransfer : c.datumIso.sourceEdgeEquiv
      (StarFrameIso.transfer iso c.starLimitIso edge) = iso.datum.sourceEdgeEquiv edge :=
    StarFrameIso.datum_sourceEdgeEquiv_transfer iso c.starLimitIso edge
  rw [frameDatum1_sourceEdge, hNorm, hLift, hMember, hTransfer]
  rfl

/-- **The upward frame isomorphism onto one candidate at the member's own pairing.** -/
noncomputable def frameIso1 (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall)
    (c : Candidate hy wall hDiscrete star (index hFour star other iso)) :
    FrameIso other.frame c.frame :=
  StarFrameIso.ofLimitSquare iso c.starLimitIso
    (frameDatum1 hFour hDiscrete star other iso c)
    (source_square1 hFour hDiscrete star other iso c)
    (edge_square1 hFour hDiscrete star other iso c)


section TwoCandidates

variable {first second : Fin 3} (c₁ : Candidate hy wall hDiscrete star first)
  (c₂ : Candidate hy wall hDiscrete star second)

/-- The composite limit dictionary between two candidates. -/
noncomputable def candLimIso2 :
    GeometricDatumIso c₁.regrowth.limit c₂.regrowth.limit :=
  c₁.datumIso.trans c₂.datumIso.symm

theorem candLimIso2_targetEdge
    (edge : (c₁.regrowth.frame.limitTarget c₁.regrowth.column).edges) :
    c₂.datumIso.targetEdge ((candLimIso2 hDiscrete star c₁ c₂).targetEdge edge) =
      c₁.datumIso.targetEdge edge := by
  change c₂.datumIso.targetEdge (c₂.datumIso.targetEdge.symm (c₁.datumIso.targetEdge edge)) = _
  rw [Equiv.apply_symm_apply]

theorem candLimIso2_rowLabel (row : W4StableSource.StablePath c₁.regrowth.limit) :
    InheritedLimitRows.rowLabel c₂.regrowth hy
        ((candLimIso2 hDiscrete star c₁ c₂).stablePathEquiv
          (InheritedLimitRows.limit_connected c₁.regrowth) row) =
      InheritedLimitRows.rowLabel c₁.regrowth hy row :=
  (c₁.starLimitIso.trans c₂.starLimitIso.symm).overCore_row row

theorem column_eq_limitColumns2 (fi : FrameIso c₁.regrowth.frame c₂.regrowth.frame) :
    fi.column = InheritedLimitRows.allColumns c₁.regrowth c₂.regrowth
      (candLimIso2 hDiscrete star c₁ c₂) :=
  FrameColumnRigidity.column_eq_allColumns c₁.regrowth c₂.regrowth hy
    (candLimIso2 hDiscrete star c₁ c₂) (candLimIso2_rowLabel hDiscrete star c₁ c₂) fi

theorem occurrence_map2 (fi : FrameIso c₁.regrowth.frame c₂.regrowth.frame)
    (label : Option (wall.frame.limitTarget wall.column).edges) :
    fi.datum.targetEdge
        (occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
          (star.right first) label) =
      occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
        (star.right second) label := by
  cases label with
  | none =>
    have hcol : fi.column c₁.regrowth.column = c₂.regrowth.column := by
      rw [column_eq_limitColumns2 hDiscrete star c₁ c₂]
      exact InheritedLimitRows.allColumns_collapsed c₁.regrowth c₂.regrowth
        (candLimIso2 hDiscrete star c₁ c₂)
    refine (congrArg fi.datum.targetEdge c₁.column_eq.symm).trans ?_
    refine (W4WallExhaustion.targetEdge_column fi c₁.regrowth.column).trans ?_
    rw [hcol]
    exact c₂.column_eq
  | some edge =>
    obtain ⟨col, hEdge⟩ : ∃ col : {col : Fin p // col ≠ c₁.regrowth.column},
        c₁.datumIso.targetEdge
          (StarMetricCompatibility.retainedColumns c₁.regrowth.frame
            c₁.regrowth.column col) = edge :=
      ⟨(StarMetricCompatibility.retainedColumns c₁.regrowth.frame
          c₁.regrowth.column).symm (c₁.datumIso.targetEdge.symm edge), by
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩
    have hLeft : occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
        (star.right first) (some edge) =
        c₁.regrowth.frame.fullDim.labelling.targetEdge col.1 := by
      rw [← hEdge]
      exact W4WallExhaustion.occurrence_retained hDiscrete star c₁ col
    have hColumn : fi.column col.1 =
        (InheritedLimitRows.limitColumns c₁.regrowth c₂.regrowth
          (candLimIso2 hDiscrete star c₁ c₂) col).1 := by
      rw [column_eq_limitColumns2 hDiscrete star c₁ c₂]
      exact InheritedLimitRows.allColumns_retained c₁.regrowth c₂.regrowth
        (candLimIso2 hDiscrete star c₁ c₂) col
    rw [hLeft, W4WallExhaustion.targetEdge_column fi col.1, hColumn]
    refine ((W4WallExhaustion.occurrence_retained hDiscrete star c₂
      (InheritedLimitRows.limitColumns c₁.regrowth c₂.regrowth
        (candLimIso2 hDiscrete star c₁ c₂) col)).symm).trans ?_
    rw [W4WallExhaustion.retainedColumns_limitColumns, candLimIso2_targetEdge hDiscrete star c₁ c₂,
      hEdge]

/-- **Two candidates related by a frame isomorphism sit at the same pairing.** -/
theorem pairing_eq_of_frameIso2 (fi : FrameIso c₁.regrowth.frame c₂.regrowth.frame) :
    first = second :=
  W4PairingRigidity.pairing_eq_of_expansionIso star first second
    fi.datum.targetVertex fi.datum.targetEdge fi.datum.ends
    (occurrence_map2 hDiscrete star c₁ c₂ fi)

end TwoCandidates


section Partial

variable (S : Fin 3 → Prop) (cand : ∀ q, S q → Candidate hy wall hDiscrete star q)

/-- The partial family's classes are pairwise distinct (request-free rigidity). -/
theorem partial_cls_injective :
    Function.Injective fun q : {q // S q} ↦ (cand q.1 q.2).starMember.cls := by
  intro a b h
  obtain ⟨fi⟩ := Quotient.exact h
  exact Subtype.ext (pairing_eq_of_frameIso2 hDiscrete star (cand a.1 a.2) (cand b.1 b.2) fi)

variable (hcover : ∀ (other : Regrowth core y degree) (iso : GeometricStar.LimitIso hy other wall),
  S (index hFour star other iso))

include hcover in
/-- Exhaustion by the partial family, as soon as every member's own pairing lies in it. -/
theorem partial_cls_surjective :
    Function.Surjective fun q : {q // S q} ↦ (cand q.1 q.2).starMember.cls := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨limIso⟩ := member.specializes
  refine ⟨⟨index hFour star member.member limIso, hcover member.member limIso⟩, ?_⟩
  have h : member.cls = (cand _ (hcover member.member limIso)).starMember.cls :=
    Quotient.sound ⟨frameIso1 hFour hDiscrete star member.member limIso
      (cand _ (hcover member.member limIso))⟩
  exact h.symm

include hFour hcover in
/-- **The star is the partial family's index set.** -/
noncomputable def partialStarEquiv : {q // S q} ≃ GeometricStar.Star hy wall :=
  Equiv.ofBijective _ ⟨partial_cls_injective hDiscrete star S cand,
    partial_cls_surjective hFour hDiscrete star S cand hcover⟩

include hFour hcover in
/-- **The star clause from a balance over all three pairings whose missing members
contribute zero.** -/
theorem even_card_starClass_odd_partial (m : Fin 3 → ℚ)
    (hm : ∀ q (h : S q), signedMult (cand q h).fullDim.labelling.presentation = m q)
    (hzero : ∀ q, ¬ S q → m q = 0) (hbal : ∑ q : Fin 3, m q = 0) :
    Even (Nat.card {c : GeometricFibre core y degree //
      GeometricStar.IsStarClass hy wall c ∧ c.IsOdd}) := by
  classical
  refine StarParityFromBalance.even_card_starClass_odd_of_equiv
    (partialStarEquiv hFour hDiscrete star S cand hcover) ?_
  have hint : ∀ q, ∃ value : ℤ, m q = (value : ℚ) := by
    intro q
    by_cases h : S q
    · obtain ⟨value, hv⟩ := isIntegralMultiplicity (cand q h).fullDim
      exact ⟨value, (hm q h).symm.trans hv⟩
    · exact ⟨0, by rw [hzero q h]; simp⟩
  have hEven := StarParityFromBalance.even_sum_num_natAbs_of_sum_eq_zero m hint hbal
  have hSplit := Fintype.sum_subtype_add_sum_subtype S (fun q ↦ (m q).num.natAbs)
  have hRest : ∑ q : {q // ¬ S q}, (m q.1).num.natAbs = 0 :=
    Finset.sum_eq_zero fun q _ ↦ by rw [hzero q.1 q.2]; rfl
  rw [hRest, add_zero] at hSplit
  rw [← hSplit] at hEven
  convert hEven using 2 with q
  change (signedMult (cand q.1 q.2).fullDim.labelling.presentation).num.natAbs = _
  rw [hm q.1 q.2]

end Partial

end PartialEngine


/-! ## 3.  Every star member's pairing is a nonsingular member of Equation (1)'s family -/

section Cover

open W4WallExhaustion (index normIso transIso)

variable (w : Regrowth core y degree) (hy : Nondegenerate y)
  (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w))
  (hDiscrete : w.limit.vertexPartition (mergeVertex w) = SheetPartition.discrete degree)

include hDiscrete in
/-- The regrown occurrence of the member carries the wall partition. -/
theorem newEdge_eq (q : Fin 3) :
    (datum w hy star q).edgePartition (occurrenceEquiv (w.frame.limitTarget w.column)
        (mergeVertex w) (star.right q) none) =
      w.limit.vertexPartition (mergeVertex w) := by
  have hSide : (datum w hy star q).vertexPartition
      (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)) =
      SheetPartition.discrete degree := (side_eq w hy star hDiscrete q false).trans hDiscrete
  have hRefines := (datum w hy star q).refines_left
    (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) (star.right q) none)
  rw [occurrenceEquiv_none] at hRefines
  have hOld : ((datum w hy star q).edgePartition (occurrenceEquiv (w.frame.limitTarget w.column)
      (mergeVertex w) (star.right q) none)).Refines
      ((datum w hy star q).vertexPartition
        (oldVertex (w.frame.limitTarget w.column) (mergeVertex w))) := hRefines
  rw [hSide] at hOld
  rw [hDiscrete]
  exact DiscreteContraction.eq_discrete_of_refines _ hOld

include hDiscrete in
/-- **At a discrete wall the member of Equation (1)'s family at `q` is literally the
uniform expansion at `q`.** -/
theorem datum_eq_expansion (q : Fin 3) :
    datum w hy star q = W4WallExhaustion.expansion w star q :=
  UniformExpansionRecognition.eq_uniformExpansion w.limit (mergeVertex w) (star.right q)
    (datum w hy star q) (side_eq w hy star hDiscrete q false) (side_eq w hy star hDiscrete q true)
    (away w hy star q) (newEdge_eq w hy star hDiscrete q) (retained w hy star q)

theorem absMult_ne_zero_iff {target : CFGraph} {data : GluingDatum target degree}
    (presentation : data.LengthMatrixPresentation (Fin p)) :
    absMult presentation ≠ 0 ↔
      (GluingDatum.LengthMatrixPresentation.matrix presentation).det ≠ 0 := by
  unfold absMult signedMult
  rw [ne_eq, abs_eq_zero, mul_eq_zero, not_or]
  have hD : ((denominatorProduct presentation : ℚ) / 2 ^ leafCount target) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast (denominatorProduct_pos presentation).ne'
    · exact pow_ne_zero _ two_ne_zero
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hD, h⟩⟩

variable (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)

include hFour hDiscrete in
/-- **Covering.**  Every member of the star of a discrete four-valent regrowth presents a
nonsingular member of Equation (1)'s family at its own pairing: the member's datum is
isomorphic to the uniform expansion at that pairing, which is the family member, and the
multiplicity of an honest labelling is an isomorphism invariant. -/
theorem det_ne_zero_index (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other w) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (lab w hy star (index hFour star other iso)).presentation).det ≠ 0 := by
  have e : GeometricDatumIso other.frame.data (datum w hy star (index hFour star other iso)) :=
    ((normIso hFour hDiscrete star other iso).trans (transIso hFour star other iso)).trans
      (UniformExpansionRecognition.ofEq (datum_eq_expansion w hy star hDiscrete _).symm)
  have habs := GeometricMultiplicity.absMult_eq_of_datumIso e other.frame.fullDim.connected
    other.frame.fullDim.labelling (lab w hy star (index hFour star other iso))
  rw [← absMult_ne_zero_iff, habs, absMult_ne_zero_iff]
  exact other.frame.fullDim.det_ne_zero

end Cover

/-! ## 4.  The star clause at every discrete four-valent regrowth -/

section Assembly

/-- **`hstar` at every discrete four-valent regrowth, with no further hypothesis.**
The star is the set of pairings at which Equation (1)'s member is nonsingular
(`partialStarEquiv`), each such member is a star candidate (`candidate`), and the
singular members contribute zero to Equation (1). -/
theorem starParityAt_of_discrete (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)
    (hDiscrete : w.limit.vertexPartition (mergeVertex w) = SheetPartition.discrete degree) :
    RegrowthWallInput.StarParityAt hy w := by
  let star : FourStar (w.frame.limitTarget w.column) (mergeVertex w) := FourStar.of_card hFour
  exact even_card_starClass_odd_partial hFour hDiscrete star
    (fun q ↦ (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0)
    (candidate w hy star hDiscrete) (det_ne_zero_index w hy star hDiscrete hFour)
    (fun q ↦ signedMult (lab w hy star q).presentation) (fun _ _ ↦ rfl)
    (fun q hq ↦ by
      simp only [not_not] at hq
      unfold signedMult
      rw [hq, mul_zero])
    (RegrowthWallInput.w4_sum_signedMult_eq_zero w hy star (initial w hy star))

/-- **The residue of `FamilyStarParity … .w4`: the non-discrete four-valent walls.**
*Interface*: equivalent to `RegrowthWallInput.FamilyStarParity degree n p .w4`
(`familyStarParity_w4_iff`). -/
def NonDiscreteW4StarParity (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree),
    (GluingDatum.incidentEdges (mergeVertex w)).card = 4 →
    w.limit.vertexPartition (mergeVertex w) ≠ SheetPartition.discrete degree →
    RegrowthWallInput.StarParityAt hy w

/-- **`FamilyStarParity … .w4` from its non-discrete residue.** -/
theorem familyStarParity_w4_of_nonDiscrete (h : NonDiscreteW4StarParity degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w4 := by
  intro core y hy w cls htag
  have hFour := (RegrowthWallInput.sourceCase_eq_w4_iff cls).mp htag
  by_cases hDiscrete : w.limit.vertexPartition (mergeVertex w) = SheetPartition.discrete degree
  · exact starParityAt_of_discrete w hy hFour hDiscrete
  · exact h core y hy w hFour hDiscrete

/-- **Interface, not progress: the W4 family clause is exactly its non-discrete part.** -/
theorem familyStarParity_w4_iff :
    RegrowthWallInput.FamilyStarParity degree n p .w4 ↔ NonDiscreteW4StarParity degree n p := by
  refine ⟨fun h core y hy w hFour _ ↦ ?_, familyStarParity_w4_of_nonDiscrete⟩
  exact h core y hy w (RegrowthWallInput.classification w hy)
    (RegrowthWallInput.sourceCase_eq_w4 w hy hFour)

/-- The W4 family clause at genus six and degree four, modulo the non-discrete residue. -/
theorem familyStarParity_w4 (h : NonDiscreteW4StarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w4 :=
  familyStarParity_w4_of_nonDiscrete h


/-- **The exact census at a discrete four-valent wall**: the star has as many classes as
Equation (1)'s family has nonsingular members. -/
theorem card_star_eq (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hFour : (GluingDatum.incidentEdges (mergeVertex w)).card = 4)
    (hDiscrete : w.limit.vertexPartition (mergeVertex w) = SheetPartition.discrete degree)
    (star : FourStar (w.frame.limitTarget w.column) (mergeVertex w)) :
    Fintype.card (GeometricStar.Star hy w) = Fintype.card {q : Fin 3 //
      (GluingDatum.LengthMatrixPresentation.matrix (lab w hy star q).presentation).det ≠ 0} :=
  (Fintype.card_congr (partialStarEquiv hFour hDiscrete star _ (candidate w hy star hDiscrete)
    (det_ne_zero_index w hy star hDiscrete hFour))).symm

end Assembly

end DraismaVargas.Count.W4StarParity
