import DraismaVargasCount.W3FourStarCensusProof
import DraismaVargasCount.W3ShiftSixMemberMultiplicity

/-!
# W3Shift star census: Equation (3)'s six members as star classes

Source: Draisma–Vargas Part I, Case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29 and Equation (3).
Balance: the six-member Equation (3) (`W3ShiftSixMemberMultiplicity.sum_signedMult_eq_zero`,
the lemma under `RegrowthBalances.exists_w3Shift_equation3`), over `w.limit` itself.  The
file follows `DraismaVargasCount.W3FourStarCensusProof` (anchoring branch-swapped members;
the family-free side invariant `frameIso_side`) and the census files
`DraismaVargasCount.W3Nd2StarCensusProof` and `DraismaVargasCount.W3Nd3StarCensusProof`.
Stage 2 (exhaustion) is proved in the companion `DraismaVargasCount.W3ShiftStarExhaustionProof`.

## The result, in one paragraph

Equation (3) has six members: for each of the three directions (largest, first, second),
Figure 29's shrink (`k − 1`, Position II.b) and grow (`k + 1`, Position II.a) member, each over
its own **gauge base**, a copy of `w.limit` obtained by two branch swaps (the pair of Part I
lives over a twice-swapped copy and is one of three).  `W3ShiftSixMemberMultiplicity`'s
`constructedPackages` chooses the pairs with `Classical.choice` and so forgets the swaps; this
file re-runs `exists_pairPackage` keeping them, as an `Anchor` (a stable-graph dictionary with
a geometric inverse fixing the target), so every member is an engine position anchored along
the inverse swaps (§1–§3).  Each nonsingular position is then a star member carrying its term
(Stage 1), and distinct nonsingular positions are distinct classes (Stage 3, §4): different
directions by the side invariant `W3FourStarCensusProof.frameIso_side`, the two members of
one direction by their regrown columns
on the moving row (`+1/(k(k−1))` against `−1/(k(k+1))`).  §5–§6 assemble the census and the
family clause from exhaustion, and §7 reduces exhaustion to decoupled transports.

## What is proved

* §1 `Anchor`, `Anchor.swap`, `Anchor.trans`.  §2 `AnchoredPair`, `AnchoredPair.toPair`,
  `exists_anchoredPair`.
* §3 `Setup` and, in its namespace, `P`, `mem`, `E`, `E_row`, `retained`, `baseWall`, `merge`,
  `branchSquare`, `rowSquare`, `engLab`, `Nonsingular`, `fdAt`, `rep`, `multNat_rep`,
  `labelling_engLab`, `signedMult_eq_zero`, **`sum_signedMult`** (Equation (3) in the engine's
  labellings), `integral_signedMult`.
* §4 `isolated`, `right_eq`, `isolated_eq`, `isolated_mem`, `not_rel_of_direction_ne`,
  `matrix_none`, `not_rel_same_direction`, **`rep_eq_of_cls_eq`** (Stage 3).
* §5 `repCls`, `repCls_injective`, `Exhausts`, `census_of_exhaustion`,
  `exhaustion_of_census`, `card_nonsingular_le`, `exhausts_iff_card`,
  `starParityAt_of_exhaustion`.
* §6 **`exists_setup`** (every `w3Shift` regrowth has a setup), `W3ShiftStarCensus`,
  `familyStarParity_w3Shift_of_census`, `W3ShiftStarExhaustion`,
  `w3ShiftStarCensus_of_exhaustion`, `exhaustion_of_w3ShiftStarCensus`,
  `w3ShiftStarExhaustion_iff`, **`familyStarParity_w3Shift_of_exhaustion`**.
* §7 `PositionTransport`, **`exhausts_of_transports`**.

## What is NOT proved here

* **In this file**, Stage 2: `familyStarParity_w3Shift_of_exhaustion` takes
  `W3ShiftStarExhaustion` as its one hypothesis.  It is discharged, with no hypothesis, by
  `W3ShiftStarExhaustionProof.w3ShiftStarExhaustion`; the unconditional clause is
  `W3ShiftStarExhaustionProof.familyStarParity_w3Shift`.
* **Non-vacuity is not shown**: no `w3Shift` wall is exhibited here.  Whether the family
  occurs at genus six is not settled here: the shift arithmetic admits degree four
  (`|A₀| = 3`, `k = (2,2,2)`; `|A₀| = 4`, `{k} = {2,3,3}`), so it is not excluded on
  arithmetic alone.

## Remarks

* The census uses the six-member balance over `w.limit` (the lemma under
  `RegrowthBalances.exists_w3Shift_equation3`), applied to this file's anchored packages,
  rather than the pair balance `RegrowthBalances.exists_w3Shift_balance`: the pair balance,
  over an unrelated `wallDatum`, would not index the star.
* The pair of Part I lives over a twice-branch-swapped copy.  This is why positions are
  anchored (`Anchor.trans` of two `Anchor.swap`s) rather than wall-anchored.
* Different directions are separated by `W3FourStarCensusProof.frameIso_side`
  (`not_rel_of_direction_ne`); the same-direction case uses the regrown column instead
  (`not_rel_same_direction`).

## Consumers

`DraismaVargasCount.W3ShiftStarExhaustionProof`, which gives the unconditional `w3Shift`
clause that `StarSupplyAssembly` uses for the trivalent wall step of
`DraismaVargasCount.Assembly`.
-/

namespace DraismaVargas.Count.W3ShiftStarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open ThirdEquation W3R1SourceProfile
open W3ShiftSourceCandidates W3ShiftSixMemberBalance W3ShiftSixMemberMatrices

/-! ## 1.  Anchors: a stable-graph dictionary with a geometric inverse -/

section Anchor

variable {target : CFGraph} {degree : ℕ}

/-- **An anchor of a gauge copy**: a stable-graph dictionary `G` from a datum to a copy, and
a geometric isomorphism `φ` from the copy back that undoes `G` on branch vertices and on
rows.  Interface: a hypothesis shaper (the data of `W3FourStarCensusProof.GaugeAnchor`
without its Figure 28 column data); inhabited by every sheet relabelling (`Anchor.swap`) and
closed under composition (`Anchor.trans`). -/
structure Anchor (data base : GluingDatum target degree) where
  G : Equivalence data base
  φ : GeometricDatumIso base data
  vertex_eq : ∀ v : BranchVertex data, φ.sourceVertexEquiv (G.vertex v).1 = v.1
  row_back : ∀ (hConnected : base.Connected) (e : NonDanglingEdge base),
    G.row (φ.stablePathEquiv hConnected e.stablePath) = e.stablePath
  /-- The copy has the same target: `φ` fixes every target vertex… -/
  vertex_fix : ∀ v, φ.targetVertex v = v
  /-- …and every target occurrence. -/
  edge_fix : ∀ e, φ.targetEdge e = e

/-- **The branch-swap anchor** (as in `W3FourStarCensusProof.GaugeAnchor.swap`). -/
noncomputable def Anchor.swap {data : GluingDatum target degree}
    (relabeling : data.SheetRelabeling) (hConnected : data.Connected) :
    Anchor data relabeling.apply where
  G := StableGraphIncidence.sheetRelabel relabeling hConnected
  φ := (GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling relabeling)).symm
  vertex_eq := fun v ↦ Subtype.ext (Prod.ext rfl (Equiv.symm_apply_apply _ _))
  row_back := fun hC e ↦ by
    rw [GeometricDatumIso.stablePathEquiv_mk]
    change SheetRelabelStable.stablePathEquiv relabeling hConnected
      (NonDanglingEdge.stablePath _) = _
    rw [SheetRelabelStable.stablePathEquiv_mk]
    apply congrArg NonDanglingEdge.stablePath
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (Equiv.apply_symm_apply _ _)
  vertex_fix _ := rfl
  edge_fix _ := rfl

/-- **Anchors compose.** -/
noncomputable def Anchor.trans {data base base' : GluingDatum target degree}
    (A : Anchor data base) (B : Anchor base base') (hConnected : base.Connected) :
    Anchor data base' where
  G := A.G.trans B.G
  φ := B.φ.trans A.φ
  vertex_eq := fun v ↦ by
    change A.φ.sourceVertexEquiv (B.φ.sourceVertexEquiv (B.G.vertex (A.G.vertex v)).1) = v.1
    rw [B.vertex_eq (A.G.vertex v), A.vertex_eq v]
  row_back := fun hC e ↦ by
    rw [GeometricDatumIso.stablePathEquiv_trans B.φ A.φ hC hConnected, Equiv.trans_apply,
      GeometricDatumIso.stablePathEquiv_mk]
    change B.G.row (A.G.row (A.φ.stablePathEquiv hConnected
      (B.φ.nonDanglingEdgeEquiv hC e).stablePath)) = _
    rw [A.row_back hConnected, ← GeometricDatumIso.stablePathEquiv_mk, B.row_back hC]
  vertex_fix v := by
    change A.φ.targetVertex (B.φ.targetVertex v) = v
    rw [B.vertex_fix, A.vertex_fix]
  edge_fix e := by
    change A.φ.targetEdge (B.φ.targetEdge e) = e
    rw [B.edge_fix, A.edge_fix]

end Anchor

/-! ## 2.  An Equation (3) pair that remembers its gauge -/

section Pair

open W3ShiftClosure W3FourDisjointness

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- **One Figure 29 pair with its anchor**: the fields of
`W3ShiftSixMemberBalance.PairPackage` with the dictionary taken to be the anchor's, so that
the inverse relabelling is remembered.  *Interface*: a hypothesis shaper, strictly stronger
than `PairPackage` (`toPair`); inhabited for every retained orientation
(`exists_anchoredPair`). -/
structure AnchoredPair (shift : ShiftProfile input) where
  base : GluingDatum target degree
  gaugeInput : W3SourceInput base star
  gaugeShift : ShiftProfile gaugeInput
  shrink : ShrinkData gaugeShift
  copy : GaugeCopy input shift gaugeInput gaugeShift
  anchor : Anchor data base
  matrix_map : ∀ (path : W4StableSource.StablePath data) (place : target.edges),
    StableSourceMatrix.matrix base (anchor.G.row path) place =
      StableSourceMatrix.matrix data path place

/-- The underlying pair package. -/
noncomputable def AnchoredPair.toPair {shift : ShiftProfile input} (A : AnchoredPair shift) :
    PairPackage shift :=
  ⟨A.base, A.gaugeInput, A.gaugeShift, A.shrink, A.copy, A.anchor.G, A.matrix_map⟩

/-- **Every orientation carries an anchored pair** (`exists_pairPackage` with its
relabellings kept). -/
theorem exists_anchoredPair (shift : ShiftProfile input)
    (hRetained : RetainedBelow shift)
    (hConnected : graph_connected target) (hGenus : genus target = 0) :
    Nonempty (AnchoredPair shift) := by
  let endpoint := data.vertexPartition wall
  have hEndpoint : endpoint.Refines (data.vertexPartition wall) :=
    SheetPartition.Refines.refl _
  obtain ⟨permFirst, hFixFirst, permSecond, hFixSecond, gaugeInput, gaugeShift,
      copy, hSheet⟩ :=
    exists_gaugeCopy_shrinkSheet_endpoint input shift endpoint hEndpoint
      (StableLocalProperties.refines_of_mem_incidentEdges data shift.firstTarget_mem)
      (StableLocalProperties.refines_of_mem_incidentEdges data shift.secondTarget_mem)
      (shift.movingAnchor_wall_rel.symm.trans shift.firstAnchor_wall_rel)
      (shift.movingAnchor_wall_rel.symm.trans shift.secondAnchor_wall_rel)
      (by simpa [endpoint] using hRetained.1)
      (by simpa [endpoint] using hRetained.2) hConnected hGenus
  obtain ⟨shrink⟩ := exists_shrinkData gaugeShift hSheet
  let firstRelabel := branchSwapOfPerm data wall
    (TargetSeparation.farEndpoint wall shift.firstTarget)
    (TargetSeparation.farEndpoint_ne
      (mem_incidentEdges_ends shift.firstTarget_mem))
    permFirst (fun sheet ↦ hEndpoint.rel (hFixFirst sheet))
  let dataOne := firstRelabel.apply
  let secondRelabel := branchSwapOfPerm dataOne wall
    (TargetSeparation.farEndpoint wall shift.secondTarget)
    (TargetSeparation.farEndpoint_ne
      (mem_incidentEdges_ends shift.secondTarget_mem))
    permSecond (fun sheet ↦
      (refines_clearData_wall data shift.firstTarget shift.firstTarget_mem endpoint
        hEndpoint permFirst hFixFirst).rel (hFixSecond sheet))
  let A : Anchor data secondRelabel.apply :=
    (Anchor.swap firstRelabel input.valid.1).trans
      (Anchor.swap secondRelabel (firstRelabel.valid input.valid).1)
      (firstRelabel.valid input.valid).1
  refine ⟨⟨_, gaugeInput, gaugeShift, shrink, copy, A, ?_⟩⟩
  intro path place
  change StableSourceMatrix.matrix secondRelabel.apply
    (SheetRelabelStable.stablePathEquiv secondRelabel (firstRelabel.valid input.valid).1
      (SheetRelabelStable.stablePathEquiv firstRelabel input.valid.1 path)) place = _
  rw [SheetRelabelStable.matrix_map, SheetRelabelStable.matrix_map]

end Pair

/-! ## 3.  Part I's data at a `w3Shift` regrowth, and Equation (3)'s six anchored members -/

section Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Part I's data at a `w3Shift` regrowth**: the W3 input and the nd3 profile of case
`{w3-r1-nd3-t2-(a>k₄)}`, and one anchored Figure 29 pair per direction.  *Interface*: a
hypothesis shaper, inhabited at every `w3Shift` regrowth (`exists_setup`); the census and
exhaustion are stated for **every** setup. -/
structure Setup (w : Regrowth core y degree) where
  star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)
  input : W3SourceInput w.limit star
  profile : Nd3Profile w.limit input.distinguishedBlock
  directions : profile.first.1.1.1 ≠ profile.second.1.1.1
  largest_lt : w.limit.sourceEdgeIndex profile.largest.1 <
    (w.limit.vertexPartition (mergeVertex w)).blockCard input.distinguishedBlock.1
  pairs : ∀ d : Fin 3, AnchoredPair (orientation profile directions largest_lt d)

namespace Setup

variable {w : Regrowth core y degree} (S : Setup w)

/-- The three pair packages. -/
noncomputable abbrev P : ∀ d : Fin 3, PairPackage (orientation S.profile S.directions
    S.largest_lt d) := fun d ↦ (S.pairs d).toPair

/-- Member `i` of Equation (3). -/
noncomputable abbrev mem (i : MemberIndex) :=
  W3ShiftSixMemberMatrices.member S.P i

/-- Its dictionary from the wall's limit. -/
noncomputable abbrev E (i : MemberIndex) :=
  W3ShiftSixMemberMatrices.memberIncidence S.P i

theorem E_row (i : MemberIndex) : (S.E i).row = W3ShiftSixMemberMatrices.rowEquiv S.P i :=
  W3ShiftSixMemberMatrices.memberIncidence_row S.P i

/-- **Retained columns are the wall's.** -/
theorem retained (i : MemberIndex) (path : StablePath w.limit)
    (place : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix (S.mem i).datum ((S.E i).row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) (S.mem i).right
          (some place)) =
      StableSourceMatrix.matrix w.limit path place := by
  rw [S.E_row]
  exact W3ShiftSixMemberMatrices.commonMatrix_retained S.P i path place

theorem baseWall (d : Fin 3) :
    (S.P d).base.vertexPartition (mergeVertex w) = w.limit.vertexPartition (mergeVertex w) :=
  (S.pairs d).copy.wallPartition

theorem merge (i : MemberIndex) :
    SheetPartition.join
        ((S.mem i).datum.vertexPartition (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)))
        ((S.mem i).datum.vertexPartition (freshVertex (w.frame.limitTarget w.column))) =
      (S.P i.1).base.vertexPartition (mergeVertex w) :=
  M11StarCensusProof.candidate_merge _ ((S.baseWall i.1).trans (M11StarCensusProof.wall_join w))

/-- **The branch square of every member.** -/
theorem branchSquare (i : MemberIndex) :
    StarCensusEngine.BranchSquare w (S.P i.1).base (S.pairs i.1).anchor.φ (E := S.E i) := by
  obtain ⟨d, pos⟩ := i
  intro v
  fin_cases pos
  · have h := W3FourStarCensusProof.graphData_branchSquare
      (W3ShiftGraphData.shrinkRowData (S.P d).shrink (S.P d).gaugeInput.valid)
      ((S.pairs d).anchor.G.vertex v).1
    change (S.pairs d).anchor.φ.sourceVertexEquiv ((S.P d).base.sourceEndpoint
      (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
        ((W3ShiftGraphData.shrinkRowData (S.P d).shrink (S.P d).gaugeInput.valid).branchImage
          ((S.pairs d).anchor.G.vertex v).1).1.1)
      ((W3ShiftGraphData.shrinkRowData (S.P d).shrink (S.P d).gaugeInput.valid).branchImage
          ((S.pairs d).anchor.G.vertex v).1).1.2) = v.1
    rw [h]
    exact (S.pairs d).anchor.vertex_eq v
  · have h := W3FourStarCensusProof.graphData_branchSquare
      (W3ShiftGraphData.growRowData (S.P d).shrink (S.P d).gaugeInput.valid)
      ((S.pairs d).anchor.G.vertex v).1
    change (S.pairs d).anchor.φ.sourceVertexEquiv ((S.P d).base.sourceEndpoint
      (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
        ((W3ShiftGraphData.growRowData (S.P d).shrink (S.P d).gaugeInput.valid).branchImage
          ((S.pairs d).anchor.G.vertex v).1).1.1)
      ((W3ShiftGraphData.growRowData (S.P d).shrink (S.P d).gaugeInput.valid).branchImage
          ((S.pairs d).anchor.G.vertex v).1).1.2) = v.1
    rw [h]
    exact (S.pairs d).anchor.vertex_eq v

/-- **The row square of every member.** -/
theorem rowSquare (i : MemberIndex) :
    StarCensusEngine.RowSquare w (S.P i.1).base (S.pairs i.1).anchor.φ (E := S.E i) := by
  obtain ⟨d, pos⟩ := i
  intro e e' he
  fin_cases pos
  · change (W3ShiftGraphData.shrinkRowData (S.P d).shrink (S.P d).gaugeInput.valid).stablePathEquiv
      ((S.pairs d).anchor.G.row ((S.pairs d).anchor.φ.stablePathEquiv _ e.stablePath)) = _
    refine (congrArg (W3ShiftGraphData.shrinkRowData (S.P d).shrink (S.P d).gaugeInput.valid).stablePathEquiv
      ((S.pairs d).anchor.row_back _ e)).trans ?_
    exact M11StarCensusProof.retainedEdge_stablePath _ _ e e' he
  · change (W3ShiftGraphData.growRowData (S.P d).shrink (S.P d).gaugeInput.valid).stablePathEquiv
      ((S.pairs d).anchor.G.row ((S.pairs d).anchor.φ.stablePathEquiv _ e.stablePath)) = _
    refine (congrArg (W3ShiftGraphData.growRowData (S.P d).shrink (S.P d).gaugeInput.valid).stablePathEquiv
      ((S.pairs d).anchor.row_back _ e)).trans ?_
    exact M11StarCensusProof.retainedEdge_stablePath _ _ e e' he

variable (hy : Nondegenerate y)

/-- The engine's labelling of member `i`, in the wall's coordinates. -/
noncomputable abbrev engLab (i : MemberIndex) :=
  StarCensusEngine.labelling w hy (S.mem i).datum (S.E i)

/-- The nonsingular positions of Equation (3). -/
def Nonsingular (i : MemberIndex) : Prop :=
  (GluingDatum.LengthMatrixPresentation.matrix (S.engLab hy i).presentation).det ≠ 0

/-- The full-dimensional presentation of a nonsingular position, from the regrowth's own
cover along the member's dictionary. -/
noncomputable def fdAt (i : MemberIndex) (h : S.Nonsingular hy i) :
    FullDimensionalSourcePresentation (S.mem i).datum (Fin p) :=
  RegrowthBalances.regrowthPresentation w hy (S.E i)
    ((S.mem i).datum_valid (S.P i.1).gaugeInput.valid)
    ((W3ShiftSixMemberMultiplicity.member_sourceGenus S.P i))
    (S.engLab hy i) h

/-- **The star member of a nonsingular position.** -/
noncomputable def rep (i : MemberIndex) (h : S.Nonsingular hy i) : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy) (E := S.E i) (fd := S.fdAt hy i h)
    (hRetained := S.retained i) (M := (S.P i.1).base) (φ := (S.pairs i.1).anchor.φ)
    (hMerge := S.merge i) (hOld := M11StarCensusProof.candidate_old _)
    (hEdge := M11StarCensusProof.candidate_edge _) (S.branchSquare i) (S.rowSquare i)

theorem multNat_rep (i : MemberIndex) (h : S.Nonsingular hy i) :
    (GeometricStar.Star.toFibre (S.rep hy i h).cls).multNat =
      (signedMult (S.engLab hy i).presentation).num.natAbs := rfl

/-- **Equation (3)'s common coordinates, selected at any member with its engine labelling,
are the engine labellings of all six.** -/
theorem labelling_engLab (sel i : MemberIndex) :
    W3ShiftSixMemberMatrices.labelling S.P sel (S.engLab hy sel) i = S.engLab hy i := by
  unfold W3ShiftSixMemberMatrices.labelling
  congr 1
  · ext x
    simp [W3ShiftSixMemberMatrices.targetCoordinates, StarCensusEngine.labelling]
  · ext x
    simp [W3ShiftSixMemberMatrices.sourceCoordinates, StarCensusEngine.labelling, S.E_row]

/-- A singular position contributes `0`. -/
theorem signedMult_eq_zero (i : MemberIndex) (h : ¬ S.Nonsingular hy i) :
    signedMult (S.engLab hy i).presentation = 0 := by
  unfold Nonsingular at h
  rw [not_not] at h
  unfold signedMult
  rw [h, mul_zero]

/-- **Equation (3) in the engine's labellings.** -/
theorem sum_signedMult : ∑ i : MemberIndex, signedMult (S.engLab hy i).presentation = 0 := by
  by_cases hEx : ∃ i, S.Nonsingular hy i
  · obtain ⟨i₀, h₀⟩ := hEx
    have h := W3ShiftSixMemberMultiplicity.sum_signedMult_eq_zero S.P
      (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w) i₀
      (S.fdAt hy i₀ h₀)
    have hLab : (S.fdAt hy i₀ h₀).labelling = S.engLab hy i₀ := rfl
    simp only [hLab, S.labelling_engLab hy] at h
    exact h
  · push Not at hEx
    exact Finset.sum_eq_zero fun i _ ↦ S.signedMult_eq_zero hy i (fun h ↦ hEx i h)

/-- **Every term of Equation (3) is an integer.** -/
theorem integral_signedMult (i : MemberIndex) :
    ∃ value : ℤ, signedMult (S.engLab hy i).presentation = (value : ℚ) := by
  by_cases h : S.Nonsingular hy i
  · exact isIntegralMultiplicity (S.fdAt hy i h)
  · exact ⟨0, by rw [S.signedMult_eq_zero hy i h, Int.cast_zero]⟩

end Setup

end Setup

/-! ## 4.  Separation (Stage 3)

Members of different directions isolate different wall occurrences on the divalent side
(`W3FourStarCensusProof.frameIso_side`).  The two members of one direction have regrown
columns that differ on the moving row: `+1/(k(k−1))` against `−1/(k(k+1))`
(`W3ShiftMultiplicityBalance.newColumn_eq`). -/

namespace Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w) (hy : Nondegenerate y)

/-- The direction member `i` isolates on the divalent side. -/
noncomputable abbrev isolated (i : MemberIndex) : (w.frame.limitTarget w.column).edges :=
  (orientation S.profile S.directions S.largest_lt i.1).movingTarget

theorem right_eq (i : MemberIndex) :
    (S.mem i).right = W3Nd2SourceCandidates.rightOf (S.isolated i) := by
  obtain ⟨d, pos⟩ := i
  have hMove := (S.pairs d).copy.movingTarget
  fin_cases pos
  · change W3Nd2SourceCandidates.rightOf (S.P d).gaugeShift.movingTarget = _
    exact congrArg _ hMove
  · change W3Nd2SourceCandidates.rightOf (S.P d).gaugeShift.movingTarget = _
    exact congrArg _ hMove

theorem isolated_eq (i : MemberIndex) :
    S.isolated i = ![S.profile.largest.1.1.1, S.profile.first.1.1.1,
      S.profile.second.1.1.1] i.1 := by
  obtain ⟨d, pos⟩ := i
  fin_cases d <;> rfl

theorem isolated_mem (i : MemberIndex) :
    S.isolated i ∈ GluingDatum.incidentEdges (mergeVertex w) :=
  (orientation S.profile S.directions S.largest_lt i.1).movingTarget_mem

/-- **Members of different directions are never frame isomorphic.** -/
theorem not_rel_of_direction_ne {i j : MemberIndex} (hi : S.Nonsingular hy i)
    (hj : S.Nonsingular hy j) (hne : i.1 ≠ j.1) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (S.rep hy i hi).member.frame
      (S.rep hy j hj).member.frame) := by
  rintro ⟨fi⟩
  have hSide := W3FourStarCensusProof.frameIso_side (hy := hy) (S.retained i) (S.retained j) fi
  rw [S.right_eq i, S.right_eq j] at hSide
  have hL : S.profile.first.1.1.1 ≠ S.profile.largest.1.1.1 := S.profile.first_target_ne
  have hL2 : S.profile.second.1.1.1 ≠ S.profile.largest.1.1.1 := S.profile.second_target_ne
  have hD : S.profile.first.1.1.1 ≠ S.profile.second.1.1.1 := S.directions
  have m0 : S.profile.largest.1.1.1 ∈ GluingDatum.incidentEdges (mergeVertex w) :=
    S.isolated_mem (0, 0)
  have m1 : S.profile.first.1.1.1 ∈ GluingDatum.incidentEdges (mergeVertex w) :=
    S.isolated_mem (1, 0)
  have m2 : S.profile.second.1.1.1 ∈ GluingDatum.incidentEdges (mergeVertex w) :=
    S.isolated_mem (2, 0)
  obtain ⟨di, pi⟩ := i
  obtain ⟨dj, pj⟩ := j
  simp only at hne hSide
  fin_cases di <;> fin_cases dj
  · exact hne rfl
  · exact W3FourStarCensusProof.false_of_side_rightOf m0 m2 hL.symm hL2 hD.symm hSide
  · exact W3FourStarCensusProof.false_of_side_rightOf m0 m1 hL2.symm hL hD hSide
  · exact W3FourStarCensusProof.false_of_side_rightOf m1 m2 hL hD.symm hL2 hSide
  · exact hne rfl
  · exact W3FourStarCensusProof.false_of_side_rightOf m1 m0 hD hL.symm hL2.symm hSide
  · exact W3FourStarCensusProof.false_of_side_rightOf m2 m1 hL2 hD hL hSide
  · exact W3FourStarCensusProof.false_of_side_rightOf m2 m0 hD.symm hL2.symm hL.symm hSide
  · exact hne rfl

/-- A member's regrown column, read at the wall's rows, is Equation (3)'s common one. -/
theorem matrix_none (i : MemberIndex) (path : StablePath w.limit) :
    StableSourceMatrix.matrix (S.mem i).datum ((S.E i).row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) (S.mem i).right none) =
      W3ShiftSixMemberMatrices.commonMatrix S.P i path none := by
  rw [S.E_row]
  rfl

/-- **The two members of one direction are never frame isomorphic.** -/
theorem not_rel_same_direction (d : Fin 3) (h0 : S.Nonsingular hy (d, 0))
    (h1 : S.Nonsingular hy (d, 1)) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (S.rep hy (d, 0) h0).member.frame
      (S.rep hy (d, 1) h1).member.frame) := by
  rintro ⟨fi⟩
  set q := W3ShiftHonestBalance.movingRow (S.P d).gaugeShift
  have hNew := StarCensusEngine.frameIso_matrix_new (S.retained (d, 0)) (S.retained (d, 1)) fi
    ((S.pairs d).anchor.G.row.symm q)
  rw [S.matrix_none, S.matrix_none] at hNew
  have h0' := W3ShiftMultiplicityBalance.newColumn_eq (S.P d).shrink
    (S.P d).gaugeInput.valid 0 q
  have h1' := W3ShiftMultiplicityBalance.newColumn_eq (S.P d).shrink
    (S.P d).gaugeInput.valid 1 q
  change W3ShiftGraphData.commonMatrix (S.P d).shrink (S.P d).gaugeInput.valid 1
      ((S.pairs d).anchor.G.row ((S.pairs d).anchor.G.row.symm q)) none =
    W3ShiftGraphData.commonMatrix (S.P d).shrink (S.P d).gaugeInput.valid 0
      ((S.pairs d).anchor.G.row ((S.pairs d).anchor.G.row.symm q)) none at hNew
  have hq : (S.pairs d).anchor.G.row ((S.pairs d).anchor.G.row.symm q) = q :=
    Equiv.apply_symm_apply _ _
  simp only [hq] at hNew
  rw [h0', h1', if_pos rfl, if_pos rfl] at hNew
  have hk := (S.P d).gaugeShift.two_le_moving
  have hkq : (2 : ℚ) ≤ (W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) := by exact_mod_cast hk
  simp only [W3ShiftMultiplicityBalance.correctionSign, W3ShiftMultiplicityBalance.factor,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hNew
  have hk' : 2 ≤ W3ShiftMultiplicityBalance.incomingIndex (shift := (S.P d).gaugeShift) := hk
  rw [Nat.cast_sub (by omega), Nat.cast_add] at hNew
  push_cast at hNew
  have hpos1 : (0 : ℚ) < (W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) * ((W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) + 1) := by positivity
  have hpos0 : (0 : ℚ) < (W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) * ((W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) - 1) := by nlinarith
  have hA : (0 : ℚ) < 1 / ((W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) * ((W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) - 1)) := by positivity
  have hB : (0 : ℚ) < 1 / ((W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) * ((W3ShiftMultiplicityBalance.incomingIndex
      (shift := (S.P d).gaugeShift) : ℚ) + 1)) := by positivity
  rw [neg_div] at hNew
  linarith

/-- **Distinct nonsingular positions are distinct star classes** (Stage 3). -/
theorem rep_eq_of_cls_eq (i : MemberIndex) (hi : S.Nonsingular hy i) (j : MemberIndex)
    (hj : S.Nonsingular hy j) (h : (S.rep hy i hi).cls = (S.rep hy j hj).cls) : i = j := by
  have hRel : Nonempty (GeometricSegmentWalls.FrameIso (S.rep hy i hi).member.frame
      (S.rep hy j hj).member.frame) := Quotient.exact h
  by_cases hd : i.1 = j.1
  · obtain ⟨di, pi⟩ := i
    obtain ⟨dj, pj⟩ := j
    simp only at hd
    subst hd
    fin_cases pi <;> fin_cases pj
    · rfl
    · exact (S.not_rel_same_direction hy di hi hj hRel).elim
    · exact (S.not_rel_same_direction hy di hj hi (hRel.elim fun fi ↦ ⟨fi.symm⟩)).elim
    · rfl
  · exact (S.not_rel_of_direction_ne hy hi hj hd hRel).elim

end Setup

/-! ## 5.  The census at one wall -/

namespace Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w) (hy : Nondegenerate y)

/-- The positions' classes, from the nonsingular positions to the star. -/
noncomputable def repCls (i : {i : MemberIndex // S.Nonsingular hy i}) :
    GeometricStar.Star hy w :=
  (S.rep hy i.1 i.2).cls

theorem repCls_injective : Function.Injective (S.repCls hy) :=
  fun a b h ↦ Subtype.ext (S.rep_eq_of_cls_eq hy a.1 a.2 b.1 b.2 h)

/-- **Exhaustion at one wall** (Stage 2 (b)).  *Interface*: equivalent to the
census at this wall (`census_of_exhaustion`, `exhaustion_of_census`) and to a count
(`exhausts_iff_card`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ i : MemberIndex, ∃ hi : S.Nonsingular hy i,
    member.cls = (S.rep hy i hi).cls

/-- **The W3Shift census at one wall from exhaustion.** -/
theorem census_of_exhaustion (hExh : S.Exhausts hy) :
    ∃ e : {i : MemberIndex // S.Nonsingular hy i} ≃ GeometricStar.Star hy w,
      ∀ i, (GeometricStar.Star.toFibre (e i)).multNat =
        (signedMult (S.engLab hy i.1).presentation).num.natAbs := by
  refine ⟨Equiv.ofBijective _ ⟨S.repCls_injective hy, ?_⟩,
    fun i ↦ S.multNat_rep hy i.1 i.2⟩
  refine Quotient.ind ?_
  intro member
  obtain ⟨i, hi, h⟩ := hExh member
  exact ⟨⟨i, hi⟩, h.symm⟩

/-- **Interface: the census implies exhaustion.** -/
theorem exhaustion_of_census
    (e : {i : MemberIndex // S.Nonsingular hy i} ≃ GeometricStar.Star hy w) :
    S.Exhausts hy := by
  classical
  have hBij : Function.Bijective (S.repCls hy) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨S.repCls_injective hy, Fintype.card_congr e⟩
  intro member
  obtain ⟨i, hi⟩ := hBij.2 member.cls
  exact ⟨i.1, i.2, hi.symm⟩

/-- **Stages 1 and 3 inject the nonsingular positions into the star**, unconditionally. -/
theorem card_nonsingular_le :
    Nat.card {i : MemberIndex // S.Nonsingular hy i} ≤ Nat.card (GeometricStar.Star hy w) :=
  Nat.card_le_card_of_injective _ (S.repCls_injective hy)

theorem exhausts_iff_card :
    S.Exhausts hy ↔
      Nat.card (GeometricStar.Star hy w) = Nat.card {i : MemberIndex // S.Nonsingular hy i} := by
  classical
  constructor
  · intro hExh
    obtain ⟨e, -⟩ := S.census_of_exhaustion hy hExh
    exact (Nat.card_congr e).symm
  · intro hCard
    refine S.exhaustion_of_census hy (Fintype.equivOfCardEq ?_)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hCard]

/-- **The star clause at one wall from exhaustion.** -/
theorem starParityAt_of_exhaustion (hExh : S.Exhausts hy) :
    RegrowthWallInput.StarParityAt hy w := by
  obtain ⟨e, hmult⟩ := S.census_of_exhaustion hy hExh
  exact StarCensusEngine.starParityAt_of_census
    (fun i ↦ signedMult (S.engLab hy i).presentation) (S.integral_signedMult hy)
    (S.sum_signedMult hy) (S.Nonsingular hy) (S.signedMult_eq_zero hy) e hmult

end Setup

/-! ## 6.  The family clause -/

section Family

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Every `w3Shift` regrowth carries a setup**: the classification's `shift` constructor,
and one anchored pair per direction (`exists_anchoredPair`). -/
theorem exists_setup (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w3Shift) : Nonempty (Setup w) := by
  cases cls with
  | w4 => cases htag
  | w2 _ _ profile => cases profile <;> cases htag
  | w3 star input classification =>
    cases classification with
    | four => cases htag
    | nd3CoarseFine => cases htag
    | nd2CoarseFine => cases htag
    | shift profile directions largest_lt _ =>
      have hRetained := W3ShiftClosure.retainedBelow_of_largest_lt profile directions largest_lt
      have hPair (d : Fin 3) :
          Nonempty (AnchoredPair (orientation profile directions largest_lt d)) := by
        fin_cases d
        · exact exists_anchoredPair _ hRetained.1 (W4StarParity.limitTarget_connected w)
            (W4StarParity.limitTarget_genus w)
        · exact exists_anchoredPair _ hRetained.2.1 (W4StarParity.limitTarget_connected w)
            (W4StarParity.limitTarget_genus w)
        · exact exists_anchoredPair _ hRetained.2.2 (W4StarParity.limitTarget_connected w)
            (W4StarParity.limitTarget_genus w)
      exact ⟨{ star := star, input := input, profile := profile, directions := directions
               largest_lt := largest_lt, pairs := fun d ↦ Classical.choice (hPair d) }⟩

/-- **The W3Shift star census.**  At every `w3Shift` regrowth, for every setup, the star is
in bijection with Equation (3)'s nonsingular positions, each class carrying its term.
*Interface*: equivalent to `W3ShiftStarExhaustion` (`w3ShiftStarExhaustion_iff`). -/
def W3ShiftStarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Shift →
    ∀ S : Setup w,
      ∃ e : {i : MemberIndex // S.Nonsingular hy i} ≃ GeometricStar.Star hy w,
        ∀ i, (GeometricStar.Star.toFibre (e i)).multNat =
          (signedMult (S.engLab hy i.1).presentation).num.natAbs

variable {degree n p : ℕ}

/-- **`FamilyStarParity … .w3Shift` from the census**: Equation (3) read mod two. -/
theorem familyStarParity_w3Shift_of_census (h : W3ShiftStarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w3Shift := by
  intro core y hy w cls htag
  obtain ⟨S⟩ := exists_setup w cls htag
  obtain ⟨e, hmult⟩ := h core y hy w cls htag S
  exact StarCensusEngine.starParityAt_of_census
    (fun i ↦ signedMult (S.engLab hy i).presentation) (S.integral_signedMult hy)
    (S.sum_signedMult hy) (S.Nonsingular hy) (S.signedMult_eq_zero hy) e hmult

/-- **Stage 2 (exhaustion), family-wide.**  *Interface*: equivalent to `W3ShiftStarCensus`
(`w3ShiftStarExhaustion_iff`). -/
def W3ShiftStarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w3Shift → ∀ S : Setup w, S.Exhausts hy

theorem w3ShiftStarCensus_of_exhaustion (hExh : W3ShiftStarExhaustion degree n p) :
    W3ShiftStarCensus degree n p :=
  fun core y hy w cls htag S ↦ S.census_of_exhaustion hy (hExh core y hy w cls htag S)

theorem exhaustion_of_w3ShiftStarCensus (hCensus : W3ShiftStarCensus degree n p) :
    W3ShiftStarExhaustion degree n p :=
  fun core y hy w cls htag S ↦
    S.exhaustion_of_census hy (hCensus core y hy w cls htag S).choose

theorem w3ShiftStarExhaustion_iff :
    W3ShiftStarExhaustion degree n p ↔ W3ShiftStarCensus degree n p :=
  ⟨w3ShiftStarCensus_of_exhaustion, exhaustion_of_w3ShiftStarCensus⟩

/-- **The `w3Shift` clause of `FamilyStarParity` at genus six and degree four, modulo
Stage 2's exhaustion alone.** -/
theorem familyStarParity_w3Shift_of_exhaustion
    (hExh : W3ShiftStarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Shift :=
  familyStarParity_w3Shift_of_census (w3ShiftStarCensus_of_exhaustion hExh)

end Family

/-! ## 7.  Stage 2 reduced to decoupled transports onto the six anchored positions -/

namespace Setup

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w) (hy : Nondegenerate y)

/-- **What a member must present to be received at position `i`**: a decoupled
transport, along its limit isomorphism followed by the position's inverse anchor (the
inverse of the two branch swaps), from its own normal form at some placement onto the
position's pasted resolution. -/
def PositionTransport (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : W3Nd2StarCensusProof.PlacementSpec other placement) (i : MemberIndex) :
    Type :=
  ResolutionExpansionFree.TransportFree (ψ.datum.trans (S.pairs i.1).anchor.φ.symm)
    (mergeVertex other) (mergeVertex w) placement (S.mem i).right
    (W3Nd2StarCensusProof.memberResolution other placement hPlacement)
    (M11StarCensusProof.pasted (S.mem i))

/-- **Stage 2 reduced to transports.** -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w,
      ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
      ∃ hPlacement : W3Nd2StarCensusProof.PlacementSpec member.member placement,
      ∃ i : MemberIndex, ∃ _ : S.Nonsingular hy i,
        Nonempty (S.PositionTransport hy member.member ψ placement hPlacement i)) :
    S.Exhausts hy := by
  intro member
  obtain ⟨ψ, placement, hPlacement, i, hi, ⟨t⟩⟩ := h member
  refine ⟨i, hi, ?_⟩
  have hNV := M11WallExhaustion.sourceVertexMap_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  have hNE := M11WallExhaustion.retainedSourceEdge_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
    (E := S.E i) (fd := S.fdAt hy i hi) (hRetained := S.retained i) (M := (S.P i.1).base)
    (φ := (S.pairs i.1).anchor.φ) (hMerge := S.merge i)
    (hOld := M11StarCensusProof.candidate_old _) (hEdge := M11StarCensusProof.candidate_edge _)
    (S.branchSquare i) (S.rowSquare i)
    (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _ (S.mem i).exterior)
    rfl member ψ (W3Nd2StarCensusProof.memberNorm member.member placement hPlacement)
    hNV hNE t

end Setup

end DraismaVargas.Count.W3ShiftStarCensusProof
