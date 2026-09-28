import DraismaVargasCount.StarCensusEngine
import DraismaVargasCount.M11LoopWall
import DraismaVargas.LocalCases.NonTrivalentValencyThreeStarCount
import DraismaVargasCount.PassOnceLollipopWitness

/-!
# The M-11 star census, Stages 1 and 3, and loop walls

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-M-11}`, Figure 32
and Equation (6); Vargas, Part II (arXiv:2609.09109): the star of a wall and
`prop-signed-mult`, the pass-once condition (`def-auxiliary-conditions`,
`lm:properties`) and the lollipop rows (`lm:bridge-and-loop`).  The census engine is
`StarCensusEngine`.

## The result, in one paragraph

`M11StarParityFree.M11StarCensus` (the residue of the `w2M11` clause) splits into
(a) every nonsingular position of Equation (6) is a star class, (b) every star class is a
position, (c) distinct positions are distinct classes.  **(a) and (c) are proved here, at
every core, degree and positive request, with no hypothesis**, and (b) is isolated as the
single residue `M11StarExhaustion`, which is *equivalent* to the census
(`m11StarExhaustion_iff`) and is proved in `M11StarExhaustionProof`.  On the way,
**loop walls are ruled out** (`not_sameDoubleRow_of_regrowth`): the hypothesis `hCol` of
`M11LoopWall.false_of_loopColumn` is discharged, so
`M11StarParityFree.loop_parity_defect` has no instance at a regrowth.

## What is proved

* **Stage 1 (a).**  `member0`, `member1`, `member2`: Equation (6)'s three positions as
  members of the wall's star, each for *any* full-dimensional presentation of its datum.
  Positions `0` and `2` are wall-anchored; position `1` (Figure 32's remote split) is
  anchored at the branch-swapped datum `M11RemoteCandidates.swappedDatum` and carried to
  the wall by `M11StarParityFree.branchIso.symm` (`remote_branchSquare`,
  `remote_rowSquare`).  `rep` selects the member of each nonsingular position (its
  presentation transported from the census's own incoming one, `fdAt`), and `multNat_rep`
  identifies its class multiplicity with `|num (signedMult (lab q))|`.
* **Stage 3 (c).**  `not_rel_02`, `not_rel_12` (split and joined positions differ in the
  valencies `1,3` / `2,2` of the regrown occurrence's ends), `not_rel_01` (the two split
  positions differ in their regrown column `2 e_{h₀}` / `2 e_{h₁}` off a loop wall);
  `rep_eq_of_cls_eq`, `repCls_injective`.
* **Loop walls.**  `two_le_incidenceCount`, `loopRow_lollipop`,
  `split_false`, `remote_false`, `joined_false`, `not_sameDoubleRow`,
  `not_sameDoubleRow_of_regrowth`: at a loop wall the loop row of any full-dimensional
  family member is a lollipop row with exactly two occurrences; a split member puts a third
  (regrown) occurrence on it, and at the joined member its leaf edge is a retained wall
  column `2 e_h`, contradicting `M11LoopWall.false_of_loopColumn`.
* **Stage 2 reduced to transports.**  `pinned`, `PositionTransport`, `memberNV`,
  `memberNE`, `exhausts_of_transports`: if every star member presents a decoupled
  transport (`ResolutionExpansionFree.TransportFree`) from its own normal form onto some
  nonsingular position -- along its limit isomorphism composed with the position's anchor
  inverse, so along the branch swap at position `1` -- the star is exhausted.  The
  obstruction to wall-anchored candidates recorded in `M11StarParityFree` concerns
  wall-anchored indices only and does not apply at the anchored position `1`.
* **Assembly.**  `census_of_exhaustion`, `exhaustion_of_census` (per wall);
  `M11StarExhaustion`, `m11StarCensus_of_exhaustion`, `exhaustion_of_m11StarCensus`,
  `m11StarExhaustion_iff`, `familyStarParity_w2M11_of_exhaustion` (the `w2M11` family
  clause, modulo `M11StarExhaustion` alone).
* **Non-vacuity.**  `nonsingular_incoming`: the incoming position is nonsingular, so
  every census has at least one class.

## What is NOT proved here (every hypothesis, explicitly)

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2M11` is not proved here.**  Its exact
  residue is `M11StarExhaustion` (Stage 2 (b)): every star member is a frame isomorph
  of some nonsingular position.  It is equivalent to `M11StarParityFree.M11StarCensus`
  (`m11StarExhaustion_iff`), so it is neither weaker nor stronger than the census, and
  it is proved in `M11StarExhaustionProof`.  Computer experiments with genus-six M-11
  walls are consistent with the census: every wall seen has at most three classes and
  a balanced near/far split.
* **What Stage 2 needs** (the hypothesis of `exhausts_of_transports`, not proved here): for a
  star member `m` with limit isomorphism `ψ`,
  (i) a W2 input and M-11 profile on `m.limit`, transported from the wall's along `ψ⁻¹`
  (`LocalCases.W2SourceTransport` transports them along a *sheet relabelling* only, not
  along a general `GeometricDatumIso`); (ii) Part I's identification
  (`M11IncomingMatching.exists_matching`) at `m`, which places `m` at position `0` or `2`
  **of its own family**; (iii) the coherence dichotomy: `m`'s own position `0` is the
  wall's position `0` or `1` according to whether `ψ`'s two occurrence permutations agree
  on the M-11 block; (iv) the resulting
  `PositionTransport` (a `ResolutionExpansionFree.TransportFree`, with representative
  gauge alignment of the three relabel fields).  Everything downstream of (iv) is proved
  (`exhausts_of_transports`, via the anchored `StarCensusEngine.cls_eq_of_transport`).
* Nothing here is specific to particular block sizes; nothing about other families.

## Tempting inferences, checked

* (i) *"Position 1's datum is the branch-swapped member, and `branchIso.symm` composed
  with the wall's limit iso is a legitimate `GeometricStar.LimitIso`."*  **Holds**:
  `member1`'s limit isomorphism is the literal contraction onto `swappedDatum` followed
  by `branchIso.symm`, and both inherited-label squares are proved (`remote_branchSquare`,
  `remote_rowSquare`: `branchIso` and `M11StableGraphs.remote` are the same literal sheet
  relabelling).
* (ii) *"Stage 2 reuses Part I's member identification at M-11 walls, which already says
  every incoming datum at an M-11 wall is a family member -- only the gauge bookkeeping is
  new."*  **False as stated.**  `M11IncomingMatching.exists_matching` identifies an
  incoming datum with position `0` or `2` *of the family built on its own contraction and
  its own profile* (and never with position `1`, which it records as "an essential
  outgoing alternative").  Applied to a star member it needs a profile on the member's
  limit (a transport along a general limit isomorphism, not proved here), and it lands the
  member at the wall's position `0` **or** `1` according to the coherence of its limit
  isomorphism -- not a gauge choice but the invariant that `not_rel_01` separates.
* Ruling out loop walls through `hCol` (`¬SameDoubleRow`): **holds**:
  `hCol` is needed only at the joined member; at a split member the lollipop row count
  (`PassOnceLollipopWitness.card_rowEdges_eq_two_of_loopRow`) already contradicts.

## Consumers

`M11StarExhaustionProof`, and through it the `w2M11` clause of the star parity (step 2
of `Assembly`).
-/

namespace DraismaVargas.Count.M11StarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open M11SourceCandidates

/-! ## 1.  Figure 32's members over an arbitrary datum: the anchor conditions -/

section Local

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}

/-- The pasted resolution of a blockwise candidate. -/
noncomputable abbrev pasted (c : BalancedGlobal.Candidate target degree data wall) :=
  ResolutionM11.LocalResolution.paste (data.vertexPartition wall) c.resolution c.contracts

theorem pasted_contracts (c : BalancedGlobal.Candidate target degree data wall) :
    (pasted c).ContractsTo (data.vertexPartition wall) :=
  ResolutionM11.LocalResolution.paste_contracts (data.vertexPartition wall) c.resolution
    c.contracts

theorem candidate_fresh (c : BalancedGlobal.Candidate target degree data wall) :
    c.datum.vertexPartition (freshVertex target) = (pasted c).right :=
  GlobalResolution.datum_vertexPartition_fresh _ _ _ _
    (GlobalAssembly.blockwiseCompatible data wall c.right c.resolution c.contracts c.exterior)

theorem candidate_oldWall (c : BalancedGlobal.Candidate target degree data wall) :
    c.datum.vertexPartition (oldVertex target wall) = (pasted c).left :=
  GlobalResolution.datum_vertexPartition_old_wall _ _ _ _
    (GlobalAssembly.blockwiseCompatible data wall c.right c.resolution c.contracts c.exterior)

/-- The fresh endpoint of any blockwise candidate refines the wall partition. -/
theorem candidate_fresh_refines (c : BalancedGlobal.Candidate target degree data wall) :
    (c.datum.vertexPartition (freshVertex target)).Refines (data.vertexPartition wall) := by
  rw [candidate_fresh]
  exact (pasted_contracts c).right_refines

/-- …and so does the retained copy of the wall. -/
theorem candidate_oldWall_refines (c : BalancedGlobal.Candidate target degree data wall) :
    (c.datum.vertexPartition (oldVertex target wall)).Refines (data.vertexPartition wall) := by
  rw [candidate_oldWall]
  exact (pasted_contracts c).left_refines

theorem candidate_old (c : BalancedGlobal.Candidate target degree data wall) (vertex : target.V)
    (hne : vertex ≠ wall) :
    c.datum.vertexPartition (oldVertex target vertex) = data.vertexPartition vertex :=
  GlobalResolution.datum_vertexPartition_old_of_ne _ _ _ _ _
    (GlobalAssembly.blockwiseCompatible data wall c.right c.resolution c.contracts c.exterior) hne

theorem candidate_edge (c : BalancedGlobal.Candidate target degree data wall)
    (edge : target.edges) :
    c.datum.edgePartition (occurrenceEquiv target wall c.right (some edge)) =
      data.edgePartition edge :=
  GlobalResolution.datum_edgePartition_old _ _ _ _
    (GlobalAssembly.blockwiseCompatible data wall c.right c.resolution c.contracts c.exterior) _

/-- Every expanded vertex refines the base partition at its contraction. -/
theorem candidate_refines (c : BalancedGlobal.Candidate target degree data wall)
    (place : Vertex target) :
    (c.datum.vertexPartition place).Refines
      (data.vertexPartition (contractVertex target wall place)) := by
  rcases place with vertex | fresh
  · by_cases hne : vertex = wall
    · subst hne
      exact candidate_oldWall_refines c
    · rw [show (Sum.inl vertex : Vertex target) = oldVertex target vertex from rfl,
        candidate_old c vertex hne]
      exact SheetPartition.Refines.refl _
  · cases fresh
    exact candidate_fresh_refines c

/-- **`hMerge` for a blockwise candidate** at a wall whose merged partition is a
constructed join (as at every contracted limit). -/
theorem candidate_merge (c : BalancedGlobal.Candidate target degree data wall)
    {a b : SheetPartition degree} (hWall : data.vertexPartition wall = SheetPartition.join a b) :
    SheetPartition.join (c.datum.vertexPartition (oldVertex target wall))
        (c.datum.vertexPartition (freshVertex target)) = data.vertexPartition wall := by
  rw [candidate_oldWall, candidate_fresh, hWall]
  apply StarCensusEngine.join_eq_of_isJoin_join
  rw [← hWall]
  exact pasted_contracts c

/-- The row of a retained occurrence is the row of any occurrence with the same literal
place and sheet. -/
theorem retainedEdge_stablePath (c : BalancedGlobal.Candidate target degree data wall)
    (hConnected : data.Connected) (e : NonDanglingEdge data) (e' : NonDanglingEdge c.datum)
    (he : e'.1.1 = (occurrenceEquiv target wall c.right (some e.1.1.1), e.1.1.2)) :
    (ResolutionAwayFromWall.retainedEdge c hConnected e).stablePath = e'.stablePath :=
  congrArg NonDanglingEdge.stablePath (Subtype.ext (Subtype.ext he.symm))

variable {star : W2R1Target.TwoStar target wall}
  (input : SecondEquation.W2SourceInput data star) {block : W4Assembly.WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-- **The branch square of the first split** (Figure 32, position `0`): the incidence
equivalence sends each branch to a source vertex whose contraction is that branch. -/
theorem split_branchSquare (v : BranchVertex data) :
    data.sourceEndpoint
        (contractVertex target wall
          ((M11SplitStableGraph.equivalence input profile hCard).vertex v).1.1.1)
        ((M11SplitStableGraph.equivalence input profile hCard).vertex v).1.1.2 = v.1 := by
  by_cases hAt : v.1.1.1 = wall
  · have hv := M11SplitVertices.oldBranch_eq_selected input profile v hAt
    have hE : (M11SplitStableGraph.equivalence input profile hCard).vertex v =
        M11SplitVertices.selectedNewBranch input profile hCard :=
      M11SplitVertices.branchVertexMap_of_wall input profile hCard v hAt
    rw [hE]
    change data.sourceEndpoint (contractVertex target wall
        ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint
          (freshVertex target) profile.third.1.1.2).1.1)
        ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint
          (freshVertex target) profile.third.1.1.2).1.2 = v.1
    rw [StarCensusEngine.sourceEndpoint_contract _ data _ _
      (candidate_refines (firstSplitPattern input profile hCard).candidate _), hv]
    apply (data.sourceEndpoint_eq_iff _ _ _).mpr
    refine ⟨rfl, ?_⟩
    exact (M11SplitSurvival.sheet_rel_of_incident_block profile.third).symm.trans
      ((data.vertexPartition wall).rel_repr_right block.1)
  · have hE := M11SplitVertices.branchVertexEquiv_away input profile hCard v hAt
    change data.sourceEndpoint (contractVertex target wall
        ((M11SplitVertices.branchVertexEquiv input profile hCard v).1.1.1))
        ((M11SplitVertices.branchVertexEquiv input profile hCard v).1.1.2) = v.1
    rw [hE]
    change data.sourceEndpoint (contractVertex target wall
        ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint
          (oldVertex target v.1.1.1) v.1.1.2).1.1)
        ((firstSplitPattern input profile hCard).candidate.datum.sourceEndpoint
          (oldVertex target v.1.1.1) v.1.1.2).1.2 = v.1
    rw [StarCensusEngine.sourceEndpoint_contract _ data _ _
      (candidate_refines (firstSplitPattern input profile hCard).candidate _)]
    exact data.sourceEndpoint_self v.1

/-- **The branch square of the joined member** (Figure 32, position `2`). -/
theorem joined_branchSquare (v : BranchVertex data) :
    data.sourceEndpoint
        (contractVertex target wall
          ((M11JoinedStableGraph.equivalence input profile hCard).vertex v).1.1.1)
        ((M11JoinedStableGraph.equivalence input profile hCard).vertex v).1.1.2 = v.1 := by
  classical
  by_cases hAt : v.1.1.1 = wall
  · have hv := M11JoinedStableGraph.eq_wallBlock_of_at_of_branch input profile v.1 hAt v.2
    have hE : ((M11JoinedStableGraph.equivalence input profile hCard).vertex v).1 =
        M11JoinedBranch.branchVertex profile hCard := by
      change (M11JoinedStableGraph.branchVertexMap input profile hCard v).1 = _
      simp only [M11JoinedStableGraph.branchVertexMap, hAt, ↓reduceDIte]
    rw [hE]
    change data.sourceEndpoint (contractVertex target wall
        ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
          (M11JoinedGeometry.endpoint target wall profile.doubleLabel) block.1).1.1)
        ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
          (M11JoinedGeometry.endpoint target wall profile.doubleLabel) block.1).1.2 = v.1
    rw [StarCensusEngine.sourceEndpoint_contract _ data _ _
      (candidate_refines (joinedPattern data star block hCard).candidate _)]
    have hc : contractVertex target wall
        (M11JoinedGeometry.endpoint target wall profile.doubleLabel) = wall := by
      unfold M11JoinedGeometry.endpoint
      split_ifs <;> rfl
    rw [hc, hv]
    rfl
  · have hE : ((M11JoinedStableGraph.equivalence input profile hCard).vertex v).1 =
        ResolutionAwayFromWall.retainedVertex (joinedPattern data star block hCard).candidate
          v.1 := by
      change (M11JoinedStableGraph.branchVertexMap input profile hCard v).1 = _
      simp only [M11JoinedStableGraph.branchVertexMap, hAt, ↓reduceDIte]
    rw [hE]
    change data.sourceEndpoint (contractVertex target wall
        ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
          (oldVertex target v.1.1.1) v.1.1.2).1.1)
        ((joinedPattern data star block hCard).candidate.datum.sourceEndpoint
          (oldVertex target v.1.1.1) v.1.1.2).1.2 = v.1
    rw [StarCensusEngine.sourceEndpoint_contract _ data _ _
      (candidate_refines (joinedPattern data star block hCard).candidate _)]
    exact data.sourceEndpoint_self v.1

end Local

/-! ## 2.  The three positions of Equation (6) as members of the wall's star (Stage 1) -/

section Positions

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)

/-- The wall's merged partition is a constructed join (Part I, Definition 15). -/
theorem wall_join : w.limit.vertexPartition (mergeVertex w) =
    SheetPartition.join
      (w.frame.data.vertexPartition (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1)
      (w.frame.data.vertexPartition (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2) :=
  contractVertexPartition_merge w.frame.data _ _ _

/-! ### Position `0`: the first split, anchored at the wall itself -/

/-- The wall-anchored row square of a blockwise candidate whose row map sends each
occurrence's row to its retained copy's. -/
theorem refl_rowSquare
    (c : BalancedGlobal.Candidate (w.frame.limitTarget w.column) degree w.limit (mergeVertex w))
    (E : StableGraphIncidence.Equivalence w.limit c.datum)
    (hRow : ∀ e : NonDanglingEdge w.limit,
      E.row e.stablePath =
        (ResolutionAwayFromWall.retainedEdge c (InheritedLimitRows.limit_connected w) e).stablePath)
    : ∀ (e : NonDanglingEdge w.limit) (e' : NonDanglingEdge c.datum),
      e'.1.1 = (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) c.right
        (some e.1.1.1), e.1.1.2) →
      E.row ((GeometricDatumIso.refl w.limit).stablePathEquiv
        (StarCensusEngine.anchor_connected w w.limit (GeometricDatumIso.refl w.limit))
        e.stablePath) = e'.stablePath := by
  intro e e' he
  rw [GeometricDatumIso.stablePathEquiv_refl, Equiv.refl_apply, hRow]
  exact retainedEdge_stablePath c _ e e' he

/-- The branch square at a wall-anchored position is the local one. -/
theorem refl_sourceVertexEquiv (x : w.limit.SourceVertex) :
    (GeometricDatumIso.refl w.limit).sourceVertexEquiv x = x := rfl

variable (fd0 : FullDimensionalSourcePresentation
  (firstSplitPattern input profile hCard).candidate.datum (Fin p))

/-- **Position `0` (Figure 32's first split) is a member of the wall's star**, for any
full-dimensional presentation of its datum. -/
noncomputable def member0 : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := M11SplitStableGraph.equivalence input profile hCard) (fd := fd0)
    (hRetained := M11SplitLimitMatrix.matrix_retained input profile hCard)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := candidate_merge _ (wall_join w))
    (hOld := candidate_old _) (hEdge := candidate_edge _)
    (fun v ↦ (refl_sourceVertexEquiv w _).trans (split_branchSquare input profile hCard v))
    (refl_rowSquare w _ _ (fun _ ↦ rfl))

/-! ### Position `2`: the joined member, anchored at the wall itself -/

variable (fd2 : FullDimensionalSourcePresentation
  (joinedPattern w.limit star block hCard).candidate.datum (Fin p))

/-- **Position `2` (Figure 32's joined member) is a member of the wall's star.** -/
noncomputable def member2 : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := M11JoinedStableGraph.equivalence input profile hCard) (fd := fd2)
    (hRetained := M11JoinedLimitMatrix.matrix_retained input profile hCard)
    (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
    (hMerge := candidate_merge _ (wall_join w))
    (hOld := candidate_old _) (hEdge := candidate_edge _)
    (fun v ↦ (refl_sourceVertexEquiv w _).trans (joined_branchSquare input profile hCard v))
    (refl_rowSquare w _ _ (fun _ ↦ rfl))

/-! ### Position `1`: the remote split, anchored at the branch-swapped datum

This is where the anchor is not the wall: the member's limit is literally the swapped
datum `M11RemoteCandidates.swappedDatum`, carried to the wall by the inverse branch swap
`M11StarParityFree.branchIso.symm`. -/

/-- The merged partition of the swapped datum is the wall's, a constructed join. -/
theorem swapped_join :
    (M11RemoteCandidates.swappedDatum profile hCard).vertexPartition (mergeVertex w) =
      SheetPartition.join
        (w.frame.data.vertexPartition
          (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1)
        (w.frame.data.vertexPartition
          (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2) :=
  (M11RemoteCandidates.swappedDatum_vertexPartition profile hCard).trans (wall_join w)

/-- **The branch square of the remote split**: the first-split square at the swapped
datum, undone by the inverse branch swap (both are the literal sheet relabelling). -/
theorem remote_branchSquare (v : BranchVertex w.limit) :
    (M11StarParityFree.branchIso profile hCard).symm.sourceVertexEquiv
      ((M11RemoteCandidates.swappedDatum profile hCard).sourceEndpoint
        (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
          ((M11StableGraphs.remote input profile hCard).vertex v).1.1.1)
        ((M11StableGraphs.remote input profile hCard).vertex v).1.1.2) = v.1 := by
  have h := split_branchSquare (M11RemoteInput.sourceInput input profile hCard)
    (M11RemoteInput.sourceProfile input profile hCard) (M11RemoteInput.swappedBlock_card profile hCard)
    ((StableGraphIncidence.sheetRelabelVertex (M11RemotePruning.branchRelabeling profile hCard)
      input.valid.1) v)
  change (M11StarParityFree.branchIso profile hCard).symm.sourceVertexEquiv
      ((M11RemoteCandidates.swappedDatum profile hCard).sourceEndpoint
        (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
          ((M11SplitStableGraph.equivalence (M11RemoteInput.sourceInput input profile hCard)
            (M11RemoteInput.sourceProfile input profile hCard)
            (M11RemoteInput.swappedBlock_card profile hCard)).vertex
            ((StableGraphIncidence.sheetRelabelVertex
              (M11RemotePruning.branchRelabeling profile hCard) input.valid.1) v)).1.1.1)
        ((M11SplitStableGraph.equivalence (M11RemoteInput.sourceInput input profile hCard)
            (M11RemoteInput.sourceProfile input profile hCard)
            (M11RemoteInput.swappedBlock_card profile hCard)).vertex
            ((StableGraphIncidence.sheetRelabelVertex
              (M11RemotePruning.branchRelabeling profile hCard) input.valid.1) v)).1.1.2) = v.1
  rw [h]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Equiv.symm_apply_apply _ _

/-- **The row square of the remote split**: the swapped datum's retained occurrence,
relabelled back by the inverse branch swap and forward again by the stable-graph
equivalence, is the literal occurrence. -/
theorem remote_rowSquare
    (e : NonDanglingEdge (M11RemoteCandidates.swappedDatum profile hCard))
    (e' : NonDanglingEdge (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.datum)
    (he : e'.1.1 = (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
      (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.right
        (some e.1.1.1), e.1.1.2)) :
    (M11StableGraphs.remote input profile hCard).row
        ((M11StarParityFree.branchIso profile hCard).symm.stablePathEquiv
          (StarCensusEngine.anchor_connected w _ (M11StarParityFree.branchIso profile hCard).symm)
          e.stablePath) = e'.stablePath := by
  rw [GeometricDatumIso.stablePathEquiv_mk]
  change (M11RemoteLimitMatrix.stablePathEquiv input profile hCard)
    (NonDanglingEdge.stablePath _) = _
  rw [M11RemoteLimitMatrix.stablePathEquiv_mk]
  apply congrArg NonDanglingEdge.stablePath
  apply Subtype.ext
  apply Subtype.ext
  rw [he]
  exact Prod.ext rfl (Equiv.apply_symm_apply _ _)

variable (fd1 : FullDimensionalSourcePresentation
  (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.datum (Fin p))

/-- **Position `1` (Figure 32's remote split) is a member of the wall's star**, through
the inverse branch swap.  This is inference (i) of the module docstring, proved: the limit
isomorphism is `contraction ≫ branchIso.symm`, a legitimate `GeometricStar.LimitIso`. -/
noncomputable def member1 : GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy)
    (E := M11StableGraphs.remote input profile hCard) (fd := fd1)
    (hRetained := M11RemoteLimitMatrix.matrix_retained input profile hCard)
    (M := M11RemoteCandidates.swappedDatum profile hCard)
    (φ := (M11StarParityFree.branchIso profile hCard).symm)
    (hMerge := candidate_merge _ (swapped_join w profile hCard))
    (hOld := candidate_old _) (hEdge := candidate_edge _)
    (remote_branchSquare w input profile hCard) (remote_rowSquare w input profile hCard)

end Positions

/-! ## 3.  The nonsingular positions of Equation (6) as star classes -/

/-- Equal absolute values have equal numerators up to sign. -/
theorem num_natAbs_eq_of_abs_eq {a b : ℚ} (h : |a| = |b|) : a.num.natAbs = b.num.natAbs := by
  have h1 := congrArg (fun q : ℚ ↦ q.num.natAbs) h
  simpa [Int.natAbs_abs] using h1

section Census

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p))

/-- The full-dimensional presentation of a nonsingular position, transported from the
incoming one along the family's stable-graph equivalence. -/
noncomputable def fdAt (q : Fin 3)
    (hq : M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q) :
    FullDimensionalSourcePresentation (M11RemoteCandidates.candidates input profile hCard q).datum
      (Fin p) :=
  M11FullDimensional.outgoingPresentation input profile hCard
    (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w) incoming q
    incomingFD hq

/-- **The star member of a nonsingular position of Equation (6).** -/
noncomputable def rep : (q : Fin 3) →
    M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q →
      GeometricStar.StarMember hy w
  | ⟨0, h0⟩, hq => member0 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨0, h0⟩ hq)
  | ⟨1, h1⟩, hq => member1 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨1, h1⟩ hq)
  | ⟨2, h2⟩, hq => member2 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨2, h2⟩ hq)

/-- **The multiplicity of a position's star class is its term of Equation (6)**, up to
sign: multiplicity does not depend on the labelling (`absMult_labelling_indep`). -/
theorem multNat_rep (q : Fin 3)
    (hq : M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q) :
    (GeometricStar.Star.toFibre (rep w hy input profile hCard incomingFD q hq).cls).multNat =
      (signedMult (M11StarParityFree.lab input profile hCard incoming incomingFD q).presentation
        ).num.natAbs := by
  match q, hq with
  | ⟨0, _⟩, _ => exact num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)
  | ⟨1, _⟩, _ => exact num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)
  | ⟨2, _⟩, _ => exact num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)

end Census

/-! ## 4.  Separation between positions (Stage 3)

Split and joined positions differ in the valencies of the regrown occurrence's ends
(`1, 3` against `2, 2`), which every frame isomorphism between positions preserves.
The two split positions differ in their regrown column, `2 e_{h₀}` against `2 e_{h₁}`,
which every frame isomorphism between positions preserves row by inherited row; the
rows differ exactly off a loop wall (`M11StarParityFree.SameDoubleRow`). -/

section Separation

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
  (fd0 : FullDimensionalSourcePresentation
    (firstSplitPattern input profile hCard).candidate.datum (Fin p))
  (fd1 : FullDimensionalSourcePresentation
    (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.datum (Fin p))
  (fd2 : FullDimensionalSourcePresentation
    (joinedPattern w.limit star block hCard).candidate.datum (Fin p))

/-- The frame of position `0`. -/
noncomputable abbrev frame0 :=
  StarCensusEngine.frame w hy (firstSplitPattern input profile hCard).candidate.datum
    (M11SplitStableGraph.equivalence input profile hCard) fd0

/-- The frame of position `1`. -/
noncomputable abbrev frame1 :=
  StarCensusEngine.frame w hy (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.datum
    (M11StableGraphs.remote input profile hCard) fd1

/-- The frame of position `2`. -/
noncomputable abbrev frame2 :=
  StarCensusEngine.frame w hy (joinedPattern w.limit star block hCard).candidate.datum
    (M11JoinedStableGraph.equivalence input profile hCard) fd2

/-- **The first split and the joined member are distinct star classes.** -/
theorem not_rel_02 :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frame0 w hy input profile hCard fd0)
      (frame2 w hy input profile hCard fd2)) := by
  rintro ⟨fi⟩
  have h := StarCensusEngine.frameIso_valencies
    (E := M11SplitStableGraph.equivalence input profile hCard)
    (E' := M11JoinedStableGraph.equivalence input profile hCard)
    (M11SplitLimitMatrix.matrix_retained input profile hCard)
    (M11JoinedLimitMatrix.matrix_retained input profile hCard) fi
  have h0 := firstSplit_target_valencies input profile hCard
  have h2 := joined_target_valencies w.limit star block hCard
  omega

/-- **The remote split and the joined member are distinct star classes.** -/
theorem not_rel_12 :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frame1 w hy input profile hCard fd1)
      (frame2 w hy input profile hCard fd2)) := by
  rintro ⟨fi⟩
  have h := StarCensusEngine.frameIso_valencies (E := M11StableGraphs.remote input profile hCard)
    (E' := M11JoinedStableGraph.equivalence input profile hCard)
    (M11RemoteLimitMatrix.matrix_retained input profile hCard)
    (M11JoinedLimitMatrix.matrix_retained input profile hCard) fi
  have h1 := M11RemoteCandidates.secondSplit_target_valencies input profile hCard
  have h2 := joined_target_valencies w.limit star block hCard
  omega

/-- **Off a loop wall the two split positions are distinct star classes**: their
regrown columns are `2 e_{h₀}` and `2 e_{h₁}` on different inherited rows. -/
theorem not_rel_01 (hNoLoop : ¬ M11StarParityFree.SameDoubleRow profile hCard) :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (frame0 w hy input profile hCard fd0)
      (frame1 w hy input profile hCard fd1)) := by
  classical
  rintro ⟨fi⟩
  have h := StarCensusEngine.frameIso_matrix_new
    (E := M11SplitStableGraph.equivalence input profile hCard)
    (E' := M11StableGraphs.remote input profile hCard)
    (M11SplitLimitMatrix.matrix_retained input profile hCard)
    (M11RemoteLimitMatrix.matrix_retained input profile hCard) fi
    (M11SplitRowDescent.newOldEdge profile hCard).stablePath
  have h0 := M11SplitLimitMatrix.matrix_new input profile hCard
    (M11SplitRowDescent.newOldEdge profile hCard).stablePath
  have h1 := M11RemoteLimitMatrix.matrix_new input profile hCard
    (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w)
    (M11SplitRowDescent.newOldEdge profile hCard).stablePath
  change StableSourceMatrix.matrix _ (M11RemoteLimitMatrix.stablePathEquiv input profile hCard _) _ =
    StableSourceMatrix.matrix _ (M11SplitRowDescent.stablePathEquiv input profile hCard _) _ at h
  rw [h0, h1, if_pos rfl,
    if_neg (show ¬ (M11SplitRowDescent.newOldEdge profile hCard).stablePath =
      (M11BranchSeparation.oppositeDouble profile hCard).stablePath from hNoLoop)] at h
  norm_num at h

end Separation


/-! ## 4b.  No loop walls: the hypothesis `hCol` discharged

At a loop wall (`SameDoubleRow`) the row `h` of the two surviving double-direction
occurrences meets the M-11 block vertex twice.  In any full-dimensional member of
Equation (6)'s family that row is therefore a loop row at a trivalent branch vertex, so it
turns at a leaf (`LollipopLeafRow.exists_leafRow_eq_of_loopRow`) and consists of exactly
two occurrences (`PassOnceLollipopWitness.card_rowEdges_eq_two_of_loopRow`).  At a split
member the row also carries a regrown survivor, so it has at least three occurrences; at
the joined member the leaf's edge is retained, so it is a wall column `2 e_h` and
`M11LoopWall.false_of_loopColumn` applies. -/

section NoLoop

open W4Assembly

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : W2R1Target.TwoStar target wall}
  (input : SecondEquation.W2SourceInput data star) {block : W4Assembly.WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

include hCard in
/-- A double-direction occurrence on a sheet of the M-11 block meets the block's vertex. -/
theorem double_incident (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident data (data.sourceEdge (star.edge profile.doubleLabel) sheet)
      (W4StableSource.WallBlock.sourceVertex data wall block) :=
  (incident_wallBlock_sourceVertex_iff data block _).mpr
    ⟨star.edge_mem_incidentEdges profile.doubleLabel, Subtype.ext (by
      change (data.vertexPartition wall).repr
        (data.sourceEdge (star.edge profile.doubleLabel) sheet).1.2 = block.1
      rw [M11BranchSeparation.double_sourceEdge_sheet profile hCard sheet hRel]
      exact hRel.symm.trans block.2)⟩

/-- **At a loop wall the loop row meets the M-11 block vertex at least twice.** -/
theorem two_le_incidenceCount (hRow : M11StarParityFree.SameDoubleRow profile hCard) :
    2 ≤ StablePathCount.incidenceCount data (W4StableSource.WallBlock.sourceVertex data wall block)
      (M11SplitRowDescent.newOldEdge profile hCard).stablePath := by
  classical
  have hNe : M11SplitRowDescent.newOldEdge profile hCard ≠
      M11BranchSeparation.oppositeDouble profile hCard := by
    intro h
    exact M11BranchSeparation.oppositeDouble_ne_sameSheet profile hCard
      (congrArg Subtype.val h).symm
  have hSub : ({M11SplitRowDescent.newOldEdge profile hCard,
      M11BranchSeparation.oppositeDouble profile hCard} : Finset (NonDanglingEdge data)) ⊆
      (StablePathCount.incidentEdges data (W4StableSource.WallBlock.sourceVertex data wall block)).filter
        (fun e ↦ e.stablePath = (M11SplitRowDescent.newOldEdge profile hCard).stablePath) := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr
        (double_incident profile hCard _
          (M11SplitSurvival.sheet_rel_of_incident_block profile.deleted.edge)), rfl⟩
    · rw [Finset.mem_singleton] at he
      subst he
      exact Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr
        (double_incident profile hCard _ (M11BranchSeparation.oppositeSheet_rel profile hCard)),
        hRow.symm⟩
  have h := Finset.card_le_card hSub
  rw [Finset.card_pair hNe] at h
  exact h

/-- **In a full-dimensional member the loop row is a lollipop row**: it turns at a leaf
and has exactly two occurrences. -/
theorem loopRow_lollipop (hRow : M11StarParityFree.SameDoubleRow profile hCard)
    {T : CFGraph.{0}} {D : GluingDatum T degree} {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (fd : FullDimensionalSourcePresentation D coordinate)
    (E : StableGraphIncidence.Equivalence data D) :
    ∃ (leaf : T.V) (hLeaf : IsLeafVertex T leaf),
      LeafFibre.leafRow fd hLeaf =
          fd.labelling.row (E.row (M11SplitRowDescent.newOldEdge profile hCard).stablePath) ∧
        (EdgeDenominator.rowEdges fd.labelling
          (fd.labelling.row (E.row (M11SplitRowDescent.newOldEdge profile hCard).stablePath))).card
            = 2 := by
  classical
  let A : BranchVertex data := ⟨W4StableSource.WallBlock.sourceVertex data wall block,
    profile.valency.ge⟩
  let h := (M11SplitRowDescent.newOldEdge profile hCard).stablePath
  have h2 : 2 ≤ StablePathCount.incidenceCount D (E.vertex A).1 (E.row h) := by
    rw [← E.incidence A h]
    exact two_le_incidenceCount profile hCard hRow
  have hSum := NonTrivalentValencyThreeStarCount.sum_incidenceCount_branchVertex D fd.valid.1
    fd.pathEnds (E.row h)
  have hle : StablePathCount.incidenceCount D (E.vertex A).1 (E.row h) ≤ 2 := by
    rw [← hSum]
    exact Finset.single_le_sum
      (f := fun v : BranchVertex D ↦ StablePathCount.incidenceCount D v.1 (E.row h))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (E.vertex A))
  have hTwo : StablePathCount.incidenceCount D (E.vertex A).1 (E.row h) = 2 := le_antisymm hle h2
  have hBranch : 3 ≤ nonDanglingValency D (E.vertex A).1 := (E.vertex A).2
  obtain ⟨leaf, hLeaf, hLeafRow⟩ :=
    LollipopLeafRow.exists_leafRow_eq_of_loopRow fd (by omega) hTwo
  exact ⟨leaf, hLeaf, hLeafRow,
    PassOnceLollipopWitness.card_rowEdges_eq_two_of_loopRow fd hBranch hTwo hLeaf hLeafRow⟩

/-- Three distinct occurrences on one row contradict a lollipop row. -/
theorem three_le_card_rowEdges {T : CFGraph} {D : GluingDatum T degree} {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (labelling : StableLengthMatrixLabelling D coordinate) (row : coordinate)
    {x y z : D.SourceEdge} (hx : x ∈ EdgeDenominator.rowEdges labelling row)
    (hy : y ∈ EdgeDenominator.rowEdges labelling row)
    (hz : z ∈ EdgeDenominator.rowEdges labelling row)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 ≤ (EdgeDenominator.rowEdges labelling row).card := by
  classical
  have hSub : ({x, y, z} : Finset D.SourceEdge) ⊆ EdgeDenominator.rowEdges labelling row := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have h := Finset.card_le_card hSub
  rwa [Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩] at h

/-- A nonzero natural-matrix entry has a surviving occurrence on its row and column. -/
theorem exists_occurrence_of_matrix_ne_zero {T : CFGraph} {D : GluingDatum T degree}
    {path : StablePath D} {edge : T.edges} (h : StableSourceMatrix.matrix D path edge ≠ 0) :
    ∃ z : D.SourceEdge, ∃ hz : ¬ IsDangling D z,
      NonDanglingEdge.stablePath (⟨z, hz⟩ : NonDanglingEdge D) = path ∧ z.1.1 = edge := by
  classical
  obtain ⟨z, hz⟩ : (StableSourceMatrix.occurrences D path edge).Nonempty := by
    by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    apply h
    unfold StableSourceMatrix.matrix
    rw [hEmpty, Finset.sum_empty]
  obtain ⟨⟨hSurv, hRow⟩, hTarget⟩ := (StableSourceMatrix.mem_occurrences path edge z).mp hz
  exact ⟨z, hSurv, hRow, hTarget⟩

/-- **A loop wall has no full-dimensional first split.** -/
theorem split_false (hRow : M11StarParityFree.SameDoubleRow profile hCard)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (firstSplitPattern input profile hCard).candidate.datum
      coordinate) : False := by
  classical
  obtain ⟨-, -, -, hTwo⟩ := loopRow_lollipop profile hCard hRow fd
    (M11SplitStableGraph.equivalence input profile hCard)
  let c := (firstSplitPattern input profile hCard).candidate
  set R := (M11SplitStableGraph.equivalence input profile hCard).row
    (M11SplitRowDescent.newOldEdge profile hCard).stablePath with hR
  have hNew := M11SplitLimitMatrix.matrix_new input profile hCard
    (M11SplitRowDescent.newOldEdge profile hCard).stablePath
  rw [if_pos rfl] at hNew
  obtain ⟨z, hzSurv, hzRow, hzTarget⟩ := exists_occurrence_of_matrix_ne_zero
    (hNew.trans_ne two_ne_zero)
  let x := ResolutionAwayFromWall.retainedEdge c input.valid.1
    (M11SplitRowDescent.newOldEdge profile hCard)
  let y := ResolutionAwayFromWall.retainedEdge c input.valid.1
    (M11BranchSeparation.oppositeDouble profile hCard)
  have hxR : x.stablePath = R := rfl
  have hyR : y.stablePath = R := by
    change (M11SplitRowDescent.stablePathEquiv input profile hCard)
      (M11BranchSeparation.oppositeDouble profile hCard).stablePath = R
    rw [← hRow]
    exact hR.symm
  have hx : x.1 ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨x.2, congrArg fd.labelling.row hxR⟩
  have hy : y.1 ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨y.2, congrArg fd.labelling.row hyR⟩
  have hz : z ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨hzSurv, congrArg fd.labelling.row hzRow⟩
  have hxy : x.1 ≠ y.1 := by
    intro h
    have := ResolutionAwayFromWall.retainedEdge_injective c input.valid.1 (Subtype.ext h)
    exact M11BranchSeparation.oppositeDouble_ne_sameSheet profile hCard
      (congrArg Subtype.val this).symm
  have hTargetNe : ∀ e : NonDanglingEdge data,
      (ResolutionAwayFromWall.retainedEdge c input.valid.1 e).1 ≠ z := by
    intro e h
    have h' := congrArg (fun e : c.datum.SourceEdge ↦ e.1.1) h
    rw [hzTarget] at h'
    exact Option.some_ne_none _ ((occurrenceEquiv target wall c.right).injective h')
  have h3 := three_le_card_rowEdges fd.labelling (fd.labelling.row R) hx hy hz hxy
    (hTargetNe _) (hTargetNe _)
  omega

/-- **A loop wall has no full-dimensional remote split.** -/
theorem remote_false (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hRow : M11StarParityFree.SameDoubleRow profile hCard)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation
      (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.datum coordinate) :
    False := by
  classical
  obtain ⟨-, -, -, hTwo⟩ := loopRow_lollipop profile hCard hRow fd
    (M11StableGraphs.remote input profile hCard)
  let c := (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate
  set R := (M11StableGraphs.remote input profile hCard).row
    (M11SplitRowDescent.newOldEdge profile hCard).stablePath with hR
  have hNew := M11RemoteLimitMatrix.matrix_new input profile hCard hConnected hGenus
    (M11SplitRowDescent.newOldEdge profile hCard).stablePath
  rw [if_pos (show (M11SplitRowDescent.newOldEdge profile hCard).stablePath =
    (M11BranchSeparation.oppositeDouble profile hCard).stablePath from hRow)] at hNew
  obtain ⟨z, hzSurv, hzRow, hzTarget⟩ := exists_occurrence_of_matrix_ne_zero
    (hNew.trans_ne two_ne_zero)
  let x := M11RemoteLimitMatrix.retainedEdge input profile hCard
    (M11SplitRowDescent.newOldEdge profile hCard)
  let y := M11RemoteLimitMatrix.retainedEdge input profile hCard
    (M11BranchSeparation.oppositeDouble profile hCard)
  have hxR : x.stablePath = R := rfl
  have hyR : y.stablePath = R := by
    change (M11RemoteLimitMatrix.stablePathEquiv input profile hCard)
      (M11BranchSeparation.oppositeDouble profile hCard).stablePath = R
    rw [← hRow]
    exact hR.symm
  have hx : x.1 ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨x.2, congrArg fd.labelling.row hxR⟩
  have hy : y.1 ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨y.2, congrArg fd.labelling.row hyR⟩
  have hz : z ∈ EdgeDenominator.rowEdges fd.labelling (fd.labelling.row R) :=
    (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨hzSurv, congrArg fd.labelling.row hzRow⟩
  have hxy : x.1 ≠ y.1 := by
    intro h
    have h1 := ResolutionAwayFromWall.retainedEdge_injective c
      (M11RemoteInput.sourceInput input profile hCard).valid.1 (Subtype.ext h)
    have h2 := (SheetRelabelStable.nonDanglingEdgeEquiv
      (M11RemotePruning.branchRelabeling profile hCard) input.valid.1).injective h1
    exact M11BranchSeparation.oppositeDouble_ne_sameSheet profile hCard
      (congrArg Subtype.val h2).symm
  have hTargetNe : ∀ e : NonDanglingEdge data,
      (M11RemoteLimitMatrix.retainedEdge input profile hCard e).1 ≠ z := by
    intro e h
    have h' := congrArg (fun e : c.datum.SourceEdge ↦ e.1.1) h
    rw [hzTarget] at h'
    exact Option.some_ne_none _ ((occurrenceEquiv target wall c.right).injective h')
  have h3 := three_le_card_rowEdges fd.labelling (fd.labelling.row R) hx hy hz hxy
    (hTargetNe _) (hTargetNe _)
  omega

include input in
/-- **A loop wall has no full-dimensional joined member**: the loop row's leaf edge is a
retained column, which is then a wall column `2 e_h`, and
`M11LoopWall.false_of_loopColumn` applies. -/
theorem joined_false (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hRow : M11StarParityFree.SameDoubleRow profile hCard)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (fd : FullDimensionalSourcePresentation (joinedPattern data star block hCard).candidate.datum
      coordinate) : False := by
  classical
  obtain ⟨leaf, hLeaf, hLeafRow, -⟩ := loopRow_lollipop profile hCard hRow fd
    (M11JoinedStableGraph.equivalence input profile hCard)
  let c := joinedPattern data star block hCard
  have hVal := joined_target_valencies data star block hCard
  -- the leaf edge is a retained occurrence
  obtain ⟨t, ht⟩ : ∃ t : target.edges,
      leafEdge hLeaf = occurrenceEquiv target wall c.candidate.right (some t) := by
    cases hLabel : (occurrenceEquiv target wall c.candidate.right).symm (leafEdge hLeaf) with
    | some t => exact ⟨t, ((Equiv.symm_apply_eq _).mp hLabel)⟩
    | none =>
      exfalso
      have hEq : leafEdge hLeaf = occurrenceEquiv target wall c.candidate.right none :=
        (Equiv.symm_apply_eq _).mp hLabel
      have hMem := leafEdge_mem hLeaf
      rw [hEq] at hMem
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
        occurrenceEquiv_none, newEnds] at hMem
      have hOne : (GluingDatum.incidentEdges leaf).card = 1 := hLeaf
      rcases hMem with h | h
      · rw [← h] at hOne
        omega
      · rw [← h] at hOne
        omega
  have hCol : ∀ path : StablePath data, StableSourceMatrix.matrix data path t =
      if path = (M11SplitRowDescent.newOldEdge profile hCard).stablePath then 2 else 0 := by
    intro path
    rw [← M11JoinedLimitMatrix.matrix_retained input profile hCard path t]
    have hM := LeafFibre.matrix_leafEdge_column fd hLeaf
      (fd.labelling.row ((M11JoinedStableGraph.equivalence input profile hCard).row path))
    rw [StableSourceMatrix.labelling_matrix_eq, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
      ht, hLeafRow] at hM
    refine hM.trans ?_
    congr 1
    apply propext
    constructor
    · intro h
      exact (M11JoinedStableGraph.equivalence input profile hCard).row.injective
        (fd.labelling.row.injective h)
    · intro h
      rw [h]
  exact M11LoopWall.false_of_loopColumn input profile hCard hConnected hGenus hRow 2
    (coordinate := coordinate) fd t hCol

/-- **No full-dimensional member of Equation (6)'s family lives over a loop wall.** -/
theorem not_sameDoubleRow (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate] (incoming : Fin 3)
    (fd : FullDimensionalSourcePresentation
      (M11RemoteCandidates.candidates input profile hCard incoming).datum coordinate) :
    ¬ M11StarParityFree.SameDoubleRow profile hCard := fun hRow ↦
  match incoming, fd with
  | ⟨0, _⟩, fd => split_false input profile hCard hRow fd
  | ⟨1, _⟩, fd => remote_false input profile hCard hConnected hGenus hRow fd
  | ⟨2, _⟩, fd => joined_false input profile hCard hConnected hGenus hRow fd

end NoLoop

/-- **Loop walls do not occur at M-11 regrowths**, at every core, degree and positive
request: the regrowth's own cover is a full-dimensional member of Equation (6)'s family
(`W2M11GraphTracking.exists_matched_tracking`), and `not_sameDoubleRow` applies.  This
discharges the hypothesis `hCol` of `M11LoopWall.false_of_loopColumn`. -/
theorem not_sameDoubleRow_of_regrowth {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
    (w : Regrowth core y degree) (hy : Nondegenerate y)
    {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
    (input : SecondEquation.W2SourceInput w.limit star)
    {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
    (profile : W2R2SourceProfile.SourceProfile w.limit star block)
    (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2) :
    ¬ M11StarParityFree.SameDoubleRow profile hCard := by
  have hForest := InheritedLimitRows.forest w hy
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data
    (InteriorProgress.hc_column w.frame.fullDim w.column)
    (InteriorProgress.hab_column w.frame.fullDim w.column)
    (InteriorProgress.hOne_column w.frame.fullDim w.column) hForest
  obtain ⟨incoming, fd, -, -, -, -, -⟩ :=
    W2M11GraphTracking.exists_matched_tracking w.frame.data
      (InteriorProgress.hc_column w.frame.fullDim w.column)
      (InteriorProgress.hab_column w.frame.fullDim w.column)
      (InteriorProgress.hOne_column w.frame.fullDim w.column) w.frame.fullDim hForest hCompat
      input profile hCard (InteriorGraphTracking.Tracks.self w.frame.fullDim)
  exact not_sameDoubleRow input profile hCard (W4StarParity.limitTarget_connected w)
    (W4StarParity.limitTarget_genus w) incoming fd

/-! ## 5.  The census from exhaustion (Stage 2 residue) -/

section Assembly

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p))

/-- **Distinct nonsingular positions are distinct star classes** (Stage 3), off a loop
wall. -/
theorem rep_eq_of_cls_eq (hNoLoop : ¬ M11StarParityFree.SameDoubleRow profile hCard) :
    ∀ (q : Fin 3) (hq : M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q)
      (q' : Fin 3) (hq' : M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q'),
      (rep w hy input profile hCard incomingFD q hq).cls =
        (rep w hy input profile hCard incomingFD q' hq').cls → q = q'
  | ⟨0, _⟩, _, ⟨0, _⟩, _, _ => rfl
  | ⟨1, _⟩, _, ⟨1, _⟩, _, _ => rfl
  | ⟨2, _⟩, _, ⟨2, _⟩, _, _ => rfl
  | ⟨0, h0⟩, hq, ⟨1, h1⟩, hq', h =>
    (not_rel_01 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨0, h0⟩ hq)
      (fdAt w input profile hCard incomingFD ⟨1, h1⟩ hq') hNoLoop (Quotient.exact h)).elim
  | ⟨1, h1⟩, hq, ⟨0, h0⟩, hq', h =>
    (not_rel_01 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨0, h0⟩ hq')
      (fdAt w input profile hCard incomingFD ⟨1, h1⟩ hq) hNoLoop
      ((Quotient.exact h).elim fun fi ↦ ⟨fi.symm⟩)).elim
  | ⟨0, h0⟩, hq, ⟨2, h2⟩, hq', h =>
    (not_rel_02 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨0, h0⟩ hq)
      (fdAt w input profile hCard incomingFD ⟨2, h2⟩ hq') (Quotient.exact h)).elim
  | ⟨2, h2⟩, hq, ⟨0, h0⟩, hq', h =>
    (not_rel_02 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨0, h0⟩ hq')
      (fdAt w input profile hCard incomingFD ⟨2, h2⟩ hq)
      ((Quotient.exact h).elim fun fi ↦ ⟨fi.symm⟩)).elim
  | ⟨1, h1⟩, hq, ⟨2, h2⟩, hq', h =>
    (not_rel_12 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨1, h1⟩ hq)
      (fdAt w input profile hCard incomingFD ⟨2, h2⟩ hq') (Quotient.exact h)).elim
  | ⟨2, h2⟩, hq, ⟨1, h1⟩, hq', h =>
    (not_rel_12 w hy input profile hCard (fdAt w input profile hCard incomingFD ⟨1, h1⟩ hq')
      (fdAt w input profile hCard incomingFD ⟨2, h2⟩ hq)
      ((Quotient.exact h).elim fun fi ↦ ⟨fi.symm⟩)).elim

/-- The positions' classes, as a map from the nonsingular positions to the star. -/
noncomputable def repCls
    (q : {q : Fin 3 // M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q}) :
    GeometricStar.Star hy w :=
  (rep w hy input profile hCard incomingFD q.1 q.2).cls

theorem repCls_injective (hNoLoop : ¬ M11StarParityFree.SameDoubleRow profile hCard) :
    Function.Injective (repCls w hy input profile hCard incomingFD) :=
  fun a b h ↦ Subtype.ext (rep_eq_of_cls_eq w hy input profile hCard incomingFD hNoLoop a.1 a.2
    b.1 b.2 h)

/-- **The exhaustion residue at one wall** (Stage 2): every member of the star is in the
class of some nonsingular position.  *Interface*: with Stage 1 and 3 it is equivalent to
the census at this wall (`census_of_exhaustion`, `exhaustion_of_census`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ q : Fin 3,
    ∃ hq : M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q,
      member.cls = (rep w hy input profile hCard incomingFD q hq).cls

theorem repCls_surjective (hExh : Exhausts w hy input profile hCard incomingFD) :
    Function.Surjective (repCls w hy input profile hCard incomingFD) := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨q, hq, h⟩ := hExh member
  exact ⟨⟨q, hq⟩, h.symm⟩

/-- **The M-11 census at one wall from exhaustion and the no-loop condition.** -/
theorem census_of_exhaustion (hNoLoop : ¬ M11StarParityFree.SameDoubleRow profile hCard)
    (hExh : Exhausts w hy input profile hCard incomingFD) :
    ∃ e : {q : Fin 3 // M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q} ≃
        GeometricStar.Star hy w,
      ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
        (signedMult (M11StarParityFree.lab input profile hCard incoming incomingFD q.1).presentation
          ).num.natAbs :=
  ⟨Equiv.ofBijective _ ⟨repCls_injective w hy input profile hCard incomingFD hNoLoop,
      repCls_surjective w hy input profile hCard incomingFD hExh⟩,
    fun q ↦ multNat_rep w hy input profile hCard incomingFD q.1 q.2⟩

/-- **Interface: the census implies exhaustion**, off a loop wall.  An injective
map between finite sets of equal cardinality is onto. -/
theorem exhaustion_of_census (hNoLoop : ¬ M11StarParityFree.SameDoubleRow profile hCard)
    (e : {q : Fin 3 // M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q} ≃
      GeometricStar.Star hy w) :
    Exhausts w hy input profile hCard incomingFD := by
  classical
  have hBij : Function.Bijective (repCls w hy input profile hCard incomingFD) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨repCls_injective w hy input profile hCard incomingFD hNoLoop, Fintype.card_congr e⟩
  intro member
  obtain ⟨q, hq⟩ := hBij.2 member.cls
  exact ⟨q.1, q.2, hq.symm⟩

end Assembly


/-! ## 5b.  Stage 2 reduced to decoupled transports onto the anchored positions

The anchored exhaustion skeleton (`StarCensusEngine.cls_eq_of_transport`) turns a
`ResolutionExpansionFree.TransportFree` from a member's own normal form
(`M11WallExhaustion.normIso`) onto a position's resolution expansion **of its anchor**
into equality of star classes.  At position `1` the transport is along the member's limit
isomorphism composed with the branch swap, which is what removes the obstruction to
wall-anchored candidates recorded in `M11StarParityFree`: an incoherent member is received
there, not at a wall-anchored index. -/

section Transport

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p))

include input in
/-- Merge pinning at an M-11 wall, from equation (C) of its W2 input. -/
theorem pinned : M11WallExhaustion.Pinned hy w :=
  M11WallExhaustion.pinned_of_targetExcess_eq_one input.equation_c

/-- **The receipt a member must present to be received at position `q`**: a decoupled
transport from its own normal form, along its limit isomorphism composed with the
position's anchor inverse, onto the position's pasted resolution. -/
def PositionTransport (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w) :
    Fin 3 → Type
  | ⟨0, _⟩ => ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm) (mergeVertex other) (mergeVertex w)
      (M11WallExhaustion.memberPlacement (pinned w hy input) star other ψ)
      (firstSplitPattern input profile hCard).candidate.right
      (M11WallExhaustion.memberResolution (pinned w hy input) star other ψ)
      (pasted (firstSplitPattern input profile hCard).candidate)
  | ⟨1, _⟩ => ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (M11StarParityFree.branchIso profile hCard).symm.symm) (mergeVertex other)
      (mergeVertex w)
      (M11WallExhaustion.memberPlacement (pinned w hy input) star other ψ)
      (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.right
      (M11WallExhaustion.memberResolution (pinned w hy input) star other ψ)
      (pasted (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate)
  | ⟨2, _⟩ => ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm) (mergeVertex other) (mergeVertex w)
      (M11WallExhaustion.memberPlacement (pinned w hy input) star other ψ)
      (joinedPattern w.limit star block hCard).candidate.right
      (M11WallExhaustion.memberResolution (pinned w hy input) star other ψ)
      (pasted (joinedPattern w.limit star block hCard).candidate)

theorem memberNV (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (vertex : other.frame.data.SourceVertex) :
    InheritedLimitBranches.vertexMap other vertex =
      GlobalResolution.sourceVertexMap other.limit (mergeVertex other)
        (M11WallExhaustion.memberPlacement (pinned w hy input) star other ψ)
        (M11WallExhaustion.memberResolution (pinned w hy input) star other ψ)
        (M11WallExhaustion.memberCompatible (pinned w hy input) star other ψ)
        ((M11WallExhaustion.normIso (pinned w hy input) star other ψ).sourceVertexEquiv vertex) :=
  M11WallExhaustion.sourceVertexMap_datumIso other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (M11WallExhaustion.memberPlacement (pinned w hy input) star other ψ)
    (M11WallExhaustion.memberPlacement_spec (pinned w hy input) star other ψ)
    other.frame.fullDim.targetConnected other.frame.fullDim.targetGenus vertex

theorem memberNE (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)
    (edge : other.limit.SourceEdge) :
    (M11WallExhaustion.normIso (pinned w hy input) star other ψ).sourceEdgeEquiv
        (InheritedLimitRows.edgeEmbedding other edge) =
      ResolutionExpansion.retainedSourceEdge other.limit (mergeVertex other)
        (M11WallExhaustion.memberPlacement (pinned w hy input) star other ψ)
        (M11WallExhaustion.memberResolution (pinned w hy input) star other ψ)
        (M11WallExhaustion.memberCompatible (pinned w hy input) star other ψ) edge :=
  M11WallExhaustion.retainedSourceEdge_datumIso other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (M11WallExhaustion.memberPlacement (pinned w hy input) star other ψ)
    (M11WallExhaustion.memberPlacement_spec (pinned w hy input) star other ψ)
    other.frame.fullDim.targetConnected other.frame.fullDim.targetGenus edge

/-- **Stage 2 reduced to transports**: if every star member presents a decoupled
transport onto some nonsingular position, the star is exhausted by the positions. -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w, ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ q : Fin 3, ∃ _ : M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q,
        Nonempty (PositionTransport w hy input profile hCard member.member ψ q)) :
    Exhausts w hy input profile hCard incomingFD := by
  intro member
  obtain ⟨ψ, q, hq, ⟨t⟩⟩ := h member
  refine ⟨q, hq, ?_⟩
  match q, hq, t with
  | ⟨0, h0⟩, hq, t =>
    exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
      (E := M11SplitStableGraph.equivalence input profile hCard)
      (fd := fdAt w input profile hCard incomingFD ⟨0, h0⟩ hq)
      (hRetained := M11SplitLimitMatrix.matrix_retained input profile hCard)
      (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
      (hMerge := candidate_merge _ (wall_join w)) (hOld := candidate_old _)
      (hEdge := candidate_edge _)
      (fun v ↦ (refl_sourceVertexEquiv w _).trans (split_branchSquare input profile hCard v))
      (refl_rowSquare w _ _ (fun _ ↦ rfl))
      (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (firstSplitPattern input profile hCard).candidate.exterior) rfl member ψ
      (M11WallExhaustion.normIso (pinned w hy input) star member.member ψ)
      (memberNV w hy input member.member ψ) (memberNE w hy input member.member ψ) t
  | ⟨1, h1⟩, hq, t =>
    exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
      (E := M11StableGraphs.remote input profile hCard)
      (fd := fdAt w input profile hCard incomingFD ⟨1, h1⟩ hq)
      (hRetained := M11RemoteLimitMatrix.matrix_retained input profile hCard)
      (M := M11RemoteCandidates.swappedDatum profile hCard)
      (φ := (M11StarParityFree.branchIso profile hCard).symm)
      (hMerge := candidate_merge _ (swapped_join w profile hCard))
      (hOld := candidate_old _) (hEdge := candidate_edge _)
      (remote_branchSquare w input profile hCard) (remote_rowSquare w input profile hCard)
      (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.exterior) rfl
      member ψ (M11WallExhaustion.normIso (pinned w hy input) star member.member ψ)
      (memberNV w hy input member.member ψ) (memberNE w hy input member.member ψ) t
  | ⟨2, h2⟩, hq, t =>
    exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
      (E := M11JoinedStableGraph.equivalence input profile hCard)
      (fd := fdAt w input profile hCard incomingFD ⟨2, h2⟩ hq)
      (hRetained := M11JoinedLimitMatrix.matrix_retained input profile hCard)
      (M := w.limit) (φ := GeometricDatumIso.refl w.limit)
      (hMerge := candidate_merge _ (wall_join w)) (hOld := candidate_old _)
      (hEdge := candidate_edge _)
      (fun v ↦ (refl_sourceVertexEquiv w _).trans (joined_branchSquare input profile hCard v))
      (refl_rowSquare w _ _ (fun _ ↦ rfl))
      (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (joinedPattern w.limit star block hCard).candidate.exterior) rfl member ψ
      (M11WallExhaustion.normIso (pinned w hy input) star member.member ψ)
      (memberNV w hy input member.member ψ) (memberNE w hy input member.member ψ) t

end Transport

/-! ## 6.  The family clause -/

section Family

open ClassifiedContinuation (SourceCase)

/-- **Stage 2's residue, family-wide**: at every `w2M11` regrowth, for every Equation (6)
presentation, every star member is in the class of a nonsingular position.
*Interface*: equivalent to `M11StarParityFree.M11StarCensus`
(`m11StarCensus_of_exhaustion`, `exhaustion_of_m11StarCensus`).  It is proved in
`M11StarExhaustionProof` (`m11StarExhaustion`). -/
def M11StarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2M11 →
    ∀ (star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : SecondEquation.W2SourceInput w.limit star)
      (block : W4Assembly.WallBlock w.limit (mergeVertex w))
      (profile : W2R2SourceProfile.SourceProfile w.limit star block)
      (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
      (incoming : Fin 3)
      (incomingFD : FullDimensionalSourcePresentation
        (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p)),
      Exhausts w hy input profile hCard incomingFD

variable {degree n p : ℕ}

/-- **The M-11 star census from exhaustion.**  Stages 1 and 3 are proved; loop walls are
excluded by `not_sameDoubleRow_of_regrowth`. -/
theorem m11StarCensus_of_exhaustion (hExh : M11StarExhaustion degree n p) :
    M11StarParityFree.M11StarCensus degree n p :=
  fun core y hy w cls htag star input block profile hCard incoming incomingFD ↦
    census_of_exhaustion w hy input profile hCard incomingFD
      (not_sameDoubleRow_of_regrowth w hy input profile hCard)
      (hExh core y hy w cls htag star input block profile hCard incoming incomingFD)

/-- **Interface**: the census implies exhaustion. -/
theorem exhaustion_of_m11StarCensus (hCensus : M11StarParityFree.M11StarCensus degree n p) :
    M11StarExhaustion degree n p :=
  fun core y hy w cls htag star input block profile hCard incoming incomingFD ↦
    exhaustion_of_census w hy input profile hCard incomingFD
      (not_sameDoubleRow_of_regrowth w hy input profile hCard)
      (hCensus core y hy w cls htag star input block profile hCard incoming incomingFD).choose

theorem m11StarExhaustion_iff :
    M11StarExhaustion degree n p ↔ M11StarParityFree.M11StarCensus degree n p :=
  ⟨m11StarCensus_of_exhaustion, exhaustion_of_m11StarCensus⟩

/-- **The `w2M11` clause of `FamilyStarParity` at genus six and degree four**, modulo
Stage 2's exhaustion alone. -/
theorem familyStarParity_w2M11_of_exhaustion
    (hExh : M11StarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2M11 :=
  M11StarParityFree.familyStarParity_w2M11 (m11StarCensus_of_exhaustion hExh)

end Family

/-! ## 7.  Non-vacuity: the incoming position is nonsingular -/

section Pilot

/-- The incoming position of Equation (6) is always nonsingular
(`M11CertifiedOpposite.incomingDet_ne_zero`), so every census has at least one class. -/
theorem nonsingular_incoming {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
    {w : Regrowth core y degree}
    {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
    (input : SecondEquation.W2SourceInput w.limit star)
    {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
    (profile : W2R2SourceProfile.SourceProfile w.limit star block)
    (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p)) :
    M11StarParityFree.Nonsingular input profile hCard incoming incomingFD incoming :=
  M11CertifiedOpposite.incomingDet_ne_zero input profile hCard incoming incomingFD

end Pilot

end DraismaVargas.Count.M11StarCensusProof
