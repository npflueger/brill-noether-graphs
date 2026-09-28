import DraismaVargasCount.W2PStarCensusProof
import DraismaVargasCount.W3FourStarCensusProof
import DraismaVargasCount.RegrowthBalances

/-!
# The M-1k star census, Stages 1 and 3, and Stage 2 reduced to transports

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-M-1k}`, Figure 33
and **Equation (7)**; Vargas, Part II (arXiv:2609.09109): the star of a wall.  Engine
`StarCensusEngine`; balance `RegrowthBalances` (`exists_w2M1k_balance`,
`m1k_sum_signedMult_eq_zero_of_source`); the same pattern as `W2PStarCensusProof` and
`W3FourStarCensusProof` (the branch-swap anchor).  This is the M-1k case of the star
parity in step 2 of `Assembly`: exhaustion of the star, and uniqueness with
multiplicity.  As in `M11StarCensusProof`, the census splits into (a) every
nonsingular position is a star class (Stage 1), (b) every star class is a position
(Stage 2), and (c) distinct positions are distinct classes (Stage 3).

## The result, in one paragraph

`RegrowthWallInput.FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2M1k` is reduced to the single
residue `W2M1kStarExhaustion` (`familyStarParity_w2M1k_of_exhaustion`), equivalent to the
census `W2M1kStarCensus` (`w2M1kStarExhaustion_iff`); the residue is discharged in
`W2M1kStarExhaustionProof`.  The positions are those of
`W2M1kLimitColumns.limitColumns` **itself** -- the family Equation (7) is stated on, with its
`LeafPair`/`DividedData` picked by `Classical.choice` -- so no identification of families is
needed: every position is anchored at the wall (`limitAnchor`: the identity at the members
over the limit, the inverse branch swap at the remote one, in either orientation), every
nonsingular position is presented by the regrowth's own cover
(`RegrowthBalances.regrowthPresentation`), and Equation (7) holds at **every** initial
labelling in `Fin p` from any one nonsingular position (and trivially when all are
singular).  Separation: the leaf position puts both wall occurrences on the fresh side and
the other two split them as the star does, so a frame isomorphism between the leaf and
another position would have to preserve or complement the side assignment on the wall
(`W3FourStarCensusProof.frameIso_side`) and can do neither; the divided and joined
positions differ in the regrown column at `e₁`'s row (`1 + … ≥ 1` against
`≤ 1/(k+1)`), with no loop case.

## What is proved

* **Anchors.**  `leaf_branchSquare` (the branch square of Figure 33's bespoke leaf
  dictionary); `DAnchor` (a hypothesis shaper for any datum on the expanded limit target
  with a row bijection, *not* a supply), `DAnchor.retained`, `DAnchor.refl`,
  `DAnchor.swap` (generic in the candidate, reused by `W2MkkStarCensusProof`); `Anchor`,
  `Anchor.retained`, `Anchor.matrix_new`; the five member anchors `localLeafAnchor`,
  `localDividedAnchor`, `joinedAnchor`, `remoteDividedAnchor`, `remoteLeafAnchor`;
  `anchorOf`, `anchorOf_iff`, `alignedAnchor`, `separatedAnchor`, `limitAnchor`;
  `right_zero`, `right_one`, `right_two`.
* **Stage 1 (a).**  `columns`, `lab`, `Nonsingular`, `fdAt`, `rep`, `multNat_rep`,
  `signedMult_eq_zero`, `integral_signedMult`, `sum_signedMult_eq_zero`.
* **Stage 3 (c), unconditional.**  `thirdNew_ne_secondNew`, `newColumn_eq_of_frameIso`,
  `side_of_frameIso`, `false_of_side_leaf`, `not_rel_leaf`, `not_rel_12`,
  `rep_eq_of_cls_eq`, `repCls_injective`.
* **Stage 2 reduced to transports.**  `PositionTransport` (along the limit isomorphism
  composed with the position's anchor inverse), `exhausts_of_transports`.
* **Assembly.**  `Exhausts`, `repCls_surjective`, `census_of_exhaustion`,
  `exhaustion_of_census`, `starParityAt_of_census`, `starParityAt_of_exhaustion`;
  `W2M1kStarCensus`, `W2M1kStarExhaustion`, `w2M1kStarCensus_of_exhaustion`,
  `exhaustion_of_w2M1kStarCensus`, `w2M1kStarExhaustion_iff`,
  `familyStarParity_w2M1k_of_census`, `familyStarParity_w2M1k_of_exhaustion`.

## What is NOT proved

* **Exhaustion is not proved here**; it is `W2M1kStarExhaustionProof`
  (`w2M1kStarExhaustion`), which makes the clause unconditional.
* The census is stated on `limitColumns`, not on the orientation Part I's identification
  names (`RegrowthBalances.exists_w2M1k_balance`'s `orientation`); the two are never
  identified, and nothing needs them to be.
* No wall carrying the tag is exhibited here: computer experiments find M-1k walls,
  but none is imported or checked here.

## Consumers

`W2M1kStarExhaustionProof`, `W2MkkStarCensusProof` (`DAnchor`).
-/

namespace DraismaVargas.Count.W2M1kStarCensusProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W2R1Target SecondEquation W4Assembly W2R2SourceProfile
open W2M1kSourceCandidates W2M1kLimitColumns W2M1kTransport
open W2M1kCommonBalance (LimitMember LimitColumns)
open W3Nd2StarCensusProof (PlacementSpec memberResolution memberNorm)

/-! ## 1.  The leaf member's branch square -/

section Leaf

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall} {profile : SourceProfile data star block}

/-- **The branch square of Figure 33's leaf member**: the member vertex an incoming source
vertex becomes, contracted and read in the incoming datum, is that vertex. -/
theorem leaf_branchSquare (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (vertex : data.SourceVertex) :
    data.sourceEndpoint (contractVertex target wall
        (W2M1kLeafStableGraph.leafBranchImage input shape pair vertex).1.1)
      (W2M1kLeafStableGraph.leafBranchImage input shape pair vertex).1.2 = vertex := by
  classical
  have hContract : ∀ (place : Vertex target) (sheet : Fin degree),
      data.sourceEndpoint (contractVertex target wall
          ((LeafPair.candidate input shape pair).datum.sourceEndpoint place sheet).1.1)
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint place sheet).1.2 =
        data.sourceEndpoint (contractVertex target wall place) sheet :=
    fun place sheet ↦ StarCensusEngine.sourceEndpoint_contract _ data place sheet
      (M11StarCensusProof.candidate_refines (LeafPair.candidate input shape pair) place)
  by_cases hAt : vertex.1.1 = wall
  · have hSelf : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSel : (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.2
    · rw [W2M1kLeafStableGraph.leafBranchImage_selected input shape pair hAt hSel]
      unfold W2M1kLeafStableGraph.leafBranchVertex
      rw [hContract]
      change data.sourceEndpoint wall pair.second = vertex
      rw [← hSelf]
      exact (data.sourceEndpoint_eq_iff wall _ _).mpr ⟨rfl, by
        change (data.vertexPartition wall).repr pair.second =
          (data.vertexPartition wall).repr ((data.sourceEndpoint wall vertex.1.2).1.2)
        rw [hSelf]
        exact pair.rel_second.symm.trans hSel⟩
    · rw [W2M1kLeafStableGraph.leafBranchImage_background input shape pair hAt hSel, hContract]
      exact hSelf
  · rw [W2M1kLeafStableGraph.leafBranchImage_away input shape pair hAt]
    change data.sourceEndpoint (contractVertex target wall
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (oldVertex target vertex.1.1) vertex.1.2).1.1)
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (oldVertex target vertex.1.1) vertex.1.2).1.2 = vertex
    rw [hContract]
    exact data.sourceEndpoint_self vertex

end Leaf

/-! ## 2.  How a Figure 33 member is anchored at the wall -/

section Anchor

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree)

/-- **How a member of a limit family is anchored at the wall.**  For a datum `D` on a
one-vertex expansion of the limit target and a row bijection `row` from the limit's stable
rows: a stable-graph dictionary `E` from the limit whose rows are `row`, the source genus,
an anchor datum `M` on the limit target with a geometric isomorphism `φ` back to the limit,
the contraction facts of `D` onto `M`, the two anchor squares of `StarCensusEngine`, and
`D`'s presentation as a resolution expansion of `M`.  *Interface*: a hypothesis
shaper, not a supply; it is inhabited at every position of
`W2M1kLimitColumns.limitColumns` (`limitAnchor`), by the identity at the members over the
limit and by the inverse branch swap at the remote one (`DAnchor.refl`, `DAnchor.swap`). -/
structure DAnchor {right : (w.frame.limitTarget w.column).edges → Bool}
    (D : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right) degree)
    (row : StablePath w.limit ≃ StablePath D) where
  E : StableGraphIncidence.Equivalence w.limit D
  E_row : ∀ path, E.row path = row path
  genus_eq : genus D.sourceGraph = genus w.limit.sourceGraph
  M : GluingDatum (w.frame.limitTarget w.column) degree
  φ : GeometricDatumIso M w.limit
  hMerge : SheetPartition.join
      (D.vertexPartition (oldVertex (w.frame.limitTarget w.column) (mergeVertex w)))
      (D.vertexPartition (freshVertex (w.frame.limitTarget w.column))) =
    M.vertexPartition (mergeVertex w)
  hOld : ∀ vertex : (w.frame.limitTarget w.column).V, vertex ≠ mergeVertex w →
    D.vertexPartition (oldVertex (w.frame.limitTarget w.column) vertex) =
      M.vertexPartition vertex
  hEdge : ∀ edge : (w.frame.limitTarget w.column).edges,
    D.edgePartition (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w)
      right (some edge)) = M.edgePartition edge
  hV : StarCensusEngine.BranchSquare w M φ (E := E)
  hR : StarCensusEngine.RowSquare w M φ (E := E)
  res : ResolutionM11.LocalResolution degree
  compat : GlobalResolution.OldCompatible M (mergeVertex w) right res
  hD : D = GlobalResolution.datum M (mergeVertex w) right res compat

/-- A Figure 33 member (`W2M1kCommonBalance.LimitMember`), anchored at the wall. -/
abbrev Anchor (m : LimitMember w.limit (mergeVertex w)) := DAnchor w m.datum m.row

variable {w}

/-- An anchored datum's retained columns are the wall's, when its rows' are. -/
theorem DAnchor.retained {right : (w.frame.limitTarget w.column).edges → Bool}
    {D : GluingDatum (graph (w.frame.limitTarget w.column) (mergeVertex w) right) degree}
    {row : StablePath w.limit ≃ StablePath D} (A : DAnchor w D row)
    (hRetained : ∀ (path : StablePath w.limit) (place : (w.frame.limitTarget w.column).edges),
      StableSourceMatrix.matrix D (row path)
          (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some place)) =
        StableSourceMatrix.matrix w.limit path place)
    (path : StablePath w.limit) (place : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix D (A.E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) right (some place)) =
      StableSourceMatrix.matrix w.limit path place := by
  rw [A.E_row]
  exact hRetained path place

/-- The member's retained columns are the wall's. -/
theorem Anchor.retained {m : LimitMember w.limit (mergeVertex w)} (A : Anchor w m)
    (path : StablePath w.limit) (place : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix m.datum (A.E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) m.right (some place)) =
      StableSourceMatrix.matrix w.limit path place :=
  DAnchor.retained A m.retained path place

/-- The regrown column, read through the anchor's rows, is the member's own. -/
theorem Anchor.matrix_new {m : LimitMember w.limit (mergeVertex w)} (A : Anchor w m)
    (path : StablePath w.limit) :
    StableSourceMatrix.matrix m.datum (A.E.row path)
        (occurrenceEquiv (w.frame.limitTarget w.column) (mergeVertex w) m.right none) =
      m.newColumnValue path := by
  rw [A.E_row]
  rfl

/-- **The identity anchor**, for a member over the limit itself that is a blockwise
candidate `c`, with a dictionary whose branch square holds at the limit and whose rows
send each surviving limit edge to its retained copy. -/
noncomputable def DAnchor.refl
    (c : BalancedGlobal.Candidate (w.frame.limitTarget w.column) degree w.limit (mergeVertex w))
    (E : StableGraphIncidence.Equivalence w.limit c.datum)
    (hGenus : genus c.datum.sourceGraph = genus w.limit.sourceGraph)
    (hBranch : ∀ v : BranchVertex w.limit,
      w.limit.sourceEndpoint (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
        (E.vertex v).1.1.1) (E.vertex v).1.1.2 = v.1)
    (hRow : ∀ e : NonDanglingEdge w.limit,
      E.row e.stablePath = (ResolutionAwayFromWall.retainedEdge c
        (InheritedLimitRows.limit_connected w) e).stablePath) :
    DAnchor w c.datum E.row where
  E := E
  E_row _ := rfl
  genus_eq := hGenus
  M := w.limit
  φ := GeometricDatumIso.refl w.limit
  hMerge := M11StarCensusProof.candidate_merge _ (M11StarCensusProof.wall_join w)
  hOld := M11StarCensusProof.candidate_old _
  hEdge := M11StarCensusProof.candidate_edge _
  hV v := (M11StarCensusProof.refl_sourceVertexEquiv w _).trans (hBranch v)
  hR := M11StarCensusProof.refl_rowSquare w _ _ hRow
  res := M11StarCensusProof.pasted c
  compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _ c.exterior
  hD := rfl

/-- **The branch-swap anchor**, for a member over a sheet-relabelled copy of the limit
that fixes the wall's partition: the dictionary is the relabelling's followed by the
member's own over the copy, and `φ` is the inverse relabelling (the anchoring of M-11's
remote split and of `W3FourStarCensusProof.GaugeAnchor.swap`). -/
noncomputable def DAnchor.swap (R : w.limit.SheetRelabeling)
    (hWall : R.apply.vertexPartition (mergeVertex w) = w.limit.vertexPartition (mergeVertex w))
    (c : BalancedGlobal.Candidate (w.frame.limitTarget w.column) degree R.apply (mergeVertex w))
    (E' : StableGraphIncidence.Equivalence R.apply c.datum)
    (hGenus : genus c.datum.sourceGraph = genus R.apply.sourceGraph)
    (hBranch : ∀ v : BranchVertex R.apply,
      R.apply.sourceEndpoint (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
        (E'.vertex v).1.1.1) (E'.vertex v).1.1.2 = v.1)
    (hRow : ∀ (hC : R.apply.Connected) (e : NonDanglingEdge R.apply),
      E'.row e.stablePath = (ResolutionAwayFromWall.retainedEdge c hC e).stablePath) :
    DAnchor w c.datum
      ((StableGraphIncidence.sheetRelabel R (InheritedLimitRows.limit_connected w)).trans
        E').row where
  E := (StableGraphIncidence.sheetRelabel R (InheritedLimitRows.limit_connected w)).trans E'
  E_row _ := rfl
  genus_eq := hGenus.trans R.sourceGraphLaplacianEquiv.genus_eq
  M := R.apply
  φ := (GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling R)).symm
  hMerge := M11StarCensusProof.candidate_merge _ (hWall.trans (M11StarCensusProof.wall_join w))
  hOld := M11StarCensusProof.candidate_old _
  hEdge := M11StarCensusProof.candidate_edge _
  hV v := by
    have h := hBranch ((StableGraphIncidence.sheetRelabel R
      (InheritedLimitRows.limit_connected w)).vertex v)
    change (GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling
        R)).symm.sourceVertexEquiv
      (R.apply.sourceEndpoint (contractVertex (w.frame.limitTarget w.column) (mergeVertex w)
        (E'.vertex ((StableGraphIncidence.sheetRelabel R
          (InheritedLimitRows.limit_connected w)).vertex v)).1.1.1)
        (E'.vertex ((StableGraphIncidence.sheetRelabel R
          (InheritedLimitRows.limit_connected w)).vertex v)).1.1.2) = v.1
    rw [h]
    exact Subtype.ext (Prod.ext rfl (Equiv.symm_apply_apply _ _))
  hR e e' he := by
    change E'.row (SheetRelabelStable.stablePathEquiv R (InheritedLimitRows.limit_connected w)
      (((GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling R)).symm).stablePathEquiv
        _ e.stablePath)) = _
    have hBack : SheetRelabelStable.stablePathEquiv R (InheritedLimitRows.limit_connected w)
        (((GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling
            R)).symm).stablePathEquiv
          (StarCensusEngine.anchor_connected w R.apply
            (GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling R)).symm)
          e.stablePath) = e.stablePath := by
      rw [GeometricDatumIso.stablePathEquiv_mk, SheetRelabelStable.stablePathEquiv_mk]
      apply congrArg NonDanglingEdge.stablePath
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl (Equiv.apply_symm_apply _ _)
    rw [hBack, hRow (StarCensusEngine.anchor_connected w R.apply
      (GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling R)).symm)]
    exact M11StarCensusProof.retainedEdge_stablePath c _ e e' he
  res := M11StarCensusProof.pasted c
  compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _ c.exterior
  hD := rfl

end Anchor

/-! ## 3.  The five Figure 33 members, anchored -/

section Members

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree}
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)

/-- `M⁽¹⁾` over the limit (Base I.a), anchored by the identity. -/
noncomputable def localLeafAnchor (pair : LeafPair profile) :
    Anchor w (localLeafMember input shape pair) :=
  DAnchor.refl (LeafPair.candidate input shape pair)
    (W2M1kLeafStableGraph.leafEquivalence input shape pair)
    (leaf_sourceGenus input shape pair)
    (fun v ↦ leaf_branchSquare input shape pair v.1)
    (fun _ ↦ rfl)

/-- `M⁽²⁾` over the limit (Base II.2.2.M), anchored by the identity. -/
noncomputable def localDividedAnchor (divided : DividedData profile) :
    Anchor w (localDividedMember input shape divided) :=
  DAnchor.refl (DividedData.candidate shape divided)
    (W2M1kGraphData.dividedEquivalence input shape divided)
    (divided_sourceGenus shape divided)
    (fun v ↦ W2PStarCensusProof.coreGraphData_branchSquare
      (W2M1kGraphData.dividedGraphData input shape divided) v)
    (fun _ ↦ rfl)

/-- `M⁽³⁾` (Base II.1.M), anchored by the identity. -/
noncomputable def joinedAnchor (geometry : GlobalM1k.Geometry w.limit (mergeVertex w)) :
    Anchor w (joinedMember input shape geometry) :=
  DAnchor.refl (joinedCandidate star geometry)
    (W2M1kGraphData.joinedEquivalence input shape geometry)
    (joined_sourceGenus geometry)
    (fun v ↦ W2PStarCensusProof.coreGraphData_branchSquare
      (W2M1kGraphData.joinedGraphData input shape geometry) v)
    (fun _ ↦ rfl)

/-- The remote `M⁽²⁾` over the branch-swapped copy, anchored by the inverse swap. -/
noncomputable def remoteDividedAnchor (other : Fin degree)
    (hOther : (w.limit.vertexPartition (mergeVertex w)).Rel (pinSheet profile 0) other)
    (divided : DividedData (swapProfile profile input.valid.1 other hOther)) :
    Anchor w (remoteDividedMember input shape other hOther divided) :=
  DAnchor.swap (swapRelabeling profile other hOther) (swap_vertexPartition_wall other hOther)
    (DividedData.candidate (swapShape shape input.valid.1 other hOther) divided)
    (W2M1kGraphData.dividedEquivalence (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) divided)
    (divided_sourceGenus (swapShape shape input.valid.1 other hOther) divided)
    (fun v ↦ W2PStarCensusProof.coreGraphData_branchSquare
      (W2M1kGraphData.dividedGraphData (swapInput input other hOther)
        (swapShape shape input.valid.1 other hOther) divided) v)
    (fun _ _ ↦ rfl)

/-- The remote `M⁽¹⁾` over the branch-swapped copy, anchored by the inverse swap. -/
noncomputable def remoteLeafAnchor (other : Fin degree)
    (hOther : (w.limit.vertexPartition (mergeVertex w)).Rel (pinSheet profile 0) other)
    (pair : LeafPair (swapProfile profile input.valid.1 other hOther)) :
    Anchor w (remoteLeafMember input shape other hOther pair) :=
  DAnchor.swap (swapRelabeling profile other hOther) (swap_vertexPartition_wall other hOther)
    (LeafPair.candidate (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) pair)
    (W2M1kLeafStableGraph.leafEquivalence (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) pair)
    (leaf_sourceGenus (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) pair)
    (fun v ↦ leaf_branchSquare (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) pair v.1)
    (fun _ _ ↦ rfl)

end Members

/-! ## 4.  The positions of Equation (7), anchored -/

section Positions

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree}
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)

/-- Equation (7)'s family at the wall: `W2M1kLimitColumns.limitColumns`, at the wall's
own connectedness and genus receipts. -/
noncomputable abbrev columns : LimitColumns profile shape :=
  limitColumns input shape (RegrowthBalances.limit_connected w) (RegrowthBalances.limit_genus w)

/-- An anchor family along an equation of families. -/
noncomputable def anchorOf {L L' : LimitColumns profile shape} (h : L = L')
    (a : ∀ j, Anchor w (L'.member j)) (j : Fin 3) : Anchor w (L.member j) :=
  cast (congrArg (fun L : LimitColumns profile shape ↦ Anchor w (L.member j)) h.symm) (a j)

/-- Everything said about an anchored member is said about its image along an equation of
families. -/
theorem anchorOf_iff {L L' : LimitColumns profile shape} (h : L = L')
    (a : ∀ j, Anchor w (L'.member j)) (j : Fin 3)
    (F : ∀ m : LimitMember w.limit (mergeVertex w), Anchor w m → Prop) :
    F (L.member j) (anchorOf shape h a j) ↔ F (L'.member j) (a j) := by
  subst h
  rfl

/-- The anchors of the aligned orientation (Base I.a): the leaf and joined members over the
limit, the divided one remote. -/
noncomputable def alignedAnchor (pair : LeafPair profile) :
    ∀ j, Anchor w ((alignedOrientation input shape pair (RegrowthBalances.limit_connected w)
      (RegrowthBalances.limit_genus w)).member j)
  | ⟨0, _⟩ => localLeafAnchor input shape pair
  | ⟨1, _⟩ => remoteDividedAnchor input shape pair.second pair.rel_second
      (remoteDivided input shape pair (RegrowthBalances.limit_connected w)
        (RegrowthBalances.limit_genus w))
  | ⟨2, _⟩ => joinedAnchor input shape (pair.geometry shape)

/-- The anchors of the separated orientation (Base II.2.2.M): the divided and joined
members over the limit, the leaf one remote. -/
noncomputable def separatedAnchor (divided : DividedData profile) :
    ∀ j, Anchor w ((separatedOrientation input shape divided
      (RegrowthBalances.limit_connected w) (RegrowthBalances.limit_genus w)).member j)
  | ⟨0, _⟩ => remoteLeafAnchor input shape (pinSheet profile 1)
      (W2SourceTransport.alignedTogether profile)
      (remoteLeaf input shape (RegrowthBalances.limit_connected w)
        (RegrowthBalances.limit_genus w))
  | ⟨1, _⟩ => localDividedAnchor input shape divided
  | ⟨2, _⟩ => joinedAnchor input shape (divided.geometry shape)

/-- **Every position of Equation (7) is anchored at the wall**, in both orientations: the
members over the limit by the identity, the remote one by the inverse branch swap. -/
noncomputable def limitAnchor (j : Fin 3) : Anchor w ((columns input shape).member j) :=
  if hAligned : pinSheet profile 0 = pinSheet profile 1 then
    anchorOf shape (limitColumns_eq_alignedOrientation input shape _ _ hAligned)
      (alignedAnchor input shape (exists_leafPair shape hAligned).some) j
  else
    anchorOf shape (limitColumns_eq_separatedOrientation input shape _ _ hAligned)
      (separatedAnchor input shape (exists_dividedData shape hAligned).some) j

/-- The leaf position puts every wall occurrence on the fresh side. -/
theorem right_zero : ((columns input shape).member 0).right = fun _ ↦ true := by
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [columns, limitColumns_eq_alignedOrientation input shape _ _ hAligned]
    rfl
  · rw [columns, limitColumns_eq_separatedOrientation input shape _ _ hAligned]
    rfl

/-- The divided position splits the wall's two occurrences as the star does. -/
theorem right_one : ((columns input shape).member 1).right = star.right := by
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [columns, limitColumns_eq_alignedOrientation input shape _ _ hAligned]
    rfl
  · rw [columns, limitColumns_eq_separatedOrientation input shape _ _ hAligned]
    rfl

/-- So does the joined position. -/
theorem right_two : ((columns input shape).member 2).right = star.right := by
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [columns, limitColumns_eq_alignedOrientation input shape _ _ hAligned]
    rfl
  · rw [columns, limitColumns_eq_separatedOrientation input shape _ _ hAligned]
    rfl

end Positions

/-! ## 5.  The nonsingular positions of Equation (7) as star members (Stage 1) -/

section Census

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (initial : StableLengthMatrixLabelling ((columns input shape).member 0).datum (Fin p))

/-- Equation (7)'s labelling of position `j`, induced from the initial one. -/
noncomputable abbrev lab (j : Fin 3) :=
  (columns input shape).labelling initial j

/-- The nonsingular positions of Equation (7). -/
def Nonsingular (j : Fin 3) : Prop :=
  ((columns input shape).squareMatrix initial j).det ≠ 0

/-- The full-dimensional presentation of a nonsingular position, from the regrowth's own
cover (`RegrowthBalances.regrowthPresentation`), at Equation (7)'s labelling. -/
noncomputable def fdAt (j : Fin 3) (hj : Nonsingular w input shape initial j) :
    FullDimensionalSourcePresentation ((columns input shape).member j).datum (Fin p) :=
  RegrowthBalances.regrowthPresentation w hy (limitAnchor input shape j).E
    (((columns input shape).member j).valid_of_old input.valid)
    (limitAnchor input shape j).genus_eq (lab w input shape initial j) hj

/-- **The star member of a nonsingular position of Equation (7).** -/
noncomputable def rep (j : Fin 3) (hj : Nonsingular w input shape initial j) :
    GeometricStar.StarMember hy w :=
  StarCensusEngine.starMember (w := w) (hy := hy) (E := (limitAnchor input shape j).E)
    (fd := fdAt w hy input shape initial j hj)
    (hRetained := (limitAnchor input shape j).retained)
    (M := (limitAnchor input shape j).M) (φ := (limitAnchor input shape j).φ)
    (hMerge := (limitAnchor input shape j).hMerge) (hOld := (limitAnchor input shape j).hOld)
    (hEdge := (limitAnchor input shape j).hEdge)
    (limitAnchor input shape j).hV (limitAnchor input shape j).hR

/-- **The multiplicity of a position's star class is its term of Equation (7)**, up to
sign. -/
theorem multNat_rep (j : Fin 3) (hj : Nonsingular w input shape initial j) :
    (GeometricStar.Star.toFibre (rep w hy input shape initial j hj).cls).multNat =
      (signedMult (lab w input shape initial j).presentation).num.natAbs :=
  M11StarCensusProof.num_natAbs_eq_of_abs_eq (absMult_labelling_indep _ _)

/-- A singular position contributes nothing to Equation (7). -/
theorem signedMult_eq_zero (j : Fin 3) (hj : ¬ Nonsingular w input shape initial j) :
    signedMult (lab w input shape initial j).presentation = 0 := by
  unfold Nonsingular at hj
  rw [not_not] at hj
  unfold signedMult
  rw [show GluingDatum.LengthMatrixPresentation.matrix (lab w input shape initial j).presentation =
    (columns input shape).squareMatrix initial j from rfl, hj, mul_zero]

include hy in
/-- **Every term of Equation (7) is an integer.** -/
theorem integral_signedMult (j : Fin 3) :
    ∃ value : ℤ, signedMult (lab w input shape initial j).presentation = (value : ℚ) := by
  by_cases hj : Nonsingular w input shape initial j
  · exact isIntegralMultiplicity (fdAt w hy input shape initial j hj)
  · exact ⟨0, by rw [signedMult_eq_zero w input shape initial j hj, Int.cast_zero]⟩

include hy in
/-- **Equation (7) at the wall, in the initial labelling**: from a nonsingular position's
own presentation (`RegrowthBalances.m1k_sum_signedMult_eq_zero_of_source`), and trivially
when every position is singular. -/
theorem sum_signedMult_eq_zero :
    ∑ j : Fin 3, signedMult (lab w input shape initial j).presentation = 0 := by
  by_cases h : ∃ j, Nonsingular w input shape initial j
  · obtain ⟨j, hj⟩ := h
    exact RegrowthBalances.m1k_sum_signedMult_eq_zero_of_source input shape _ _ initial
      (limitAnchor input shape j).E (limitAnchor input shape j).genus_eq
      (fdAt w hy input shape initial j hj)
  · simp only [not_exists] at h
    exact Finset.sum_eq_zero fun j _ ↦ signedMult_eq_zero w input shape initial j (h j)

end Census

/-! ## 6.  Distinct positions are distinct star classes (Stage 3) -/

/-- The regrown-column arithmetic separating `M⁽²⁾` from `M⁽³⁾`: at `e₁`'s row `c⁽²⁾` is at
least `1` while `c⁽³⁾ - s` is at most `1/(k+1)`. -/
theorem thirdNew_ne_secondNew {target : CFGraph} {degree : ℕ} {wall : target.V}
    {data : GluingDatum target degree} {star : TwoStar target wall}
    {block : WallBlock data wall} {profile : SourceProfile data star block}
    (shape : Shape profile)
    (h : ∀ path, W2M1kCommonBalance.thirdNewColumn profile shape path =
      W2M1kCommonBalance.secondNewColumn profile shape path) : False := by
  have h1 := h (W2M1kCommonBalance.firstRow profile)
  have hk := W2M1kCommonBalance.one_lt_k_cast profile shape
  simp only [W2M1kCommonBalance.thirdNewColumn, W2M1kCommonBalance.secondNewColumn,
    ite_true] at h1
  have hA : (if W2M1kCommonBalance.firstRow profile = W2M1kCommonBalance.thirdRow profile
      then (1 : ℚ) else 0) / ((shape.k : ℚ) + 1) ≤ 1 / ((shape.k : ℚ) + 1) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    split_ifs <;> norm_num
  have hB : (0 : ℚ) ≤ (if W2M1kCommonBalance.firstRow profile =
      W2M1kCommonBalance.secondRow profile then (1 : ℚ) else 0) / ((shape.k : ℚ) - 1) := by
    apply div_nonneg _ (by linarith)
    split_ifs <;> norm_num
  have hC : 1 / ((shape.k : ℚ) + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

section Separation

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (initial : StableLengthMatrixLabelling ((columns input shape).member 0).datum (Fin p))

/-- A frame isomorphism between positions preserves the regrown column. -/
theorem newColumn_eq_of_frameIso {j j' : Fin 3} {hj : Nonsingular w input shape initial j}
    {hj' : Nonsingular w input shape initial j'}
    (fi : GeometricSegmentWalls.FrameIso (rep w hy input shape initial j hj).member.frame
      (rep w hy input shape initial j' hj').member.frame) (path : StablePath w.limit) :
    W2M1kCommonBalance.newColumn profile shape j' path =
      W2M1kCommonBalance.newColumn profile shape j path := by
  have h := StarCensusEngine.frameIso_matrix_new (E := (limitAnchor input shape j).E)
    (E' := (limitAnchor input shape j').E) (limitAnchor input shape j).retained
    (limitAnchor input shape j').retained fi path
  rwa [Anchor.matrix_new, Anchor.matrix_new, (columns input shape).regrown,
    (columns input shape).regrown] at h

/-- A frame isomorphism between positions preserves or complements the side assignment. -/
theorem side_of_frameIso {j j' : Fin 3} {hj : Nonsingular w input shape initial j}
    {hj' : Nonsingular w input shape initial j'}
    (fi : GeometricSegmentWalls.FrameIso (rep w hy input shape initial j hj).member.frame
      (rep w hy input shape initial j' hj').member.frame) :
    (∀ e ∈ GluingDatum.incidentEdges (mergeVertex w),
        ((columns input shape).member j').right e = ((columns input shape).member j).right e) ∨
      (∀ e ∈ GluingDatum.incidentEdges (mergeVertex w),
        ((columns input shape).member j').right e =
          !((columns input shape).member j).right e) :=
  W3FourStarCensusProof.frameIso_side (hy := hy) (limitAnchor input shape j).retained
    (limitAnchor input shape j').retained fi

/-- The leaf position against a position splitting the wall as the star does. -/
theorem false_of_side_leaf (right : (w.frame.limitTarget w.column).edges → Bool)
    (hRight : right = star.right)
    (h : (∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), right e = true) ∨
      (∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), right e = !true)) : False := by
  subst hRight
  rcases h with h | h
  · have := h (star.edge 0) (star.edge_mem_incidentEdges 0)
    rw [star.right_edge_zero] at this
    exact Bool.false_ne_true this
  · have := h (star.edge 1) (star.edge_mem_incidentEdges 1)
    rw [star.right_edge_one] at this
    exact absurd this (by decide)

/-- **The leaf position is not in the class of any other position.** -/
theorem not_rel_leaf {j : Fin 3} (hj0 : j ≠ 0) {h0 : Nonsingular w input shape initial 0}
    {hj : Nonsingular w input shape initial j} :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (rep w hy input shape initial 0 h0).member.frame
      (rep w hy input shape initial j hj).member.frame) := by
  rintro ⟨fi⟩
  have hSide := side_of_frameIso w hy input shape initial fi
  rw [right_zero] at hSide
  have hRight : ((columns input shape).member j).right = star.right := by
    fin_cases j
    · exact absurd rfl hj0
    · exact right_one input shape
    · exact right_two input shape
  exact false_of_side_leaf w _ hRight hSide

/-- **The divided and joined positions are distinct star classes.** -/
theorem not_rel_12 {h1 : Nonsingular w input shape initial 1}
    {h2 : Nonsingular w input shape initial 2} :
    ¬ Nonempty (GeometricSegmentWalls.FrameIso (rep w hy input shape initial 1 h1).member.frame
      (rep w hy input shape initial 2 h2).member.frame) := fun ⟨fi⟩ ↦
  thirdNew_ne_secondNew shape (newColumn_eq_of_frameIso w hy input shape initial fi)

end Separation

/-! ## 7.  The census from exhaustion (Stage 2 residue) -/

section Assembly

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (initial : StableLengthMatrixLabelling ((columns input shape).member 0).datum (Fin p))

/-- **Distinct nonsingular positions are distinct star classes** (Stage 3), at every
wall. -/
theorem rep_eq_of_cls_eq (j : Fin 3) (hj : Nonsingular w input shape initial j)
    (j' : Fin 3) (hj' : Nonsingular w input shape initial j')
    (h : (rep w hy input shape initial j hj).cls = (rep w hy input shape initial j' hj').cls) :
    j = j' := by
  have hRel := Quotient.exact h
  have hRel' : Nonempty (GeometricSegmentWalls.FrameIso
      (rep w hy input shape initial j' hj').member.frame
      (rep w hy input shape initial j hj).member.frame) :=
    hRel.elim fun fi ↦ ⟨fi.symm⟩
  fin_cases j <;> fin_cases j'
  · rfl
  · exact (not_rel_leaf w hy input shape initial (by decide) hRel).elim
  · exact (not_rel_leaf w hy input shape initial (by decide) hRel).elim
  · exact (not_rel_leaf w hy input shape initial (by decide) hRel').elim
  · rfl
  · exact (not_rel_12 w hy input shape initial hRel).elim
  · exact (not_rel_leaf w hy input shape initial (by decide) hRel').elim
  · exact (not_rel_12 w hy input shape initial hRel').elim
  · rfl

/-- The positions' classes, as a map from the nonsingular positions to the star. -/
noncomputable def repCls (j : {j : Fin 3 // Nonsingular w input shape initial j}) :
    GeometricStar.Star hy w :=
  (rep w hy input shape initial j.1 j.2).cls

theorem repCls_injective : Function.Injective (repCls w hy input shape initial) :=
  fun a b h ↦ Subtype.ext (rep_eq_of_cls_eq w hy input shape initial a.1 a.2 b.1 b.2 h)

/-- **The exhaustion residue at one wall** (Stage 2): every member of the star is in the
class of some nonsingular position.  *Interface*: with Stages 1 and 3 it is equivalent to
the census at this wall (`census_of_exhaustion`, `exhaustion_of_census`). -/
def Exhausts : Prop :=
  ∀ member : GeometricStar.StarMember hy w, ∃ j : Fin 3,
    ∃ hj : Nonsingular w input shape initial j,
      member.cls = (rep w hy input shape initial j hj).cls

theorem repCls_surjective (hExh : Exhausts w hy input shape initial) :
    Function.Surjective (repCls w hy input shape initial) := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨j, hj, h⟩ := hExh member
  exact ⟨⟨j, hj⟩, h.symm⟩

/-- **The M-1k census at one wall from exhaustion.** -/
theorem census_of_exhaustion (hExh : Exhausts w hy input shape initial) :
    ∃ e : {j : Fin 3 // Nonsingular w input shape initial j} ≃ GeometricStar.Star hy w,
      ∀ j, (GeometricStar.Star.toFibre (e j)).multNat =
        (signedMult (lab w input shape initial j.1).presentation).num.natAbs :=
  ⟨Equiv.ofBijective _ ⟨repCls_injective w hy input shape initial,
      repCls_surjective w hy input shape initial hExh⟩,
    fun j ↦ multNat_rep w hy input shape initial j.1 j.2⟩

/-- **Interface: the census implies exhaustion.** -/
theorem exhaustion_of_census
    (e : {j : Fin 3 // Nonsingular w input shape initial j} ≃ GeometricStar.Star hy w) :
    Exhausts w hy input shape initial := by
  classical
  have hBij : Function.Bijective (repCls w hy input shape initial) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨repCls_injective w hy input shape initial, Fintype.card_congr e⟩
  intro member
  obtain ⟨j, hj⟩ := hBij.2 member.cls
  exact ⟨j.1, j.2, hj.symm⟩

/-- **The star clause from Equation (7) and the census**: the singular positions
contribute `0`, the census reads the nonsingular ones as the star
(`StarCensusEngine.starParityAt_of_census`). -/
theorem starParityAt_of_census
    (e : {j : Fin 3 // Nonsingular w input shape initial j} ≃ GeometricStar.Star hy w)
    (hmult : ∀ j, (GeometricStar.Star.toFibre (e j)).multNat =
      (signedMult (lab w input shape initial j.1).presentation).num.natAbs) :
    RegrowthWallInput.StarParityAt hy w :=
  StarCensusEngine.starParityAt_of_census
    (fun j ↦ signedMult (lab w input shape initial j).presentation)
    (integral_signedMult w hy input shape initial)
    (sum_signedMult_eq_zero w hy input shape initial)
    (Nonsingular w input shape initial) (signedMult_eq_zero w input shape initial) e hmult

/-- **Stage 2 is the whole content of the clause at a wall.** -/
theorem starParityAt_of_exhaustion (hExh : Exhausts w hy input shape initial) :
    RegrowthWallInput.StarParityAt hy w := by
  obtain ⟨e, hmult⟩ := census_of_exhaustion w hy input shape initial hExh
  exact starParityAt_of_census w hy input shape initial e hmult

end Assembly

/-! ## 8.  Stage 2 reduced to decoupled transports -/

section Transport

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (initial : StableLengthMatrixLabelling ((columns input shape).member 0).datum (Fin p))

/-- **The receipt a member must present to be received at position `j`**: a decoupled
transport, along its limit isomorphism composed with the position's anchor inverse, from
its own normal form at some placement onto the position's pasted resolution. -/
abbrev PositionTransport (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : PlacementSpec other placement) (j : Fin 3) : Type :=
  ResolutionExpansionFree.TransportFree
    (ψ.datum.trans (limitAnchor input shape j).φ.symm) (mergeVertex other) (mergeVertex w)
    placement ((columns input shape).member j).right
    (memberResolution other placement hPlacement) (limitAnchor input shape j).res

/-- **Stage 2 reduced to transports**: if every star member presents a decoupled
transport onto some nonsingular position, from its own normal form at some placement,
the star is exhausted by the positions. -/
theorem exhausts_of_transports
    (h : ∀ member : GeometricStar.StarMember hy w,
      ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
      ∃ hPlacement : PlacementSpec member.member placement,
      ∃ j : Fin 3, ∃ _ : Nonsingular w input shape initial j,
        Nonempty (PositionTransport w hy input shape member.member ψ placement hPlacement j)) :
    Exhausts w hy input shape initial := by
  intro member
  obtain ⟨ψ, placement, hPlacement, j, hj, ⟨t⟩⟩ := h member
  refine ⟨j, hj, ?_⟩
  have hNV := M11WallExhaustion.sourceVertexMap_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  have hNE := M11WallExhaustion.retainedSourceEdge_datumIso member.member.frame.data rfl
    (fst_ne_snd (member.member.frame.edgeOf member.member.column))
    (member.member.frame.numEdges_edgeOf member.member.column) placement hPlacement
    member.member.frame.fullDim.targetConnected member.member.frame.fullDim.targetGenus
  exact StarCensusEngine.cls_eq_of_transport (w := w) (hy := hy)
    (E := (limitAnchor input shape j).E)
    (fd := fdAt w hy input shape initial j hj)
    (hRetained := (limitAnchor input shape j).retained)
    (M := (limitAnchor input shape j).M) (φ := (limitAnchor input shape j).φ)
    (hMerge := (limitAnchor input shape j).hMerge) (hOld := (limitAnchor input shape j).hOld)
    (hEdge := (limitAnchor input shape j).hEdge)
    (limitAnchor input shape j).hV (limitAnchor input shape j).hR
    (compat := (limitAnchor input shape j).compat) (limitAnchor input shape j).hD
    member ψ (memberNorm member.member placement hPlacement) hNV hNE t

end Transport

/-! ## 9.  The family clause -/

section Family

/-- **The M-1k star census**: at every `w2M1k` regrowth, for every Equation (7)
labelling, the nonsingular positions are the star, class by class, with their
multiplicities. -/
def W2M1kStarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2M1k →
    ∀ (star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W2SourceInput w.limit star) (block : WallBlock w.limit (mergeVertex w))
      (profile : SourceProfile w.limit star block) (shape : Shape profile)
      (initial : StableLengthMatrixLabelling ((columns input shape).member 0).datum (Fin p)),
      ∃ e : {j : Fin 3 // Nonsingular w input shape initial j} ≃ GeometricStar.Star hy w,
        ∀ j, (GeometricStar.Star.toFibre (e j)).multNat =
          (signedMult (lab w input shape initial j.1).presentation).num.natAbs

/-- **Stage 2's residue, family-wide**: at every `w2M1k` regrowth, for every Equation (7)
labelling, every star member is in the class of a nonsingular position.
*Interface*: equivalent to `W2M1kStarCensus` (`w2M1kStarExhaustion_iff`). -/
def W2M1kStarExhaustion (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2M1k →
    ∀ (star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : W2SourceInput w.limit star) (block : WallBlock w.limit (mergeVertex w))
      (profile : SourceProfile w.limit star block) (shape : Shape profile)
      (initial : StableLengthMatrixLabelling ((columns input shape).member 0).datum (Fin p)),
      Exhausts w hy input shape initial

variable {degree n p : ℕ}

theorem w2M1kStarCensus_of_exhaustion (hExh : W2M1kStarExhaustion degree n p) :
    W2M1kStarCensus degree n p :=
  fun core y hy w cls htag star input block profile shape initial ↦
    census_of_exhaustion w hy input shape initial
      (hExh core y hy w cls htag star input block profile shape initial)

theorem exhaustion_of_w2M1kStarCensus (hCensus : W2M1kStarCensus degree n p) :
    W2M1kStarExhaustion degree n p :=
  fun core y hy w cls htag star input block profile shape initial ↦
    exhaustion_of_census w hy input shape initial
      (hCensus core y hy w cls htag star input block profile shape initial).choose

/-- **Interface**: exhaustion is equivalent to the census. -/
theorem w2M1kStarExhaustion_iff :
    W2M1kStarExhaustion degree n p ↔ W2M1kStarCensus degree n p :=
  ⟨w2M1kStarCensus_of_exhaustion, exhaustion_of_w2M1kStarCensus⟩

/-- **`FamilyStarParity … .w2M1k` from the M-1k star census**: Equation (7) at the
regrowth, read mod two through the census, at the wall labelling of the leaf position
(`StarCensusEngine.labelling`). -/
theorem familyStarParity_w2M1k_of_census (h : W2M1kStarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w2M1k := by
  intro core y hy w cls htag
  obtain ⟨star, input, block, profile, shape, -⟩ :=
    RegrowthBalances.exists_w2M1k_balance w hy cls htag
  let initial := StarCensusEngine.labelling w hy ((columns input shape).member 0).datum
    (limitAnchor input shape 0).E
  obtain ⟨e, hmult⟩ := h core y hy w cls htag star input block profile shape initial
  exact starParityAt_of_census w hy input shape initial e hmult

/-- **The `w2M1k` clause of `FamilyStarParity` at genus six and degree four**, modulo
Stage 2's exhaustion alone. -/
theorem familyStarParity_w2M1k_of_exhaustion
    (hExh : W2M1kStarExhaustion (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2M1k :=
  familyStarParity_w2M1k_of_census (w2M1kStarCensus_of_exhaustion hExh)

end Family

end DraismaVargas.Count.W2M1kStarCensusProof
