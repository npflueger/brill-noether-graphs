import DraismaVargas.LocalCases.GlobalM1k
import DraismaVargas.LocalCases.M11SourceGenus
import DraismaVargas.LocalCases.W3ShiftSourceCandidates

/-!
# Source-derived M-1k geometry (Figure 33, Equation (7))

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7).  This is the `w2M1k` tag of `ClassifiedContinuation.SourceCase`.
The neighbouring divalent case `w2M11` (Figure 32) is treated in
`M11SourceCandidates` / `M11SourceGenus` / `M11RemoteCandidates`, which this
file follows closely.

## The datum this is about

The input is `SecondEquation.W2SourceInput`, an actual `W2R2SourceProfile`
occurrence profile at a wall block with `r₀(A₀) = 2` and non-dangling valency
three, plus the `Shape` refinement below: Cardinality M (the dangling
occurrence `e₄` is above `t₃`) and `k₁ = 1` with `k = k₂ ≥ 2`, so
`|A₀| = k + 1` and `|e₃| = k`.  `W2SourceInput` carries
`equation_c : data.targetExcess wall = 1`, so this module is on the limit/wall
side of the `AuxR0SourceInput` / `FullDimensionalSourcePresentation` bridge --
the same side as `AuxR0SourceInput`, never a
`FullDimensionalSourcePresentation` datum.

`Shape`'s fields are jointly satisfiable: `W2R2SourceProfile.SourceProfile.cases` already
offers Cardinality M as one of its two disjuncts, `unit_index` fixes which of
the two survivors of the double direction is `e₁`, and `1 < k` is exactly what
separates this case from `w2M11` (`k = 1`) and is compatible with everything
else, since `blockCard` then reads `|A₀| = k + 1 ≥ 3`.

## What is constructed

All three Figure 33 members as actual arbitrary-degree outgoing gluing data,
with every background receipt and exterior refinement **derived** from the
occurrence indices rather than assumed:

* `LeafPair.candidate` -- `M^{(1)}`, Base I.a: joined leaf pair, singleton
  detached at the trivalent endpoint, discrete new edge;
* `DividedData.candidate` -- `M^{(2)}`, Base II.2.2.M: opposite singleton
  detachments at two divalent endpoints, `|e'| = 1` and `|e''| = k - 1`;
* `joinedCandidate` -- `M^{(3)}`, Base II.1.M: the whole block retained at
  both divalent endpoints and along the new edge, `|e'| = k + 1`.

Each comes with validity (`leaf_valid`, `divided_valid`, `joined_valid`),
preservation of the source genus (`leaf_sourceGenus`, `divided_sourceGenus`,
`joined_sourceGenus`) and the actual target valencies of its expanded wall
(`leaf_target_valencies` = `1, 3`, the other two = `2, 2`).  The genus proofs
use the blockwise Euler count, not the star form: on the distinguished block
neither `M^{(1)}` nor `M^{(2)}` is a star.

## What is **not** constructed

Equation (7)'s determinant balance on actual matrices, the honest stable
presentations, the common retained columns, and the stable-graph incidence
transport; those are in `W2M1kCommonBalance`, `W2M1kLimitColumns` and
`W2M1kStableIncidence`.

## `M^{(1)}` and `M^{(2)}` never share a datum

`M^{(1)}` and `M^{(2)}` are **never** resolutions of the same gluing datum
(`no_common_geometry`, `not_leafPair_and_dividedData`): the first needs both
target directions to isolate one and the same sheet of `A₀`
(`firstPattern_forces_aligned`, the source's `k₁ = |A''| = k₄` in Base I.a),
the second needs them to isolate distinct sheets (Base II.2.2.M).  Exactly one
of the two is therefore available over any given datum
(`exists_leafPair_or_dividedData`).

This is a **gauge** phenomenon, not a matter of Figure 33 itself: swapping the two
sheets along one wall branch fixes the wall partition and the other branch's
occurrence partition and transports the moved one by the transposition, which
exchanges the two situations (`branchSwap_aligns`, `branchSwap_separates`,
with `branchSwapped_valid` for the validity transport).  Figure 32 has the same
feature and `GlobalM11Arbitrary.candidates` accommodates it by taking its second
member over `SwappedDatum`.  `GlobalM1k.candidates` takes all three patterns
over one `data` and one `Geometry`, so `GlobalM1k.exists_valid_positive_exit`
has no instance at an actual `w2M1k` profile; `GlobalM1k.swappedCandidates`
takes the second member over the branch-swapped datum instead.  The
branch-swap lemmas here carry the branch **separation** as the explicit
hypothesis `hSeparated`.  It is proved in general, from
`graph_connected target` and `genus target = 0`
(`FullDimensionalSourcePresentation.targetConnected` / `targetGenus`), by
`Infrastructure.TargetSeparation.edgeMoved_eq_false`.  But
`branchSwapped_block_fixed`, `branchSwap_aligns` and `branchSwap_separates`
below take neither of those two target-tree hypotheses -- only `data`, `star`,
`shape`/`profile` and the swap data -- so `hSeparated` is carried here:
adding the two hypotheses to these signatures would only relocate the carried
assumption, not discharge it.
-/

namespace DraismaVargas.LocalCases.W2M1kSourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The literal `w2M1k` source shape -/

/-- The actual M-1k refinement of a `w2-r2-nd3` source profile. -/
structure Shape {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block) where
  /-- `k = k₂ = k₃`, so that `|A₀| = k + 1`. -/
  k : ℕ
  one_lt_k : 1 < k
  blockCard : (data.vertexPartition wall).blockCard block.1 = k + 1
  /-- Cardinality M: the dangling occurrence `e₄` lies above `t₃`. -/
  deleted_single : profile.deleted.edge.1.1.1 = star.edge profile.singleLabel
  /-- `k₁ = 1`: the first survivor of the double direction is `e₁`. -/
  unit_index : data.sourceEdgeIndex profile.first.1 = 1

namespace Shape

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Cardinality M, read off the profile's own case disjunction. -/
theorem cardinality (shape : Shape profile) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 =
        (data.vertexPartition wall).blockCard block.1 ∧
      data.sourceEdgeIndex profile.third.1 + 1 =
        (data.vertexPartition wall).blockCard block.1 := by
  rcases profile.cases with ⟨_, hPair, hSingle⟩ | ⟨hDouble, _, _⟩
  · exact ⟨hPair, hSingle⟩
  · exact absurd
      (star.edge_injective (shape.deleted_single.symm.trans hDouble)).symm
      profile.labels_ne

/-- `k₂ = k`: the second survivor above `t₂` carries the rest of the block. -/
theorem second_index (shape : Shape profile) :
    data.sourceEdgeIndex profile.second.1 = shape.k := by
  have hPair := shape.cardinality.1
  rw [shape.unit_index, shape.blockCard] at hPair
  omega

/-- `k₃ = k`: the single direction's survivor `e₃` has index `k`. -/
theorem third_index (shape : Shape profile) :
    data.sourceEdgeIndex profile.third.1 = shape.k := by
  have hSingle := shape.cardinality.2
  rw [shape.blockCard] at hSingle
  omega

/-- The two target directions are the profile's own labels. -/
theorem label_cases (profile : W2R2SourceProfile.SourceProfile data star block)
    (label : Fin 2) : label = profile.doubleLabel ∨ label = profile.singleLabel := by
  have := profile.labels_ne
  omega

end Shape

/-- The unique index-one incident occurrence in each target direction: `e₁`
above `t₂`, and the dangling `e₄` above `t₃`.  These are the two occurrences
Figure 33 detaches, one at each endpoint. -/
noncomputable def pinnedOccurrence {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block) (label : Fin 2) :
    IncidentSourceEdge data (WallBlock.sourceVertex data wall block) :=
  if label = profile.doubleLabel then profile.first else profile.deleted.edge

/-- The sheet pinned as a singleton in one target direction. -/
noncomputable def pinSheet {block : WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block) (label : Fin 2) :
    Fin degree := (pinnedOccurrence profile label).1.1.2

section Pinned

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem pinnedOccurrence_double :
    pinnedOccurrence profile profile.doubleLabel = profile.first := by
  unfold pinnedOccurrence
  exact if_pos rfl

theorem pinnedOccurrence_single :
    pinnedOccurrence profile profile.singleLabel = profile.deleted.edge := by
  unfold pinnedOccurrence
  exact if_neg profile.labels_ne.symm

/-- Every pinned sheet lies in the distinguished wall block. -/
theorem pinSheet_rel (label : Fin 2) :
    (data.vertexPartition wall).Rel block.1 (pinSheet profile label) := by
  have hIncident := (incident_wallBlock_sourceVertex_iff data block
    (pinnedOccurrence profile label).1).mp (pinnedOccurrence profile label).2
  exact (WallBlock.ofSheet_eq_iff_rel data wall block (pinSheet profile label)).mp hIncident.2

theorem pinnedOccurrence_target (shape : Shape profile) (label : Fin 2) :
    (pinnedOccurrence profile label).1.1.1 = star.edge label := by
  rcases Shape.label_cases profile label with rfl | rfl
  · rw [pinnedOccurrence_double]; exact profile.first_target
  · rw [pinnedOccurrence_single]; exact shape.deleted_single

theorem pinnedOccurrence_index (shape : Shape profile) (label : Fin 2) :
    data.sourceEdgeIndex (pinnedOccurrence profile label).1 = 1 := by
  rcases Shape.label_cases profile label with rfl | rfl
  · rw [pinnedOccurrence_double]; exact shape.unit_index
  · rw [pinnedOccurrence_single]; exact profile.deleted.index_one

theorem pinSheet_blockCard (shape : Shape profile) (label : Fin 2) :
    (data.edgePartition (star.edge label)).blockCard (pinSheet profile label) = 1 := by
  have hIndex : data.sourceEdgeIndex (pinnedOccurrence profile label).1 =
      (data.edgePartition (pinnedOccurrence profile label).1.1.1).blockCard
        (pinSheet profile label) := rfl
  rw [pinnedOccurrence_target shape label, pinnedOccurrence_index shape label] at hIndex
  exact hIndex.symm

/-- Each pinned sheet is a singleton block of its own direction's occurrence
partition.  This is the entire local content of `k₁ = 1` and of
dangling-no-glue at `e₄`. -/
theorem pinSheet_block (shape : Shape profile) (label : Fin 2) :
    (data.edgePartition (star.edge label)).block (pinSheet profile label) =
      {pinSheet profile label} :=
  SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _ (pinSheet_blockCard shape label)

theorem pinSheet_blockCard_wall (shape : Shape profile) (label : Fin 2) :
    (data.vertexPartition wall).blockCard (pinSheet profile label) = shape.k + 1 := by
  unfold SheetPartition.blockCard
  rw [← (data.vertexPartition wall).block_eq_of_rel (pinSheet_rel label)]
  exact shape.blockCard

end Pinned



/-! ## Identifying the pinned sheets -/

section Identification

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- On the M-1k block each target direction carries exactly one incident
occurrence of index one, namely the pinned one.  The other survivor of that
direction has index `k ≥ 2`. -/
theorem eq_pinnedOccurrence_of_index_one (shape : Shape profile) (label : Fin 2)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block))
    (hTarget : edge.1.1.1 = star.edge label)
    (hIndex : data.sourceEdgeIndex edge.1 = 1) :
    edge = pinnedOccurrence profile label := by
  have hk := shape.one_lt_k
  rcases profile.exhaustive edge with rfl | rfl | rfl | rfl
  · have hLabel : profile.doubleLabel = label :=
      star.edge_injective (profile.first_target.symm.trans hTarget)
    rw [← hLabel, pinnedOccurrence_double]
  · rw [shape.second_index] at hIndex; omega
  · rw [shape.third_index] at hIndex; omega
  · have hLabel : profile.singleLabel = label :=
      star.edge_injective (shape.deleted_single.symm.trans hTarget)
    rw [← hLabel, pinnedOccurrence_single]

/-- **The pinned sheet is the only sheet of the block that one direction's
occurrence partition isolates.**  Everything downstream about which Figure 33
member a given datum admits is a corollary of this. -/
theorem eq_pinSheet_of_block_singleton (shape : Shape profile) (label : Fin 2)
    (sheet : Fin degree) (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hSingleton : (data.edgePartition (star.edge label)).block sheet = {sheet}) :
    sheet = pinSheet profile label := by
  have hRepr : (data.edgePartition (star.edge label)).repr sheet = sheet := by
    have hMem : (data.edgePartition (star.edge label)).repr sheet ∈
        (data.edgePartition (star.edge label)).block sheet :=
      ((data.edgePartition (star.edge label)).mem_block_iff sheet _).mpr
        ((data.edgePartition (star.edge label)).rel_repr_right sheet)
    rw [hSingleton] at hMem
    simpa using hMem
  have hIncident : Incident data (data.sourceEdge (star.edge label) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    refine ⟨star.edge_mem_incidentEdges label, ?_⟩
    apply (WallBlock.ofSheet_eq_iff_rel data wall block _).mpr
    exact hRel.trans ((star.edgePartition_refines_wall data label).rel
      ((data.edgePartition (star.edge label)).rel_repr_right sheet))
  have hIndex : data.sourceEdgeIndex (data.sourceEdge (star.edge label) sheet) = 1 := by
    rw [GluingDatum.sourceEdgeIndex_sourceEdge]
    simp [SheetPartition.blockCard, hSingleton]
  have hEq := eq_pinnedOccurrence_of_index_one shape label
    ⟨data.sourceEdge (star.edge label) sheet, hIncident⟩ rfl hIndex
  have hSheet := congrArg (fun edge ↦ edge.1.1.2) hEq
  change (data.edgePartition (star.edge label)).repr sheet = pinSheet profile label at hSheet
  rw [hRepr] at hSheet
  exact hSheet

/-- Each direction's occurrence partition isolates its own pinned sheet, so it
refines the endpoint partition that detaches it. -/
theorem edgePartition_refines_detachSheet (shape : Shape profile) (label : Fin 2)
    (remainder : Fin degree) (hne : pinSheet profile label ≠ remainder)
    (hTogether : (data.vertexPartition wall).Rel (pinSheet profile label) remainder) :
    (data.edgePartition (star.edge label)).Refines
      ((data.vertexPartition wall).detachSheet (pinSheet profile label) remainder
        hne hTogether) :=
  SheetPartition.refines_detachSheet_of_block_singleton _ _ _ _ hne hTogether
    (star.edgePartition_refines_wall data label) (pinSheet_block shape label)

end Identification


/-! ## Backgrounds and geometries -/

/-- Every occurrence at a divalent wall carries one of the two star labels. -/
theorem exists_label (star : TwoStar target wall) (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) : ∃ label, star.edge label = edge :=
  ⟨star.label.symm ⟨edge, hAt⟩,
    congrArg Subtype.val (star.label.apply_symm_apply ⟨edge, hAt⟩)⟩

section Geometries

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The `M^{(1)}` background, anchored at an arbitrary sheet of the
distinguished block rather than at its canonical representative.  Every other
wall block is r0 and grows unit-index leaf arms; this is
`M11SourceCandidates.splitBackgroundOfUnramified` with the anchor moved. -/
noncomputable def splitBackgroundAt (input : W2SourceInput data star)
    (hR : data.localRamification wall block = 2) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    Background data wall anchor :=
  M11SourceCandidates.splitBackgroundOfUnramified data star anchor (by
    intro other hOther
    apply W2RankObstructions.other_localRamification_eq_zero input block hR
      (WallBlock.ofSheet data wall other)
    intro hEq
    apply hOther
    change (data.vertexPartition wall).repr anchor = (data.vertexPartition wall).repr other
    rw [← hAnchor, block.2]
    exact (congrArg Subtype.val hEq).symm)

/-- Figure 33's `M^{(2)}` geometry: the two pinned sheets are detached at
opposite divalent endpoints and the residual `k - 1` class is named by a third
sheet of the block. -/
noncomputable def dividedGeometry (shape : Shape profile)
    (hPins : pinSheet profile 0 ≠ pinSheet profile 1) (third : Fin degree)
    (hThird : (data.vertexPartition wall).Rel (pinSheet profile 0) third)
    (hFirstThird : pinSheet profile 0 ≠ third)
    (hSecondThird : pinSheet profile 1 ≠ third) :
    GlobalM1k.Geometry data wall where
  first := pinSheet profile 0
  second := pinSheet profile 1
  third := third
  first_second := (pinSheet_rel 0).symm.trans (pinSheet_rel 1)
  first_third := hThird
  first_ne_second := hPins
  first_ne_third := hFirstThird
  second_ne_third := hSecondThird
  k := shape.k
  one_lt_k := shape.one_lt_k
  blockCard := pinSheet_blockCard_wall shape 0

/-- Figure 33's `M^{(1)}` geometry: the single pinned sheet is detached at the
trivalent endpoint and paired with one further sheet at the new leaf. -/
noncomputable def leafGeometry (shape : Shape profile)
    (second third : Fin degree)
    (hSecond : (data.vertexPartition wall).Rel (pinSheet profile 0) second)
    (hThird : (data.vertexPartition wall).Rel (pinSheet profile 0) third)
    (hFirstSecond : pinSheet profile 0 ≠ second)
    (hFirstThird : pinSheet profile 0 ≠ third) (hSecondThird : second ≠ third) :
    GlobalM1k.Geometry data wall where
  first := pinSheet profile 0
  second := second
  third := third
  first_second := hSecond
  first_third := hThird
  first_ne_second := hFirstSecond
  first_ne_third := hFirstThird
  second_ne_third := hSecondThird
  k := shape.k
  one_lt_k := shape.one_lt_k
  blockCard := pinSheet_blockCard_wall shape 0

/-- A block of size `k + 1 ≥ 3` supplies the residual class of `M^{(2)}`. -/
theorem exists_dividedGeometry_third (shape : Shape profile)
    (hPins : pinSheet profile 0 ≠ pinSheet profile 1) :
    ∃ third, (data.vertexPartition wall).Rel (pinSheet profile 0) third ∧
      pinSheet profile 0 ≠ third ∧ pinSheet profile 1 ≠ third :=
  (data.vertexPartition wall).exists_third_of_blockCard_eq_add_one
    (pinSheet profile 0) (pinSheet profile 1) hPins
    ((pinSheet_rel 0).symm.trans (pinSheet_rel 1)) shape.k shape.one_lt_k
    (pinSheet_blockCard_wall shape 0)

/-- The same block supplies the leaf pair and the residual sheet of `M^{(1)}`. -/
theorem exists_leafGeometry_pair (shape : Shape profile) :
    ∃ second third, (data.vertexPartition wall).Rel (pinSheet profile 0) second ∧
      (data.vertexPartition wall).Rel (pinSheet profile 0) third ∧
      pinSheet profile 0 ≠ second ∧ pinSheet profile 0 ≠ third ∧ second ≠ third := by
  obtain ⟨second, hSecond, hNeSecond⟩ :=
    (data.vertexPartition wall).exists_other_of_one_lt_blockCard (pinSheet profile 0)
      (by rw [pinSheet_blockCard_wall shape 0]; have := shape.one_lt_k; omega)
  obtain ⟨third, hThird, hNeThird, hSecondThird⟩ :=
    (data.vertexPartition wall).exists_third_of_blockCard_eq_add_one
      (pinSheet profile 0) second hNeSecond hSecond shape.k shape.one_lt_k
      (pinSheet_blockCard_wall shape 0)
  exact ⟨second, third, hSecond, hThird, hNeSecond, hNeThird, hSecondThird⟩

end Geometries


/-! ## The three Figure 33 patterns -/

section Patterns

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem joinedBackground_right (distinguished : Fin degree) (edge : target.edges) :
    (M11SourceCandidates.joinedBackground data star distinguished).right edge =
      star.right edge := rfl

theorem splitBackgroundAt_right (input : W2SourceInput data star)
    (hR : data.localRamification wall block = 2) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) (edge : target.edges) :
    (splitBackgroundAt input hR anchor hAnchor).right edge = true := rfl

/-- Figure 33's `M^{(3)}`: both endpoints keep the whole wall partition.  No
occurrence hypothesis at all is used, so this member always exists. -/
noncomputable def joinedPattern (twoStar : TwoStar target wall)
    (geometry : GlobalM1k.Geometry data wall) :
    GlobalM1k.ThirdPattern geometry where
  background := M11SourceCandidates.joinedBackground data twoStar geometry.first
  leftExternal := twoStar.edge 0
  rightExternal := twoStar.edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    have hRefines := refines_of_mem_incidentEdges data (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAt)
    simpa only [GlobalM1k.Geometry.thirdLocal, thirdResolution, joinedResolutionAt,
      ite_self] using hRefines

/-- Figure 33's `M^{(2)}`: each divalent endpoint detaches the pinned sheet of
its own target direction.  The exterior refinements are derived from the actual
occurrence indices, not assumed. -/
noncomputable def dividedPattern (shape : Shape profile)
    (hPins : pinSheet profile 0 ≠ pinSheet profile 1) (third : Fin degree)
    (hThird : (data.vertexPartition wall).Rel (pinSheet profile 0) third)
    (hFirstThird : pinSheet profile 0 ≠ third)
    (hSecondThird : pinSheet profile 1 ≠ third) :
    GlobalM1k.SecondPattern
      (dividedGeometry shape hPins third hThird hFirstThird hSecondThird) where
  background := M11SourceCandidates.joinedBackground data star (pinSheet profile 0)
  leftExternal := star.edge 0
  rightExternal := star.edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    obtain ⟨label, rfl⟩ := exists_label star edge (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAt)
    have hLabel : label = 0 ∨ label = 1 := by omega
    rcases hLabel with rfl | rfl
    · split_ifs with hRight
      · exact absurd (hRight.symm.trans (joinedBackground_right (pinSheet profile 0)
          (star.edge 0))) (by simp)
      · exact SheetPartition.refines_detachSheet_of_block_singleton
          (data.edgePartition (star.edge 0)) (data.vertexPartition wall)
          (pinSheet profile 0) (pinSheet profile 1) hPins
          ((pinSheet_rel 0).symm.trans (pinSheet_rel 1))
          (star.edgePartition_refines_wall data 0) (pinSheet_block shape 0)
    · split_ifs with hRight
      · exact SheetPartition.refines_detachSheet_of_block_singleton
          (data.edgePartition (star.edge 1)) (data.vertexPartition wall)
          (pinSheet profile 1) (pinSheet profile 0) hPins.symm
          (((pinSheet_rel 0).symm.trans (pinSheet_rel 1)).symm)
          (star.edgePartition_refines_wall data 1) (pinSheet_block shape 1)
      · exact absurd ((joinedBackground_right (pinSheet profile 0)
          (star.edge 1)).trans star.right_edge_one) hRight

/-- Figure 33's `M^{(1)}`: the new leaf keeps one pair, the trivalent endpoint
detaches the pinned sheet, and the new edge is discrete on the block.  Both
target directions must isolate the *same* sheet, which is exactly the source's
Base I.a identification `k₁ = |A''| = k₄`. -/
noncomputable def leafPattern (input : W2SourceInput data star) (shape : Shape profile)
    (hAligned : pinSheet profile 0 = pinSheet profile 1)
    (second third : Fin degree)
    (hSecond : (data.vertexPartition wall).Rel (pinSheet profile 0) second)
    (hThird : (data.vertexPartition wall).Rel (pinSheet profile 0) third)
    (hFirstSecond : pinSheet profile 0 ≠ second)
    (hFirstThird : pinSheet profile 0 ≠ third) (hSecondThird : second ≠ third) :
    GlobalM1k.FirstPattern
      (leafGeometry shape second third hSecond hThird hFirstSecond hFirstThird
        hSecondThird) where
  background := splitBackgroundAt input profile.ramification (pinSheet profile 0)
    (pinSheet_rel 0)
  firstExternal := star.edge 0
  secondExternal := star.edge 1
  leftEdges := rfl
  rightEdges := rfl
  exterior := by
    intro edge hAt
    obtain ⟨label, rfl⟩ := exists_label star edge (by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hAt)
    have hPin : pinSheet profile label = pinSheet profile 0 := by
      have hLabel : label = 0 ∨ label = 1 := by omega
      rcases hLabel with rfl | rfl
      · rfl
      · exact hAligned.symm
    have hSingleton : (data.edgePartition (star.edge label)).block (pinSheet profile 0) =
        {pinSheet profile 0} := by
      rw [← hPin]
      exact pinSheet_block shape label
    split_ifs with hRight
    · exact SheetPartition.refines_detachSheet_of_block_singleton
        (data.edgePartition (star.edge label)) (data.vertexPartition wall)
        (pinSheet profile 0) second hFirstSecond hSecond
        (star.edgePartition_refines_wall data label) hSingleton
    · exact absurd (splitBackgroundAt_right input profile.ramification
        (pinSheet profile 0) (pinSheet_rel 0) (star.edge label)) hRight

end Patterns


/-! ## Blockwise Euler counts for the three local resolutions -/

section Counts

variable {d : ℕ}

/-- Retaining one pair inside a block leaves `|A₀| - 1` induced blocks. -/
theorem pairBlock_blockCountWithin (partition : SheetPartition d)
    (first second sheet : Fin d) (hne : first ≠ second)
    (hTogether : partition.Rel first second) (hSheet : partition.Rel first sheet) :
    (partition.pairBlock first second hne).blockCountWithin partition sheet + 1 =
      partition.blockCard sheet := by
  classical
  have hBlock : partition.block sheet = partition.block first :=
    (partition.block_eq_of_rel hSheet).symm
  have hImage : (partition.block sheet).image (partition.pairBlock first second hne).repr =
      (partition.block first).erase second := by
    rw [hBlock]
    ext value
    simp only [Finset.mem_image, Finset.mem_erase, SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      by_cases hSecond : source = second
      · subst source
        rw [partition.pairBlock_repr_second first second hne hTogether]
        exact ⟨hne, rfl⟩
      · rw [partition.pairBlock_repr_of_rel_of_ne_second first second source hne
          hSource hSecond]
        exact ⟨hSecond, hSource⟩
    · rintro ⟨hValue, hMem⟩
      exact ⟨value, hMem,
        partition.pairBlock_repr_of_rel_of_ne_second first second value hne hMem hValue⟩
  have hMem : second ∈ partition.block first :=
    (partition.mem_block_iff first second).mpr hTogether
  have hPos : 0 < (partition.block first).card :=
    Finset.card_pos.mpr ⟨first, partition.self_mem_block first⟩
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  rw [hImage, hBlock, Finset.card_erase_of_mem hMem]
  omega

/-- Candidate 2's new edge induces exactly three blocks: the two detached
sheets and the residual `k - 1` class. -/
theorem secondNewEdge_blockCountWithin (partition : SheetPartition d)
    (first second third sheet : Fin d)
    (hFirstSecond : partition.Rel first second)
    (hFirstThird : partition.Rel first third)
    (hneFirstSecond : first ≠ second) (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) (hSheet : partition.Rel first sheet) :
    (secondNewEdge partition first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).blockCountWithin
      partition sheet = 3 := by
  classical
  have hInnerFirst :
      (partition.detachSheet first second hneFirstSecond hFirstSecond).repr first = first :=
    SheetPartition.detachSheet_repr_single partition first second hneFirstSecond hFirstSecond
  have hInnerOther : ∀ source, partition.Rel first source → source ≠ first →
      (partition.detachSheet first second hneFirstSecond hFirstSecond).repr source = second :=
    fun source hRel hNe ↦ SheetPartition.detachSheet_repr_of_rel_of_ne partition first second
      source hneFirstSecond hFirstSecond hNe hRel
  have hInnerRel :
      (partition.detachSheet first second hneFirstSecond hFirstSecond).Rel second third :=
    detachFirst_rel_second_third partition first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird
  have hNotRel :
      ¬ (partition.detachSheet first second hneFirstSecond hFirstSecond).Rel second first := by
    intro hRel
    apply hneFirstSecond
    exact (((hInnerOther second hFirstSecond hneFirstSecond.symm).symm.trans hRel).trans
      hInnerFirst).symm
  have hReprFirst :
      (secondNewEdge partition first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).repr first = first :=
    (SheetPartition.detachSheet_repr_of_not_rel
      (partition.detachSheet first second hneFirstSecond hFirstSecond) second third first
      hneSecondThird hInnerRel hNotRel).trans hInnerFirst
  have hReprSecond :
      (secondNewEdge partition first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).repr second = second :=
    SheetPartition.detachSheet_repr_single
      (partition.detachSheet first second hneFirstSecond hFirstSecond) second third
      hneSecondThird hInnerRel
  have hReprOther : ∀ source, partition.Rel first source → source ≠ first → source ≠ second →
      (secondNewEdge partition first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).repr source = third := by
    intro source hRel hNeFirst hNeSecond
    apply SheetPartition.detachSheet_repr_of_rel_of_ne
      (partition.detachSheet first second hneFirstSecond hFirstSecond) second third source
      hneSecondThird hInnerRel hNeSecond
    show (partition.detachSheet first second hneFirstSecond hFirstSecond).repr second =
      (partition.detachSheet first second hneFirstSecond hFirstSecond).repr source
    rw [hInnerOther second hFirstSecond hneFirstSecond.symm, hInnerOther source hRel hNeFirst]
  have hBlock : partition.block sheet = partition.block first :=
    (partition.block_eq_of_rel hSheet).symm
  have hImage : (partition.block sheet).image
      (secondNewEdge partition first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).repr =
      ({first, second, third} : Finset (Fin d)) := by
    rw [hBlock]
    apply Finset.Subset.antisymm
    · intro value hValue
      obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hValue
      have hRel := (partition.mem_block_iff first source).mp hSource
      by_cases hNeFirst : source = first
      · rw [hNeFirst, hReprFirst]; simp
      · by_cases hNeSecond : source = second
        · rw [hNeSecond, hReprSecond]; simp
        · rw [hReprOther source hRel hNeFirst hNeSecond]; simp
    · intro value hValue
      simp only [Finset.mem_insert, Finset.mem_singleton] at hValue
      rcases hValue with hValue | hValue | hValue
      · rw [hValue]
        exact Finset.mem_image.mpr ⟨first, partition.self_mem_block first, hReprFirst⟩
      · rw [hValue]
        exact Finset.mem_image.mpr ⟨second,
          (partition.mem_block_iff first second).mpr hFirstSecond, hReprSecond⟩
      · rw [hValue]
        exact Finset.mem_image.mpr ⟨third,
          (partition.mem_block_iff first third).mpr hFirstThird,
          hReprOther third hFirstThird hneFirstThird.symm hneSecondThird.symm⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by simp [hneFirstSecond, hneFirstThird]),
    Finset.card_insert_of_notMem (by simp [hneSecondThird]), Finset.card_singleton]

end Counts


/-! ## The three candidates, their validity, and their source genus -/

section Candidates

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The leaf pair of `M^{(1)}`, together with Base I.a's identification of the
two pinned sheets.  A block of size `k + 1 ≥ 3` always supplies the sheets;
the identification is an extra condition on the datum. -/
structure LeafPair (profile : W2R2SourceProfile.SourceProfile data star block) where
  aligned : pinSheet profile 0 = pinSheet profile 1
  second : Fin degree
  third : Fin degree
  rel_second : (data.vertexPartition wall).Rel (pinSheet profile 0) second
  rel_third : (data.vertexPartition wall).Rel (pinSheet profile 0) third
  ne_second : pinSheet profile 0 ≠ second
  ne_third : pinSheet profile 0 ≠ third
  second_ne_third : second ≠ third

/-- The residual `k - 1` class of `M^{(2)}`, together with Base II.2.2.M's
requirement that the two pinned sheets be distinct. -/
structure DividedData (profile : W2R2SourceProfile.SourceProfile data star block) where
  pins_ne : pinSheet profile 0 ≠ pinSheet profile 1
  third : Fin degree
  rel_third : (data.vertexPartition wall).Rel (pinSheet profile 0) third
  ne_first : pinSheet profile 0 ≠ third
  ne_second : pinSheet profile 1 ≠ third

theorem exists_leafPair (shape : Shape profile)
    (hAligned : pinSheet profile 0 = pinSheet profile 1) : Nonempty (LeafPair profile) := by
  obtain ⟨second, third, hSecond, hThird, hNeSecond, hNeThird, hSecondThird⟩ :=
    exists_leafGeometry_pair shape
  exact ⟨⟨hAligned, second, third, hSecond, hThird, hNeSecond, hNeThird, hSecondThird⟩⟩

theorem exists_dividedData (shape : Shape profile)
    (hPins : pinSheet profile 0 ≠ pinSheet profile 1) : Nonempty (DividedData profile) := by
  obtain ⟨third, hThird, hNeFirst, hNeSecond⟩ := exists_dividedGeometry_third shape hPins
  exact ⟨⟨hPins, third, hThird, hNeFirst, hNeSecond⟩⟩

/-- Exactly one of the two split members is available over a given datum:
the pinned sheets either agree or they do not. -/
theorem exists_leafPair_or_dividedData (shape : Shape profile) :
    Nonempty (LeafPair profile) ∨ Nonempty (DividedData profile) := by
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · exact Or.inl (exists_leafPair shape hAligned)
  · exact Or.inr (exists_dividedData shape hAligned)

/-- ... and never both. -/
theorem not_leafPair_and_dividedData (pair : LeafPair profile)
    (divided : DividedData profile) : False :=
  divided.pins_ne pair.aligned

/-- Figure 33's `M^{(1)}` geometry, bundled. -/
noncomputable def LeafPair.geometry (shape : Shape profile) (pair : LeafPair profile) :
    GlobalM1k.Geometry data wall :=
  leafGeometry shape pair.second pair.third pair.rel_second pair.rel_third
    pair.ne_second pair.ne_third pair.second_ne_third

/-- Figure 33's `M^{(1)}` occurrence pattern, bundled. -/
noncomputable def LeafPair.pattern (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) : GlobalM1k.FirstPattern (pair.geometry shape) :=
  leafPattern input shape pair.aligned pair.second pair.third pair.rel_second
    pair.rel_third pair.ne_second pair.ne_third pair.second_ne_third

/-- Figure 33's `M^{(1)}` as an actual arbitrary-degree outgoing gluing datum. -/
noncomputable def LeafPair.candidate (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) : BalancedGlobal.Candidate target degree data wall :=
  (pair.pattern input shape).candidate

/-- Figure 33's `M^{(2)}` geometry, bundled. -/
noncomputable def DividedData.geometry (shape : Shape profile) (divided : DividedData profile) :
    GlobalM1k.Geometry data wall :=
  dividedGeometry shape divided.pins_ne divided.third divided.rel_third
    divided.ne_first divided.ne_second

/-- Figure 33's `M^{(2)}` occurrence pattern, bundled. -/
noncomputable def DividedData.pattern (shape : Shape profile) (divided : DividedData profile) :
    GlobalM1k.SecondPattern (divided.geometry shape) :=
  dividedPattern shape divided.pins_ne divided.third divided.rel_third
    divided.ne_first divided.ne_second

/-- Figure 33's `M^{(2)}` as an actual arbitrary-degree outgoing gluing datum. -/
noncomputable def DividedData.candidate (shape : Shape profile)
    (divided : DividedData profile) : BalancedGlobal.Candidate target degree data wall :=
  (divided.pattern shape).candidate

/-- Figure 33's `M^{(3)}` as an actual arbitrary-degree outgoing gluing datum. -/
noncomputable def joinedCandidate (twoStar : TwoStar target wall)
    (geometry : GlobalM1k.Geometry data wall) :
    BalancedGlobal.Candidate target degree data wall :=
  (joinedPattern twoStar geometry).candidate

/-! ### Validity -/

theorem leaf_valid (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (LeafPair.candidate input shape pair).datum.Valid :=
  (LeafPair.candidate input shape pair).datum_valid input.valid

theorem divided_valid (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) :
    (DividedData.candidate shape divided).datum.Valid :=
  (DividedData.candidate shape divided).datum_valid input.valid

theorem joined_valid (input : W2SourceInput data star)
    (geometry : GlobalM1k.Geometry data wall) :
    (joinedCandidate star geometry).datum.Valid :=
  (joinedCandidate star geometry).datum_valid input.valid

/-! ### Target valencies -/

/-- `M^{(1)}` has the leaf/trivalent target `T_∅`. -/
theorem leaf_target_valencies (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    (GluingDatum.incidentEdges
      (target := graph target wall (LeafPair.candidate input shape pair).right)
      (oldVertex target wall)).card = 1 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (LeafPair.candidate input shape pair).right)
      (freshVertex target)).card = 3 :=
  M11SourceCandidates.candidate_target_valencies (LeafPair.candidate input shape pair)

/-- `M^{(2)}` and `M^{(3)}` have the divalent/divalent target `T_2`. -/
theorem divided_target_valencies (shape : Shape profile) (divided : DividedData profile) :
    (GluingDatum.incidentEdges
      (target := graph target wall (DividedData.candidate shape divided).right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (DividedData.candidate shape divided).right)
      (freshVertex target)).card = 2 :=
  M11SourceCandidates.candidate_target_valencies (DividedData.candidate shape divided)

theorem joined_target_valencies (geometry : GlobalM1k.Geometry data wall) :
    (GluingDatum.incidentEdges
      (target := graph target wall (joinedCandidate star geometry).right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (joinedCandidate star geometry).right)
      (freshVertex target)).card = 2 :=
  M11SourceCandidates.candidate_target_valencies (joinedCandidate star geometry)

/-! ### Source genus -/

theorem joined_sourceGenus (geometry : GlobalM1k.Geometry data wall) :
    genus (joinedCandidate star geometry).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : (joinedCandidate star geometry).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) geometry.first
        (thirdResolution (data.vertexPartition wall))
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  simp only [LocalResolution.onBlock, ite_self]
  exact Or.inl ⟨rfl, rfl⟩

theorem divided_sourceGenus (shape : Shape profile) (divided : DividedData profile) :
    genus (DividedData.candidate shape divided).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro anchor _
  have hResolution : (DividedData.candidate shape divided).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile 0)
        (secondResolution (data.vertexPartition wall) (pinSheet profile 0)
          (pinSheet profile 1) divided.third
          ((pinSheet_rel 0).symm.trans (pinSheet_rel 1)) divided.rel_third
          divided.pins_ne divided.ne_first divided.ne_second)
        (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel (pinSheet profile 0) anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    have hNew := secondNewEdge_blockCountWithin (data.vertexPartition wall)
      (pinSheet profile 0) (pinSheet profile 1) divided.third anchor
      ((pinSheet_rel 0).symm.trans (pinSheet_rel 1)) divided.rel_third
      divided.pins_ne divided.ne_first divided.ne_second hSelected
    have hLeft := W3ShiftSourceCandidates.detachSheet_blockCountWithin_self
      (data.vertexPartition wall) (pinSheet profile 0) (pinSheet profile 1) anchor
      divided.pins_ne ((pinSheet_rel 0).symm.trans (pinSheet_rel 1)) hSelected
    have hRight := W3ShiftSourceCandidates.detachSheet_blockCountWithin_self
      (data.vertexPartition wall) (pinSheet profile 1) (pinSheet profile 0) anchor
      divided.pins_ne.symm ((pinSheet_rel 0).symm.trans (pinSheet_rel 1)).symm
      (((pinSheet_rel 0).symm.trans (pinSheet_rel 1)).symm.trans hSelected)
    simp only [secondResolution]
    omega
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self]

theorem leaf_sourceGenus (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    genus (LeafPair.candidate input shape pair).datum.sourceGraph = genus data.sourceGraph := by
  apply M11SourceGenus.candidate_sourceGenus_of_blockwise_euler
  intro anchor _
  have hResolution : (LeafPair.candidate input shape pair).resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile 0)
        (firstResolution (data.vertexPartition wall) (pinSheet profile 0) pair.second
          pair.ne_second pair.rel_second)
        (M11SourceCandidates.backgroundResolution (data.vertexPartition wall)) anchor := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel (pinSheet profile 0) anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    have hNew := SheetPartition.splitBlock_blockCountWithin_of_rel
      (data.vertexPartition wall) (pinSheet profile 0) anchor hSelected
    have hLeft := pairBlock_blockCountWithin (data.vertexPartition wall)
      (pinSheet profile 0) pair.second anchor pair.ne_second pair.rel_second hSelected
    have hRight := W3ShiftSourceCandidates.detachSheet_blockCountWithin_self
      (data.vertexPartition wall) (pinSheet profile 0) pair.second anchor
      pair.ne_second pair.rel_second hSelected
    simp only [firstResolution]
    omega
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    simp only [M11SourceCandidates.backgroundResolution, LocalResolution.reverse,
      splitResolutionAt, SheetPartition.blockCountWithin_self]

end Candidates


/-! ## `M^{(1)}` and `M^{(2)}` never resolve the same datum

Figure 33 draws its three members over one limit `M₀`.  On an actual `w2M1k`
source profile that is impossible for the first two: `M^{(1)}` detaches a
single sheet at its trivalent endpoint and therefore needs *both* target
directions to isolate that one sheet (the source's Base I.a identification
`k₁ = |A''| = k₄`), while `M^{(2)}` detaches one sheet at each of its two
divalent endpoints and therefore needs the two isolated sheets to be
*distinct* (Base II.2.2.M, where `|e'| = 1` and `|e''| = k - 1` leave the
dangling sheet alone above `t₃`).

The obstruction is a gauge, not a contradiction in the source: a branch swap
of the two sheets across one of the two wall directions exchanges the two
situations, exactly as `M11RemoteCandidates` realizes Figure 32's second split
over `M11RemoteCandidates.swappedDatum` rather than over `data`.
`GlobalM1k.candidates` takes all three patterns over one `data` and one
`Geometry`, whereas `GlobalM11Arbitrary.candidates` takes its second member
over `SwappedDatum`; `GlobalM1k.swappedCandidates` is the M-1k form of that
slot.
-/

section Incompatibility

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- `M^{(1)}` puts every old occurrence at the trivalent endpoint, so both
target directions isolate the distinguished sheet. -/
theorem firstPattern_first_eq_pinSheet (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hRelFirst : (data.vertexPartition wall).Rel block.1 geometry.first)
    (pattern : GlobalM1k.FirstPattern geometry) (label : Fin 2) :
    geometry.first = pinSheet profile label := by
  have hEmpty : wallEdgesAssigned target wall pattern.background.right false = ∅ := by
    have hList := pattern.background.leftEdges_eq
    rw [pattern.leftEdges, Multiset.coe_nil] at hList
    exact Finset.val_eq_zero.mp hList.symm
  have hInc : ((star.edge label : target.V × target.V).1 = wall ∨
      (star.edge label : target.V × target.V).2 = wall) := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using star.edge_mem_incidentEdges label
  have hRight : pattern.background.right (star.edge label) = true := by
    by_contra hFalse
    have hMem : star.edge label ∈ wallEdgesAssigned target wall pattern.background.right false :=
      (mem_wallEdgesAssigned target wall pattern.background.right false _).mpr
        ⟨hInc, by simpa using hFalse⟩
    rw [hEmpty] at hMem
    exact absurd hMem (Finset.notMem_empty _)
  have hRefines : (data.edgePartition (star.edge label)).Refines geometry.firstLocal.right := by
    have hExterior := pattern.exterior (star.edge label) hInc
    rw [hRight] at hExterior
    exact hExterior
  have hSingleton : (data.edgePartition (star.edge label)).block geometry.first =
      {geometry.first} :=
    SheetPartition.block_eq_singleton_of_refines hRefines geometry.first
      (SheetPartition.detachSheet_block_single (data.vertexPartition wall) geometry.first
        geometry.second geometry.first_ne_second geometry.first_second)
  exact eq_pinSheet_of_block_singleton shape label geometry.first hRelFirst hSingleton

/-- `M^{(2)}` isolates the sheet detached at its fresh divalent endpoint. -/
theorem secondPattern_second_eq_pinSheet (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hRelFirst : (data.vertexPartition wall).Rel block.1 geometry.first)
    (pattern : GlobalM1k.SecondPattern geometry) :
    ∃ label, geometry.second = pinSheet profile label := by
  have hMem : pattern.rightExternal ∈
      wallEdgesAssigned target wall pattern.background.right true := by
    have hList := pattern.background.rightEdges_eq
    rw [pattern.rightEdges] at hList
    rw [← Finset.mem_val, ← hList]
    simp
  obtain ⟨hInc, hRight⟩ :=
    (mem_wallEdgesAssigned target wall pattern.background.right true _).mp hMem
  have hAt : pattern.rightExternal ∈ GluingDatum.incidentEdges wall := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hInc
  obtain ⟨label, hLabel⟩ := exists_label star pattern.rightExternal hAt
  refine ⟨label, ?_⟩
  have hRefines : (data.edgePartition pattern.rightExternal).Refines
      geometry.secondLocal.right := by
    have hExterior := pattern.exterior pattern.rightExternal hInc
    rw [hRight] at hExterior
    exact hExterior
  have hSingleton : (data.edgePartition pattern.rightExternal).block geometry.second =
      {geometry.second} :=
    SheetPartition.block_eq_singleton_of_refines hRefines geometry.second
      (SheetPartition.detachSheet_block_single (data.vertexPartition wall) geometry.second
        geometry.first geometry.first_ne_second.symm geometry.first_second.symm)
  rw [← hLabel] at hSingleton
  exact eq_pinSheet_of_block_singleton shape label geometry.second
    (hRelFirst.trans geometry.first_second) hSingleton

/-- Base I.a, derived: a `w2M1k` datum carrying `M^{(1)}` has its two pinned
sheets equal. -/
theorem firstPattern_forces_aligned (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hRelFirst : (data.vertexPartition wall).Rel block.1 geometry.first)
    (pattern : GlobalM1k.FirstPattern geometry) :
    pinSheet profile 0 = pinSheet profile 1 :=
  (firstPattern_first_eq_pinSheet shape geometry hRelFirst pattern 0).symm.trans
    (firstPattern_first_eq_pinSheet shape geometry hRelFirst pattern 1)

/-- **No actual `w2M1k` gluing datum carries both `M^{(1)}` and `M^{(2)}` on
the distinguished block.**  Consequently `GlobalM1k.exists_valid_positive_exit`
has no instance at an actual `w2M1k` source profile: its `FirstPattern` and
`SecondPattern` hypotheses are jointly unsatisfiable there. -/
theorem no_common_geometry (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    (hRelFirst : (data.vertexPartition wall).Rel block.1 geometry.first)
    (first : GlobalM1k.FirstPattern geometry)
    (second : GlobalM1k.SecondPattern geometry) : False := by
  obtain ⟨label, hSecond⟩ :=
    secondPattern_second_eq_pinSheet shape geometry hRelFirst second
  exact geometry.first_ne_second
    ((firstPattern_first_eq_pinSheet shape geometry hRelFirst first label).trans hSecond.symm)

end Incompatibility


/-! ## The obstruction is a gauge: the branch swap exchanges the two members

Swapping two sheets of the distinguished block along one of the two wall
branches fixes the wall partition, fixes the *other* branch's occurrence
partition, and transports the moved branch's by the transposition.  Which sheet
each direction isolates is therefore not an invariant of the datum: it is
exactly what the swap moves.  The extra input is the *separation* of the two
branches, i.e. that the far endpoint of one wall occurrence is not reachable
from the far endpoint of the other after deleting the wall.  That is automatic
for tree targets (`graph_connected target` and `genus target = 0`, as carried
by `FullDimensionalSource.FullDimensionalSourcePresentation`), and
`Infrastructure.TargetSeparation.edgeMoved_eq_false` proves it from exactly
those two facts.  Neither is a hypothesis of any theorem below, though, so it
appears as the carried hypothesis `hSeparated`: discharging it here
would mean adding `graph_connected target` / `genus target = 0` to signatures
that do not already have them, which only relocates the assumption.
-/

section Gauge

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- A branch swap is a gauge move: the swapped datum is valid whenever the
original is. -/
theorem branchSwapped_valid (input : W2SourceInput data star) (root : target.V)
    (hRoot : root ≠ wall) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q) :
    (GlobalM11Arbitrary.SwappedDatum data wall root hRoot p q hTogether).Valid :=
  wallBranchSwap_preserves_valid data input.valid wall root hRoot p q hTogether

theorem branchSwapped_edgePartition_of_fixed (root : target.V) (hRoot : root ≠ wall)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q)
    (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false) :
    (GlobalM11Arbitrary.SwappedDatum data wall root hRoot p q hTogether).edgePartition edge =
      data.edgePartition edge := by
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) (Equiv.swap p q)) = _
  rw [hFixed]
  apply SheetPartition.ext_repr
  rfl

theorem branchSwapped_edgePartition_of_moved (root : target.V) (hRoot : root ≠ wall)
    (p q : Fin degree) (hTogether : (data.vertexPartition wall).Rel p q)
    (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true) :
    (GlobalM11Arbitrary.SwappedDatum data wall root hRoot p q hTogether).edgePartition edge =
      (data.edgePartition edge).relabel (Equiv.swap p q) := by
  change (data.edgePartition edge).relabel
    (GluingDatum.SheetRelabeling.togglePermutation
      (TargetBranchRegion.edgeMoved wall root hRoot edge) (Equiv.swap p q)) = _
  rw [hMoved]
  rfl

/-- The occurrence across which we swap is always moved. -/
theorem edgeMoved_self (label : Fin 2) :
    TargetBranchRegion.edgeMoved wall (M11RemoteCandidates.branchRoot star label)
      (M11RemoteCandidates.branchRoot_ne star label) (star.edge label) = true := by
  have hRootMoved : TargetBranchRegion.vertexMoved wall
      (M11RemoteCandidates.branchRoot star label)
      (M11RemoteCandidates.branchRoot_ne star label)
      (M11RemoteCandidates.branchRoot star label) = true := by
    rw [TargetBranchRegion.vertexMoved_eq_true_iff]
    exact ⟨M11RemoteCandidates.branchRoot_ne star label, SimpleGraph.Reachable.refl _⟩
  unfold TargetBranchRegion.edgeMoved
  rcases M11RemoteCandidates.branchRoot_ends star label with hEnds | hEnds <;>
    rw [hEnds] <;> simp [hRootMoved]

/-- After the swap across the second direction, the first direction still
isolates exactly the sheets it isolated before. -/
theorem branchSwapped_block_fixed (shape : Shape profile) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q)
    (hSeparated : TargetBranchRegion.edgeMoved wall
      (M11RemoteCandidates.branchRoot star 1) (M11RemoteCandidates.branchRoot_ne star 1)
      (star.edge 0) = false) :
    ((GlobalM11Arbitrary.SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
        (M11RemoteCandidates.branchRoot_ne star 1) p q hTogether).edgePartition
      (star.edge 0)).block (pinSheet profile 0) = {pinSheet profile 0} := by
  rw [branchSwapped_edgePartition_of_fixed _ _ p q hTogether (star.edge 0) hSeparated]
  exact pinSheet_block shape 0

/-- After the swap, the second direction isolates the image of its old pinned
sheet under the transposition. -/
theorem branchSwapped_block_moved (shape : Shape profile) (p q : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel p q) :
    ((GlobalM11Arbitrary.SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
        (M11RemoteCandidates.branchRoot_ne star 1) p q hTogether).edgePartition
      (star.edge 1)).block (Equiv.swap p q (pinSheet profile 1)) =
      {Equiv.swap p q (pinSheet profile 1)} := by
  rw [branchSwapped_edgePartition_of_moved _ _ p q hTogether (star.edge 1) (edgeMoved_self 1),
    SheetPartition.relabel_block, pinSheet_block shape 1]
  simp

/-- **`M^{(2)}` is a branch swap away from `M^{(1)}`.**  If the two pinned
sheets are distinct, swapping them across the second branch makes both
directions isolate the first one — the exterior refinement condition of
Figure 33's `M^{(1)}` — on a datum that is valid whenever the original is. -/
theorem branchSwap_aligns (shape : Shape profile)
    (hSeparated : TargetBranchRegion.edgeMoved wall
      (M11RemoteCandidates.branchRoot star 1) (M11RemoteCandidates.branchRoot_ne star 1)
      (star.edge 0) = false) :
    ∀ label : Fin 2,
      ((GlobalM11Arbitrary.SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
          (M11RemoteCandidates.branchRoot_ne star 1) (pinSheet profile 0) (pinSheet profile 1)
          ((pinSheet_rel 0).symm.trans (pinSheet_rel 1))).edgePartition
        (star.edge label)).block (pinSheet profile 0) = {pinSheet profile 0} := by
  intro label
  have hLabel : label = 0 ∨ label = 1 := by omega
  rcases hLabel with rfl | rfl
  · exact branchSwapped_block_fixed shape _ _ _ hSeparated
  · have hSwap : Equiv.swap (pinSheet profile 0) (pinSheet profile 1) (pinSheet profile 1) =
        pinSheet profile 0 := Equiv.swap_apply_right _ _
    have hBlock := branchSwapped_block_moved (star := star) shape (pinSheet profile 0)
      (pinSheet profile 1) ((pinSheet_rel 0).symm.trans (pinSheet_rel 1))
    rwa [hSwap] at hBlock

/-- Conversely, if the two pinned sheets already agree, swapping the common
sheet with any other sheet of the block across the second branch separates
them — the exterior refinement condition of Figure 33's `M^{(2)}`. -/
theorem branchSwap_separates (shape : Shape profile)
    (hAligned : pinSheet profile 0 = pinSheet profile 1) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (hNe : pinSheet profile 0 ≠ other)
    (hSeparated : TargetBranchRegion.edgeMoved wall
      (M11RemoteCandidates.branchRoot star 1) (M11RemoteCandidates.branchRoot_ne star 1)
      (star.edge 0) = false) :
    ((GlobalM11Arbitrary.SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
          (M11RemoteCandidates.branchRoot_ne star 1) (pinSheet profile 0) other
          hOther).edgePartition (star.edge 0)).block (pinSheet profile 0) =
        {pinSheet profile 0} ∧
      ((GlobalM11Arbitrary.SwappedDatum data wall (M11RemoteCandidates.branchRoot star 1)
          (M11RemoteCandidates.branchRoot_ne star 1) (pinSheet profile 0) other
          hOther).edgePartition (star.edge 1)).block other = {other} ∧
      pinSheet profile 0 ≠ other := by
  refine ⟨branchSwapped_block_fixed shape _ _ _ hSeparated, ?_, hNe⟩
  have hSwap : Equiv.swap (pinSheet profile 0) other (pinSheet profile 1) = other := by
    rw [← hAligned]
    exact Equiv.swap_apply_left _ _
  have hBlock := branchSwapped_block_moved (star := star) shape (pinSheet profile 0) other hOther
  rwa [hSwap] at hBlock

end Gauge


end DraismaVargas.LocalCases.W2M1kSourceCandidates
