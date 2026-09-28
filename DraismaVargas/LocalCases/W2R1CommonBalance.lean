import DraismaVargas.LocalCases.W2R1RowDescent
import Utilities.IntegralGeometry.WallColumnDeterminant

/-!
# Equation (10): the common balance of the two `{w2-r1}` members

Source: Draisma--Vargas Part I, case `{w2-r1}`, sub-cases `{w2-r1-nd3}`
(Figure 37) and `{w2-r1-nd2}` (Figure 38), the proof of Equation (*) for case
`{w2-r1}` and **Equation (10)**.

Figure 38's limit box as computed here differs from Part I's display in one
index: Part I displays `σ₀(J_{A₀},2) = c_h/k₁`, while the box computed here is
`σ₀(J_{A₀},2) = c_h/k₂`, `σ₀(J_{A₀},3) = c_h/(k₂+1)` -- that is,
`localColumn_double_nd2` and `localColumn_single` read with
`W2R1SourceCandidates.nd2_displayed_indices`.  Nothing below transcribes the
displayed index.

## What Equation (10) says

Part I displays, with `c⁽ⁱ⁾ = σ⁽ⁱ⁾(J_{A₀},1) + σ⁽ⁱ⁾(J_{B₀},1) + s`,

    c⁽¹⁾ + c⁽²⁾ = σ₀(2) + σ₀(3) = 0 + 0 = 0,

with **unit weights**: two members, and their plain sum.  The weights are not
posited here.  They are forced the same way Equation (9)'s are
(`W2PCommonBalance.figure35_weights_forced`): `equation_ten_weights_forced`
shows that the coefficient equations of the column identity have a
one-dimensional solution space, and `equation_ten_weights_normalized` pins it
at `(1,1)` once the first weight is `1`.

## The four regrown evaluations, and why they are the old local columns

Read at one ramification-one block, a member is *retained* there
(`position = double`, Figure 37/38 gluing I) or *resolved* there
(`position ≠ double`, gluing II).  `W2R1LimitMatrix` evaluates the regrown
half in each case; this module supplies the target of that evaluation, the
**local part of an old wall column above one block**:

* `localColumn_single`: above the block the single direction `t₃` displays
  exactly `e₃`, so `σ₀(J,3) = c(e₃)/k₃` -- `= c_h/(k₂+1)` in nd2;
* `localColumn_double_nd3`: the doubled direction displays `e₁` and `e₂`, so
  `σ₀(J,2) = c(e₁)/k₁ + c(e₂)/k₂`;
* `localColumn_double_nd2`: with `e₁` dangling only `e₂` is displayed, so
  `σ₀(J,2) = c_h/k₂`.

The retained member's regrown half is Figure 37/38's `σ⁽¹⁾(J,1)` and equals
`σ₀(J,3)`; the resolved member's is `σ⁽²⁾(J,1)` and equals `σ₀(J,2)`.  Their
sum is therefore `σ₀(J,2) + σ₀(J,3)`, which is the display just below each of
Figures 37 and 38.  Since `{double, single} = {0, 1}` that sum is
**direction-symmetric**, which is what lets the two blocks be added even in
the opposite configuration, where `A₀` and `B₀` have different doubled
directions.

## The background `s`

`s` is `LimitChainTwoBlock.backgroundColumn` at the anchor set `{A₀, B₀}`, and
both members carry the `t₂` one (their `retainedTarget` is `star.edge 0`).
`background_sum_eq` proves the two directions' backgrounds agree: every wall
block other than `A₀` and `B₀` is unramified (`Pair.background`), so its
source vertex is divalent, its two occurrences are dangling together, share a
stable row and have the block's own size as common index.  That is what turns
`2s` into `s + s` on two different directions.

## Part A and Part B

Everything through `equation_ten` and `positiveBalance_of_relations` is
unconditional on a `Pair`, `data.Valid` and -- where the background enters --
nothing else.  Part B is the matrix-level chain over a `LimitColumns` receipt,
whose inhabitant is `W2R1LimitMatrix.limitColumns`.
-/

namespace DraismaVargas.LocalCases.W2R1CommonBalance

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix
open W2R1SourceCandidates
open W2R1StableGraph
open W2R1StableLift
open W2R1RowDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §1  The local part of an old wall column above one block -/

/-- The occurrences of one old wall column whose sheet lies above one block. -/
noncomputable def localOccurrences (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) (path : StablePath data) (place : target.edges) :
    Finset data.SourceEdge := by
  classical
  exact (occurrences data path place).filter
    (fun edge ↦ (data.vertexPartition wall).Rel anchor edge.1.2)

theorem mem_localOccurrences (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) (path : StablePath data) (place : target.edges)
    (edge : data.SourceEdge) :
    edge ∈ localOccurrences data wall anchor path place ↔
      edge ∈ occurrences data path place ∧
        (data.vertexPartition wall).Rel anchor edge.1.2 := by
  classical
  simp only [localOccurrences, Finset.mem_filter]

/-- `σ₀(J,·)` of the figures: the part of one old wall column contributed by
one block, on one old stable row. -/
noncomputable def localColumn (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) (path : StablePath data) (place : target.edges) : ℚ :=
  ∑ edge ∈ localOccurrences data wall anchor path place,
    (1 : ℚ) / data.sourceEdgeIndex edge

/-- **Every old wall column is `A₀`'s part, `B₀`'s part and the background.**
The two-block analogue of `W2PCommonBalance.double_matrix_decomposition`'s
split, before either local part is evaluated. -/
theorem matrix_split_pair (pair : Pair data star) (path : StablePath data)
    (place : target.edges) :
    matrix data path place =
      localColumn data wall pair.first.1 path place +
        localColumn data wall pair.second.1 path place +
        LimitChainTwoBlock.backgroundColumn data wall (anchors pair) path place := by
  classical
  have hUnion : (occurrences data path place).filter
        (fun edge ↦ LimitChainTwoBlock.IsSelected data wall (anchors pair) edge.1.2) =
      localOccurrences data wall pair.first.1 path place ∪
        localOccurrences data wall pair.second.1 path place := by
    ext edge
    simp only [Finset.mem_union, Finset.mem_filter, mem_localOccurrences]
    constructor
    · rintro ⟨hMem, hSel⟩
      rcases (isSelected_iff pair edge.1.2).mp hSel with hRel | hRel
      · exact Or.inl ⟨hMem, hRel⟩
      · exact Or.inr ⟨hMem, hRel⟩
    · rintro (⟨hMem, hRel⟩ | ⟨hMem, hRel⟩)
      · exact ⟨hMem, (isSelected_iff pair edge.1.2).mpr (Or.inl hRel)⟩
      · exact ⟨hMem, (isSelected_iff pair edge.1.2).mpr (Or.inr hRel)⟩
  have hDisjoint : Disjoint (localOccurrences data wall pair.first.1 path place)
      (localOccurrences data wall pair.second.1 path place) := by
    rw [Finset.disjoint_left]
    intro edge hFirst hSecond
    exact pair.separate (((mem_localOccurrences _ _ _ _ _ edge).mp hFirst).2.trans
      ((mem_localOccurrences _ _ _ _ _ edge).mp hSecond).2.symm)
  have hSplit := Finset.sum_filter_add_sum_filter_not (occurrences data path place)
    (fun edge ↦ LimitChainTwoBlock.IsSelected data wall (anchors pair) edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  rw [hUnion, Finset.sum_union hDisjoint] at hSplit
  exact hSplit.symm


/-! ## §2  The block's own three occurrences, and the two local columns

Above a ramification-one block the doubled direction displays `e₁` and `e₂`
and the single direction displays `e₃`.  These are the two boxes labelled
`σ₀(J_{A₀},2)` and `σ₀(J_{A₀},3)` in Figures 37 and 38, with Figure 38's box
read with the index `k₂` (see the module docstring). -/

section LocalColumns

variable {block : WallBlock data wall}

/-- An occurrence of one wall direction above the block is one of the block's
own three. -/
theorem local_edge_cases (profile : W2R1SourceProfile.OccurrenceProfile data star block)
    (label : Fin 2) {path : StablePath data} (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path (star.edge label))
    (hRel : (data.vertexPartition wall).Rel block.1 edge.1.2) :
    edge = profile.first.1 ∨ edge = profile.second.1 ∨ edge = profile.third.1 := by
  obtain ⟨_, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge (WallBlock.sourceVertex data wall block) := by
    refine (incident_iff_target_mem_and_rel data edge _).mpr ⟨?_, ?_⟩
    · rw [hTarget]
      exact star.edge_mem_incidentEdges label
    · change (data.vertexPartition wall).Rel
        ((data.vertexPartition wall).repr block.1) edge.1.2
      exact ((data.vertexPartition wall).rel_repr_left block.1).trans hRel
  rcases profile.exhaustive ⟨edge, hIncident⟩ with hEq | hEq | hEq
  · exact Or.inl (congrArg Subtype.val hEq)
  · exact Or.inr (Or.inl (congrArg Subtype.val hEq))
  · exact Or.inr (Or.inr (congrArg Subtype.val hEq))

/-- The stable row of `e₂`, which in `nd2` is Figure 38's `h`. -/
noncomputable def secondRow (profile : W2R1SourceProfile.SourceProfile data star block) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩

/-- The stable row of `e₃`; in `nd2` it is `secondRow`
(`W2R1SourceProfile.SourceProfile.nd2_stablePath_eq`). -/
noncomputable def thirdRow (profile : W2R1SourceProfile.SourceProfile data star block) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩

/-- The stable row of `e₁`, which exists only in `nd3`. -/
noncomputable def firstRow (profile : W2R1SourceProfile.SourceProfile data star block)
    (hNd3 : ¬ IsDangling data profile.first.1) : StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.first.1, hNd3⟩

/-- In `nd2` the two survivors above the block share one stable row: Figure
38's `h = h(e₂) = h(e₃)`. -/
theorem nd2_thirdRow_eq_secondRow
    (profile : W2R1SourceProfile.SourceProfile data star block)
    (hNd2 : IsDangling data profile.first.1) :
    thirdRow profile = secondRow profile :=
  (profile.nd2_stablePath_eq ((nd2_displayed_indices profile hNd2).1)).symm

private theorem mem_occurrences_iff_row (edge : NonDanglingEdge data)
    (path : StablePath data) (place : target.edges) (hTarget : edge.1.1.1 = place) :
    edge.1 ∈ occurrences data path place ↔ path = edge.stablePath := by
  rw [mem_occurrences]
  exact ⟨fun h ↦ h.1.choose_spec.symm, fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩

/-- **`σ₀(J,3) = c(e₃)/k₃`.**  Above the block the single direction displays
exactly `e₃`.  With `k₃ = k₂ + 1` this is Figure 38's box
`σ₀(J_{A₀},3) = c_h/(k₂+1)`, as read here. -/
theorem localColumn_single (profile : W2R1SourceProfile.SourceProfile data star block)
    (path : StablePath data) :
    localColumn data wall block.1 path (star.edge profile.singleLabel) =
      (if path = thirdRow profile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex profile.third.1 : ℚ) := by
  classical
  have hSet : localOccurrences data wall block.1 path (star.edge profile.singleLabel) =
      ({profile.third.1} : Finset data.SourceEdge).filter
        (fun edge ↦ edge ∈ occurrences data path (star.edge profile.singleLabel)) := by
    ext edge
    simp only [mem_localOccurrences, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      refine ⟨?_, hMem⟩
      rcases local_edge_cases profile.toOccurrenceProfile profile.singleLabel edge hMem hRel with
        hEq | hEq | hEq
      · exact absurd (((((mem_occurrences _ _ _).mp hMem).2).symm.trans
          (congrArg (fun e : data.SourceEdge ↦ e.1.1) hEq)).trans profile.first_target)
          (star.edge_injective.ne profile.labels_ne.symm)
      · exact absurd (((((mem_occurrences _ _ _).mp hMem).2).symm.trans
          (congrArg (fun e : data.SourceEdge ↦ e.1.1) hEq)).trans profile.second_target)
          (star.edge_injective.ne profile.labels_ne.symm)
      · exact hEq
    · rintro ⟨rfl, hMem⟩
      exact ⟨hMem, sheet_rel_of_incident profile.third⟩
  have hThird : profile.third.1 ∈ occurrences data path (star.edge profile.singleLabel) ↔
      path = thirdRow profile :=
    mem_occurrences_iff_row ⟨profile.third.1, profile.third_survives⟩ path _
      profile.third_target
  unfold localColumn
  rw [hSet, Finset.sum_filter, Finset.sum_singleton]
  simp only [hThird]
  split_ifs <;> ring

/-- The doubled direction's occurrences above the block are `e₁` and `e₂`,
whichever of them happens to lie in the given row. -/
theorem localOccurrences_double (profile : W2R1SourceProfile.SourceProfile data star block)
    (path : StablePath data) :
    localOccurrences data wall block.1 path (star.edge profile.doubleLabel) =
      ({profile.first.1, profile.second.1} : Finset data.SourceEdge).filter
        (fun edge ↦ edge ∈ occurrences data path (star.edge profile.doubleLabel)) := by
  classical
  ext edge
  simp only [mem_localOccurrences, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hMem, hRel⟩
    refine ⟨?_, hMem⟩
    rcases local_edge_cases profile.toOccurrenceProfile profile.doubleLabel edge hMem hRel with
      hEq | hEq | hEq
    · exact Or.inl hEq
    · exact Or.inr hEq
    · exact absurd (((((mem_occurrences _ _ _).mp hMem).2).symm.trans
        (congrArg (fun e : data.SourceEdge ↦ e.1.1) hEq)).trans profile.third_target)
        (star.edge_injective.ne profile.labels_ne)
  · rintro ⟨hEq, hMem⟩
    refine ⟨hMem, ?_⟩
    rcases hEq with rfl | rfl
    · exact sheet_rel_of_incident profile.first
    · exact sheet_rel_of_incident profile.second

/-- **`σ₀(J,2) = c(e₁)/k₁ + c(e₂)/k₂` in `nd3`.** -/
theorem localColumn_double_nd3 (profile : W2R1SourceProfile.SourceProfile data star block)
    (hNd3 : ¬ IsDangling data profile.first.1) (path : StablePath data) :
    localColumn data wall block.1 path (star.edge profile.doubleLabel) =
      (if path = firstRow profile hNd3 then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (if path = secondRow profile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex profile.second.1 : ℚ) := by
  classical
  have hSet : localOccurrences data wall block.1 path (star.edge profile.doubleLabel) =
      ({profile.first.1, profile.second.1} : Finset data.SourceEdge).filter
        (fun edge ↦ edge ∈ occurrences data path (star.edge profile.doubleLabel)) :=
    localOccurrences_double profile path
  have hFirst : profile.first.1 ∈ occurrences data path (star.edge profile.doubleLabel) ↔
      path = firstRow profile hNd3 :=
    mem_occurrences_iff_row ⟨profile.first.1, hNd3⟩ path _ profile.first_target
  have hSecond : profile.second.1 ∈ occurrences data path (star.edge profile.doubleLabel) ↔
      path = secondRow profile :=
    mem_occurrences_iff_row ⟨profile.second.1, profile.second_survives⟩ path _
      profile.second_target
  unfold localColumn
  rw [hSet, Finset.sum_filter,
    Finset.sum_pair (first_ne_second_val profile.toOccurrenceProfile)]
  simp only [hFirst, hSecond]
  split_ifs <;> ring

/-- **`σ₀(J,2) = c_h/k₂` in `nd2`** -- Figure 38's box with the index `k₂`
(Part I displays `k₁`).  The dangling `e₁` lies in no stable row and
contributes nothing. -/
theorem localColumn_double_nd2 (profile : W2R1SourceProfile.SourceProfile data star block)
    (hNd2 : IsDangling data profile.first.1) (path : StablePath data) :
    localColumn data wall block.1 path (star.edge profile.doubleLabel) =
      (if path = secondRow profile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex profile.second.1 : ℚ) := by
  classical
  have hSet := localOccurrences_double profile path
  have hFirst : profile.first.1 ∉ occurrences data path (star.edge profile.doubleLabel) := by
    intro hMem
    exact ((mem_occurrences _ _ _).mp hMem).1.choose hNd2
  have hSecond : profile.second.1 ∈ occurrences data path (star.edge profile.doubleLabel) ↔
      path = secondRow profile :=
    mem_occurrences_iff_row ⟨profile.second.1, profile.second_survives⟩ path _
      profile.second_target
  unfold localColumn
  rw [hSet, Finset.sum_filter,
    Finset.sum_pair (first_ne_second_val profile.toOccurrenceProfile), if_neg hFirst]
  simp only [hSecond]
  split_ifs <;> ring

end LocalColumns


/-! ## §3  The background `s`, and why the two directions agree

Every wall block other than `A₀` and `B₀` is unramified (`Pair.background`),
so its incoming source vertex is divalent: the two directions' occurrences
there are dangling together, share a stable row and have the block's own size
as common index.  Transporting one direction's background occurrence to the
other's is therefore a bijection that preserves both the row and the index,
which is Figures 37/38's `s`. -/

section Background

variable (pair : Pair data star)

/-- Above a background block each direction has a single occurrence, so any
occurrence of that direction over a related sheet **is** the canonical one. -/
theorem background_sourceEdge_eq (label : Fin 2) {sheet : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬ (data.vertexPartition wall).Rel pair.second.1 sheet)
    (edge : data.SourceEdge) (hTarget : edge.1.1 = star.edge label)
    (hRel : (data.vertexPartition wall).Rel sheet edge.1.2) :
    data.sourceEdge (star.edge label) sheet = edge := by
  have hBlocks := SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data label) sheet
    (background_blockCount pair label hFirst hSecond)
  have hMember := ((data.vertexPartition wall).mem_block_iff sheet edge.1.2).mpr hRel
  rw [← hBlocks] at hMember
  have hFine := ((data.edgePartition (star.edge label)).mem_block_iff sheet edge.1.2).mp hMember
  calc
    data.sourceEdge (star.edge label) sheet
        = data.sourceEdge (star.edge label) edge.1.2 := by
          apply Subtype.ext
          exact Prod.ext rfl hFine
    _ = edge := by
          apply Subtype.ext
          refine Prod.ext hTarget.symm ?_
          have hRepr := edge.2
          rw [hTarget] at hRepr
          exact hRepr

/-- A background wall vertex is divalent in the quotient source. -/
theorem background_old_card_incident {sheet : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬ (data.vertexPartition wall).Rel pair.second.1 sheet) :
    Fintype.card (IncidentSourceEdge data (data.sourceEndpoint wall sheet)) = 2 := by
  have h := W2SourceInput.card_incidentSourceEdge_wallBlock (data := data) star
    ((data.vertexPartition wall).toBlock sheet)
  rw [background_ramification_zero pair hFirst hSecond] at h
  have hVertex : WallBlock.sourceVertex data wall ((data.vertexPartition wall).toBlock sheet) =
      data.sourceEndpoint wall sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (data.vertexPartition wall).repr_idem sheet
  rw [hVertex] at h
  omega

/-- so its two occurrences are dangling together. -/
theorem background_isDangling_iff (one two : Fin 2) {sheet : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬ (data.vertexPartition wall).Rel pair.second.1 sheet) :
    IsDangling data (data.sourceEdge (star.edge one) sheet) ↔
      IsDangling data (data.sourceEdge (star.edge two) sheet) := by
  have hDegree : vertex_degree data.sourceGraph (data.sourceEndpoint wall sheet) = 2 := by
    rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge]
    exact_mod_cast background_old_card_incident pair hFirst hSecond
  rcases eq_or_ne one two with rfl | hNe
  · exact Iff.rfl
  · have hNeEdge : data.sourceEdge (star.edge one) sheet ≠
        data.sourceEdge (star.edge two) sheet := by
      intro h
      exact star.edge_injective.ne hNe (congrArg (fun e : data.SourceEdge ↦ e.1.1) h)
    exact ⟨fun h ↦ isDangling_of_incident_of_vertex_degree_eq_two data hNeEdge
        (incident_sourceEdge_sourceEndpoint data wall _
          (star.edge_mem_incidentEdges one) sheet)
        (incident_sourceEdge_sourceEndpoint data wall _
          (star.edge_mem_incidentEdges two) sheet) hDegree h,
      fun h ↦ isDangling_of_incident_of_vertex_degree_eq_two data hNeEdge.symm
        (incident_sourceEdge_sourceEndpoint data wall _
          (star.edge_mem_incidentEdges two) sheet)
        (incident_sourceEdge_sourceEndpoint data wall _
          (star.edge_mem_incidentEdges one) sheet) hDegree h⟩

/-- and share a stable row. -/
theorem background_old_stablePath_eq (hValid : data.Valid) {sheet : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬ (data.vertexPartition wall).Rel pair.second.1 sheet)
    (first second : NonDanglingEdge data)
    (hFirstIncident : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecondIncident : Incident data second.1 (data.sourceEndpoint wall sheet)) :
    first.stablePath = second.stablePath :=
  M11SplitRows.stablePath_eq_of_incident_card_two data hValid.1 first second _
    hFirstIncident hSecondIncident (background_old_card_incident pair hFirst hSecond)

/-- and the block's own size is the common index. -/
theorem background_index_eq (label : Fin 2) {sheet : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel pair.first.1 sheet)
    (hSecond : ¬ (data.vertexPartition wall).Rel pair.second.1 sheet) :
    data.sourceEdgeIndex (data.sourceEdge (star.edge label) sheet) =
      (data.vertexPartition wall).blockCard sheet := by
  rw [GluingDatum.sourceEdgeIndex_sourceEdge]
  exact SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data label) sheet
    (background_blockCount pair label hFirst hSecond)

private theorem background_transfer_mem (hValid : data.Valid) (path : StablePath data)
    (one two : Fin 2) (edge : data.SourceEdge)
    (hMem : edge ∈ LimitChainTwoBlock.backgroundOccurrences data wall (anchors pair) path
      (star.edge one)) :
    data.sourceEdge (star.edge two) edge.1.2 ∈
      LimitChainTwoBlock.backgroundOccurrences data wall (anchors pair) path
        (star.edge two) := by
  obtain ⟨hOld, hBackground⟩ :=
    (LimitChainTwoBlock.mem_backgroundOccurrences data wall (anchors pair) path _ edge).mp hMem
  have hNotFirst := not_rel_first_of_not_isSelected hBackground
  have hNotSecond := not_rel_second_of_not_isSelected hBackground
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
  have hCanonical := background_sourceEdge_eq pair one hNotFirst hNotSecond edge hTarget rfl
  have hOldSurvives : ¬ IsDangling data (data.sourceEdge (star.edge one) edge.1.2) := by
    rw [hCanonical]; exact hSurvives
  have hNew : ¬ IsDangling data (data.sourceEdge (star.edge two) edge.1.2) :=
    fun h ↦ hOldSurvives
      ((background_isDangling_iff pair two one hNotFirst hNotSecond).mp h)
  refine (LimitChainTwoBlock.mem_backgroundOccurrences data wall (anchors pair) path _ _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hNew, ?_⟩, rfl⟩, ?_⟩
  · refine Eq.trans (background_old_stablePath_eq pair hValid hNotFirst hNotSecond
      ⟨data.sourceEdge (star.edge two) edge.1.2, hNew⟩ ⟨edge, hSurvives⟩
      (incident_sourceEdge_sourceEndpoint data wall _
        (star.edge_mem_incidentEdges two) edge.1.2) ?_) hRow
    have hIncident := incident_sourceEdge_sourceEndpoint data wall _
      (star.edge_mem_incidentEdges one) edge.1.2
    rw [hCanonical] at hIncident
    exact hIncident
  · exact fun h ↦ hBackground (LimitChainTwoBlock.isSelected_trans h
      ((star.edgePartition_refines_wall data two).rel
        ((data.edgePartition (star.edge two)).rel_repr_left edge.1.2)))

private theorem background_transfer_inverse (path : StablePath data) (one two : Fin 2)
    (edge : data.SourceEdge)
    (hMem : edge ∈ LimitChainTwoBlock.backgroundOccurrences data wall (anchors pair) path
      (star.edge one)) :
    data.sourceEdge (star.edge one) (data.sourceEdge (star.edge two) edge.1.2).1.2 = edge := by
  obtain ⟨hOld, hBackground⟩ :=
    (LimitChainTwoBlock.mem_backgroundOccurrences data wall (anchors pair) path _ edge).mp hMem
  have hRel := (star.edgePartition_refines_wall data two).rel
    ((data.edgePartition (star.edge two)).rel_repr_left edge.1.2)
  have hNotSelected : ¬ LimitChainTwoBlock.IsSelected data wall (anchors pair)
      (data.sourceEdge (star.edge two) edge.1.2).1.2 :=
    fun h ↦ hBackground (LimitChainTwoBlock.isSelected_trans h hRel)
  exact background_sourceEdge_eq pair one (not_rel_first_of_not_isSelected hNotSelected)
    (not_rel_second_of_not_isSelected hNotSelected) edge
    ((mem_occurrences _ _ _).mp hOld).2 hRel

/-- **`s` does not depend on the direction.**  Figure 37/38's `s` read on the
`t₂` column and on the `t₃` column agree on every old stable row. -/
theorem background_sum_eq (hValid : data.Valid) (path : StablePath data) (one two : Fin 2) :
    LimitChainTwoBlock.backgroundColumn data wall (anchors pair) path (star.edge one) =
      LimitChainTwoBlock.backgroundColumn data wall (anchors pair) path (star.edge two) := by
  classical
  unfold LimitChainTwoBlock.backgroundColumn
  apply Finset.sum_nbij' (fun edge ↦ data.sourceEdge (star.edge two) edge.1.2)
    (fun edge ↦ data.sourceEdge (star.edge one) edge.1.2)
    (fun edge h ↦ background_transfer_mem pair hValid path one two edge h)
    (fun edge h ↦ background_transfer_mem pair hValid path two one edge h)
    (fun edge h ↦ background_transfer_inverse pair path one two edge h)
    (fun edge h ↦ background_transfer_inverse pair path two one edge h)
  intro edge hMem
  obtain ⟨hOld, hBackground⟩ :=
    (LimitChainTwoBlock.mem_backgroundOccurrences data wall (anchors pair) path _ edge).mp hMem
  have hNotFirst := not_rel_first_of_not_isSelected hBackground
  have hNotSecond := not_rel_second_of_not_isSelected hBackground
  have hCanonical := background_sourceEdge_eq pair one hNotFirst hNotSecond edge
    ((mem_occurrences _ _ _).mp hOld).2 rfl
  have hIdx : data.sourceEdgeIndex edge = (data.vertexPartition wall).blockCard edge.1.2 :=
    (congrArg data.sourceEdgeIndex hCanonical).symm.trans
      (background_index_eq pair one hNotFirst hNotSecond)
  rw [hIdx, background_index_eq pair two hNotFirst hNotSecond]

end Background


/-! ## §4  Equation (10)'s weights are derived, not posited

The source displays `c⁽¹⁾ + c⁽²⁾` with **unit** weights.  The five free
quantities in the column identity are the two blocks' retained and resolved
boxes -- `X_A`, `Y_A`, `X_B`, `Y_B` -- and the background `s`; each member
carries one box from each block, and the two members carry complementary
boxes, because `δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)` (Part I's proof of Equation (*) for case
`{w2-r1}`).  Asking the weighted sum to be
a combination of the two old columns already forces all four coefficients
equal. -/

/-- **The coefficient equations of Equation (10).**  With the two members
`X_A + Y_B + s` and `Y_A + X_B + s`, general weights `w₀, w₁` and general old
column multipliers `α` (on `σ₀(2) = Y_A + Y_B + s`) and `β` (on
`σ₀(3) = X_A + X_B + s`), the identity of rational functions gives these
four. -/
theorem equation_ten_coefficients {w₀ w₁ α β : ℚ}
    (hIdentity : ∀ xa ya xb yb s : ℚ,
      w₀ * (xa + yb + s) + w₁ * (ya + xb + s) =
        α * (ya + yb + s) + β * (xa + xb + s)) :
    w₀ = β ∧ w₁ = β ∧ w₁ = α ∧ w₀ = α := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hIdentity 1 0 0 0 0; linarith
  · have h := hIdentity 0 0 1 0 0; linarith
  · have h := hIdentity 0 1 0 0 0; linarith
  · have h := hIdentity 0 0 0 1 0; linarith

/-- **Equation (10)'s weights are forced.**  The solution space of the
coefficient equations is one-dimensional. -/
theorem equation_ten_weights_forced {w₀ w₁ α β : ℚ}
    (hIdentity : ∀ xa ya xb yb s : ℚ,
      w₀ * (xa + yb + s) + w₁ * (ya + xb + s) =
        α * (ya + yb + s) + β * (xa + xb + s)) :
    w₁ = w₀ ∧ α = w₀ ∧ β = w₀ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := equation_ten_coefficients hIdentity
  exact ⟨h₂.trans h₁.symm, h₄.symm, h₁.symm⟩

/-- and normalizing the first at `1` gives the source's `c⁽¹⁾ + c⁽²⁾`. -/
theorem equation_ten_weights_normalized {w₁ α β : ℚ}
    (hIdentity : ∀ xa ya xb yb s : ℚ,
      (1 : ℚ) * (xa + yb + s) + w₁ * (ya + xb + s) =
        α * (ya + yb + s) + β * (xa + xb + s)) :
    w₁ = 1 ∧ α = 1 ∧ β = 1 :=
  equation_ten_weights_forced hIdentity

/-- **The unit weights do solve it.**  `c⁽¹⁾ + c⁽²⁾ = σ₀(2) + σ₀(3)`, as an
identity of rational functions of the five free quantities. -/
theorem equation_ten_column_identity (xa ya xb yb s : ℚ) :
    (1 : ℚ) * (xa + yb + s) + (1 : ℚ) * (ya + xb + s) =
      (1 : ℚ) * (ya + yb + s) + (1 : ℚ) * (xa + xb + s) := by ring

/-- **Equation (10)** on the two figures' boxes: with both old wall
columns vanishing on a stable row, the two members' regrown entries sum to
zero there.  `0 + 0 = 0` is the source's own right-hand side. -/
theorem equation_ten_of_relations {xa ya xb yb s cLeft cRight : ℚ}
    (hLeft : ya + yb + s = cLeft) (hRight : xa + xb + s = cRight) :
    (xa + yb + s) + (ya + xb + s) = cLeft + cRight := by
  rw [← hLeft, ← hRight]; ring


/-! ## §5  The two members' regrown columns, and Equation (10) on them

Each member carries one box from `A₀` and one from `B₀`, and the two members
carry complementary boxes because the two blocks are always given opposite
positions (`Pair.positions_opposite`, Part I's `ch u = ch v = 1`).  The
boxes are named by the block's own local data; `firstBox_retained` and its
three siblings evaluate them as Figures 37 and 38 print them. -/

/-- A sum over the two wall directions does not see which is which. -/
theorem sum_over_labels (f : Fin 2 → ℚ) {a b : Fin 2} (hNe : a ≠ b) :
    f a + f b = f 0 + f 1 := by
  have hCases : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  rcases hCases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact add_comm _ _

section Boxes

variable (pair : Pair data star)

/-- **`σ⁽ᵠ⁾(J_{A₀},1)`**: the member's regrown half above `A₀`.  Gluing I when
`A₀` is retained there, gluing II when it is resolved. -/
noncomputable def firstBox (position : Fin 2) (path : StablePath data) : ℚ :=
  if position = pair.firstProfile.doubleLabel then
    localColumn data wall pair.first.1 path (star.edge pair.firstProfile.singleLabel)
  else localColumn data wall pair.first.1 path (star.edge pair.firstProfile.doubleLabel)

/-- **`σ⁽ᵠ⁾(J_{B₀},1)`**, at the **opposite** position. -/
noncomputable def secondBox (position : Fin 2) (path : StablePath data) : ℚ :=
  if other position = pair.secondProfile.doubleLabel then
    localColumn data wall pair.second.1 path (star.edge pair.secondProfile.singleLabel)
  else localColumn data wall pair.second.1 path (star.edge pair.secondProfile.doubleLabel)

/-- **Figure 37/38 gluing I at `A₀`: `σ⁽¹⁾(J_{A₀},1) = c(e₃)/k₃`**, which in
`nd2` is `c_h/(k₂+1)` and in `nd3` is `c(e₃)/(k₁+k₂)`. -/
theorem firstBox_retained {position : Fin 2}
    (hPosition : position = pair.firstProfile.doubleLabel) (path : StablePath data) :
    firstBox pair position path =
      (if path = thirdRow pair.firstProfile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex pair.firstProfile.third.1 : ℚ) := by
  rw [firstBox, if_pos hPosition, localColumn_single]

/-- **Figure 37 gluing II at `A₀` (`nd3`): `σ⁽²⁾(J_{A₀},1) = c(e₁)/k₁ +
c(e₂)/k₂`.** -/
theorem firstBox_resolved_nd3 {position : Fin 2}
    (hPosition : position ≠ pair.firstProfile.doubleLabel)
    (hNd3 : ¬ IsDangling data pair.firstProfile.first.1) (path : StablePath data) :
    firstBox pair position path =
      (if path = firstRow pair.firstProfile hNd3 then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex pair.firstProfile.first.1 : ℚ) +
        (if path = secondRow pair.firstProfile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex pair.firstProfile.second.1 : ℚ) := by
  rw [firstBox, if_neg hPosition, localColumn_double_nd3 _ hNd3]

/-- **Figure 38 gluing II at `A₀` (`nd2`): `σ⁽²⁾(J_{A₀},1) = c_h/k₂`.**  The
pruned `e₁` class contributes nothing. -/
theorem firstBox_resolved_nd2 {position : Fin 2}
    (hPosition : position ≠ pair.firstProfile.doubleLabel)
    (hNd2 : IsDangling data pair.firstProfile.first.1) (path : StablePath data) :
    firstBox pair position path =
      (if path = secondRow pair.firstProfile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex pair.firstProfile.second.1 : ℚ) := by
  rw [firstBox, if_neg hPosition, localColumn_double_nd2 _ hNd2]

/-- The `B₀` twin of `firstBox_retained`. -/
theorem secondBox_retained {position : Fin 2}
    (hPosition : other position = pair.secondProfile.doubleLabel) (path : StablePath data) :
    secondBox pair position path =
      (if path = thirdRow pair.secondProfile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex pair.secondProfile.third.1 : ℚ) := by
  rw [secondBox, if_pos hPosition, localColumn_single]

/-- The `B₀` twin of `firstBox_resolved_nd3`. -/
theorem secondBox_resolved_nd3 {position : Fin 2}
    (hPosition : other position ≠ pair.secondProfile.doubleLabel)
    (hNd3 : ¬ IsDangling data pair.secondProfile.first.1) (path : StablePath data) :
    secondBox pair position path =
      (if path = firstRow pair.secondProfile hNd3 then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex pair.secondProfile.first.1 : ℚ) +
        (if path = secondRow pair.secondProfile then (1 : ℚ) else 0) /
          (data.sourceEdgeIndex pair.secondProfile.second.1 : ℚ) := by
  rw [secondBox, if_neg hPosition, localColumn_double_nd3 _ hNd3]

/-- The `B₀` twin of `firstBox_resolved_nd2`. -/
theorem secondBox_resolved_nd2 {position : Fin 2}
    (hPosition : other position ≠ pair.secondProfile.doubleLabel)
    (hNd2 : IsDangling data pair.secondProfile.first.1) (path : StablePath data) :
    secondBox pair position path =
      (if path = secondRow pair.secondProfile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex pair.secondProfile.second.1 : ℚ) := by
  rw [secondBox, if_neg hPosition, localColumn_double_nd2 _ hNd2]

/-- **The display below Figure 37 and below Figure 38, at `A₀`:**
`σ⁽¹⁾(J_{A₀},1) + σ⁽²⁾(J_{A₀},1) = σ₀(J_{A₀},2) + σ₀(J_{A₀},3)`.  Stated on
the two wall directions rather than on the block's own labelling, which is
what lets `A₀` and `B₀` be added in the opposite configuration too. -/
theorem firstBox_sum (path : StablePath data) :
    firstBox pair 0 path + firstBox pair 1 path =
      localColumn data wall pair.first.1 path (star.edge 0) +
        localColumn data wall pair.first.1 path (star.edge 1) := by
  by_cases hZero : (0 : Fin 2) = pair.firstProfile.doubleLabel
  · have hOne : (1 : Fin 2) ≠ pair.firstProfile.doubleLabel := by
      rw [← hZero]; decide
    rw [firstBox, if_pos hZero, firstBox, if_neg hOne]
    exact sum_over_labels
      (fun label ↦ localColumn data wall pair.first.1 path (star.edge label))
      pair.firstProfile.labels_ne.symm
  · have hOne : (1 : Fin 2) = pair.firstProfile.doubleLabel := by omega
    rw [firstBox, if_neg hZero, firstBox, if_pos hOne]
    exact sum_over_labels
      (fun label ↦ localColumn data wall pair.first.1 path (star.edge label))
      pair.firstProfile.labels_ne

/-- The `B₀` twin: the display below the figures read at `B₀`, where, as
Part I says, the previous analysis holds. -/
theorem secondBox_sum (path : StablePath data) :
    secondBox pair 0 path + secondBox pair 1 path =
      localColumn data wall pair.second.1 path (star.edge 0) +
        localColumn data wall pair.second.1 path (star.edge 1) := by
  by_cases hZero : other (0 : Fin 2) = pair.secondProfile.doubleLabel
  · have hOne : other (1 : Fin 2) ≠ pair.secondProfile.doubleLabel := by
      rw [← hZero]; decide
    rw [secondBox, if_pos hZero, secondBox, if_neg hOne]
    exact sum_over_labels
      (fun label ↦ localColumn data wall pair.second.1 path (star.edge label))
      pair.secondProfile.labels_ne.symm
  · have hOne : other (1 : Fin 2) = pair.secondProfile.doubleLabel := by
      revert hZero
      generalize pair.secondProfile.doubleLabel = d
      revert d
      decide
    rw [secondBox, if_neg hZero, secondBox, if_pos hOne]
    exact sum_over_labels
      (fun label ↦ localColumn data wall pair.second.1 path (star.edge label))
      pair.secondProfile.labels_ne

/-- **`c⁽ᵠ⁾ = σ⁽ᵠ⁾(J_{A₀},1) + σ⁽ᵠ⁾(J_{B₀},1) + s`** (Part I's Equation (10)), as a column
of the limit matrix. -/
noncomputable def newColumn (position : Fin 2) (path : StablePath data) : ℚ :=
  firstBox pair position path + secondBox pair position path +
    LimitChainTwoBlock.backgroundColumn data wall (anchors pair) path (star.edge 0)

/-- **Equation (10) at column level, on the real incoming datum.**
`c⁽¹⁾ + c⁽²⁾ = σ₀(2) + σ₀(3)`, with unit weights and with both old columns
read as the literal stable-source matrix entries of the incoming datum. -/
theorem newColumn_sum (hValid : data.Valid) (path : StablePath data) :
    newColumn pair 0 path + newColumn pair 1 path =
      matrix data path (star.edge 0) + matrix data path (star.edge 1) := by
  have hA := firstBox_sum pair path
  have hB := secondBox_sum pair path
  have hBackground := background_sum_eq pair hValid path 0 1
  rw [matrix_split_pair pair path (star.edge 0), matrix_split_pair pair path (star.edge 1)]
  unfold newColumn
  linarith

end Boxes


/-! ## PART B — the matrix-level chain, over a supplied limit-matrix receipt

`LimitColumns` packages exactly the three facts a limit-matrix module must
supply about the two members `W2R1SourceCandidates.Pair.candidate` already
builds: the geometric stable-row bijection of each member, the literal
equality of every retained column with the incoming wall column read through
it, and the evaluation of the regrown column as `newColumn` -- that is, as
Figures 37 and 38 print it plus one background `s`.  Nothing in it is a
numerical or genericity assumption.  `W2R1LimitMatrix.limitColumns` inhabits
it on every `{w2-r1}` datum. -/

/-- Retained target occurrences use the canonical expansion labelling; `none`
names the regrown wall occurrence. -/
noncomputable def columnEquiv (pair : Pair data star) (position : Fin 2) :
    Option target.edges ≃
      (TargetExpansion.graph target wall (pair.candidate position).right).edges :=
  occurrenceEquiv target wall (pair.candidate position).right

/-- **The limit-matrix receipt this module consumes.** -/
structure LimitColumns (pair : Pair data star) where
  /-- The member's geometric stable-row bijection. -/
  row : ∀ position : Fin 2, StablePath data ≃ StablePath (pair.candidate position).datum
  /-- Every retained column is literally the incoming wall column. -/
  retained : ∀ (position : Fin 2) (path : StablePath data) (place : target.edges),
    matrix (pair.candidate position).datum (row position path)
        (occurrenceEquiv target wall (pair.candidate position).right (some place)) =
      matrix data path place
  /-- The regrown column is Equation (10)'s displayed one. -/
  regrown : ∀ (position : Fin 2) (path : StablePath data),
    matrix (pair.candidate position).datum (row position path)
        (occurrenceEquiv target wall (pair.candidate position).right none) =
      newColumn pair position path

namespace LimitColumns

variable {pair : Pair data star}

/-- The two members' honest natural matrices in one common coordinate system:
incoming stable rows through `row`, `Option target.edges` columns. -/
noncomputable def commonMatrix (limit : LimitColumns pair) (position : Fin 2) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ matrix (pair.candidate position).datum
    (limit.row position path) (columnEquiv pair position place)

theorem commonMatrix_retained (limit : LimitColumns pair) (position : Fin 2)
    (path : StablePath data) (place : target.edges) :
    limit.commonMatrix position path (some place) = matrix data path place :=
  limit.retained position path place

theorem commonMatrix_new (limit : LimitColumns pair) (position : Fin 2)
    (path : StablePath data) :
    limit.commonMatrix position path none = newColumn pair position path :=
  limit.regrown position path

/-- **Equation (10) at column level, on the real matrices.**  The two regrown
columns, with the derived **unit** weights, add up to the two old wall
columns.  No hypothesis is introduced beyond `data.Valid`. -/
theorem weighted_column_balance (limit : LimitColumns pair) (hValid : data.Valid)
    (path : StablePath data) :
    (1 : ℚ) * limit.commonMatrix 0 path none + (1 : ℚ) * limit.commonMatrix 1 path none =
      (1 : ℚ) * matrix data path (star.edge 0) + (1 : ℚ) * matrix data path (star.edge 1) := by
  rw [limit.commonMatrix_new 0, limit.commonMatrix_new 1, one_mul, one_mul, one_mul, one_mul]
  exact newColumn_sum pair hValid path

variable (limit : LimitColumns pair) {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]

/-- A single honest member labelling supplies only the finite coordinate
order; every inter-member row correspondence comes from `LimitColumns.row`. -/
noncomputable def sourceCoordinates
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    StablePath data ≃ coordinate :=
  (limit.row 0).trans initial.row

noncomputable def targetCoordinates
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    coordinate ≃ Option target.edges :=
  initial.targetEdge.trans (columnEquiv pair 0).symm

/-- The induced honest square labelling of each of the two members. -/
noncomputable def labelling
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) :
    StableLengthMatrixLabelling (pair.candidate position).datum coordinate where
  row := (limit.row position).symm.trans (limit.sourceCoordinates initial)
  targetEdge := (targetCoordinates initial).trans (columnEquiv pair position)

/-- The honest square length matrix of one member. -/
noncomputable def squareMatrix
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix (limit.labelling initial position).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    coordinate :=
  (targetCoordinates initial).symm none

theorem squareMatrix_common
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) (row column : coordinate) :
    limit.squareMatrix initial position row column =
      limit.commonMatrix position ((limit.sourceCoordinates initial).symm row)
        (targetCoordinates initial column) :=
  labelling_matrix_eq (limit.labelling initial position) row column

theorem squareMatrix_retained
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) (row : coordinate) (place : target.edges) :
    limit.squareMatrix initial position row
        ((targetCoordinates initial).symm (some place)) =
      matrix data ((limit.sourceCoordinates initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

theorem squareMatrix_new
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) (row : coordinate) :
    limit.squareMatrix initial position row (wallColumn initial) =
      limit.commonMatrix position ((limit.sourceCoordinates initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

/-- **The two members' matrices agree away from the regrown wall column.** -/
theorem matrices_agree
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (first second : Fin 2) :
    AgreeOffColumn (limit.squareMatrix initial first) (limit.squareMatrix initial second)
      (wallColumn initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : targetCoordinates initial column with
  | none => exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

/-- **The common cofactors.** -/
theorem common_cofactors
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) (row : coordinate) :
    (limit.squareMatrix initial position).adjugate (wallColumn initial) row =
      (limit.squareMatrix initial 0).adjugate (wallColumn initial) row :=
  adjugate_wallRow_eq_of_agreeOffColumn (limit.matrices_agree initial position 0) row

/-- Each old column's cofactor-weighted contribution vanishes: this is the
`0 + 0 = 0` of Equation (10). -/
theorem old_column_annihilation
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (place : target.edges) :
    columnContribution (limit.squareMatrix initial 0) (wallColumn initial)
      ((targetCoordinates initial).symm (some place)) = 0 := by
  apply columnContribution_eq_zero
  intro h
  have hLabels := (targetCoordinates initial).symm.injective h
  cases hLabels

/-- **Equation (10)** for the two actual members in their induced common
labellings: `det⁽¹⁾ + det⁽²⁾ = 0`.  Neither member is assumed nonsingular and
the weights are the derived unit ones. -/
theorem determinant_balance (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    (1 : ℚ) * (limit.squareMatrix initial 0).det +
        (1 : ℚ) * (limit.squareMatrix initial 1).det = 0 := by
  classical
  set A := limit.squareMatrix initial with hA
  set k := wallColumn initial with hk
  set leftColumn := (targetCoordinates initial).symm (some (star.edge 0)) with hLeft
  set rightColumn := (targetCoordinates initial).symm (some (star.edge 1)) with hRight
  have hDet (position : Fin 2) : (A position).det =
      ∑ row, A position row k * (A 0).adjugate k row :=
    det_eq_sum_wallColumn_mul_commonCofactor (limit.matrices_agree initial position 0)
  have hColumn (row : coordinate) :
      (1 : ℚ) * A 0 row k + (1 : ℚ) * A 1 row k =
        (1 : ℚ) * A 0 row leftColumn + (1 : ℚ) * A 0 row rightColumn := by
    rw [hA, hk, hLeft, hRight, squareMatrix_new, squareMatrix_new,
      squareMatrix_retained, squareMatrix_retained]
    exact limit.weighted_column_balance hValid _
  calc
    (1 : ℚ) * (A 0).det + (1 : ℚ) * (A 1).det =
        ∑ row, ((1 : ℚ) * A 0 row k + (1 : ℚ) * A 1 row k) * (A 0).adjugate k row := by
      rw [hDet 0, hDet 1]
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (1 : ℚ) * columnContribution (A 0) k leftColumn +
        (1 : ℚ) * columnContribution (A 0) k rightColumn := by
      simp_rw [hColumn]
      simp only [columnContribution, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 0 := by
      rw [hA, hk, hLeft, hRight, limit.old_column_annihilation initial,
        limit.old_column_annihilation initial]
      ring

/-- **Equation (10) as a positive balance, with the unit weights derived.** -/
theorem positiveBalance (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    BalancingValencyTwo.PositiveBalance ![(1 : ℚ), (1 : ℚ)]
      (fun position ↦ (limit.squareMatrix initial position).det) := by
  constructor
  · intro position
    fin_cases position <;> norm_num
  · have h := limit.determinant_balance hValid initial
    simpa [Fin.sum_univ_succ, add_assoc] using h

/-! ### The balanced family -/

/-- The two actual `{w2-r1}` members with their honest stable-length matrices
and the proved Equation (10) balance. -/
noncomputable def family (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    BalancedGlobal.Family (coordinate := coordinate) 2 data where
  candidate := fun position ↦ (pair.candidate position).certified
  matrix := limit.squareMatrix initial
  wallColumn := wallColumn initial
  weight := ![(1 : ℚ), (1 : ℚ)]
  positiveBalance := limit.positiveBalance hValid initial
  agreeOffWall := limit.matrices_agree initial

theorem family_matrix_is_honest (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) :
    (limit.family hValid initial).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (limit.labelling initial position).presentation := rfl

/-- **The honest presented family.**  Its matrices are the honest
`GluingDatum.LengthMatrixPresentation.matrix` of a `StableLengthMatrixLabelling`
on the two members' real data -- not a presentation assembled from bare row
paths. -/
noncomputable def honestPresentedFamily (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    BalancedGlobal.PresentedFamily (coordinate := coordinate) 2 data wall where
  candidate := fun position ↦ pair.candidate position
  presentation := fun position ↦ (limit.labelling initial position).presentation
  wallColumn := wallColumn initial
  weight := ![(1 : ℚ), (1 : ℚ)]
  positiveBalance := limit.positiveBalance hValid initial
  agreeOffWall := limit.matrices_agree initial

theorem honestPresentedFamily_toFamily (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate) :
    (limit.honestPresentedFamily hValid initial).toFamily = limit.family hValid initial := rfl

theorem honestPresentedFamily_candidate (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) :
    (limit.honestPresentedFamily hValid initial).candidate position =
      pair.candidate position := rfl

theorem honestPresentedFamily_matrix (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (position : Fin 2) :
    GluingDatum.LengthMatrixPresentation.matrix
        ((limit.honestPresentedFamily hValid initial).presentation position) =
      limit.squareMatrix initial position := rfl

/-- Any nonsingular chosen member has an actual valid opposite-sign member. -/
theorem exists_valid_opposite (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (incoming : Fin 2)
    (hIncoming : (limit.squareMatrix initial incoming).det ≠ 0) :
    ∃ outgoing, (pair.candidate outgoing).datum.Valid ∧
      (limit.squareMatrix initial incoming).det *
        (limit.squareMatrix initial outgoing).det < 0 := by
  obtain ⟨outgoing, hSign⟩ :=
    BalancingValencyTwo.exists_opposite_of_positiveBalance
      (limit.positiveBalance hValid initial) hIncoming
  exact ⟨outgoing, (pair.candidate outgoing).datum_valid hValid, hSign⟩

/-- **The identified-member positive exit for Equation (10).** -/
theorem exists_valid_positive_exit_with_pencil (hValid : data.Valid)
    (initial : StableLengthMatrixLabelling (pair.candidate 0).datum coordinate)
    (hTargetConnected : graph_connected target) (hTargetGenus : genus target = 0)
    (root : target.V) (incoming : Fin 2)
    (hIncoming : (limit.squareMatrix initial incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 2 → coordinate → ℚ)
    (hz : z (wallColumn initial) = 0)
    (hzpos : ∀ i, i ≠ wallColumn initial → 0 < z i)
    (hSystems : ∀ outgoing, (limit.squareMatrix initial outgoing).det ≠ 0 →
      (limit.squareMatrix initial incoming).mulVec incomingVelocity =
        (limit.squareMatrix initial outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity (wallColumn initial) < 0) :
    ∃ outgoing,
      (pair.candidate outgoing).datum.Valid ∧
      (limit.squareMatrix initial incoming).det *
        (limit.squareMatrix initial outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (limit.squareMatrix initial outgoing).mulVec (z + t • outgoingVelocity outgoing) =
          (limit.squareMatrix initial incoming).mulVec z +
            t • (limit.squareMatrix initial incoming).mulVec incomingVelocity ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil
          (pair.candidate outgoing)
          (limit.labelling initial outgoing).presentation
          (z + t • outgoingVelocity outgoing)) :=
  (limit.honestPresentedFamily hValid initial).exists_valid_positive_exit_with_pencil
    hValid hTargetConnected hTargetGenus root incoming hIncoming z incomingVelocity
    outgoingVelocity hz hzpos hSystems hIncomingDirection

end LimitColumns


/-! ### Canonical square coordinates

`W2SourceInput.stablePath_card` already pins the number of stable rows, so no
square labelling need be supplied from outside. -/

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

namespace LimitColumns

variable {pair : Pair data star} (limit : LimitColumns pair)

/-- The `w2` source census supplies a canonical square coordinate order; it
asserts no extra geometric row matching. -/
noncomputable def canonicalRowOrder (input : W2SourceInput data star) :
    StablePath data ≃ Option target.edges :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_option, Multiset.card_coe]
    exact input.stablePath_card)

noncomputable def canonicalInitialLabelling (input : W2SourceInput data star) :
    StableLengthMatrixLabelling (pair.candidate 0).datum (Option target.edges) where
  row := (limit.row 0).symm.trans (canonicalRowOrder input)
  targetEdge := columnEquiv pair 0

noncomputable def canonicalMatrix (input : W2SourceInput data star) (position : Fin 2) :
    Matrix (Option target.edges) (Option target.edges) ℚ :=
  limit.squareMatrix (limit.canonicalInitialLabelling input) position

/-- **Equation (10) with no supplied square labelling.** -/
theorem canonical_determinant_balance (input : W2SourceInput data star) :
    (1 : ℚ) * (limit.canonicalMatrix input 0).det +
        (1 : ℚ) * (limit.canonicalMatrix input 1).det = 0 :=
  limit.determinant_balance input.valid (limit.canonicalInitialLabelling input)

noncomputable def canonicalFamily (input : W2SourceInput data star) :
    BalancedGlobal.Family (coordinate := Option target.edges) 2 data :=
  limit.family input.valid (limit.canonicalInitialLabelling input)

theorem canonicalFamily_matrix_is_honest (input : W2SourceInput data star)
    (position : Fin 2) :
    (limit.canonicalFamily input).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (limit.labelling (limit.canonicalInitialLabelling input) position).presentation := rfl

/-- **The honest presented family of Equation (10)'s two members**, in the
canonical coordinates. -/
noncomputable def canonicalPresentedFamily (input : W2SourceInput data star) :
    BalancedGlobal.PresentedFamily (coordinate := Option target.edges) 2 data wall :=
  limit.honestPresentedFamily input.valid (limit.canonicalInitialLabelling input)

theorem canonicalPresentedFamily_candidate (input : W2SourceInput data star)
    (position : Fin 2) :
    (limit.canonicalPresentedFamily input).candidate position = pair.candidate position := rfl

end LimitColumns

end DraismaVargas.LocalCases.W2R1CommonBalance
