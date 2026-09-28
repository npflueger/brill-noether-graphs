import DraismaVargas.LocalCases.W2PSourceCandidates
import DraismaVargas.LocalCases.M11JoinedDescentGeometry
import Utilities.IntegralGeometry.WallColumnDeterminant

/-!
# Figure 35's common balance: Equation (9)

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-P}`, Figure 35 and
**Equation (9)**.  The ambient hypotheses are those of Cases `{w2-r2}` and
`{w2-r2-nd3}`; Base II.1.P / II.2.1.P / II.2.2.P are listed at the start of
case `{w2-r2-nd3}`, and the local case they invoke is (r1-nd2) of the local
properties.  This development differs from the Base II.2 paragraph of Part I
as follows: there the Cardinality P alternative at `A'` is stated with
`|e'| = |A'| + 1 = k₁ + 1`, while here it is `|e'| = |A'| = k₁ + 1`
(`W2PSourceCandidates.firstLocal_newEdge_blockCard_eq_left`), the form in which
Case (r1-nd2) of the local properties gives it; nothing below uses
`|e'| = |A'| + 1`.

`W2PSourceCandidates` builds Figure 35's three members `M⁽¹⁾`, `M⁽²⁾` and
`M⁽³⁾` over one datum and one `GlobalP.Geometry`, with validity, source genus
preservation, divalence at both new endpoints, the displayed new-edge indices
and the induced block counts.  This module proves their common balance.
`W2PSourceCandidates.literalThirdMember` -- built on
`ResolutionP.residualResolution`, a shape that raises the source genus -- is
**not** used anywhere below; `thirdMember`, built on `leftSplitResolution`, is.

## What Equation (9) says, and what the column identity is

Equation (9) of Part I reads

    (k₁+1) c⁽¹⁾ + (k₂+1) c⁽²⁾ + (k₁+k₂) c⁽³⁾
      = (k₁+k₂+1)(c(e₁)/k₁ + c(e₂)/k₂ + s) + (k₁+k₂+1)(c(e₃)/(k₁+k₂+1) + s)
      = 0 + 0 = 0,

where Figure 35's boxes give `c⁽¹⁾ = c(e₁)/(k₁+1) + c(e₂)/k₂ + s`,
`c⁽²⁾ = c(e₁)/k₁ + c(e₂)/(k₂+1) + s`, `c⁽³⁾ = c(e₃)/(k₁+k₂) + s`, and the `M₀`
box gives the two vanishing brackets.  `equation_nine` is exactly this, stated
at an actual case-P profile with the profile's **own** third index `k₃` in
place of the figure's `k₁+k₂+1`; the two are identified by
`Shape.third_index`, which is this case's only free identity and the exact
analogue of `W3Nd3CommonBalance.largest_index_cast`.  `figure35_column_identity`
is the first equality alone, as an identity of rational functions.

At column level (`LimitColumns.weighted_column_balance`) the same statement
reads: the three regrown columns, weighted by `k₁+1`, `k₂+1`, `k₁+k₂`, add up
to `k₃` times the old `t₂` column plus `k₃` times the old `t₃` column.  Both old
columns are decomposed here, on the real incoming datum:
`double_matrix_decomposition` (inside `A₀` the `t₂` column displays exactly `e₁`
and `e₂` -- Cardinality P's dangling `e₄` lies above `t₂` but contributes
nothing, being in no stable row) and `single_matrix_decomposition` (it displays
exactly `e₃`).  Their two background sums are **equal**, which is Figure 35's
`σ₀(J₀,2) = σ₀(J₀,3) = s`: `background_sum_eq`, proved from the fact that a wall
block outside `A₀` is unramified, so its source vertex is divalent and its two
occurrences are dangling together, share a stable row and have the block's own
size as common index.

## The weights are derived, not posited

Unlike the nd3 pair, this case does not balance with unit weights.  The three
weights are the three members' **own** new-edge block cardinalities --
`|e'| = k₁+1` for `M⁽¹⁾`, `|e''| = k₂+1` for `M⁽²⁾`, `|e'| = k₁+k₂` for
`M⁽³⁾` -- which is `figure35_weights_eq_indices`, read off
`W2PSourceCandidates.firstMember_indices` and its two siblings.  They are also
forced: `figure35_weights_forced` shows that the four coefficient equations of
the column identity (the coefficients of `c(e₁)`, `c(e₂)`, `c(e₃)` and of the
background, listed in `figure35_coefficients`) have a one-dimensional solution
space, and `figure35_weights_normalized` pins it once the first weight is fixed
at `k₁+1`.  So `![k₁+1, k₂+1, k₁+k₂]` is the only weight vector, up to one
overall scale, for which the three regrown columns combine into old columns at
all.  `BalancingValencyTwo.balance_P` is the right tool and is used
(`positiveBalance_of_relations`); its `hright` is stated with `k₁+k₂+1` and
`Shape.third_index` converts.

## PART A and PART B: what is unconditional and what is not

**Everything up to and including `positiveBalance_of_relations` is
unconditional**, with exactly `W2PSourceCandidates`' hypothesis bundle (a
`W2R2SourceProfile.SourceProfile`, a `Shape`, and -- where the background is
involved -- the `SecondEquation.W2SourceInput` that `W2PSourceCandidates`'
callers already carry).  No new hypothesis is introduced anywhere in Part A.

**Part B is conditional on `LimitColumns`**, which
`W2PLimitMatrix.limitColumns` inhabits on every datum of the case.
`LimitColumns` packages the three facts a limit-matrix module must supply for
Figure 35's members: the geometric stable-row bijection of each member, the
literal equality of every retained column with the incoming wall column read
through it, and the evaluation of the regrown column as Figure 35's box gives
it.  For the nd3 pair those three are `W3Nd3LimitMatrix`'s
`coarseStablePathEquiv` / `coarse_matrix_retained` /
`coarse_matrix_new_on_old_row` and their fine mirrors, resting on
`W3Nd3StableGraph`; for M11 they are `M11SplitRowDescent`,
`M11RemoteLimitMatrix` and `M11JoinedLimitMatrix`, resting on
`M11SplitSurvival` / `M11JoinedSurvival` and the stable lifts; for
`{w2-r2-nd3-P}` they are `W2PLimitMatrix`, resting on `W2PSurvival` and
`W2PStableLift`.  The certified exit is `W2PArbitraryExit.outgoingPresentation`.

Nothing in `LimitColumns` is a numerical or genericity assumption: all three
fields are statements proved about the members `W2PSourceCandidates` builds.
In particular a supplier must prove that `M⁽³⁾`'s surviving new occurrence lies
in `e₃`'s stable row (its `t₃` endpoint has surviving valency two, the dangling
singleton of `thirdMember_indices` being the third incidence) while `M⁽¹⁾`'s
and `M⁽²⁾`'s two new occurrences lie in `e₁`'s and `e₂`'s rows.

## What Part B proves

* `LimitColumns.commonMatrix`, `commonMatrix_retained` -- the three members'
  honest natural matrices in one coordinate system.
* `weighted_column_balance` -- **Equation (9) at column level on the real
  matrices**.
* `matrices_agree`, `common_cofactors` -- from the retained columns alone; no
  nonsingularity and no supplied cofactor correspondence.
* `old_column_annihilation`, `determinant_balance` -- Equation (9) for the three
  actual members' honest square matrices, with the derived weights.  No member
  is assumed nonsingular.
* `family`, `honestPresentedFamily`, `family_matrix_is_honest` -- a
  `BalancedGlobal.Family` and a `BalancedGlobal.PresentedFamily 3 data wall` on
  the one datum, whose matrices are the honest
  `GluingDatum.LengthMatrixPresentation.matrix` of a
  `StableLengthMatrixLabelling` on the real data.
* `exists_valid_opposite`, `exists_valid_positive_exit_with_pencil` -- the
  identified-member exit, assuming only that the chosen incoming member is
  nonsingular.
* `canonicalRowOrder`, `canonicalMatrix`, `canonical_determinant_balance`,
  `canonicalFamily`, `canonicalPresentedFamily` -- the same with the coordinate
  order forced by `W2SourceInput.stablePath_card`.

## Routing

`BalancedGlobal.PresentedFamily` is used, not `GlobalP`'s pattern-typed family.
`GlobalP`'s `Geometry.thirdLocal` is `ResolutionP.residualResolution`, which
raises the source genus by one (`W2PSourceCandidates`), so the `M⁽³⁾` of
Figure 35 used here is not of the shape `GlobalP.candidates` builds;
`PresentedFamily` needs no pattern and takes the three actual
`BalancedGlobal.Candidate`s on the one datum, exactly as `W3Nd3CommonBalance`
does for the nd3 pair.

`BalancedGlobal.Family.exists_valid_opposite` is **not** invoked:
`(family …).matrix incoming` and `squareMatrix initial incoming` are
definitionally equal but the unifier does not get there within the default
heartbeat budget, because `Family.candidate` forces `Candidate.certified` open.
`exists_valid_opposite` therefore goes straight through
`BalancingValencyTwo.exists_opposite_of_positiveBalance` and
`BalancedGlobal.Candidate.datum_valid`, which is the same proof the library
theorem gives.  `PresentedFamily.exists_valid_positive_exit_with_pencil` has no
such trouble and is used unchanged.

## What is deliberately not here

Identifying an *arbitrary* incoming case-P datum with a named Figure 35 member
(the analogue of `W3Nd2IncomingMemberMatching` / `W3Nd3IncomingMatching`) is
`W2PIncomingMatching`, and the `LimitColumns` supplier is `W2PLimitMatrix`.
-/

namespace DraismaVargas.LocalCases.W2PCommonBalance

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open W2PSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The one free identity -/

/-- **`k₃ = k₁ + k₂ + 1` in `ℚ`.** -/
theorem third_index_cast (shape : Shape profile) :
    (data.sourceEdgeIndex profile.third.1 : ℚ) =
      (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ) + 1 := by
  exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℚ)) shape.third_index

theorem first_ne_second : profile.first.1 ≠ profile.second.1 :=
  fun h ↦ profile.first_ne_second (Subtype.ext h)

/-! ## The two old wall columns -/

/-- The stable row of `e₁`. -/
noncomputable def firstRow : StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.first.1, profile.first_survives⟩

/-- The stable row of `e₂`. -/
noncomputable def secondRow : StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩

/-- The stable row of `e₃`. -/
noncomputable def thirdRow : StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩

private theorem selected_double_eq {path : StablePath data} (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path (star.edge profile.doubleLabel))
    (hRel : (data.vertexPartition wall).Rel block.1 edge.1.2) :
    edge = profile.first.1 ∨ edge = profile.second.1 := by
  obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge (WallBlock.sourceVertex data wall block) := by
    apply (incident_iff_target_mem_and_rel data edge _).mpr
    refine ⟨hTarget ▸ star.edge_mem_incidentEdges profile.doubleLabel, ?_⟩
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr block.1) edge.1.2
    exact ((data.vertexPartition wall).rel_repr_left block.1).trans hRel
  rcases profile.exhaustive ⟨edge, hIncident⟩ with hEq | hEq | hEq | hEq
  · exact Or.inl (congrArg Subtype.val hEq)
  · exact Or.inr (congrArg Subtype.val hEq)
  · exact absurd ((hTarget.symm.trans
      (congrArg (fun e : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ e.1.1.1) hEq)).trans profile.third_target)
      (star.edge_injective.ne profile.labels_ne)
  · refine absurd ?_ hSurvives
    have hDeleted : edge = profile.deleted.edge.1 := congrArg Subtype.val hEq
    rw [hDeleted]
    exact profile.deleted.dangling

private theorem selected_single_eq {path : StablePath data} (edge : data.SourceEdge)
    (hMem : edge ∈ occurrences data path (star.edge profile.singleLabel))
    (hRel : (data.vertexPartition wall).Rel block.1 edge.1.2) :
    edge = profile.third.1 := by
  obtain ⟨⟨hSurvives, _⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
  have hIncident : Incident data edge (WallBlock.sourceVertex data wall block) := by
    apply (incident_iff_target_mem_and_rel data edge _).mpr
    refine ⟨hTarget ▸ star.edge_mem_incidentEdges profile.singleLabel, ?_⟩
    change (data.vertexPartition wall).Rel
      ((data.vertexPartition wall).repr block.1) edge.1.2
    exact ((data.vertexPartition wall).rel_repr_left block.1).trans hRel
  rcases profile.exhaustive ⟨edge, hIncident⟩ with hEq | hEq | hEq | hEq
  · exact absurd ((hTarget.symm.trans
      (congrArg (fun e : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ e.1.1.1) hEq)).trans profile.first_target)
      (star.edge_injective.ne profile.labels_ne.symm)
  · exact absurd ((hTarget.symm.trans
      (congrArg (fun e : IncidentSourceEdge data
        (WallBlock.sourceVertex data wall block) ↦ e.1.1.1) hEq)).trans profile.second_target)
      (star.edge_injective.ne profile.labels_ne.symm)
  · exact congrArg Subtype.val hEq
  · refine absurd ?_ hSurvives
    have hDeleted : edge = profile.deleted.edge.1 := congrArg Subtype.val hEq
    rw [hDeleted]
    exact profile.deleted.dangling


/-- The occurrences of one old wall column that lie **outside** the
distinguished block `A₀`: Figure 35's background, whose cofactor-weighted sum
is the `s` of the limit box. -/
noncomputable def backgroundOccurrences (star : TwoStar target wall)
    (block : WallBlock data wall) (path : StablePath data) (label : Fin 2) :
    Finset data.SourceEdge := by
  classical
  exact (occurrences data path (star.edge label)).filter
    (fun edge ↦ ¬ (data.vertexPartition wall).Rel block.1 edge.1.2)

theorem mem_backgroundOccurrences (star : TwoStar target wall)
    (block : WallBlock data wall) (path : StablePath data) (label : Fin 2)
    (edge : data.SourceEdge) :
    edge ∈ backgroundOccurrences star block path label ↔
      edge ∈ occurrences data path (star.edge label) ∧
        ¬ (data.vertexPartition wall).Rel block.1 edge.1.2 := by
  classical
  simp only [backgroundOccurrences, Finset.mem_filter]

/-- Figure 35's `s`, read on one old wall column and one old stable row. -/
noncomputable def backgroundColumn (star : TwoStar target wall)
    (block : WallBlock data wall) (path : StablePath data) (label : Fin 2) : ℚ :=
  ∑ edge ∈ backgroundOccurrences star block path label,
    (1 : ℚ) / data.sourceEdgeIndex edge

/-- **The old `t₂` column.**  Inside `A₀` it displays exactly `e₁` and `e₂`:
the third survivor `e₃` lies above `t₃`, and the dangling `e₄` -- which
Cardinality P puts above `t₂` -- contributes nothing, because a dangling
occurrence is in no stable row at all. -/
theorem double_matrix_decomposition (path : StablePath data) :
    matrix data path (star.edge profile.doubleLabel) =
      (if path = firstRow profile then (1 : ℚ) else 0) /
          data.sourceEdgeIndex profile.first.1 +
        (if path = secondRow profile then (1 : ℚ) else 0) /
          data.sourceEdgeIndex profile.second.1 +
        backgroundColumn star block path profile.doubleLabel := by
  classical
  let selected := (occurrences data path (star.edge profile.doubleLabel)).filter
    (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2)
  have hSelected : selected =
      ({profile.first.1, profile.second.1} : Finset data.SourceEdge).filter
        (fun edge ↦ edge ∈ occurrences data path (star.edge profile.doubleLabel)) := by
    ext edge
    simp only [selected, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      exact ⟨selected_double_eq profile edge hMem hRel, hMem⟩
    · rintro ⟨hEq, hMem⟩
      refine ⟨hMem, ?_⟩
      rcases hEq with rfl | rfl
      · exact sheet_rel_of_incident profile.first
      · exact sheet_rel_of_incident profile.second
  have hMem (edge : NonDanglingEdge data)
      (hTarget : edge.1.1.1 = star.edge profile.doubleLabel) :
      edge.1 ∈ occurrences data path (star.edge profile.doubleLabel) ↔
        path = edge.stablePath := by
    rw [mem_occurrences]
    exact ⟨fun h ↦ h.1.choose_spec.symm, fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (occurrences data path (star.edge profile.doubleLabel))
    (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  change (∑ edge ∈ selected, (1 : ℚ) / data.sourceEdgeIndex edge) +
      backgroundColumn star block path profile.doubleLabel =
        matrix data path (star.edge profile.doubleLabel) at hSplit
  rw [hSelected, Finset.sum_filter,
    Finset.sum_pair (first_ne_second profile)] at hSplit
  simp only [hMem ⟨profile.first.1, profile.first_survives⟩ profile.first_target,
    hMem ⟨profile.second.1, profile.second_survives⟩ profile.second_target] at hSplit
  rw [← hSplit]
  show _ = (if path = NonDanglingEdge.stablePath
        ⟨profile.first.1, profile.first_survives⟩ then (1 : ℚ) else 0) /
          data.sourceEdgeIndex profile.first.1 +
      (if path = NonDanglingEdge.stablePath
        ⟨profile.second.1, profile.second_survives⟩ then (1 : ℚ) else 0) /
          data.sourceEdgeIndex profile.second.1 + _
  split_ifs <;> ring

/-- **The old `t₃` column.**  Inside `A₀` it displays only `e₃`. -/
theorem single_matrix_decomposition (path : StablePath data) :
    matrix data path (star.edge profile.singleLabel) =
      (if path = thirdRow profile then (1 : ℚ) else 0) /
          data.sourceEdgeIndex profile.third.1 +
        backgroundColumn star block path profile.singleLabel := by
  classical
  let selected := (occurrences data path (star.edge profile.singleLabel)).filter
    (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2)
  have hSelected : selected =
      ({profile.third.1} : Finset data.SourceEdge).filter
        (fun edge ↦ edge ∈ occurrences data path (star.edge profile.singleLabel)) := by
    ext edge
    simp only [selected, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hMem, hRel⟩
      exact ⟨selected_single_eq profile edge hMem hRel, hMem⟩
    · rintro ⟨rfl, hMem⟩
      exact ⟨hMem, sheet_rel_of_incident profile.third⟩
  have hMem (edge : NonDanglingEdge data)
      (hTarget : edge.1.1.1 = star.edge profile.singleLabel) :
      edge.1 ∈ occurrences data path (star.edge profile.singleLabel) ↔
        path = edge.stablePath := by
    rw [mem_occurrences]
    exact ⟨fun h ↦ h.1.choose_spec.symm, fun h ↦ ⟨⟨edge.2, h.symm⟩, hTarget⟩⟩
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (occurrences data path (star.edge profile.singleLabel))
    (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2)
    (fun edge ↦ (1 : ℚ) / data.sourceEdgeIndex edge)
  change (∑ edge ∈ selected, (1 : ℚ) / data.sourceEdgeIndex edge) +
      backgroundColumn star block path profile.singleLabel =
        matrix data path (star.edge profile.singleLabel) at hSplit
  rw [hSelected, Finset.sum_filter, Finset.sum_singleton] at hSplit
  simp only [hMem ⟨profile.third.1, profile.third_survives⟩ profile.third_target] at hSplit
  rw [← hSplit]
  show _ = (if path = NonDanglingEdge.stablePath
        ⟨profile.third.1, profile.third_survives⟩ then (1 : ℚ) else 0) /
          data.sourceEdgeIndex profile.third.1 + _
  split_ifs <;> ring

/-! ## Figure 35's `s`: the two old backgrounds agree -/

include profile in
/-- Away from `A₀` each direction displays one occurrence of the wall block,
of the block's own size. -/
theorem background_index_eq (input : W2SourceInput data star) (label : Fin 2)
    (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    data.sourceEdgeIndex (data.sourceEdge (star.edge label) sheet) =
      (data.vertexPartition wall).blockCard sheet := by
  rw [GluingDatum.sourceEdgeIndex_sourceEdge]
  exact SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one _ _
    (star.edgePartition_refines_wall data label) sheet
    (M11JoinedBackground.background_blockCount input profile label sheet hBackground)

include profile in
/-- A background wall vertex is divalent in the quotient source, so its two
occurrences are dangling together. -/
theorem background_isDangling_iff (input : W2SourceInput data star) (one two : Fin 2)
    (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    IsDangling data (data.sourceEdge (star.edge one) sheet) ↔
      IsDangling data (data.sourceEdge (star.edge two) sheet) := by
  have hDegree : vertex_degree data.sourceGraph (data.sourceEndpoint wall sheet) = 2 := by
    rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge]
    exact_mod_cast M11JoinedDescentGeometry.background_old_card_incident input profile sheet
      hBackground
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

include profile in
private theorem background_transfer_mem (input : W2SourceInput data star)
    (path : StablePath data) (one two : Fin 2) (edge : data.SourceEdge)
    (hMem : edge ∈ backgroundOccurrences star block path one) :
    data.sourceEdge (star.edge two) edge.1.2 ∈
      backgroundOccurrences star block path two := by
  have hData := (mem_backgroundOccurrences star block path one edge).mp hMem
  obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hData.1
  have hCanonical := M11JoinedStableLift.background_sourceEdge_eq input profile one
    edge.1.2 hData.2 edge hTarget rfl
  have hOld : ¬ IsDangling data (data.sourceEdge (star.edge one) edge.1.2) := by
    rw [hCanonical]; exact hSurvives
  have hNew : ¬ IsDangling data (data.sourceEdge (star.edge two) edge.1.2) :=
    fun h ↦ hOld ((background_isDangling_iff profile input two one edge.1.2 hData.2).mp h)
  refine (mem_backgroundOccurrences star block path two _).mpr
    ⟨(mem_occurrences _ _ _).mpr ⟨⟨hNew, ?_⟩, rfl⟩, ?_⟩
  · have hPaths := M11JoinedDescentGeometry.background_old_stablePath_eq input profile
      edge.1.2 hData.2 ⟨data.sourceEdge (star.edge two) edge.1.2, hNew⟩ ⟨edge, hSurvives⟩
      (incident_sourceEdge_sourceEndpoint data wall _
        (star.edge_mem_incidentEdges two) edge.1.2)
      (by
        have hIncident := incident_sourceEdge_sourceEndpoint data wall _
          (star.edge_mem_incidentEdges one) edge.1.2
        rw [hCanonical] at hIncident
        exact hIncident)
    exact hPaths.trans hRow
  · exact fun h ↦ hData.2 (h.trans ((star.edgePartition_refines_wall data two).rel
      ((data.edgePartition (star.edge two)).rel_repr_left edge.1.2)))

include profile in
private theorem background_transfer_inverse (input : W2SourceInput data star)
    (path : StablePath data) (one two : Fin 2) (edge : data.SourceEdge)
    (hMem : edge ∈ backgroundOccurrences star block path one) :
    data.sourceEdge (star.edge one) (data.sourceEdge (star.edge two) edge.1.2).1.2 =
      edge := by
  have hData := (mem_backgroundOccurrences star block path one edge).mp hMem
  have hRel := (star.edgePartition_refines_wall data two).rel
    ((data.edgePartition (star.edge two)).rel_repr_left edge.1.2)
  exact M11JoinedStableLift.background_sourceEdge_eq input profile one _
    (fun h ↦ hData.2 (h.trans hRel)) edge ((mem_occurrences _ _ _).mp hData.1).2 hRel

include profile in
/-- **Figure 35's `s = σ₀(J₀,2) = σ₀(J₀,3)`.**  The two old wall columns have
the same background sum on every old stable row: outside `A₀` the wall vertex
is an unramified divalent junction, so its two occurrences are dangling
together, share a stable row and have the block's size as common index. -/
theorem background_sum_eq (input : W2SourceInput data star) (path : StablePath data)
    (one two : Fin 2) :
    backgroundColumn star block path one = backgroundColumn star block path two := by
  classical
  apply Finset.sum_nbij' (fun edge ↦ data.sourceEdge (star.edge two) edge.1.2)
    (fun edge ↦ data.sourceEdge (star.edge one) edge.1.2)
    (fun edge h ↦ background_transfer_mem profile input path one two edge h)
    (fun edge h ↦ background_transfer_mem profile input path two one edge h)
    (fun edge h ↦ background_transfer_inverse profile input path one two edge h)
    (fun edge h ↦ background_transfer_inverse profile input path two one edge h)
  intro edge hMem
  have hData := (mem_backgroundOccurrences star block path one edge).mp hMem
  have hCanonical := M11JoinedStableLift.background_sourceEdge_eq input profile one
    edge.1.2 hData.2 edge ((mem_occurrences _ _ _).mp hData.1).2 rfl
  have hIdx : data.sourceEdgeIndex edge =
      data.sourceEdgeIndex (data.sourceEdge (star.edge one) edge.1.2) :=
    congrArg data.sourceEdgeIndex hCanonical.symm
  rw [hIdx, background_index_eq profile input one edge.1.2 hData.2,
    background_index_eq profile input two edge.1.2 hData.2]

/-! ## Equation (9) -/

/-- **Equation (9)'s first equality**, as an identity of rational
functions of `k₁`, `k₂` and of four free column entries.  The three Figure 35
determinants weighted by `k₁+1`, `k₂+1`, `k₁+k₂` are the two vanishing `M₀`
brackets, each taken `k₁+k₂+1` times. -/
theorem figure35_column_identity {k₁ k₂ c₁ c₂ c₃ b : ℚ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    (k₁ + 1) * (c₁ / (k₁ + 1) + c₂ / k₂ + b) +
        (k₂ + 1) * (c₁ / k₁ + c₂ / (k₂ + 1) + b) +
        (k₁ + k₂) * (c₃ / (k₁ + k₂) + b) =
      (k₁ + k₂ + 1) * (c₁ / k₁ + c₂ / k₂ + b) +
        (k₁ + k₂ + 1) * (c₃ / (k₁ + k₂ + 1) + b) := by
  have h₁ : k₁ ≠ 0 := ne_of_gt hk₁
  have h₂ : k₂ ≠ 0 := ne_of_gt hk₂
  have h₃ : k₁ + 1 ≠ 0 := by positivity
  have h₄ : k₂ + 1 ≠ 0 := by positivity
  have h₅ : k₁ + k₂ ≠ 0 := by positivity
  have h₆ : k₁ + k₂ + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **The four coefficient equations of the column identity.**  Reading
`figure35_column_identity` off the coefficients of `c₁`, `c₂`, `c₃` and of the
background `b`, with a general weight vector `(w₁, w₂, w₃)` and general old
column multipliers `(α, β)`, gives exactly these four, cleared of
denominators.  The Figure 35 weights satisfy them. -/
theorem figure35_coefficients (k₁ k₂ : ℚ) :
    (k₁ + 1) * k₁ + (k₂ + 1) * (k₁ + 1) = (k₁ + k₂ + 1) * (k₁ + 1) ∧
      (k₁ + 1) * (k₂ + 1) + (k₂ + 1) * k₂ = (k₁ + k₂ + 1) * (k₂ + 1) ∧
        (k₁ + k₂) * (k₁ + k₂ + 1) = (k₁ + k₂ + 1) * (k₁ + k₂) ∧
          (k₁ + 1) + (k₂ + 1) + (k₁ + k₂) = (k₁ + k₂ + 1) + (k₁ + k₂ + 1) :=
  ⟨by ring, by ring, by ring, by ring⟩

/-- **The Equation (9) weights are forced, up to one overall scale.**  Given
the four coefficient equations of `figure35_coefficients` for unknown weights
`w₁, w₂, w₃` and unknown old-column multipliers `α, β`, every solution is the
Figure 35 one scaled by `w₁ / (k₁ + 1)`.  Nothing is posited: the weight vector
`![k₁+1, k₂+1, k₁+k₂]` is the only one, up to scale, for which the three new
columns combine into old columns at all. -/
theorem figure35_weights_forced {k₁ k₂ w₁ w₂ w₃ α β : ℚ}
    (hFirst : w₁ * k₁ + w₂ * (k₁ + 1) = α * (k₁ + 1))
    (hSecond : w₁ * (k₂ + 1) + w₂ * k₂ = α * (k₂ + 1))
    (hThird : w₃ * (k₁ + k₂ + 1) = β * (k₁ + k₂))
    (hFourth : w₁ + w₂ + w₃ = α + β) :
    w₂ * (k₁ + 1) = w₁ * (k₂ + 1) ∧
      α * (k₁ + 1) = w₁ * (k₁ + k₂ + 1) ∧
        w₃ * (k₁ + 1) = w₁ * (k₁ + k₂) ∧
          β * (k₁ + 1) = w₁ * (k₁ + k₂ + 1) := by
  have key₁ : w₂ * (k₁ + 1) = w₁ * (k₂ + 1) := by
    linear_combination (k₂ + 1) * hFirst - (k₁ + 1) * hSecond
  have key₂ : α * (k₁ + 1) = w₁ * (k₁ + k₂ + 1) := by
    linear_combination key₁ - hFirst
  have key₃ : w₃ * (k₁ + 1) = w₁ * (k₁ + k₂) := by
    linear_combination (k₁ + 1) * hThird - (k₁ + k₂) * (k₁ + 1) * hFourth +
      (k₁ + k₂) * key₁ - (k₁ + k₂) * key₂
  refine ⟨key₁, key₂, key₃, ?_⟩
  linear_combination (-(k₁ + 1)) * hFourth + key₁ - key₂ + key₃

/-- The normalized form of `figure35_weights_forced`: fixing the first weight
at Figure 35's `k₁ + 1` pins the other two and both old-column multipliers. -/
theorem figure35_weights_normalized {k₁ k₂ w₂ w₃ α β : ℚ} (hk₁ : 0 < k₁)
    (hFirst : (k₁ + 1) * k₁ + w₂ * (k₁ + 1) = α * (k₁ + 1))
    (hSecond : (k₁ + 1) * (k₂ + 1) + w₂ * k₂ = α * (k₂ + 1))
    (hThird : w₃ * (k₁ + k₂ + 1) = β * (k₁ + k₂))
    (hFourth : (k₁ + 1) + w₂ + w₃ = α + β) :
    w₂ = k₂ + 1 ∧ α = k₁ + k₂ + 1 ∧ w₃ = k₁ + k₂ ∧ β = k₁ + k₂ + 1 := by
  have hne : k₁ + 1 ≠ 0 := by positivity
  obtain ⟨key₁, key₂, key₃, key₄⟩ :=
    figure35_weights_forced hFirst hSecond hThird hFourth
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_right_cancel₀ hne (key₁.trans (by ring))
  · exact mul_right_cancel₀ hne (key₂.trans (by ring))
  · exact mul_right_cancel₀ hne (key₃.trans (by ring))
  · exact mul_right_cancel₀ hne (key₄.trans (by ring))

/-- **Figure 35's weights are the three members' own new-edge indices.**
`M⁽¹⁾` contributes `|e'| = k₁ + 1`, `M⁽²⁾` contributes `|e''| = k₂ + 1`, and
`M⁽³⁾` contributes `|e'| = k₁ + k₂`.  These are exactly the three
coefficients of Equation (9). -/
theorem figure35_weights_eq_indices (shape : Shape profile) :
    (geometry shape).firstLocal.newEdge.blockCard (firstSheet profile) =
        data.sourceEdgeIndex profile.first.1 + 1 ∧
      (geometry shape).secondLocal.newEdge.blockCard (secondSheet profile) =
        data.sourceEdgeIndex profile.second.1 + 1 ∧
        (thirdLocal shape).newEdge.blockCard (firstSheet profile) =
          data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 :=
  ⟨(firstMember_indices shape).1, (secondMember_indices shape).1,
    (thirdMember_indices shape).1⟩

/-- **Equation (9)** at an actual case-P source profile.  The two
hypotheses are Figure 35's `M₀` box, stated with the profile's own third index
`k₃` rather than with the figure's `k₁ + k₂ + 1`; `Shape.third_index` is what
identifies them, and it is the case's only free identity.  The middle
expression of Equation (9) is the right-hand side. -/
theorem equation_nine (shape : Shape profile) {c₁ c₂ c₃ s : ℚ}
    (hLeft : c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
      c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s = 0)
    (hRight : c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s = 0) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) *
          (c₁ / ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) +
            c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s) +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) *
          (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
            c₂ / ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) + s) +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          (c₃ / ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) + s) =
      ((data.sourceEdgeIndex profile.third.1 : ℚ)) *
          (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
            c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s) +
        ((data.sourceEdgeIndex profile.third.1 : ℚ)) *
          (c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s) ∧
      ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) *
          (c₁ / ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) +
            c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s) +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) *
          (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
            c₂ / ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) + s) +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          (c₃ / ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) + s) = 0 := by
  have hk₁ : (0 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) := by
    exact_mod_cast sourceEdgeIndex_pos data profile.first.1
  have hk₂ : (0 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    exact_mod_cast sourceEdgeIndex_pos data profile.second.1
  have hCast := third_index_cast profile shape
  have hIdentity := figure35_column_identity (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (b := s) hk₁ hk₂
  rw [← hCast] at hIdentity
  refine ⟨hIdentity, ?_⟩
  rw [hIdentity, hLeft, hRight]
  ring

/-- **Equation (9) as a positive balance**, in the exact shape
`BalancingValencyTwo.balance_P` states it, with the weights derived rather than
supplied. -/
theorem positiveBalance_of_relations (shape : Shape profile) {c₁ c₂ c₃ s : ℚ}
    (hLeft : c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
      c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s = 0)
    (hRight : c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s = 0) :
    BalancingValencyTwo.PositiveBalanceThree
      ![(data.sourceEdgeIndex profile.first.1 : ℚ) + 1,
        (data.sourceEdgeIndex profile.second.1 : ℚ) + 1,
        (data.sourceEdgeIndex profile.first.1 : ℚ) +
          (data.sourceEdgeIndex profile.second.1 : ℚ)]
      ![c₁ / ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) +
          c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s,
        c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
          c₂ / ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) + s,
        c₃ / ((data.sourceEdgeIndex profile.first.1 : ℚ) +
          (data.sourceEdgeIndex profile.second.1 : ℚ)) + s] := by
  have hk₁ : (0 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) := by
    exact_mod_cast sourceEdgeIndex_pos data profile.first.1
  have hk₂ : (0 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    exact_mod_cast sourceEdgeIndex_pos data profile.second.1
  refine BalancingValencyTwo.balance_P hk₁ hk₂ hLeft ?_
  rw [← third_index_cast profile shape]
  exact hRight

/-! ## PART B — the matrix-level chain, over a supplied limit-matrix receipt -/

/-- Figure 35's three members, indexed: `M⁽¹⁾`, `M⁽²⁾` and `M⁽³⁾` (built on
`leftSplitResolution`).  `W2PSourceCandidates.literalThirdMember` is
deliberately not here. -/
noncomputable def members (shape : Shape profile) :
    Fin 3 → BalancedGlobal.Candidate target degree data wall :=
  ![firstMember shape, secondMember shape, thirdMember shape]

@[simp] theorem members_zero (shape : Shape profile) :
    members profile shape 0 = firstMember shape := rfl

@[simp] theorem members_one (shape : Shape profile) :
    members profile shape 1 = secondMember shape := rfl

@[simp] theorem members_two (shape : Shape profile) :
    members profile shape 2 = thirdMember shape := rfl

/-- `M⁽¹⁾`'s regrown column: `c⁽¹⁾ = c(e₁)/(k₁+1) + c(e₂)/k₂ + s`. -/
noncomputable def firstNewColumn (path : StablePath data) : ℚ :=
  (if path = firstRow profile then (1 : ℚ) else 0) /
      ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) +
    (if path = secondRow profile then (1 : ℚ) else 0) /
      (data.sourceEdgeIndex profile.second.1 : ℚ) +
    backgroundColumn star block path profile.doubleLabel

/-- `M⁽²⁾`'s regrown column: `c⁽²⁾ = c(e₁)/k₁ + c(e₂)/(k₂+1) + s`. -/
noncomputable def secondNewColumn (path : StablePath data) : ℚ :=
  (if path = firstRow profile then (1 : ℚ) else 0) /
      (data.sourceEdgeIndex profile.first.1 : ℚ) +
    (if path = secondRow profile then (1 : ℚ) else 0) /
      ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) +
    backgroundColumn star block path profile.doubleLabel

/-- `M⁽³⁾`'s regrown column: `c⁽³⁾ = c(e₃)/(k₁+k₂) + s`. The dangling singleton
of `thirdMember_indices` contributes nothing. -/
noncomputable def thirdNewColumn (path : StablePath data) : ℚ :=
  (if path = thirdRow profile then (1 : ℚ) else 0) /
      ((data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ)) +
    backgroundColumn star block path profile.doubleLabel

/-- Figure 35's three regrown columns, indexed. -/
noncomputable def newColumn : Fin 3 → StablePath data → ℚ :=
  ![firstNewColumn profile, secondNewColumn profile, thirdNewColumn profile]

@[simp] theorem newColumn_zero : newColumn profile 0 = firstNewColumn profile := rfl
@[simp] theorem newColumn_one : newColumn profile 1 = secondNewColumn profile := rfl
@[simp] theorem newColumn_two : newColumn profile 2 = thirdNewColumn profile := rfl

/-- Retained target occurrences use the canonical expansion labelling; `none`
names the regrown wall occurrence. -/
noncomputable def columnEquiv (shape : Shape profile) (position : Fin 3) :
    Option target.edges ≃
      (TargetExpansion.graph target wall (members profile shape position).right).edges :=
  occurrenceEquiv target wall (members profile shape position).right

/-- **The limit-matrix receipt this module consumes.**

Everything below this point is conditional on an inhabitant of this structure;
`W2PLimitMatrix.limitColumns` / `nonempty_limitColumns` produce one.  Its three
fields are exactly what `W3Nd3LimitMatrix` supplies for the nd3 pair
(`coarseStablePathEquiv`, `coarse_matrix_retained`,
`coarse_matrix_new_on_old_row`, and their fine mirrors), and what the M11 chain
supplies through `M11SplitRowDescent` / `M11RemoteLimitMatrix` /
`M11JoinedLimitMatrix`.

The `row` field is the geometric stable-row bijection of each member, not an
arbitrary equinumerosity; `retained` says every non-regrown column of the
member's honest `StableSourceMatrix.matrix` is literally the incoming wall
column read through it; `regrown` evaluates the new column as Figure 35's box
does.  A supplier must prove all three, and in particular must prove that the
surviving new occurrence of `M⁽³⁾` lies in `e₃`'s stable row while its dangling
singleton lies in none. -/
structure LimitColumns (shape : Shape profile) where
  /-- The member's geometric stable-row bijection. -/
  row : ∀ position : Fin 3, StablePath data ≃ StablePath (members profile shape position).datum
  /-- Every retained column is literally the incoming wall column. -/
  retained : ∀ (position : Fin 3) (path : StablePath data) (place : target.edges),
    matrix (members profile shape position).datum (row position path)
        (occurrenceEquiv target wall (members profile shape position).right (some place)) =
      matrix data path place
  /-- The regrown column is Figure 35's displayed one. -/
  regrown : ∀ (position : Fin 3) (path : StablePath data),
    matrix (members profile shape position).datum (row position path)
        (occurrenceEquiv target wall (members profile shape position).right none) =
      newColumn profile position path

namespace LimitColumns

variable {profile} {shape : Shape profile}

/-- The three members' honest natural matrices in one common coordinate
system: incoming stable rows through `row`, `Option target.edges` columns. -/
noncomputable def commonMatrix (limit : LimitColumns profile shape) (position : Fin 3) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ matrix (members profile shape position).datum
    (limit.row position path) (columnEquiv profile shape position place)

theorem commonMatrix_retained (limit : LimitColumns profile shape) (position : Fin 3)
    (path : StablePath data) (place : target.edges) :
    limit.commonMatrix position path (some place) = matrix data path place :=
  limit.retained position path place

theorem commonMatrix_new (limit : LimitColumns profile shape) (position : Fin 3)
    (path : StablePath data) :
    limit.commonMatrix position path none = newColumn profile position path :=
  limit.regrown position path

/-- **Equation (9) at column level, on the real matrices.**  The three regrown
columns weighted by the members' own new-edge indices `k₁+1`, `k₂+1`, `k₁+k₂`
add up to `k₃` times each of the two old wall columns.  The two sides meet only
through `Shape.third_index` (`k₃ = k₁+k₂+1`) and `background_sum_eq`
(`σ₀(J₀,2) = σ₀(J₀,3)`); no hypothesis is introduced. -/
theorem weighted_column_balance (input : W2SourceInput data star)
    (limit : LimitColumns profile shape) (path : StablePath data) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) *
          limit.commonMatrix 0 path none +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) *
          limit.commonMatrix 1 path none +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          limit.commonMatrix 2 path none =
      (data.sourceEdgeIndex profile.third.1 : ℚ) *
          matrix data path (star.edge profile.doubleLabel) +
        (data.sourceEdgeIndex profile.third.1 : ℚ) *
          matrix data path (star.edge profile.singleLabel) := by
  have hk₁ : ((data.sourceEdgeIndex profile.first.1 : ℚ)) ≠ 0 := by
    have := sourceEdgeIndex_pos data profile.first.1
    positivity
  have hk₂ : ((data.sourceEdgeIndex profile.second.1 : ℚ)) ≠ 0 := by
    have := sourceEdgeIndex_pos data profile.second.1
    positivity
  have hk₁p : ((data.sourceEdgeIndex profile.first.1 : ℚ)) + 1 ≠ 0 := by positivity
  have hk₂p : ((data.sourceEdgeIndex profile.second.1 : ℚ)) + 1 ≠ 0 := by positivity
  have hsum : ((data.sourceEdgeIndex profile.first.1 : ℚ)) +
      ((data.sourceEdgeIndex profile.second.1 : ℚ)) ≠ 0 := by
    have h₁ := sourceEdgeIndex_pos data profile.first.1
    have h₂ := sourceEdgeIndex_pos data profile.second.1
    positivity
  rw [limit.commonMatrix_new 0, limit.commonMatrix_new 1, limit.commonMatrix_new 2,
    double_matrix_decomposition profile path, single_matrix_decomposition profile path,
    background_sum_eq profile input path profile.singleLabel profile.doubleLabel,
    third_index_cast profile shape]
  simp only [newColumn_zero, newColumn_one, newColumn_two, firstNewColumn,
    secondNewColumn, thirdNewColumn]
  field_simp
  ring

end LimitColumns

namespace LimitColumns

variable {profile} {shape : Shape profile} (limit : LimitColumns profile shape)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- A single honest member labelling supplies only the finite coordinate
order; every inter-member row correspondence comes from `LimitColumns.row`. -/
noncomputable def sourceCoordinates
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    StablePath data ≃ coordinate :=
  (limit.row 0).trans initial.row

noncomputable def targetCoordinates
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    coordinate ≃ Option target.edges :=
  initial.targetEdge.trans (columnEquiv profile shape 0).symm

/-- The induced honest square labelling of each of the three members. -/
noncomputable def labelling
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (position : Fin 3) :
    StableLengthMatrixLabelling (members profile shape position).datum coordinate where
  row := (limit.row position).symm.trans (limit.sourceCoordinates initial)
  targetEdge := (targetCoordinates initial).trans (columnEquiv profile shape position)

/-- The honest square length matrix of one member. -/
noncomputable def squareMatrix
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (position : Fin 3) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix (limit.labelling initial position).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    coordinate :=
  (targetCoordinates initial).symm none

theorem squareMatrix_common
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (position : Fin 3) (row column : coordinate) :
    limit.squareMatrix initial position row column =
      limit.commonMatrix position ((limit.sourceCoordinates initial).symm row)
        (targetCoordinates initial column) :=
  labelling_matrix_eq (limit.labelling initial position) row column

theorem squareMatrix_retained
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (position : Fin 3) (row : coordinate) (place : target.edges) :
    limit.squareMatrix initial position row ((targetCoordinates initial).symm (some place)) =
      matrix data ((limit.sourceCoordinates initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

theorem squareMatrix_new
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (position : Fin 3) (row : coordinate) :
    limit.squareMatrix initial position row (wallColumn initial) =
      limit.commonMatrix position ((limit.sourceCoordinates initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

/-- **The three members' matrices agree away from the regrown wall column.**
This is the retained-column receipt and nothing else: no nonsingularity and no
supplied cofactor correspondence enters. -/
theorem matrices_agree
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (first second : Fin 3) :
    AgreeOffColumn (limit.squareMatrix initial first) (limit.squareMatrix initial second)
      (wallColumn initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : targetCoordinates initial column with
  | none => exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

/-- **The common cofactors.**  The wall row of the adjugate is literally the
same for all three members. -/
theorem common_cofactors
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (position : Fin 3) (row : coordinate) :
    (limit.squareMatrix initial position).adjugate (wallColumn initial) row =
      (limit.squareMatrix initial 0).adjugate (wallColumn initial) row :=
  adjugate_wallRow_eq_of_agreeOffColumn (limit.matrices_agree initial position 0) row

/-- Each old column's cofactor-weighted contribution vanishes: it is an
off-diagonal entry of `adjugate A * A = det A • 1`. -/
theorem old_column_annihilation
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (place : target.edges) :
    columnContribution (limit.squareMatrix initial 0) (wallColumn initial)
      ((targetCoordinates initial).symm (some place)) = 0 := by
  apply columnContribution_eq_zero
  intro h
  have hLabels := (targetCoordinates initial).symm.injective h
  cases hLabels

/-- **Equation (9)**, for the three actual Figure 35 members in their induced
common labellings.  No member is assumed nonsingular, and the weights are the
members' own new-edge indices. -/
theorem determinant_balance (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) *
          (limit.squareMatrix initial 0).det +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) *
          (limit.squareMatrix initial 1).det +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          (limit.squareMatrix initial 2).det = 0 := by
  classical
  set A := limit.squareMatrix initial with hA
  set k := wallColumn initial with hk
  set doubleColumn := (targetCoordinates initial).symm
    (some (star.edge profile.doubleLabel)) with hDouble
  set singleColumn := (targetCoordinates initial).symm
    (some (star.edge profile.singleLabel)) with hSingle
  have hDet (position : Fin 3) : (A position).det =
      ∑ row, A position row k * (A 0).adjugate k row :=
    det_eq_sum_wallColumn_mul_commonCofactor (limit.matrices_agree initial position 0)
  have hColumn (row : coordinate) :
      ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) * A 0 row k +
          ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) * A 1 row k +
          ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) * A 2 row k =
        (data.sourceEdgeIndex profile.third.1 : ℚ) * A 0 row doubleColumn +
          (data.sourceEdgeIndex profile.third.1 : ℚ) * A 0 row singleColumn := by
    rw [hA, hk, hDouble, hSingle, squareMatrix_new, squareMatrix_new, squareMatrix_new,
      squareMatrix_retained, squareMatrix_retained]
    exact limit.weighted_column_balance input _
  calc
    ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) * (A 0).det +
          ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) * (A 1).det +
          ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) * (A 2).det =
        ∑ row, (((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) * A 0 row k +
            ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) * A 1 row k +
            ((data.sourceEdgeIndex profile.first.1 : ℚ) +
              (data.sourceEdgeIndex profile.second.1 : ℚ)) * A 2 row k) *
          (A 0).adjugate k row := by
      rw [hDet 0, hDet 1, hDet 2]
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (data.sourceEdgeIndex profile.third.1 : ℚ) *
          columnContribution (A 0) k doubleColumn +
        (data.sourceEdgeIndex profile.third.1 : ℚ) *
          columnContribution (A 0) k singleColumn := by
      simp_rw [hColumn]
      simp only [columnContribution, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 0 := by
      rw [hA, hk, hDouble, hSingle, limit.old_column_annihilation initial,
        limit.old_column_annihilation initial]
      ring

theorem positiveBalance (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    BalancingValencyTwo.PositiveBalance
      ![(data.sourceEdgeIndex profile.first.1 : ℚ) + 1,
        (data.sourceEdgeIndex profile.second.1 : ℚ) + 1,
        (data.sourceEdgeIndex profile.first.1 : ℚ) +
          (data.sourceEdgeIndex profile.second.1 : ℚ)]
      (fun position ↦ (limit.squareMatrix initial position).det) := by
  have hk₁ : (0 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) := by
    exact_mod_cast sourceEdgeIndex_pos data profile.first.1
  have hk₂ : (0 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    exact_mod_cast sourceEdgeIndex_pos data profile.second.1
  constructor
  · intro position
    fin_cases position <;> simp <;> linarith
  · have h := limit.determinant_balance input initial
    simpa [Fin.sum_univ_succ, add_assoc] using h

end LimitColumns

namespace LimitColumns

variable {profile} {shape : Shape profile} (limit : LimitColumns profile shape)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ### The balanced family -/

/-- The three actual Figure 35 members with their honest stable-length
matrices and the proved Equation (9) balance.  Possibly singular members are
kept. -/
noncomputable def family (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    BalancedGlobal.Family (coordinate := coordinate) 3 data where
  candidate := fun position ↦ (members profile shape position).certified
  matrix := limit.squareMatrix initial
  wallColumn := wallColumn initial
  weight := ![(data.sourceEdgeIndex profile.first.1 : ℚ) + 1,
    (data.sourceEdgeIndex profile.second.1 : ℚ) + 1,
    (data.sourceEdgeIndex profile.first.1 : ℚ) +
      (data.sourceEdgeIndex profile.second.1 : ℚ)]
  positiveBalance := limit.positiveBalance input initial
  agreeOffWall := limit.matrices_agree initial

theorem family_matrix_is_honest (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (position : Fin 3) :
    (limit.family input initial).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (limit.labelling initial position).presentation := rfl

/-- The same family before forgetting the actual candidates and their honest
presentations: the form a semantic positive exit consumes. -/
noncomputable def honestPresentedFamily (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    BalancedGlobal.PresentedFamily (coordinate := coordinate) 3 data wall where
  candidate := members profile shape
  presentation := fun position ↦ (limit.labelling initial position).presentation
  wallColumn := wallColumn initial
  weight := ![(data.sourceEdgeIndex profile.first.1 : ℚ) + 1,
    (data.sourceEdgeIndex profile.second.1 : ℚ) + 1,
    (data.sourceEdgeIndex profile.first.1 : ℚ) +
      (data.sourceEdgeIndex profile.second.1 : ℚ)]
  positiveBalance := limit.positiveBalance input initial
  agreeOffWall := limit.matrices_agree initial

theorem honestPresentedFamily_toFamily (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate) :
    (limit.honestPresentedFamily input initial).toFamily = limit.family input initial := rfl

theorem honestPresentedFamily_candidate (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (position : Fin 3) :
    (limit.honestPresentedFamily input initial).candidate position =
      members profile shape position := rfl

/-- Any nonsingular chosen member has an actual valid opposite-sign member;
no nonsingularity is imposed on the other two. -/
theorem exists_valid_opposite (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (incoming : Fin 3)
    (hIncoming : (limit.squareMatrix initial incoming).det ≠ 0) :
    ∃ outgoing, (members profile shape outgoing).datum.Valid ∧
      (limit.squareMatrix initial incoming).det *
        (limit.squareMatrix initial outgoing).det < 0 := by
  obtain ⟨outgoing, hSign⟩ :=
    BalancingValencyTwo.exists_opposite_of_positiveBalance
      (limit.positiveBalance input initial) hIncoming
  exact ⟨outgoing, (members profile shape outgoing).datum_valid input.valid, hSign⟩

/-- **The identified-member positive exit.**  For an identified incoming
member of the actual Figure 35 triple whose honest square matrix is
nonsingular, Equation (9) selects a valid opposite-sign member and the
one-column cone-wall calculation supplies the positive rational step together
with its cleared rank-one pencil.  Only the chosen incoming member is assumed
nonsingular. -/
theorem exists_valid_positive_exit_with_pencil (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (members profile shape 0).datum coordinate)
    (hTargetConnected : graph_connected target) (hTargetGenus : genus target = 0)
    (root : target.V) (incoming : Fin 3)
    (hIncoming : (limit.squareMatrix initial incoming).det ≠ 0)
    (z incomingVelocity : coordinate → ℚ)
    (outgoingVelocity : Fin 3 → coordinate → ℚ)
    (hz : z (wallColumn initial) = 0)
    (hzpos : ∀ i, i ≠ wallColumn initial → 0 < z i)
    (hSystems : ∀ outgoing, (limit.squareMatrix initial outgoing).det ≠ 0 →
      (limit.squareMatrix initial incoming).mulVec incomingVelocity =
        (limit.squareMatrix initial outgoing).mulVec (outgoingVelocity outgoing))
    (hIncomingDirection : incomingVelocity (wallColumn initial) < 0) :
    ∃ outgoing,
      (members profile shape outgoing).datum.Valid ∧
      (limit.squareMatrix initial incoming).det *
        (limit.squareMatrix initial outgoing).det < 0 ∧
      ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
        (∀ i, 0 < (z + t • outgoingVelocity outgoing) i) ∧
        (limit.squareMatrix initial outgoing).mulVec (z + t • outgoingVelocity outgoing) =
          (limit.squareMatrix initial incoming).mulVec z +
            t • (limit.squareMatrix initial incoming).mulVec incomingVelocity ∧
        Nonempty (BalancedGlobal.Candidate.ClearedPencil
          (members profile shape outgoing)
          (limit.labelling initial outgoing).presentation
          (z + t • outgoingVelocity outgoing)) :=
  (limit.honestPresentedFamily input initial).exists_valid_positive_exit_with_pencil
    input.valid hTargetConnected hTargetGenus root incoming hIncoming z incomingVelocity
    outgoingVelocity hz hzpos hSystems hIncomingDirection

end LimitColumns

/-! ### Canonical square coordinates -/

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

namespace LimitColumns

variable {profile} {shape : Shape profile} (limit : LimitColumns profile shape)

/-- The W2 source census supplies a canonical square coordinate order; it
asserts no extra geometric row matching. -/
noncomputable def canonicalRowOrder (input : W2SourceInput data star) :
    StablePath data ≃ Option target.edges :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_option, Multiset.card_coe]
    exact input.stablePath_card)

noncomputable def canonicalInitialLabelling (input : W2SourceInput data star) :
    StableLengthMatrixLabelling (members profile shape 0).datum (Option target.edges) where
  row := (limit.row 0).symm.trans (canonicalRowOrder input)
  targetEdge := columnEquiv profile shape 0

noncomputable def canonicalMatrix (input : W2SourceInput data star) (position : Fin 3) :
    Matrix (Option target.edges) (Option target.edges) ℚ :=
  limit.squareMatrix (limit.canonicalInitialLabelling input) position

/-- **Equation (9) with no supplied square labelling.** -/
theorem canonical_determinant_balance (input : W2SourceInput data star) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) + 1) * (limit.canonicalMatrix input 0).det +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) + 1) *
          (limit.canonicalMatrix input 1).det +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          (limit.canonicalMatrix input 2).det = 0 :=
  limit.determinant_balance input (limit.canonicalInitialLabelling input)

noncomputable def canonicalFamily (input : W2SourceInput data star) :
    BalancedGlobal.Family (coordinate := Option target.edges) 3 data :=
  limit.family input (limit.canonicalInitialLabelling input)

theorem canonicalFamily_matrix_is_honest (input : W2SourceInput data star)
    (position : Fin 3) :
    (limit.canonicalFamily input).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (limit.labelling (limit.canonicalInitialLabelling input) position).presentation := rfl

/-- The canonical family in presented form, retaining the three actual
Figure 35 members. -/
noncomputable def canonicalPresentedFamily (input : W2SourceInput data star) :
    BalancedGlobal.PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  limit.honestPresentedFamily input (limit.canonicalInitialLabelling input)

theorem canonicalPresentedFamily_candidate (input : W2SourceInput data star)
    (position : Fin 3) :
    (limit.canonicalPresentedFamily input).candidate position =
      members profile shape position := rfl

end LimitColumns

end DraismaVargas.LocalCases.W2PCommonBalance
