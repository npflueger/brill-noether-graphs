import DraismaVargas.LocalCases.W2MkkSourceCandidates
import DraismaVargas.LocalCases.M11JoinedDescentGeometry
import Utilities.IntegralGeometry.WallColumnDeterminant

/-!
# Figure 34's common balance: Equation (8)

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-kk}`, Figure 34 and
**Equation (8)**.  The ambient hypotheses are `{w2-r2}` (where the Base I/II
vocabulary is fixed once for the whole `{w2}` section) and `{w2-r2-nd3}` (where
Cardinality M and P are separated, and Base II.1.M / II.2.1.M / II.2.2.M are
defined); the local case they invoke is (r1-nd2).  The case hypothesis is
`k₁ ≥ 2`, `k₂ ≥ 2`; the neighbours are `W2M1kSourceCandidates` (`k₁ = 1`) and
the `M11*` files (`k₁ = k₂ = 1`).

`W2MkkSourceCandidates` builds Figure 34's members over one datum and one
`Shape`, on `ResolutionMkk.bothDetachedResolution`, with validity, source genus
preservation, divalence at both new endpoints, the displayed new-edge indices
and the induced block counts on `A₀`.  This module is the M-kk analogue of
`W2PCommonBalance`.

## Equation (8), checked against Figure 34

Equation (8) was checked here against Figure 34's own indices before any
coefficient was transcribed, and it holds as displayed in Part I:

    (k₁-1) c⁽¹⁾ + (k₂-1) c⁽²⁾ + (k₁+k₂) c⁽³⁾
      = ((k₁+k₂-1)/k₁ · c(e₁) + (k₁+k₂-1)/k₂ · c(e₂) + (k₁+k₂-1) s)
        + (c(e₃) + (k₁+k₂-1) s)
      = 0 + 0 = 0,

and expanding Figure 34's boxes `c⁽¹⁾ = c(e₁)/(k₁-1) + c(e₂)/k₂ + s`,
`c⁽²⁾ = c(e₁)/k₁ + c(e₂)/(k₂-1) + s`, `c⁽³⁾ = c(e₃)/(k₁+k₂) + s` gives

    (k₁+k₂-1)(c(e₁)/k₁ + c(e₂)/k₂) + c(e₃) + 2(k₁+k₂-1) s

on both sides.  **Both** brackets carry the factor `k₁+k₂-1`, symmetrically.
(Part I's display of Equation (7), by contrast, shows its factor `2` on the
first bracket only; see `W2M1kLeafLimitMatrix`.)  The `M₀` box of Figure 34 supplies
`c(e₁)/k₁ + c(e₂)/k₂ + s = 0` and `c(e₃)/(k₁+k₂-1) + s = 0`, which kills the two
brackets.  `figure34_column_identity` is the first equality alone, as an
identity of rational functions; `equation_eight` is the whole display at an
actual M-kk profile, with the profile's **own** third index `k₃` in place of the
figure's `k₁ + k₂ - 1`.  The two are identified by `Shape.third_index`
(`k₃ + 1 = k₁ + k₂`, Part I's `|A⁽ᵠ⁾| = |A₀| - 1`), which is this case's only free
identity and the exact analogue of `W2PCommonBalance.third_index_cast`.

At column level (`LimitColumns.weighted_column_balance`) the same statement
reads: the three regrown columns, weighted by `k₁-1`, `k₂-1`, `k₁+k₂`, add up to
`k₃` times the old `t₂` column plus `k₃` times the old `t₃` column.  Both old
columns are decomposed here, on the real incoming datum:
`double_matrix_decomposition` (inside `A₀` the `t₂` column displays exactly `e₁`
and `e₂`) and `single_matrix_decomposition` (inside `A₀` the `t₃` column
displays exactly `e₃`; Cardinality M's dangling `e₄` lies above `t₃` but
contributes nothing, being in no stable row at all).  Their two background sums
are **equal**, which is Figure 34's `σ₀(J₀,2) = σ₀(J₀,3) = s`:
`background_sum_eq`, proved from the fact that a wall block outside `A₀` is
unramified, so its source vertex is divalent and its two occurrences are
dangling together, share a stable row and have the block's own size as common
index.

## The weights are derived, not posited

Unlike the nd3 `M-11` pair, this case does not balance with unit weights: the
weight vector is `![k₁-1, k₂-1, k₁+k₂]`, and it is positive only because the
case hypothesis is `k₁, k₂ ≥ 2` (`Shape.one_lt_first`, `Shape.one_lt_second`).

The three weights are the three members' **own** new-edge block cardinalities.
For a detaching member this is uniform and needs no case split:
`detach_weight_eq` says the new edge's surviving block at the partner sheet has
one sheet fewer than the pinned sheet's own `t₂` endpoint block, read off
`W2MkkSourceCandidates.detach_indices_first` / `detach_indices_second`; which of
`k₁`, `k₂` that block size is, is `detach_weight_dichotomy`, and the two named
members give `firstMember_weight` (`|e'| = k₁ - 1`) and `secondMember_weight`
(`|e''| = k₂ - 1`).  For `M⁽³⁾` it is `thirdMember_weight` (`|e'| = k₁ + k₂`),
off `joined_newEdge_blockCard`.

They are also forced: `figure34_weights_forced` shows that the four coefficient
equations of the column identity (the coefficients of `c(e₁)`, `c(e₂)`, `c(e₃)`
and of the background, listed in `figure34_coefficients`) have a
one-dimensional solution space, and `figure34_weights_normalized` pins it once
the first weight is fixed at `k₁ - 1`.  So `![k₁-1, k₂-1, k₁+k₂]` is the only
weight vector, up to one overall scale, for which the three regrown columns
combine into old columns at all.  `BalancingValencyTwo.balance_M_kk` is the
right tool and is used (`positiveBalance_of_relations`); its `hright` is stated
with `k₁ + k₂ - 1` and `third_index_cast` converts.

## Why the receipt carries datums and not `BalancedGlobal.Candidate`s

`W2PCommonBalance.LimitColumns` could quantify over
`members profile shape : Fin 3 → BalancedGlobal.Candidate target degree data wall`
because `W2PSourceCandidates.members_share_datum` puts all three Figure 35
members over one datum.  **M-kk is the opposite case.**
`W2MkkSourceCandidates.no_common_geometry` says no single `w2Mkk` gluing datum
carries both detaching members (Part I compares gluing data up to isomorphism,
so this is a matter of choosing representatives, not an obstruction): the `t₃`
exterior refinement pins the detached sheet to `e₄`'s sheet, and that sheet lies
in exactly one of `e₁`, `e₂`.  The second member therefore lives over the
branch-swapped datum, exactly as `GlobalMkk.swappedCandidates` and
`GlobalMkk.swappedBalancedFamily` arrange it.

`LimitColumns` below is shaped for that.  A member is a `LimitMember`, which
records `right`/`datum`/`valid_of_old` -- the three fields of a
`BalancedGlobal.CertifiedCandidate data`, refined by the expanded target the
member actually lives over -- together with its row bijection and its retained
columns, rather than a `Candidate target degree data wall`, which the remote
member is not.  A member over the incoming datum supplies `valid_of_old` from
`BalancedGlobal.Candidate.datum_valid`; the remote one from
`GlobalMkk.DivalentPattern.remoteCertified`.  Because `LimitMember` carries no
position index, the three of them are supplied as a plain `![m₀, m₁, m₂]` and a
consumer needs no dependent matching.

Consequently this module builds a `BalancedGlobal.Family` and
`exists_valid_opposite`, and **not** a `PresentedFamily` or a cleared pencil:
that is the same boundary `GlobalMkk.exists_valid_positive_exit_swapped` stops
at, and for the same reason.

## PART A and PART B: what is unconditional and what is not

**Everything up to and including `positiveBalance_of_relations` is
unconditional**, with exactly `W2MkkSourceCandidates`' hypothesis bundle (a
`W2R2SourceProfile.SourceProfile`, a `Shape`, and -- where the background is
involved -- the `SecondEquation.W2SourceInput` that `W2MkkSourceCandidates`'
callers already carry).  No new hypothesis is introduced anywhere in Part A.

**Part B is conditional on `LimitColumns`, and no inhabitant of `LimitColumns`
is built here.**  Its three analytic fields are exactly what a limit-matrix
module must supply -- the geometric stable-row bijection of each member, the
literal equality of every retained column with the incoming wall column read
through it, and the evaluation of the regrown column as Figure 34's box gives
it -- and are the M-kk analogues of `W2PRowDescent.stablePathEquiv`,
`W2PLimitMatrix.matrix_retained` and `W2PLimitMatrix.firstMember_regrown` and
siblings.  For M-kk the survival, endpoint and background census is
`W2MkkStableGraph`; the stable lift, the row descent and the limit matrices are
`W2MkkStableLift`, `W2MkkRowDescent` and `W2MkkLimitMatrix`, and
`W2MkkLimitColumns.limitColumns` builds the inhabitant from them.  Nothing
in `LimitColumns` is a numerical or genericity assumption: every field is a
statement a successor module must *prove* about members
`W2MkkSourceCandidates` already built.  In particular a supplier must prove
that a detaching member's surviving new occurrences lie in `e₁`'s and `e₂`'s
rows while its new occurrence through the pinned sheet dies with `e₄`
(`W2MkkStableGraph.detach_new_pin_dangling`), and that `M⁽³⁾`'s surviving new
occurrence lies in `e₃`'s row
(`W2MkkStableGraph.joined_new_stablePath_eq_third`).

## What Part B proves

* `LimitColumns.commonMatrix`, `commonMatrix_retained` -- the three members'
  honest natural matrices in one coordinate system.
* `weighted_column_balance` -- **Equation (8) at column level on the real
  matrices**.
* `matrices_agree`, `common_cofactors` -- from the retained columns alone; no
  nonsingularity and no supplied cofactor correspondence.
* `old_column_annihilation`, `determinant_balance` -- Equation (8) for the
  three actual members' honest square matrices, with the derived weights.  No
  member is assumed nonsingular.
* `positiveBalance`, `certified`, `family` -- a `BalancedGlobal.Family` on the
  one incoming datum whose matrices are the honest
  `GluingDatum.LengthMatrixPresentation.matrix` of a
  `StableLengthMatrixLabelling` on the real data.
* `exists_valid_opposite` -- the identified-member exit, assuming only that the
  chosen incoming member is nonsingular.
* `canonicalRowOrder`, `canonicalMatrix`, `canonical_determinant_balance`,
  `canonicalFamily` -- the same with the coordinate order forced by
  `W2SourceInput.stablePath_card`.

## What is deliberately not here

The limit-matrix supplier; the transported `Shape` over the branch-swapped
datum (`W2MkkTransport`); identifying an *arbitrary* incoming M-kk datum with a
named Figure 34 member (`W2MkkIncomingMatching`); and `GlobalMkk` itself.
-/

namespace DraismaVargas.LocalCases.W2MkkCommonBalance

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open W2MkkSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The one free identity -/

/-- **`k₃ = k₁ + k₂ - 1` in `ℚ`.**  This is Cardinality M: the `t₃` endpoint
block `A⁽ᵠ⁾` is `A₀` minus the sheet carrying the dangling `e₄`. -/
theorem third_index_cast (shape : Shape profile) :
    (data.sourceEdgeIndex profile.third.1 : ℚ) =
      (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ) - 1 := by
  have h : (data.sourceEdgeIndex profile.third.1 : ℚ) + 1 =
      (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℚ)) shape.third_index
  linarith

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
distinguished block `A₀`: Figure 34's background, whose cofactor-weighted sum
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

/-- Figure 34's `s`, read on one old wall column and one old stable row. -/
noncomputable def backgroundColumn (star : TwoStar target wall)
    (block : WallBlock data wall) (path : StablePath data) (label : Fin 2) : ℚ :=
  ∑ edge ∈ backgroundOccurrences star block path label,
    (1 : ℚ) / data.sourceEdgeIndex edge

/-- **The old `t₂` column.**  Inside `A₀` it displays exactly `e₁` and `e₂`:
the third survivor `e₃` lies above `t₃`, and so does Cardinality M's dangling
`e₄`. -/
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

/-- **The old `t₃` column.**  Inside `A₀` it displays only `e₃`: Cardinality M
puts the dangling `e₄` above `t₃` too, but a dangling occurrence is in no
stable row at all and contributes nothing. -/
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

/-! ## Figure 34's `s`: the two old backgrounds agree -/

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
/-- **Figure 34's `s = σ₀(J₀,2) = σ₀(J₀,3)`.**  The two old wall columns have
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

/-! ## Equation (8) -/

/-- **Equation (8)'s first equality**, as an identity of rational
functions of `k₁`, `k₂` and of four free column entries.  The three Figure 34
determinants weighted by `k₁-1`, `k₂-1`, `k₁+k₂` are the two vanishing `M₀`
brackets, each taken `k₁+k₂-1` times.  Both brackets carry the same factor. -/
theorem figure34_column_identity {k₁ k₂ c₁ c₂ c₃ b : ℚ} (hk₁ : 1 < k₁) (hk₂ : 1 < k₂) :
    (k₁ - 1) * (c₁ / (k₁ - 1) + c₂ / k₂ + b) +
        (k₂ - 1) * (c₁ / k₁ + c₂ / (k₂ - 1) + b) +
        (k₁ + k₂) * (c₃ / (k₁ + k₂) + b) =
      (k₁ + k₂ - 1) * (c₁ / k₁ + c₂ / k₂ + b) +
        (k₁ + k₂ - 1) * (c₃ / (k₁ + k₂ - 1) + b) := by
  have h₁ : k₁ ≠ 0 := ne_of_gt (by linarith)
  have h₂ : k₂ ≠ 0 := ne_of_gt (by linarith)
  have h₃ : k₁ - 1 ≠ 0 := ne_of_gt (by linarith)
  have h₄ : k₂ - 1 ≠ 0 := ne_of_gt (by linarith)
  have h₅ : k₁ + k₂ ≠ 0 := ne_of_gt (by linarith)
  have h₆ : k₁ + k₂ - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **The four coefficient equations of the column identity.**  Reading
`figure34_column_identity` off the coefficients of `c₁`, `c₂`, `c₃` and of the
background `b`, with a general weight vector `(w₁, w₂, w₃)` and general old
column multipliers `(α, β)`, gives exactly these four, cleared of
denominators.  The Figure 34 weights satisfy them. -/
theorem figure34_coefficients (k₁ k₂ : ℚ) :
    (k₁ - 1) * k₁ + (k₂ - 1) * (k₁ - 1) = (k₁ + k₂ - 1) * (k₁ - 1) ∧
      (k₁ - 1) * (k₂ - 1) + (k₂ - 1) * k₂ = (k₁ + k₂ - 1) * (k₂ - 1) ∧
        (k₁ + k₂) * (k₁ + k₂ - 1) = (k₁ + k₂ - 1) * (k₁ + k₂) ∧
          (k₁ - 1) + (k₂ - 1) + (k₁ + k₂) = (k₁ + k₂ - 1) + (k₁ + k₂ - 1) :=
  ⟨by ring, by ring, by ring, by ring⟩

/-- **The Equation (8) weights are forced, up to one overall scale.**  Given
the four coefficient equations of `figure34_coefficients` for unknown weights
`w₁, w₂, w₃` and unknown old-column multipliers `α, β`, every solution is the
Figure 34 one scaled by `w₁ / (k₁ - 1)`.  Nothing is posited: the weight vector
`![k₁-1, k₂-1, k₁+k₂]` is the only one, up to scale, for which the three new
columns combine into old columns at all. -/
theorem figure34_weights_forced {k₁ k₂ w₁ w₂ w₃ α β : ℚ}
    (hFirst : w₁ * k₁ + w₂ * (k₁ - 1) = α * (k₁ - 1))
    (hSecond : w₁ * (k₂ - 1) + w₂ * k₂ = α * (k₂ - 1))
    (hThird : w₃ * (k₁ + k₂ - 1) = β * (k₁ + k₂))
    (hFourth : w₁ + w₂ + w₃ = α + β) :
    w₂ * (k₁ - 1) = w₁ * (k₂ - 1) ∧
      α * (k₁ - 1) = w₁ * (k₁ + k₂ - 1) ∧
        w₃ * (k₁ - 1) = w₁ * (k₁ + k₂) ∧
          β * (k₁ - 1) = w₁ * (k₁ + k₂ - 1) := by
  have key₁ : w₂ * (k₁ - 1) = w₁ * (k₂ - 1) := by
    linear_combination (k₁ - 1) * hSecond - (k₂ - 1) * hFirst
  have key₂ : α * (k₁ - 1) = w₁ * (k₁ + k₂ - 1) := by
    linear_combination key₁ - hFirst
  have key₃ : w₃ * (k₁ - 1) = w₁ * (k₁ + k₂) := by
    linear_combination (-(k₁ - 1)) * hThird + (k₁ + k₂) * (k₁ - 1) * hFourth -
      (k₁ + k₂) * key₁ + (k₁ + k₂) * key₂
  refine ⟨key₁, key₂, key₃, ?_⟩
  linear_combination (-(k₁ - 1)) * hFourth + key₁ - key₂ + key₃

/-- The normalized form of `figure34_weights_forced`: fixing the first weight
at Figure 34's `k₁ - 1` pins the other two and both old-column multipliers.
This is where the case hypothesis `k₁ ≥ 2` is used: at `k₁ = 1` the first
weight degenerates to `0` and nothing is pinned. -/
theorem figure34_weights_normalized {k₁ k₂ w₂ w₃ α β : ℚ} (hk₁ : 1 < k₁)
    (hFirst : (k₁ - 1) * k₁ + w₂ * (k₁ - 1) = α * (k₁ - 1))
    (hSecond : (k₁ - 1) * (k₂ - 1) + w₂ * k₂ = α * (k₂ - 1))
    (hThird : w₃ * (k₁ + k₂ - 1) = β * (k₁ + k₂))
    (hFourth : (k₁ - 1) + w₂ + w₃ = α + β) :
    w₂ = k₂ - 1 ∧ α = k₁ + k₂ - 1 ∧ w₃ = k₁ + k₂ ∧ β = k₁ + k₂ - 1 := by
  have hne : k₁ - 1 ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨key₁, key₂, key₃, key₄⟩ :=
    figure34_weights_forced hFirst hSecond hThird hFourth
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_right_cancel₀ hne (key₁.trans (by ring))
  · exact mul_right_cancel₀ hne (key₂.trans (by ring))
  · exact mul_right_cancel₀ hne (key₃.trans (by ring))
  · exact mul_right_cancel₀ hne (key₄.trans (by ring))

/-! ### The weights are the members' own new-edge block cardinalities -/

/-- **A detaching member's weight is its own new-edge block cardinality**, and
it is one less than the size of the `t₂` endpoint block holding the pinned
sheet.  This is uniform in `detach` and needs no case split: the statement is
`W2MkkSourceCandidates.detach_indices_first`'s and `detach_indices_second`'s
common content. -/
theorem detach_weight_eq (shape : Shape profile) (detach : DetachData profile) :
    detach.selected.newEdge.blockCard detach.remainder + 1 =
      (endpointPartition profile).blockCard (pinSheet profile) := by
  have hCard : ((endpointPartition profile).detachSheet (pinSheet profile) detach.remainder
      detach.ne_remainder detach.together).blockCard detach.remainder =
      (endpointPartition profile).blockCard (pinSheet profile) - 1 :=
    (endpointPartition profile).detachSheet_blockCard_remainder (pinSheet profile)
      detach.remainder detach.ne_remainder detach.together
  have hOne := one_lt_pinSheet_endpoint_blockCard shape
  have hRewrite : detach.selected.newEdge.blockCard detach.remainder =
      (endpointPartition profile).blockCard (pinSheet profile) - 1 := hCard
  omega

/-- **Which of `k₁`, `k₂` the detaching member's weight is, is decided by the
datum.**  The pinned sheet lies in exactly one of the two `t₂` endpoint blocks
(`W2MkkSourceCandidates.pinSheet_mem`), and that block's size is the one the
weight is read from.  Over one datum the two disjuncts are exclusive --
`not_first_and_second` -- which is `W2MkkSourceCandidates.no_common_geometry`
in weight form. -/
theorem detach_weight_dichotomy (shape : Shape profile) (detach : DetachData profile) :
    ((endpointPartition profile).Rel (firstSheet profile) (pinSheet profile) ∧
        detach.selected.newEdge.blockCard detach.remainder + 1 =
          data.sourceEdgeIndex profile.first.1) ∨
      ((endpointPartition profile).Rel (secondSheet profile) (pinSheet profile) ∧
        detach.selected.newEdge.blockCard detach.remainder + 1 =
          data.sourceEdgeIndex profile.second.1) := by
  rcases pinSheet_mem shape with hFirst | hSecond
  · exact Or.inl ⟨hFirst, (detach_indices_first shape detach hFirst).2.1⟩
  · exact Or.inr ⟨hSecond, (detach_indices_second shape detach hSecond).2.1⟩

/-- **Figure 34's first weight is `M⁽¹⁾`'s own `|e'| = k₁ - 1`** (Base
II.2.1.M). -/
theorem firstMember_weight (shape : Shape profile) (member : FirstMember profile) :
    (member.toDetachData.selected.newEdge.blockCard member.toDetachData.remainder : ℚ) =
      (data.sourceEdgeIndex profile.first.1 : ℚ) - 1 := by
  have h := (detach_indices_first shape member.toDetachData member.pin_first).2.1
  have hq : (member.toDetachData.selected.newEdge.blockCard
      member.toDetachData.remainder : ℚ) + 1 =
      (data.sourceEdgeIndex profile.first.1 : ℚ) := by exact_mod_cast h
  linarith

/-- **Figure 34's second weight is `M⁽²⁾`'s own `|e''| = k₂ - 1`** (Base
II.2.2.M). -/
theorem secondMember_weight (shape : Shape profile) (member : SecondMember profile) :
    (member.toDetachData.selected.newEdge.blockCard member.toDetachData.remainder : ℚ) =
      (data.sourceEdgeIndex profile.second.1 : ℚ) - 1 := by
  have h := (detach_indices_second shape member.toDetachData member.pin_second).2.1
  have hq : (member.toDetachData.selected.newEdge.blockCard
      member.toDetachData.remainder : ℚ) + 1 =
      (data.sourceEdgeIndex profile.second.1 : ℚ) := by exact_mod_cast h
  linarith

/-- **Figure 34's third weight is `M⁽³⁾`'s own `|e'| = k₁ + k₂`** (Base
II.1.M). -/
theorem thirdMember_weight (shape : Shape profile) (distinguished anchor sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    ((((joinedCandidate profile distinguished).resolution anchor).newEdge.blockCard
        sheet : ℕ) : ℚ) =
      (data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ) := by
  have h := joined_newEdge_blockCard shape distinguished anchor sheet hSheet
  exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℚ)) h

/-! ### Equation (8) itself -/

/-- **Equation (8)** at an actual M-kk source profile.  The two
hypotheses are Figure 34's `M₀` box, stated with the profile's own
third index `k₃` rather than with the figure's `k₁ + k₂ - 1`;
`Shape.third_index` is what identifies them, and it is the case's only free
identity.  The middle expression of Equation (8) is the right-hand side. -/
theorem equation_eight (shape : Shape profile) {c₁ c₂ c₃ s : ℚ}
    (hLeft : c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
      c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s = 0)
    (hRight : c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s = 0) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) *
          (c₁ / ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) +
            c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s) +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) *
          (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
            c₂ / ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) + s) +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          (c₃ / ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) + s) =
      ((data.sourceEdgeIndex profile.third.1 : ℚ)) *
          (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
            c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s) +
        ((data.sourceEdgeIndex profile.third.1 : ℚ)) *
          (c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s) ∧
      ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) *
          (c₁ / ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) +
            c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s) +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) *
          (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
            c₂ / ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) + s) +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          (c₃ / ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) + s) = 0 := by
  have hk₁ : (1 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) := by
    exact_mod_cast shape.one_lt_first
  have hk₂ : (1 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    exact_mod_cast shape.one_lt_second
  have hCast := third_index_cast profile shape
  have hIdentity := figure34_column_identity (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (b := s) hk₁ hk₂
  rw [← hCast] at hIdentity
  refine ⟨hIdentity, ?_⟩
  rw [hIdentity, hLeft, hRight]
  ring

/-- **Equation (8) as a positive balance**, in the exact shape
`BalancingValencyTwo.balance_M_kk` states it, with the weights derived rather
than supplied.  Positivity of the first two weights is `k₁, k₂ ≥ 2`. -/
theorem positiveBalance_of_relations (shape : Shape profile) {c₁ c₂ c₃ s : ℚ}
    (hLeft : c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
      c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s = 0)
    (hRight : c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s = 0) :
    BalancingValencyTwo.PositiveBalanceThree
      ![(data.sourceEdgeIndex profile.first.1 : ℚ) - 1,
        (data.sourceEdgeIndex profile.second.1 : ℚ) - 1,
        (data.sourceEdgeIndex profile.first.1 : ℚ) +
          (data.sourceEdgeIndex profile.second.1 : ℚ)]
      ![c₁ / ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) +
          c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s,
        c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
          c₂ / ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) + s,
        c₃ / ((data.sourceEdgeIndex profile.first.1 : ℚ) +
          (data.sourceEdgeIndex profile.second.1 : ℚ)) + s] := by
  have hk₁ : (1 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) := by
    exact_mod_cast shape.one_lt_first
  have hk₂ : (1 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    exact_mod_cast shape.one_lt_second
  refine BalancingValencyTwo.balance_M_kk hk₁ hk₂ hLeft ?_
  rw [← third_index_cast profile shape]
  exact hRight

/-! ## PART B — the matrix-level chain, over a supplied limit-matrix receipt -/

/-- `M⁽¹⁾`'s regrown column: `c⁽¹⁾ = c(e₁)/(k₁-1) + c(e₂)/k₂ + s`. -/
noncomputable def firstNewColumn (path : StablePath data) : ℚ :=
  (if path = firstRow profile then (1 : ℚ) else 0) /
      ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) +
    (if path = secondRow profile then (1 : ℚ) else 0) /
      (data.sourceEdgeIndex profile.second.1 : ℚ) +
    backgroundColumn star block path profile.doubleLabel

/-- `M⁽²⁾`'s regrown column: `c⁽²⁾ = c(e₁)/k₁ + c(e₂)/(k₂-1) + s`. -/
noncomputable def secondNewColumn (path : StablePath data) : ℚ :=
  (if path = firstRow profile then (1 : ℚ) else 0) /
      (data.sourceEdgeIndex profile.first.1 : ℚ) +
    (if path = secondRow profile then (1 : ℚ) else 0) /
      ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) +
    backgroundColumn star block path profile.doubleLabel

/-- `M⁽³⁾`'s regrown column: `c⁽³⁾ = c(e₃)/(k₁+k₂) + s`. -/
noncomputable def thirdNewColumn (path : StablePath data) : ℚ :=
  (if path = thirdRow profile then (1 : ℚ) else 0) /
      ((data.sourceEdgeIndex profile.first.1 : ℚ) +
        (data.sourceEdgeIndex profile.second.1 : ℚ)) +
    backgroundColumn star block path profile.doubleLabel

/-- Figure 34's three regrown columns, indexed. -/
noncomputable def newColumn : Fin 3 → StablePath data → ℚ :=
  ![firstNewColumn profile, secondNewColumn profile, thirdNewColumn profile]

@[simp] theorem newColumn_zero : newColumn profile 0 = firstNewColumn profile := rfl
@[simp] theorem newColumn_one : newColumn profile 1 = secondNewColumn profile := rfl
@[simp] theorem newColumn_two : newColumn profile 2 = thirdNewColumn profile := rfl

/-- **One Figure 34 member's limit-matrix receipt.**

A member is recorded by its wall-side assignment `right` (which names the
expanded outgoing target `TargetExpansion.graph target wall right`), its honest
outgoing gluing datum, its global validity implication, its geometric
stable-row bijection, and the statement that every retained column of its
honest `StableSourceMatrix.matrix` is literally the incoming wall column.

This is deliberately **not** `BalancedGlobal.Candidate target degree data wall`:
`W2MkkSourceCandidates.no_common_geometry` forbids putting Figure 34's two
detaching members over one datum, so one of them lives over the branch-swapped
datum of `GlobalMkk.Geometry.swapped` and is a member *for* `data` only through
`GlobalMkk.DivalentPattern.remoteCertified`.  Both kinds inhabit this structure:

* over the incoming datum, `right := c.right`, `datum := c.datum`,
  `valid_of_old := c.datum_valid` for `c` a `BalancedGlobal.Candidate`, with
  `row` and `retained` from the row-descent and limit-matrix modules;
* remotely, the same with `valid_of_old` from `remoteCertified`, or, as the
  inhabitant `W2MkkLimitColumns.remoteMember` does, from
  `GluingDatum.SheetRelabeling.valid` composed with `Candidate.datum_valid`. -/
structure LimitMember (data : GluingDatum target degree) (wall : target.V) where
  /-- The member's wall-side assignment, naming its expanded outgoing target. -/
  right : target.edges → Bool
  /-- The member's honest outgoing gluing datum. -/
  datum : GluingDatum (TargetExpansion.graph target wall right) degree
  /-- The member is globally valid whenever the incoming datum is. -/
  valid_of_old : data.Valid → datum.Valid
  /-- The member's geometric stable-row bijection. -/
  row : StablePath data ≃ StablePath datum
  /-- Every retained column is literally the incoming wall column. -/
  retained : ∀ (path : StablePath data) (place : target.edges),
    matrix datum (row path)
        (occurrenceEquiv target wall right (some place)) =
      matrix data path place

namespace LimitMember

/-- The member's regrown wall column, read in an incoming stable row. -/
noncomputable def newColumnValue (member : LimitMember data wall)
    (path : StablePath data) : ℚ :=
  matrix member.datum (member.row path)
    (occurrenceEquiv target wall member.right none)

end LimitMember

/-- **The limit-matrix receipt this module consumes and does not build**
(`W2MkkLimitColumns.limitColumns` builds it).

Everything below this point is conditional on an inhabitant of this structure.
Its content is the M-kk analogue of what `W2PRowDescent.stablePathEquiv`,
`W2PLimitMatrix.matrix_retained` and `W2PLimitMatrix.firstMember_regrown` (and
siblings) supply for Figure 35, and of what `W3Nd3LimitMatrix` and the `M11*`
chain supply for their cases.

Position `0` is `M⁽¹⁾` (Base II.2.1.M), position `1` is `M⁽²⁾` (Base II.2.2.M)
and position `2` is `M⁽³⁾` (Base II.1.M).  The three members are supplied as a
plain `Fin 3`-indexed family of `LimitMember`s -- no dependent matching is
needed to build one, so a consumer writes `member := ![m₀, m₁, m₂]` -- and the
only position-dependent field left is `regrown`, which evaluates each member's
new column as Figure 34's box gives it.

Nothing here is an assumption of nonsingularity, genericity, or numerical
value: every field is a statement a supplier must *prove* about members
`W2MkkSourceCandidates` builds.  In particular a supplier must prove
that a detaching member's surviving new occurrences lie in `e₁`'s and `e₂`'s
rows while its new occurrence through the pinned sheet dies with `e₄`
(`W2MkkStableGraph.detach_new_pin_dangling`), and that `M⁽³⁾`'s surviving new
occurrence lies in `e₃`'s row
(`W2MkkStableGraph.joined_new_stablePath_eq_third`). -/
structure LimitColumns (shape : Shape profile) where
  /-- The three Figure 34 members, with their row bijections and retained
  columns. -/
  member : Fin 3 → LimitMember data wall
  /-- The regrown column is Figure 34's displayed one. -/
  regrown : ∀ (position : Fin 3) (path : StablePath data),
    (member position).newColumnValue path = newColumn profile position path

namespace LimitColumns

variable {profile} {shape : Shape profile}

/-- Retained target occurrences use the canonical expansion labelling; `none`
names the regrown wall occurrence. -/
noncomputable def columnEquiv (limit : LimitColumns profile shape) (position : Fin 3) :
    Option target.edges ≃
      (TargetExpansion.graph target wall (limit.member position).right).edges :=
  occurrenceEquiv target wall (limit.member position).right

/-- The three members' honest natural matrices in one common coordinate
system: incoming stable rows through `row`, `Option target.edges` columns. -/
noncomputable def commonMatrix (limit : LimitColumns profile shape) (position : Fin 3) :
    Matrix (StablePath data) (Option target.edges) ℚ :=
  fun path place ↦ matrix (limit.member position).datum
    ((limit.member position).row path) (limit.columnEquiv position place)

theorem commonMatrix_retained (limit : LimitColumns profile shape) (position : Fin 3)
    (path : StablePath data) (place : target.edges) :
    limit.commonMatrix position path (some place) = matrix data path place :=
  (limit.member position).retained path place

theorem commonMatrix_new (limit : LimitColumns profile shape) (position : Fin 3)
    (path : StablePath data) :
    limit.commonMatrix position path none = newColumn profile position path :=
  limit.regrown position path

/-- **Equation (8) at column level, on the real matrices.**  The three regrown
columns weighted by the members' own new-edge indices `k₁-1`, `k₂-1`, `k₁+k₂`
add up to `k₃` times each of the two old wall columns.  The two sides meet only
through `Shape.third_index` (`k₃ = k₁+k₂-1`) and `background_sum_eq`
(`σ₀(J₀,2) = σ₀(J₀,3)`); no hypothesis is introduced. -/
theorem weighted_column_balance (input : W2SourceInput data star)
    (limit : LimitColumns profile shape) (path : StablePath data) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) *
          limit.commonMatrix 0 path none +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) *
          limit.commonMatrix 1 path none +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          limit.commonMatrix 2 path none =
      (data.sourceEdgeIndex profile.third.1 : ℚ) *
          matrix data path (star.edge profile.doubleLabel) +
        (data.sourceEdgeIndex profile.third.1 : ℚ) *
          matrix data path (star.edge profile.singleLabel) := by
  have hk₁ : (1 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) := by
    exact_mod_cast shape.one_lt_first
  have hk₂ : (1 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    exact_mod_cast shape.one_lt_second
  have h₁ : ((data.sourceEdgeIndex profile.first.1 : ℚ)) ≠ 0 := ne_of_gt (by linarith)
  have h₂ : ((data.sourceEdgeIndex profile.second.1 : ℚ)) ≠ 0 := ne_of_gt (by linarith)
  have h₃ : ((data.sourceEdgeIndex profile.first.1 : ℚ)) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h₄ : ((data.sourceEdgeIndex profile.second.1 : ℚ)) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h₅ : ((data.sourceEdgeIndex profile.first.1 : ℚ)) +
      ((data.sourceEdgeIndex profile.second.1 : ℚ)) ≠ 0 := ne_of_gt (by linarith)
  have h₆ : ((data.sourceEdgeIndex profile.first.1 : ℚ)) +
      ((data.sourceEdgeIndex profile.second.1 : ℚ)) - 1 ≠ 0 := ne_of_gt (by linarith)
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
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    StablePath data ≃ coordinate :=
  ((limit.member 0).row).trans initial.row

noncomputable def targetCoordinates
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    coordinate ≃ Option target.edges :=
  initial.targetEdge.trans (limit.columnEquiv 0).symm

/-- The induced honest square labelling of each of the three members. -/
noncomputable def labelling
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) :
    StableLengthMatrixLabelling (limit.member position).datum coordinate where
  row := ((limit.member position).row).symm.trans (limit.sourceCoordinates initial)
  targetEdge := (limit.targetCoordinates initial).trans (limit.columnEquiv position)

/-- The honest square length matrix of one member. -/
noncomputable def squareMatrix
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) : Matrix coordinate coordinate ℚ :=
  GluingDatum.LengthMatrixPresentation.matrix (limit.labelling initial position).presentation

/-- The coordinate naming the regrown wall column. -/
noncomputable def wallColumn
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    coordinate :=
  (limit.targetCoordinates initial).symm none

theorem squareMatrix_common
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) (row column : coordinate) :
    limit.squareMatrix initial position row column =
      limit.commonMatrix position ((limit.sourceCoordinates initial).symm row)
        (limit.targetCoordinates initial column) :=
  labelling_matrix_eq (limit.labelling initial position) row column

theorem squareMatrix_retained
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) (row : coordinate) (place : target.edges) :
    limit.squareMatrix initial position row
        ((limit.targetCoordinates initial).symm (some place)) =
      matrix data ((limit.sourceCoordinates initial).symm row) place := by
  rw [squareMatrix_common, Equiv.apply_symm_apply, commonMatrix_retained]

theorem squareMatrix_new
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) (row : coordinate) :
    limit.squareMatrix initial position row (limit.wallColumn initial) =
      limit.commonMatrix position ((limit.sourceCoordinates initial).symm row) none := by
  rw [squareMatrix_common, wallColumn, Equiv.apply_symm_apply]

/-- **The three members' matrices agree away from the regrown wall column.**
This is the retained-column receipt and nothing else: no nonsingularity and no
supplied cofactor correspondence enters. -/
theorem matrices_agree
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (first second : Fin 3) :
    AgreeOffColumn (limit.squareMatrix initial first) (limit.squareMatrix initial second)
      (limit.wallColumn initial) := by
  intro row column hColumn
  rw [squareMatrix_common, squareMatrix_common]
  cases hPlace : limit.targetCoordinates initial column with
  | none => exact (hColumn ((Equiv.eq_symm_apply _).mpr hPlace)).elim
  | some place => rw [commonMatrix_retained, commonMatrix_retained]

/-- **The common cofactors.**  The wall row of the adjugate is literally the
same for all three members. -/
theorem common_cofactors
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) (row : coordinate) :
    (limit.squareMatrix initial position).adjugate (limit.wallColumn initial) row =
      (limit.squareMatrix initial 0).adjugate (limit.wallColumn initial) row :=
  adjugate_wallRow_eq_of_agreeOffColumn (limit.matrices_agree initial position 0) row

/-- Each old column's cofactor-weighted contribution vanishes: it is an
off-diagonal entry of `adjugate A * A = det A • 1`. -/
theorem old_column_annihilation
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (place : target.edges) :
    columnContribution (limit.squareMatrix initial 0) (limit.wallColumn initial)
      ((limit.targetCoordinates initial).symm (some place)) = 0 := by
  apply columnContribution_eq_zero
  intro h
  have hLabels := (limit.targetCoordinates initial).symm.injective h
  cases hLabels

/-- **Equation (8)**, for the three actual Figure 34 members in their induced
common labellings.  No member is assumed nonsingular, and the weights are the
members' own new-edge indices. -/
theorem determinant_balance (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) *
          (limit.squareMatrix initial 0).det +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) *
          (limit.squareMatrix initial 1).det +
        ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) *
          (limit.squareMatrix initial 2).det = 0 := by
  classical
  set A := limit.squareMatrix initial with hA
  set k := limit.wallColumn initial with hk
  set doubleColumn := (limit.targetCoordinates initial).symm
    (some (star.edge profile.doubleLabel)) with hDouble
  set singleColumn := (limit.targetCoordinates initial).symm
    (some (star.edge profile.singleLabel)) with hSingle
  have hDet (position : Fin 3) : (A position).det =
      ∑ row, A position row k * (A 0).adjugate k row :=
    det_eq_sum_wallColumn_mul_commonCofactor (limit.matrices_agree initial position 0)
  have hColumn (row : coordinate) :
      ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) * A 0 row k +
          ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) * A 1 row k +
          ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) * A 2 row k =
        (data.sourceEdgeIndex profile.third.1 : ℚ) * A 0 row doubleColumn +
          (data.sourceEdgeIndex profile.third.1 : ℚ) * A 0 row singleColumn := by
    rw [hA, hk, hDouble, hSingle, squareMatrix_new, squareMatrix_new, squareMatrix_new,
      squareMatrix_retained, squareMatrix_retained]
    exact limit.weighted_column_balance input _
  calc
    ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) * (A 0).det +
          ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) * (A 1).det +
          ((data.sourceEdgeIndex profile.first.1 : ℚ) +
            (data.sourceEdgeIndex profile.second.1 : ℚ)) * (A 2).det =
        ∑ row, (((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) * A 0 row k +
            ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) * A 1 row k +
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
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    BalancingValencyTwo.PositiveBalance
      ![(data.sourceEdgeIndex profile.first.1 : ℚ) - 1,
        (data.sourceEdgeIndex profile.second.1 : ℚ) - 1,
        (data.sourceEdgeIndex profile.first.1 : ℚ) +
          (data.sourceEdgeIndex profile.second.1 : ℚ)]
      (fun position ↦ (limit.squareMatrix initial position).det) := by
  have hk₁ : (1 : ℚ) < (data.sourceEdgeIndex profile.first.1 : ℚ) := by
    exact_mod_cast shape.one_lt_first
  have hk₂ : (1 : ℚ) < (data.sourceEdgeIndex profile.second.1 : ℚ) := by
    exact_mod_cast shape.one_lt_second
  have hn₁ : 1 < data.sourceEdgeIndex profile.first.1 := shape.one_lt_first
  have hn₂ : 1 < data.sourceEdgeIndex profile.second.1 := shape.one_lt_second
  constructor
  · intro position
    fin_cases position <;> simp <;> first | omega | linarith
  · have h := limit.determinant_balance input initial
    simpa [Fin.sum_univ_succ, add_assoc] using h

/-! ### The balanced family -/

/-- The member as a `BalancedGlobal.CertifiedCandidate` for the **incoming**
datum.  A member over the branch-swapped datum is certified for `data` exactly
as `GlobalMkk.DivalentPattern.remoteCertified` certifies it. -/
noncomputable def certified (position : Fin 3) :
    BalancedGlobal.CertifiedCandidate data where
  outgoingTarget := TargetExpansion.graph target wall (limit.member position).right
  datum := (limit.member position).datum
  valid_of_old := (limit.member position).valid_of_old

@[simp] theorem certified_datum (position : Fin 3) :
    (limit.certified position).datum = (limit.member position).datum := rfl

/-- The three actual Figure 34 members with their honest stable-length
matrices and the proved Equation (8) balance.  Possibly singular members are
kept.  This is a `Family`, not a `PresentedFamily`: one member is remote, so
`GlobalMkk`'s swapped route is the one available, exactly as in
`GlobalMkk.swappedBalancedFamily`. -/
noncomputable def family (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    BalancedGlobal.Family (coordinate := coordinate) 3 data where
  candidate := limit.certified
  matrix := limit.squareMatrix initial
  wallColumn := limit.wallColumn initial
  weight := ![(data.sourceEdgeIndex profile.first.1 : ℚ) - 1,
    (data.sourceEdgeIndex profile.second.1 : ℚ) - 1,
    (data.sourceEdgeIndex profile.first.1 : ℚ) +
      (data.sourceEdgeIndex profile.second.1 : ℚ)]
  positiveBalance := limit.positiveBalance input initial
  agreeOffWall := limit.matrices_agree initial

theorem family_matrix_is_honest (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) :
    (limit.family input initial).matrix position =
      GluingDatum.LengthMatrixPresentation.matrix
        (limit.labelling initial position).presentation := rfl

theorem family_candidate_datum (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (position : Fin 3) :
    ((limit.family input initial).candidate position).datum =
      (limit.member position).datum := rfl

/-- Any nonsingular chosen member has an actual valid opposite-sign member;
no nonsingularity is imposed on the other two. -/
theorem exists_valid_opposite (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate)
    (incoming : Fin 3)
    (hIncoming : (limit.squareMatrix initial incoming).det ≠ 0) :
    ∃ outgoing, (limit.member outgoing).datum.Valid ∧
      (limit.squareMatrix initial incoming).det *
        (limit.squareMatrix initial outgoing).det < 0 := by
  obtain ⟨outgoing, hSign⟩ :=
    BalancingValencyTwo.exists_opposite_of_positiveBalance
      (limit.positiveBalance input initial) hIncoming
  exact ⟨outgoing, (limit.member outgoing).valid_of_old input.valid, hSign⟩

end LimitColumns

/-! ### Canonical square coordinates -/

noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

namespace LimitColumns

variable {profile} {shape : Shape profile} (limit : LimitColumns profile shape)

/-- The existing W2 source census supplies a canonical square coordinate
order; it asserts no extra geometric row matching. -/
noncomputable def canonicalRowOrder (input : W2SourceInput data star) :
    StablePath data ≃ Option target.edges :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_option, Multiset.card_coe]
    exact input.stablePath_card)

noncomputable def canonicalInitialLabelling (input : W2SourceInput data star) :
    StableLengthMatrixLabelling (limit.member 0).datum (Option target.edges) where
  row := ((limit.member 0).row).symm.trans (canonicalRowOrder input)
  targetEdge := limit.columnEquiv 0

noncomputable def canonicalMatrix (input : W2SourceInput data star) (position : Fin 3) :
    Matrix (Option target.edges) (Option target.edges) ℚ :=
  limit.squareMatrix (limit.canonicalInitialLabelling input) position

/-- **Equation (8) with no supplied square labelling.** -/
theorem canonical_determinant_balance (input : W2SourceInput data star) :
    ((data.sourceEdgeIndex profile.first.1 : ℚ) - 1) * (limit.canonicalMatrix input 0).det +
        ((data.sourceEdgeIndex profile.second.1 : ℚ) - 1) *
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

theorem canonicalFamily_candidate_datum (input : W2SourceInput data star)
    (position : Fin 3) :
    ((limit.canonicalFamily input).candidate position).datum =
      (limit.member position).datum := rfl

end LimitColumns

end DraismaVargas.LocalCases.W2MkkCommonBalance
