import DraismaVargas.LocalCases.W2M1kSourceCandidates
import DraismaVargas.LocalCases.M11JoinedDescentGeometry
import Utilities.IntegralGeometry.WallColumnDeterminant

/-!
# Figure 33's common balance: Equation (7)

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
**Equation (7)**.  The ambient hypotheses are `{w2-r2}` (where the Base I/II
vocabulary is fixed once for the whole `{w2}` section) and `{w2-r2-nd3}` (where
Cardinality M and P are separated); Base I.a / II.2.2.M / II.1.M are the three
members, and the local case they invoke is (r1-nd2) of Part I's local
properties (`prop-local`).  The case hypothesis is `k₁ = 1`, `k = k₂ ≥ 2`; the
neighbours are `W2MkkSourceCandidates` (`k₁ ≥ 2`) and the `M11*` files
(`k₁ = k₂ = 1`).

`W2M1kSourceCandidates` builds Figure 33's three members as actual
arbitrary-degree gluing data over one datum and one `Shape`, with validity,
source genus preservation and the displayed target valencies.  This module is
the M-1k analogue of `W2MkkCommonBalance`.

## Equation (7) as Part I displays it, and as it is proved here

Part I displays

    c⁽¹⁾ + 2(k-1) c⁽²⁾ + 2(k+1) c⁽³⁾
      = 2(k c(e₁) + c(e₂) + k s) + (c(e₃) + k s) = 2 · 0 + 0 = 0,

with no factor 2 on the second bracket.  The identity proved here carries the
factor 2 on both brackets,

    c⁽¹⁾ + 2(k-1) c⁽²⁾ + 2(k+1) c⁽³⁾
      = 2(k c(e₁) + c(e₂) + k s) + 2(c(e₃) + k s) = 2 · 0 + 2 · 0 = 0,

exactly as Part I's Equation (6) is written for M-11, and exactly what
`BalancingValencyTwo.balance_M_1k` proves: its `calc` rewrites the weighted sum
as `2k(c(e₁) + c(e₂)/k + s) + 2k(c(e₃)/k + s)`.  Nothing here is transcribed
from the display; every coefficient below is either read off Figure 33's own
boxes or derived.

Four declarations make the comparison precise.  `figure33_column_identity` is
the first equality with both factors 2, as an identity of rational functions
of `k` and of four free column entries.  `equation_seven_printed_discrepancy`
computes the difference between the weighted sum and the right-hand side as
displayed: it is `c(e₃) + k s`, neither zero nor cancelling, so the displayed
equality is **not an identity of rational functions**.
`printed_second_bracket_vanishes` is why the two readings nevertheless lead to
the same conclusion: Figure 33's own `M₀` box `c(e₃)/k + s = 0` makes that
difference vanish at every actual profile.  And
`figure33_brackets_forced_equal` shows the factor is not a free choice: the two
old-column multipliers of *any* weight vector satisfying the column identity
are forced equal, so no choice of weights produces the grouping
`2 · (…) + 1 · (…)`.

`equation_seven` is the whole display at an actual M-1k profile, with the
profile's **own** indices `k₁ = |e₁|`, `k₂ = |e₂|`, `k₃ = |e₃|` in the `M₀`
box and Figure 33's `k` in the weights.  The two are identified by
`first_index_cast` (`k₁ = 1`, `Shape.unit_index`), `second_index_cast`
(`k₂ = k`) and `third_index_cast` (`k₃ = k`), which are this case's only free
identities -- Cardinality M (`|A⁽ᵠ⁾| = |A₀| - 1`) together with `k₁ = 1` -- and
the exact analogue of `W2MkkCommonBalance.third_index_cast`.

At column level (`LimitColumns.weighted_column_balance`) the same statement
reads: the three regrown columns, weighted by `1`, `2(k-1)`, `2(k+1)`, add up
to `2k` times the old `t₂` column plus `2k` times the old `t₃` column.  Both
old columns are decomposed here, on the real incoming datum:
`double_matrix_decomposition` (inside `A₀` the `t₂` column displays exactly
`e₁` and `e₂`) and `single_matrix_decomposition` (inside `A₀` the `t₃` column
displays exactly `e₃`; Cardinality M's dangling `e₄` lies above `t₃` but
contributes nothing, being in no stable row at all).  Their two background sums
are **equal**, which is Figure 33's `σ₀(J₀,2) = σ₀(J₀,3) = s`:
`background_sum_eq`, proved from the fact that a wall block outside `A₀` is
unramified, so its source vertex is divalent and its two occurrences are
dangling together, share a stable row and have the block's own size as common
index.

## Where the two factors of 2 come from

Equation (7)'s weight vector is `![1, 2(k-1), 2(k+1)]`, and the asymmetry is
real: two of the three weights carry a factor 2 and the first does not.  The
reason is in `M⁽¹⁾`'s box, not in the weights.  Base I.a detaches a **pair** of
sheets at a new target leaf, so `M⁽¹⁾`'s new edge is discrete there with
`|e'| = |e''| = 1` (`leaf_newEdge_blockCard`), and the census of
`W2M1kStableGraph` puts **both** index-one arms in `e₁`'s stable row
(`W2M1kStableGraph.leaf_new_pin_stablePath_eq`,
`leaf_new_second_stablePath_eq`).  Figure 33 therefore prints
`c⁽¹⁾ = 2c(e₁)`: the doubling is inside the box.  Written per arm the weights
are uniform -- `2` times the member's own new-edge block cardinality at every
position (`figure33_uniform_balance`, weights `![2·1, 2(k-1), 2(k+1)]` against
the per-arm values `![c(e₁), c⁽²⁾, c⁽³⁾]`) -- and the source's `![1, …]` is
that vector with `M⁽¹⁾`'s 2 moved from its weight into its box.

## The weights are derived twice, not posited

**Geometrically**, the three weights are the three members' own new-edge block
cardinalities, doubled.  `leaf_newEdge_blockCard`: `M⁽¹⁾`'s new edge has
`|e'| = |e''| = 1` at every sheet of `A₀`, off
`ResolutionM1k.firstResolution_newEdge_blockCard`.
`divided_newEdge_blockCard_pin` and `divided_newEdge_blockCard_residual`:
`M⁽²⁾`'s new edge isolates **both** pinned sheets as singletons and keeps the
residual `k - 1` class, off `ResolutionM1k.secondNewEdge_blockCard_first` /
`_second` / `_third`.  Figure 33's box lists only `|e'| = 1` and
`|e''| = k - 1` because the third block, the one through `e₄`'s sheet, is
pruned (`W2M1kStableGraph.divided_new_deleted_dangling`); the box and the
partition are consistent, not contradictory.  `joined_newEdge_blockCard`:
`M⁽³⁾`'s new edge is the whole block, `|e'| = |A₀| = k + 1`, off
`ResolutionM1k.thirdResolution_newEdge_blockCard`.

**Algebraically**, they are forced.  `figure33_coefficients` lists the four
coefficient equations of the column identity -- the coefficients of `c(e₁)`,
`c(e₂)`, `c(e₃)` and of the background -- for a general weight vector
`(w₁, w₂, w₃)` and general old-column multipliers `(α, β)`, and checks that
Figure 33's own numbers satisfy them.  `figure33_weights_forced` then shows the
solution space is **one-dimensional**: every solution is
`(w₁, 2(k-1)w₁, 2(k+1)w₁, 2k w₁, 2k w₁)`.  No hypothesis on `k` is needed
anywhere in that derivation; it is four linear equations in five unknowns and
nothing is divided by.  `figure33_weights_normalized` pins all four remaining
numbers once the first weight is fixed at Figure 33's `1`.

Two features of the coefficient system carry the whole forcing, and both are
`M⁽¹⁾`'s:

* the `2` in the first equation `2w₁ + w₂ = α` is `c⁽¹⁾ = 2c(e₁)`, the two
  index-one arms landing in one row;
* the **absence** of `w₁` from the background equation `w₂ + w₃ = α + β` is
  `σ¹(J₀,1) = σ¹(J₁,1) = 0`, Figure 33's own statement that `M⁽¹⁾` has no
  background at all -- every one of its background new occurrences is pruned
  at a monovalent leaf.

Drop either and the relative factor 2 between `w₁` and `w₂, w₃` is no longer
determined.

## Why the receipt carries datums and not `BalancedGlobal.Candidate`s

`W2PCommonBalance.LimitColumns` could quantify over
`members profile shape : Fin 3 → BalancedGlobal.Candidate target degree data wall`
because `W2PSourceCandidates.members_share_datum` puts all three Figure 35
members over one datum.  **M-1k is the opposite case**, for the same reason
M-kk is.  `W2M1kSourceCandidates.no_common_geometry` and
`W2M1kSwapped.no_common_patterns` (a question of gauge -- which copy of the
datum a member lives over -- not of Part I) say no single `w2M1k` gluing datum
carries both `M⁽¹⁾` and `M⁽²⁾`: Base I.a forces the
two wall directions to isolate the *same* sheet (`p₀ = p₁`,
`firstPattern_forces_aligned`) and Base II.2.2.M forces them to isolate
*distinct* ones (`secondPattern_second_eq_pinSheet`).  The second member
therefore lives over the branch-swapped datum, exactly as
`GlobalM1k.swappedCandidates` and `GlobalM1k.swappedBalancedFamily` arrange it,
and as `W2M1kSwapped.SwappedBundle` instantiates it.

`LimitColumns` below is shaped for that.  A member is a `LimitMember`, which
records `right`/`datum`/`valid_of_old` -- the three fields of a
`BalancedGlobal.CertifiedCandidate data`, refined by the expanded target the
member actually lives over -- together with its row bijection and its retained
columns, rather than a `Candidate target degree data wall`, which the remote
member is not.  A member over the incoming datum supplies `valid_of_old` from
`BalancedGlobal.Candidate.datum_valid`; the remote one from
`GlobalM1k.SecondPattern.remoteCertified`, or equivalently from
`GluingDatum.SheetRelabeling.valid` composed with `Candidate.datum_valid`, which
is the route `W2MkkLimitColumns.remoteMember` actually took for Figure 34.
Because `LimitMember` carries no position index, the three of them are supplied
as a plain `![m₀, m₁, m₂]` and assembling them needs no dependent matching.

**Position `1` is the remote one** -- over an `M⁽¹⁾`-shaped (aligned, `p₀ = p₁`)
datum; over an `M⁽²⁾`-shaped one position `0` is the remote one
(`W2M1kLimitColumns.limitColumns`, a `dite` on `pinSheet profile 0 = pinSheet
profile 1`).  Position `0` is `M⁽¹⁾` (Base I.a),
position `1` is `M⁽²⁾` (Base II.2.2.M) and position `2` is `M⁽³⁾` (Base
II.1.M); this is `GlobalM1k.swappedCandidates`' own order, whose middle entry
is `SecondPattern.remoteCertified`.  M-kk's remote member is its *second
detaching* one and which of positions `0`, `1` it occupies is decided by the
datum; M-1k's is position `1` outright, because `M⁽¹⁾` and `M⁽³⁾` both live
over the incoming datum in every orientation.

Consequently this module builds a `BalancedGlobal.Family` and
`exists_valid_opposite`, and **not** a `PresentedFamily` or a cleared pencil:
that is the same boundary `GlobalM1k.exists_valid_positive_exit_swapped` and
`W2M1kSwapped.SwappedBundle.exists_valid_positive_exit` stop at, and for the
same reason.  `W2PCommonBalance.honestPresentedFamily` is available to P and
not here precisely because a `PresentedFamily`'s `candidate` field is
`Fin 3 → Candidate target degree data wall`.

## PART A and PART B: what is unconditional and what is not

**Everything up to and including `positiveBalance_of_relations` is
unconditional**, with exactly `W2M1kSourceCandidates`' hypothesis bundle (a
`W2R2SourceProfile.SourceProfile`, a `Shape`, and -- where the background is
involved -- the `SecondEquation.W2SourceInput` that `W2M1kSourceCandidates`'
callers already carry).  No new hypothesis is introduced anywhere in Part A.

**Part B is conditional on `LimitColumns`, and no inhabitant of `LimitColumns`
is built here.**  Its two fields are exactly what a limit-matrix module must
supply -- each member's geometric stable-row bijection together with the
literal equality of every retained column with the incoming wall column read
through it, and the evaluation of the regrown column as Figure 33's box gives
it -- and are the M-1k analogues of `W2PRowDescent.stablePathEquiv`,
`W2PLimitMatrix.matrix_retained` and `W2PLimitMatrix.firstMember_regrown` and
siblings.  For M-1k the survival, endpoint and background census is in
`W2M1kLeaves` and `W2M1kStableGraph`; the stable lift, the row descent and the
limit matrices are in `W2M1kStableLift`, `W2M1kRowDescent` and
`W2M1kLimitMatrix`; and `W2M1kLimitColumns` builds the inhabitant from the two.
Nothing in `LimitColumns` is a numerical or genericity assumption: every field
is a statement to be *proved* about members `W2M1kSourceCandidates` builds.  In
particular a supplier must prove
that `M⁽¹⁾`'s two surviving new occurrences both lie in `e₁`'s row while all of
its background new occurrences are pruned
(`W2M1kStableGraph.leaf_new_pin_stablePath_eq`,
`leaf_new_second_stablePath_eq`), that `M⁽²⁾`'s unit and residual new
occurrences lie in `e₁`'s and `e₂`'s rows while the one through `e₄`'s sheet
dies with `e₄` (`W2M1kStableGraph.divided_new_unit_stablePath_eq`,
`divided_new_third_stablePath_eq`, `divided_new_deleted_dangling`), and that
`M⁽³⁾`'s surviving new occurrence lies in `e₃`'s row
(`W2M1kStableGraph.joined_new_stablePath_eq_third`).

### How `LimitColumns` is inhabited

This module imports none of the limit-matrix modules; `W2M1kLimitColumns`
assembles the inhabitant.  At positions `1` and `2`, `right`, `datum` and
`valid_of_old` are `DividedData.candidate` / `joinedCandidate` and their
`datum_valid`, `row` is `W2M1kRowDescent.dividedStablePathEquiv` /
`joinedStablePathEquiv`, `retained` is
`W2M1kLimitMatrix.divided_matrix_retained` / `joined_matrix_retained`, and
`regrown` at position `2` is `W2M1kLimitMatrix.joinedMember_regrown` **by
`rfl`**, at position `1` the same after one anchor move by that module's own
`backgroundColumn_congr`.  Position `0` needs a separate leaf chain
(`W2M1kLeafStableLift`, `W2M1kLeafRowDescent`, `W2M1kLeafLimitMatrix`, in the
style of `M11SplitStableLift` / `M11SplitRowDescent` / `M11SplitLimitMatrix`),
for the reason `W2M1kStableLift.leaf_not_wallCandidate` records: Base I.a's
retained endpoint is a target leaf, so `M⁽¹⁾` has no
`LimitChainCore.WallCandidate` and hence no core lift, descent or limit matrix.
Exactly one of positions `0`/`1` is built over the incoming datum, the other
over `swappedData`.

## What Part B proves

* `LimitColumns.commonMatrix`, `commonMatrix_retained` -- the three members'
  honest natural matrices in one coordinate system.
* `weighted_column_balance` -- **Equation (7) at column level on the real
  matrices**.
* `matrices_agree`, `common_cofactors` -- from the retained columns alone; no
  nonsingularity and no supplied cofactor correspondence.
* `old_column_annihilation`, `determinant_balance` -- Equation (7) for the
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

The limit-matrix supplier; the transported `Shape` and `DividedData` over the
branch-swapped datum (`W2SourceTransport` has the four transports and
`W2M1kSwapped.AlignedProfile` the assembly); identifying an *arbitrary*
incoming M-1k datum with a named Figure 33 member (`W2M1kIncomingCensus`,
`W2M1kIncomingMatching`); and `GlobalM1k` itself.
-/

namespace DraismaVargas.LocalCases.W2M1kCommonBalance

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open W2M1kSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## The three free identities -/

/-- **`k₁ = 1` in `ℚ`.**  This is the case hypothesis `Shape.unit_index`: the
first survivor of the double direction is the index-one occurrence `e₁`. -/
theorem first_index_cast (shape : Shape profile) :
    (data.sourceEdgeIndex profile.first.1 : ℚ) = 1 := by
  exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℚ)) shape.unit_index

/-- **`k₂ = k` in `ℚ`.**  With `k₁ = 1` the second survivor above `t₂` carries
the rest of `A₀`, which has `k + 1` sheets. -/
theorem second_index_cast (shape : Shape profile) :
    (data.sourceEdgeIndex profile.second.1 : ℚ) = (shape.k : ℚ) := by
  exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℚ)) shape.second_index

/-- **`k₃ = k` in `ℚ`.**  This is Cardinality M: the `t₃` endpoint block
`A⁽ᵠ⁾` is `A₀` minus the sheet carrying the dangling `e₄`. -/
theorem third_index_cast (shape : Shape profile) :
    (data.sourceEdgeIndex profile.third.1 : ℚ) = (shape.k : ℚ) := by
  exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℚ)) shape.third_index

/-- The two indices Figure 33 writes with the same letter really are equal:
`|e₂| = |e₃| = k`.  This is the M-1k analogue of M-kk's `k₃ + 1 = k₁ + k₂`. -/
theorem third_eq_second_cast (shape : Shape profile) :
    (data.sourceEdgeIndex profile.third.1 : ℚ) =
      (data.sourceEdgeIndex profile.second.1 : ℚ) :=
  (third_index_cast profile shape).trans (second_index_cast profile shape).symm

theorem one_lt_k_cast (shape : Shape profile) : (1 : ℚ) < (shape.k : ℚ) := by
  exact_mod_cast shape.one_lt_k

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

/-- Every occurrence incident to the distinguished block's source vertex has
its sheet in that block.  A local copy of
`W2MkkSourceCandidates.sheet_rel_of_incident`, which this module does not
import; the statement mentions no local case and belongs naturally with
`W2R2SourceProfile`. -/
theorem sheet_rel_of_incident
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (data.vertexPartition wall).Rel block.1 edge.1.1.2 := by
  have hIncident := (incident_wallBlock_sourceVertex_iff data block edge.1).mp edge.2
  exact (WallBlock.ofSheet_eq_iff_rel data wall block edge.1.1.2).mp hIncident.2

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
distinguished block `A₀`: Figure 33's background, whose cofactor-weighted sum
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

/-- Figure 33's `s`, read on one old wall column and one old stable row. -/
noncomputable def backgroundColumn (star : TwoStar target wall)
    (block : WallBlock data wall) (path : StablePath data) (label : Fin 2) : ℚ :=
  ∑ edge ∈ backgroundOccurrences star block path label,
    (1 : ℚ) / data.sourceEdgeIndex edge

/-- **The old `t₂` column.**  Inside `A₀` it displays exactly `e₁` and `e₂`:
the third survivor `e₃` lies above `t₃`, and so does Cardinality M's dangling
`e₄`.  This is the census of the incoming wall in `W2M1kStableGraph` §1 (each
direction carries one pinned occurrence of index one and one bulk occurrence
of index `k`), proved here directly from the
profile's own `exhaustive`. -/
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

/-! ## Figure 33's `s`: the two old backgrounds agree -/

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
/-- **Figure 33's `s = σ₀(J₀,2) = σ₀(J₀,3)`.**  The two old wall columns have
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

/-! ## Equation (7)

As explained in the module docstring, Part I's display has no factor `2` on its
second bracket, while the identity proved here has it on both.  Everything in
this section is stated in Figure 33's
own letters: `k` is the case's `k = k₂ = k₃` with `|A₀| = k + 1`, `c₁`, `c₂`,
`c₃` are the cofactor-weighted contributions `c(e₁)`, `c(e₂)`, `c(e₃)` of the
three surviving old occurrences, and `b` is the common background `s`.  As in
the source, `c₁` carries no denominator: `k₁ = |e₁| = 1`.
-/

/-- **Equation (7)'s first equality**, with the factor `2` on both brackets, as
an identity of rational functions of `k` and of four free column entries.  The
three Figure 33 determinants weighted by `1`, `2(k-1)`, `2(k+1)` are the two
vanishing `M₀` brackets, each taken `2k` times.  **Both** brackets carry the
same factor; in Part I's display the second one carries none. -/
theorem figure33_column_identity {k c₁ c₂ c₃ b : ℚ} (hk : 1 < k) :
    1 * (2 * c₁) + 2 * (k - 1) * (c₁ + c₂ / (k - 1) + b) +
        2 * (k + 1) * (c₃ / (k + 1) + b) =
      2 * k * (c₁ + c₂ / k + b) + 2 * k * (c₃ / k + b) := by
  have h₁ : k ≠ 0 := ne_of_gt (by linarith)
  have h₂ : k - 1 ≠ 0 := ne_of_gt (by linarith)
  have h₃ : k + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The two brackets of `figure33_column_identity`, cleared of denominators
into the shape the source prints them in: `2(k c(e₁) + c(e₂) + k s)` and
`2(c(e₃) + k s)`.  The first is the display's first bracket verbatim; the
second is the display's second bracket **with a factor 2**. -/
theorem figure33_printed_brackets {k c₁ c₂ c₃ b : ℚ} (hk : k ≠ 0) :
    2 * k * (c₁ + c₂ / k + b) = 2 * (k * c₁ + c₂ + k * b) ∧
      2 * k * (c₃ / k + b) = 2 * (c₃ + k * b) := by
  constructor <;> field_simp

/-- **The displayed right-hand side, compared.**  Part I displays Equation
(7)'s right-hand side as `2(k c(e₁) + c(e₂) + k s) + (c(e₃) + k s)`, with no
factor `2` on the second bracket.  The difference between Equation (7)'s
weighted sum and *that* expression is `c(e₃) + k s`, which is not identically
zero: the displayed equality is **not an identity of rational functions**, and
no regrouping makes it one. -/
theorem equation_seven_printed_discrepancy {k c₁ c₂ c₃ b : ℚ} (hk : 1 < k) :
    (1 * (2 * c₁) + 2 * (k - 1) * (c₁ + c₂ / (k - 1) + b) +
          2 * (k + 1) * (c₃ / (k + 1) + b)) -
        (2 * (k * c₁ + c₂ + k * b) + (c₃ + k * b)) =
      c₃ + k * b := by
  have h₁ : k ≠ 0 := ne_of_gt (by linarith)
  have h₂ : k - 1 ≠ 0 := ne_of_gt (by linarith)
  have h₃ : k + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **Why the two readings agree at every profile.**  Figure 33's own `M₀` box
supplies `c(e₃)/k + s = 0`, and that is exactly the difference computed by
`equation_seven_printed_discrepancy`.  So at every actual profile the displayed
right-hand side and the one proved here agree, and both are `0`. -/
theorem printed_second_bracket_vanishes {k c₃ b : ℚ} (hk : k ≠ 0)
    (hright : c₃ / k + b = 0) : c₃ + k * b = 0 := by
  field_simp at hright
  linarith

/-- **The four coefficient equations of the column identity.**  Reading
`figure33_column_identity` off the coefficients of `c₁`, `c₂`, `c₃` and of the
background `b`, with a general weight vector `(w₁, w₂, w₃)` and general old
column multipliers `(α, β)`, gives exactly these four, cleared of
denominators.  The Figure 33 weights `(1, 2(k-1), 2(k+1))` and multipliers
`(2k, 2k)` satisfy them.

Two coefficients are `M⁽¹⁾`'s and carry the whole forcing below: the `2`
multiplying `w₁` in the first equation is `c⁽¹⁾ = 2c(e₁)`, its two index-one
arms landing in one row; and `w₁` is **absent** from the fourth equation
because `σ¹(J₀,1) = σ¹(J₁,1) = 0`, `M⁽¹⁾` having no background at all. -/
theorem figure33_coefficients (k : ℚ) :
    2 * 1 + 2 * (k - 1) = 2 * k ∧
      2 * (k - 1) * k = 2 * k * (k - 1) ∧
        2 * (k + 1) * k = 2 * k * (k + 1) ∧
          2 * (k - 1) + 2 * (k + 1) = 2 * k + 2 * k :=
  ⟨by ring, by ring, by ring, by ring⟩

/-- **The Equation (7) weights are forced, up to one overall scale.**  Given
the four coefficient equations of `figure33_coefficients` for unknown weights
`w₁, w₂, w₃` and unknown old-column multipliers `α, β`, every solution is the
Figure 33 one scaled by `w₁`.  Nothing is posited: the weight vector
`![1, 2(k-1), 2(k+1)]` is the only one, up to scale, for which the three new
columns combine into old columns at all.

Unlike the M-kk analogue this derivation is purely linear: no denominator is
cleared and **no hypothesis on `k` is used**. -/
theorem figure33_weights_forced {k w₁ w₂ w₃ α β : ℚ}
    (hFirst : 2 * w₁ + w₂ = α)
    (hSecond : w₂ * k = α * (k - 1))
    (hThird : w₃ * k = β * (k + 1))
    (hFourth : w₂ + w₃ = α + β) :
    w₂ = 2 * (k - 1) * w₁ ∧ α = 2 * k * w₁ ∧ β = 2 * k * w₁ ∧
      w₃ = 2 * (k + 1) * w₁ := by
  have key₁ : w₂ = 2 * (k - 1) * w₁ := by
    linear_combination hSecond - (k - 1) * hFirst
  have key₂ : α = 2 * k * w₁ := by
    linear_combination key₁ - hFirst
  have key₃ : β = 2 * k * w₁ := by
    linear_combination (-1 : ℚ) * hThird + k * hFourth + (-k) * hFirst
  refine ⟨key₁, key₂, key₃, ?_⟩
  linear_combination hFourth - key₁ + key₂ + key₃

/-- **The two old-column multipliers are forced equal.**  Whatever weights one
puts on Figure 33's three boxes, if they combine into old columns at all then
the two `M₀` brackets appear with the *same* multiplier.  So no choice of
weights produces the grouping `2 · (…) + 1 · (…)` of Part I's display. -/
theorem figure33_brackets_forced_equal {k w₁ w₂ w₃ α β : ℚ}
    (hFirst : 2 * w₁ + w₂ = α)
    (hSecond : w₂ * k = α * (k - 1))
    (hThird : w₃ * k = β * (k + 1))
    (hFourth : w₂ + w₃ = α + β) : α = β := by
  obtain ⟨_, key₂, key₃, _⟩ := figure33_weights_forced hFirst hSecond hThird hFourth
  rw [key₂, key₃]

/-- The normalized form of `figure33_weights_forced`: fixing the first weight
at Figure 33's own `1` pins the other two weights and both old-column
multipliers. -/
theorem figure33_weights_normalized {k w₂ w₃ α β : ℚ}
    (hFirst : 2 * 1 + w₂ = α)
    (hSecond : w₂ * k = α * (k - 1))
    (hThird : w₃ * k = β * (k + 1))
    (hFourth : w₂ + w₃ = α + β) :
    w₂ = 2 * (k - 1) ∧ α = 2 * k ∧ β = 2 * k ∧ w₃ = 2 * (k + 1) := by
  obtain ⟨key₁, key₂, key₃, key₄⟩ :=
    figure33_weights_forced hFirst hSecond hThird hFourth
  exact ⟨by linarith [key₁], by linarith [key₂], by linarith [key₃], by linarith [key₄]⟩

/-! ### The weights are the members' own new-edge block cardinalities

Figure 33's boxes print `|e'| = |e''| = 1` for `M⁽¹⁾`, `|e'| = 1` and
`|e''| = k - 1` for `M⁽²⁾`, and `|e'| = k + 1` for `M⁽³⁾`.  Each is a block
cardinality of the member's **own** new edge, read off the partition
`ResolutionM1k` builds, on the real incoming datum.
-/

/-- **`M⁽¹⁾`'s new edge is discrete on `A₀`: `|e'| = |e''| = 1`** (Base I.a).
Base I.a pairs the pinned sheet with one partner at a fresh target
leaf and splits the block along the new edge, so every sheet of `A₀` has unit
index on it -- in particular the two whose arms survive pruning. -/
theorem leaf_newEdge_blockCard (shape : Shape profile) (pair : LeafPair profile)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (LeafPair.geometry shape pair).firstLocal.newEdge.blockCard sheet = 1 :=
  ResolutionM1k.firstResolution_newEdge_blockCard _ _ _ _ _ _
    ((pinSheet_rel 0).symm.trans hSheet)

/-- **`M⁽²⁾`'s new edge isolates each pinned sheet: `|e'| = 1`**
(Base II.2.2.M).  Both wall directions' pinned sheets become singletons of the new
edge; Figure 33's box lists one of them because the other -- the one through
`e₄`'s sheet -- is pruned with `e₄`
(`W2M1kStableGraph.divided_new_deleted_dangling`). -/
theorem divided_newEdge_blockCard_pin (shape : Shape profile)
    (divided : DividedData profile) (label : Fin 2) :
    (DividedData.geometry shape divided).secondLocal.newEdge.blockCard
        (pinSheet profile label) = 1 := by
  fin_cases label
  · exact ResolutionM1k.secondNewEdge_blockCard_first (data.vertexPartition wall) _ _ _
      (DividedData.geometry shape divided).first_second
      (DividedData.geometry shape divided).first_third
      (DividedData.geometry shape divided).first_ne_second
      (DividedData.geometry shape divided).first_ne_third
      (DividedData.geometry shape divided).second_ne_third
  · exact ResolutionM1k.secondNewEdge_blockCard_second (data.vertexPartition wall) _ _ _
      (DividedData.geometry shape divided).first_second
      (DividedData.geometry shape divided).first_third
      (DividedData.geometry shape divided).first_ne_second
      (DividedData.geometry shape divided).first_ne_third
      (DividedData.geometry shape divided).second_ne_third

/-- **`M⁽²⁾`'s residual new-edge block: `|e''| = k - 1`** (Base II.2.2.M).  With
both pinned sheets detached, the rest of `A₀` -- which has `k + 1` sheets -- is
a single block of size `k - 1`. -/
theorem divided_newEdge_blockCard_residual (shape : Shape profile)
    (divided : DividedData profile) :
    (DividedData.geometry shape divided).secondLocal.newEdge.blockCard divided.third =
      shape.k - 1 :=
  ResolutionM1k.secondNewEdge_blockCard_third (data.vertexPartition wall) _ _ _
    (DividedData.geometry shape divided).first_second
    (DividedData.geometry shape divided).first_third
    (DividedData.geometry shape divided).first_ne_second
    (DividedData.geometry shape divided).first_ne_third
    (DividedData.geometry shape divided).second_ne_third shape.k
    (pinSheet_blockCard_wall shape 0)

/-- **`M⁽³⁾`'s new edge is the whole block: `|e'| = |A₀| = k + 1`** (Base
II.1.M).  `GlobalM1k.Geometry.thirdLocal` is this resolution for every
geometry, so the statement needs no geometry at all. -/
theorem joined_newEdge_blockCard (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (ResolutionM1k.thirdResolution (data.vertexPartition wall)).newEdge.blockCard sheet =
      shape.k + 1 :=
  ResolutionM1k.thirdResolution_newEdge_blockCard _ (pinSheet profile 0) sheet shape.k
    (pinSheet_blockCard_wall shape 0) ((pinSheet_rel 0).symm.trans hSheet)

theorem joined_newEdge_blockCard_thirdLocal (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    geometry.thirdLocal.newEdge.blockCard sheet = shape.k + 1 :=
  joined_newEdge_blockCard profile shape sheet hSheet

/-- `M⁽¹⁾`'s weight in `ℚ`: the common cardinality of its two new-edge blocks. -/
theorem leafMember_weight (shape : Shape profile) (pair : LeafPair profile)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (((LeafPair.geometry shape pair).firstLocal.newEdge.blockCard sheet : ℕ) : ℚ) = 1 := by
  rw [leaf_newEdge_blockCard profile shape pair sheet hSheet]
  norm_num

/-- `M⁽²⁾`'s unit weight in `ℚ`. -/
theorem dividedMember_unit_weight (shape : Shape profile) (divided : DividedData profile)
    (label : Fin 2) :
    (((DividedData.geometry shape divided).secondLocal.newEdge.blockCard
        (pinSheet profile label) : ℕ) : ℚ) = 1 := by
  rw [divided_newEdge_blockCard_pin profile shape divided label]
  norm_num

/-- `M⁽²⁾`'s residual weight in `ℚ`: Figure 33's `k - 1`. -/
theorem dividedMember_residual_weight (shape : Shape profile)
    (divided : DividedData profile) :
    (((DividedData.geometry shape divided).secondLocal.newEdge.blockCard
        divided.third : ℕ) : ℚ) = (shape.k : ℚ) - 1 := by
  have hk := shape.one_lt_k
  rw [divided_newEdge_blockCard_residual profile shape divided,
    Nat.cast_sub (by omega)]
  norm_num

/-- `M⁽³⁾`'s weight in `ℚ`: Figure 33's `k + 1`. -/
theorem joinedMember_weight (shape : Shape profile) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (((ResolutionM1k.thirdResolution (data.vertexPartition wall)).newEdge.blockCard
        sheet : ℕ) : ℚ) = (shape.k : ℚ) + 1 := by
  rw [joined_newEdge_blockCard profile shape sheet hSheet]
  push_cast
  ring

/-! ### Equation (7) itself -/

/-- **Equation (7)**, with the factor `2` on both brackets, at an actual M-1k
source profile.  The two hypotheses are Figure 33's `M₀` box, stated with the
profile's own indices `k₁ = |e₁|`, `k₂ = |e₂|`,
`k₃ = |e₃|` rather than with the figure's `1` and `k`; `first_index_cast`,
`second_index_cast` and `third_index_cast` are what identify them, and they are
the case's only free identities.  The middle expression of Equation (7) is the
right-hand side, with **both** brackets carrying the factor `2k₃`. -/
theorem equation_seven (shape : Shape profile) {c₁ c₂ c₃ s : ℚ}
    (hLeft : c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
      c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s = 0)
    (hRight : c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s = 0) :
    1 * (2 * (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ))) +
          2 * ((shape.k : ℚ) - 1) *
            (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
              c₂ / ((shape.k : ℚ) - 1) + s) +
          2 * ((shape.k : ℚ) + 1) * (c₃ / ((shape.k : ℚ) + 1) + s) =
        2 * (data.sourceEdgeIndex profile.third.1 : ℚ) *
            (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
              c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s) +
          2 * (data.sourceEdgeIndex profile.third.1 : ℚ) *
            (c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s) ∧
      1 * (2 * (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ))) +
          2 * ((shape.k : ℚ) - 1) *
            (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
              c₂ / ((shape.k : ℚ) - 1) + s) +
          2 * ((shape.k : ℚ) + 1) * (c₃ / ((shape.k : ℚ) + 1) + s) = 0 := by
  have hL : c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) + c₂ / (shape.k : ℚ) + s = 0 := by
    rw [← second_index_cast profile shape]; exact hLeft
  have hR : c₃ / (shape.k : ℚ) + s = 0 := by
    rw [← third_index_cast profile shape]; exact hRight
  have hIdentity := figure33_column_identity
    (c₁ := c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ)) (c₂ := c₂) (c₃ := c₃) (b := s)
    (one_lt_k_cast profile shape)
  constructor
  · rw [third_index_cast profile shape, second_index_cast profile shape]
    exact hIdentity
  · rw [hIdentity, hL, hR]
    ring

/-- **Equation (7) as a positive balance**, in the exact shape
`BalancingValencyTwo.balance_M_1k` states it -- which is Equation (7) with the
factor `2` on both brackets, its `calc` rewriting the weighted sum as
`2k(c(e₁) + c(e₂)/k + s) + 2k(c(e₃)/k + s)` -- with the weights derived rather
than supplied.  Positivity of the second weight is `k ≥ 2`. -/
theorem positiveBalance_of_relations (shape : Shape profile) {c₁ c₂ c₃ s : ℚ}
    (hLeft : c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
      c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s = 0)
    (hRight : c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s = 0) :
    BalancingValencyTwo.PositiveBalanceThree
      ![1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)]
      ![2 * (c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ)),
        c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
          c₂ / ((shape.k : ℚ) - 1) + s,
        c₃ / ((shape.k : ℚ) + 1) + s] := by
  refine BalancingValencyTwo.balance_M_1k (one_lt_k_cast profile shape) ?_ ?_
  · rw [← second_index_cast profile shape]; exact hLeft
  · rw [← third_index_cast profile shape]; exact hRight

/-- **Equation (7) with the weights written uniformly.**  Reading `M⁽¹⁾`'s box
per arm -- `c(e₁)`, not Figure 33's doubled `c⁽¹⁾ = 2c(e₁)` -- the weight at
every position is exactly **twice the member's own new-edge block
cardinality**: `2 · 1`, `2 · (k-1)`, `2 · (k+1)`, matching
`leaf_newEdge_blockCard`, `divided_newEdge_blockCard_residual` and
`joined_newEdge_blockCard`.  Figure 33's printed vector `![1, 2(k-1), 2(k+1)]`
is this one with `M⁽¹⁾`'s factor `2` moved out of its weight and into its box;
that, and nothing else, is where the display's two visible factors of `2` come
from. -/
theorem figure33_uniform_balance (shape : Shape profile) {c₁ c₂ c₃ s : ℚ}
    (hLeft : c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
      c₂ / (data.sourceEdgeIndex profile.second.1 : ℚ) + s = 0)
    (hRight : c₃ / (data.sourceEdgeIndex profile.third.1 : ℚ) + s = 0) :
    BalancingValencyTwo.PositiveBalanceThree
      ![2 * 1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)]
      ![c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ),
        c₁ / (data.sourceEdgeIndex profile.first.1 : ℚ) +
          c₂ / ((shape.k : ℚ) - 1) + s,
        c₃ / ((shape.k : ℚ) + 1) + s] := by
  have hk : (1 : ℚ) < (shape.k : ℚ) := one_lt_k_cast profile shape
  obtain ⟨_, hSum⟩ := positiveBalance_of_relations profile shape hLeft hRight
  have hkn := shape.one_lt_k
  refine ⟨fun i ↦ ?_, ?_⟩
  · fin_cases i <;> simp <;> first | omega | linarith
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hSum ⊢
    linarith

/-! ## PART B — the matrix-level chain, over a supplied limit-matrix receipt

Figure 33's `s` is read below at the label `0`, not at `profile.doubleLabel`.
Nothing depends on the choice -- `background_sum_eq` says every label gives the
same background sum on every old stable row, and `weighted_column_balance`
moves both old columns' backgrounds to it -- but `0` is the label a
limit-matrix supplier meets: M-1k's members are built over the raw `star`
rather than over an oriented one, so the core's retained direction at each of
them is `star.edge 0`.  `backgroundColumn star block path label` is
definitionally `LimitChainCore.backgroundColumn data wall block.1 path
(star.edge label)`, and a supplier whose anchor is another sheet of `A₀` moves
it there freely. -/

/-- `M⁽¹⁾`'s regrown column: `c⁽¹⁾ = 2c(e₁)`.

Two things distinguish this box from the other two, and both are Base I.a's
target **leaf**.  The new edge is discrete at the leaf, so both surviving new
occurrences have index one (`leaf_newEdge_blockCard`), and the census of
`W2M1kStableGraph` puts both of them in `e₁`'s stable row
(`W2M1kStableGraph.leaf_new_pin_stablePath_eq`,
`leaf_new_second_stablePath_eq`) -- hence the two identical summands below,
which is Figure 33's factor two.  And there is **no background term**:
`σ¹(J₀,1) = σ¹(J₁,1) = 0`, because every one of `M⁽¹⁾`'s background new
occurrences sits at a monovalent leaf vertex and is pruned. -/
noncomputable def firstNewColumn (path : StablePath data) : ℚ :=
  (if path = firstRow profile then (1 : ℚ) else 0) +
    (if path = firstRow profile then (1 : ℚ) else 0)

/-- Figure 33 prints `M⁽¹⁾`'s box in the doubled form. -/
theorem firstNewColumn_eq_two_mul (path : StablePath data) :
    firstNewColumn profile path =
      2 * (if path = firstRow profile then (1 : ℚ) else 0) := by
  unfold firstNewColumn
  ring

/-- **`c(e₁)` carries no denominator because `k₁ = 1`.**  The bare indicator
Figure 33 writes in `M⁽¹⁾`'s and `M⁽²⁾`'s boxes really is the old `t₂` column's
own `e₁` entry, `1/k₁`; this is the only place the case hypothesis
`Shape.unit_index` enters the boxes. -/
theorem firstEntry_eq (shape : Shape profile) (path : StablePath data) :
    (if path = firstRow profile then (1 : ℚ) else 0) =
      (if path = firstRow profile then (1 : ℚ) else 0) /
        (data.sourceEdgeIndex profile.first.1 : ℚ) := by
  rw [first_index_cast profile shape, div_one]

/-- `M⁽²⁾`'s regrown column: `c⁽²⁾ = c(e₁) + c(e₂)/(k-1) + s`.  The unit new
occurrence joins `e₁`'s row and the residual `k - 1` one joins `e₂`'s
(`W2M1kStableGraph.divided_new_unit_stablePath_eq`,
`divided_new_third_stablePath_eq`); the third new-edge block, the singleton
through `e₄`'s sheet, is pruned with `e₄` and does not appear
(`divided_new_deleted_dangling`). -/
noncomputable def secondNewColumn (shape : Shape profile) (path : StablePath data) : ℚ :=
  (if path = firstRow profile then (1 : ℚ) else 0) +
    (if path = secondRow profile then (1 : ℚ) else 0) / ((shape.k : ℚ) - 1) +
    backgroundColumn star block path 0

/-- `M⁽³⁾`'s regrown column: `c⁽³⁾ = c(e₃)/(k+1) + s`.  Its one surviving new
occurrence has index `|A₀| = k + 1` and joins `e₃`'s row
(`W2M1kStableGraph.joined_new_stablePath_eq_third`). -/
noncomputable def thirdNewColumn (shape : Shape profile) (path : StablePath data) : ℚ :=
  (if path = thirdRow profile then (1 : ℚ) else 0) / ((shape.k : ℚ) + 1) +
    backgroundColumn star block path 0

/-- Figure 33's three regrown columns, indexed.  Position `0` is `M⁽¹⁾` (Base
I.a), position `1` is `M⁽²⁾` (Base II.2.2.M), position `2` is `M⁽³⁾` (Base
II.1.M) -- `GlobalM1k.swappedCandidates`' own order. -/
noncomputable def newColumn (shape : Shape profile) : Fin 3 → StablePath data → ℚ :=
  ![firstNewColumn profile, secondNewColumn profile shape, thirdNewColumn profile shape]

@[simp] theorem newColumn_zero (shape : Shape profile) :
    newColumn profile shape 0 = firstNewColumn profile := rfl

@[simp] theorem newColumn_one (shape : Shape profile) :
    newColumn profile shape 1 = secondNewColumn profile shape := rfl

@[simp] theorem newColumn_two (shape : Shape profile) :
    newColumn profile shape 2 = thirdNewColumn profile shape := rfl

/-- **One Figure 33 member's limit-matrix receipt.**

A member is recorded by its wall-side assignment `right` (which names the
expanded outgoing target `TargetExpansion.graph target wall right`), its honest
outgoing gluing datum, its global validity implication, its geometric
stable-row bijection, and the statement that every retained column of its
honest `StableSourceMatrix.matrix` is literally the incoming wall column.

This is deliberately **not** `BalancedGlobal.Candidate target degree data wall`:
`W2M1kSourceCandidates.no_common_geometry` forbids putting `M⁽¹⁾` and `M⁽²⁾`
over one datum, so `M⁽²⁾` lives over the branch-swapped datum of
`W2M1kSwapped.swappedData` and is a member *for* `data` only through
`GlobalM1k.SecondPattern.remoteCertified`.  Both kinds inhabit this structure:

* over the incoming datum, `right := c.right`, `datum := c.datum`,
  `valid_of_old := c.datum_valid` for `c` a `BalancedGlobal.Candidate`, with
  `row` and `retained` from the row descent and the limit matrix
  (`W2M1kRowDescent`, `W2M1kLimitMatrix`);
* remotely, the same with `valid_of_old` from `remoteCertified`, or
  equivalently from `GluingDatum.SheetRelabeling.valid` composed with
  `Candidate.datum_valid` -- the route `W2MkkLimitColumns.remoteMember` took for
  Figure 34, and the one `W2M1kSwapped.AlignedProfile.swappedSecondPattern`
  makes available here. -/
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
(`W2M1kLimitColumns.limitColumns` builds it).

Everything below this point is conditional on an inhabitant of this structure.
Its content is the M-1k analogue of what `W2PRowDescent.stablePathEquiv`,
`W2PLimitMatrix.matrix_retained` and `W2PLimitMatrix.firstMember_regrown` (and
siblings) supply for Figure 35, and of what `W3Nd3LimitMatrix` and the `M11*`
chain supply for their cases.

Position `0` is `M⁽¹⁾` (Base I.a), position `1` is `M⁽²⁾` (Base II.2.2.M) and
position `2` is `M⁽³⁾` (Base II.1.M).  **Position `1` is the remote one** (in the aligned orientation; `W2M1kLimitColumns`
makes position `0` remote when `p₀ ≠ p₁`): it is
the entry `GlobalM1k.swappedCandidates` fills with
`SecondPattern.remoteCertified`, over `W2M1kSwapped.swappedData`.  Positions `0`
and `2` are over the incoming datum in every orientation, which is where M-1k
differs from M-kk: there, which of the two detaching members is remote is
decided by the datum.

The three members are supplied as a plain `Fin 3`-indexed family of
`LimitMember`s -- no dependent matching is needed to build one, so one writes
`member := ![m₀, m₁, m₂]` -- and the only position-dependent field left
is `regrown`, which evaluates each member's new column as Figure 33's box gives
it.

Nothing here is an assumption of nonsingularity, genericity, or numerical
value: every field is a statement to be *proved* about members
`W2M1kSourceCandidates` builds.  In particular a supplier must prove
that `M⁽¹⁾`'s two surviving new occurrences both lie in `e₁`'s row while all of
its background ones are pruned, that `M⁽²⁾`'s unit and residual new occurrences
lie in `e₁`'s and `e₂`'s rows while the one through `e₄`'s sheet dies with `e₄`
(`W2M1kStableGraph.divided_new_deleted_dangling`), and that `M⁽³⁾`'s surviving
new occurrence lies in `e₃`'s row
(`W2M1kStableGraph.joined_new_stablePath_eq_third`). -/
structure LimitColumns (shape : Shape profile) where
  /-- The three Figure 33 members, with their row bijections and retained
  columns.  Position `1` is the remote one in the aligned orientation, position
  `0` in the separated one (`W2M1kLimitColumns`). -/
  member : Fin 3 → LimitMember data wall
  /-- The regrown column is Figure 33's displayed one. -/
  regrown : ∀ (position : Fin 3) (path : StablePath data),
    (member position).newColumnValue path = newColumn profile shape position path

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
    limit.commonMatrix position path none = newColumn profile shape position path :=
  limit.regrown position path

/-- **Equation (7) at column level, on the real matrices**, with the factor `2`
on both brackets.  The three regrown columns weighted by `1`, `2(k-1)`,
`2(k+1)` add up to `2k₃` times each of the two old wall columns -- both
brackets with the same multiplier, where Part I's display has a factor `2` on
the first only.  The two
sides meet only through `first_index_cast` (`k₁ = 1`), `second_index_cast` and
`third_index_cast` (`k₂ = k₃ = k`) and `background_sum_eq`
(`σ₀(J₀,2) = σ₀(J₀,3)`); no hypothesis is introduced. -/
theorem weighted_column_balance (input : W2SourceInput data star)
    (limit : LimitColumns profile shape) (path : StablePath data) :
    1 * limit.commonMatrix 0 path none +
        2 * ((shape.k : ℚ) - 1) * limit.commonMatrix 1 path none +
        2 * ((shape.k : ℚ) + 1) * limit.commonMatrix 2 path none =
      2 * (data.sourceEdgeIndex profile.third.1 : ℚ) *
          matrix data path (star.edge profile.doubleLabel) +
        2 * (data.sourceEdgeIndex profile.third.1 : ℚ) *
          matrix data path (star.edge profile.singleLabel) := by
  have hk : (1 : ℚ) < (shape.k : ℚ) := one_lt_k_cast profile shape
  have h₁ : (shape.k : ℚ) ≠ 0 := ne_of_gt (by linarith)
  have h₂ : (shape.k : ℚ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h₃ : (shape.k : ℚ) + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [limit.commonMatrix_new 0, limit.commonMatrix_new 1, limit.commonMatrix_new 2,
    double_matrix_decomposition profile path, single_matrix_decomposition profile path,
    background_sum_eq profile input path profile.singleLabel 0,
    background_sum_eq profile input path profile.doubleLabel 0,
    first_index_cast profile shape, second_index_cast profile shape,
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
order; every inter-member row correspondence comes from `LimitMember.row`. -/
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

/-- **Equation (7)**, with the factor `2` on both brackets, for the three
actual Figure 33 members in their induced common labellings.  No member is assumed
nonsingular, and the weights are the members' own new-edge indices, doubled at
the two positions whose boxes are not already doubled. -/
theorem determinant_balance (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    1 * (limit.squareMatrix initial 0).det +
        2 * ((shape.k : ℚ) - 1) * (limit.squareMatrix initial 1).det +
        2 * ((shape.k : ℚ) + 1) * (limit.squareMatrix initial 2).det = 0 := by
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
      1 * A 0 row k + 2 * ((shape.k : ℚ) - 1) * A 1 row k +
          2 * ((shape.k : ℚ) + 1) * A 2 row k =
        2 * (data.sourceEdgeIndex profile.third.1 : ℚ) * A 0 row doubleColumn +
          2 * (data.sourceEdgeIndex profile.third.1 : ℚ) * A 0 row singleColumn := by
    rw [hA, hk, hDouble, hSingle, squareMatrix_new, squareMatrix_new, squareMatrix_new,
      squareMatrix_retained, squareMatrix_retained]
    exact limit.weighted_column_balance input _
  calc
    1 * (A 0).det + 2 * ((shape.k : ℚ) - 1) * (A 1).det +
          2 * ((shape.k : ℚ) + 1) * (A 2).det =
        ∑ row, (1 * A 0 row k + 2 * ((shape.k : ℚ) - 1) * A 1 row k +
            2 * ((shape.k : ℚ) + 1) * A 2 row k) * (A 0).adjugate k row := by
      rw [hDet 0, hDet 1, hDet 2]
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (data.sourceEdgeIndex profile.third.1 : ℚ) *
          columnContribution (A 0) k doubleColumn +
        2 * (data.sourceEdgeIndex profile.third.1 : ℚ) *
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
      ![1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)]
      (fun position ↦ (limit.squareMatrix initial position).det) := by
  have hk : (1 : ℚ) < (shape.k : ℚ) := one_lt_k_cast profile shape
  have hn : 1 < shape.k := shape.one_lt_k
  constructor
  · intro position
    fin_cases position <;> simp <;> first | omega | linarith
  · have h := limit.determinant_balance input initial
    simpa [Fin.sum_univ_succ, add_assoc] using h

end LimitColumns

namespace LimitColumns

variable {profile} {shape : Shape profile} (limit : LimitColumns profile shape)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-! ### The balanced family -/

/-- The member as a `BalancedGlobal.CertifiedCandidate` for the **incoming**
datum.  Position `1`, the member over the branch-swapped datum, is certified for
`data` exactly as `GlobalM1k.SecondPattern.remoteCertified` certifies it. -/
noncomputable def certified (position : Fin 3) :
    BalancedGlobal.CertifiedCandidate data where
  outgoingTarget := TargetExpansion.graph target wall (limit.member position).right
  datum := (limit.member position).datum
  valid_of_old := (limit.member position).valid_of_old

@[simp] theorem certified_datum (position : Fin 3) :
    (limit.certified position).datum = (limit.member position).datum := rfl

/-- The three actual Figure 33 members with their honest stable-length
matrices and the proved Equation (7) balance.  Possibly singular members are
kept.  This is a `Family`, not a `PresentedFamily`: position `1` is remote, so
`GlobalM1k`'s swapped route is the one available, exactly as in
`GlobalM1k.swappedBalancedFamily` and `W2M1kSwapped.SwappedBundle`. -/
noncomputable def family (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    BalancedGlobal.Family (coordinate := coordinate) 3 data where
  candidate := limit.certified
  matrix := limit.squareMatrix initial
  wallColumn := limit.wallColumn initial
  weight := ![1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)]
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

theorem family_weight (input : W2SourceInput data star)
    (initial : StableLengthMatrixLabelling (limit.member 0).datum coordinate) :
    (limit.family input initial).weight =
      ![1, 2 * ((shape.k : ℚ) - 1), 2 * ((shape.k : ℚ) + 1)] := rfl

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

/-- The `w2` source census supplies a canonical square coordinate order; it
asserts no extra geometric row matching. -/
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

/-- **Equation (7) with no supplied square labelling.** -/
theorem canonical_determinant_balance (input : W2SourceInput data star) :
    1 * (limit.canonicalMatrix input 0).det +
        2 * ((shape.k : ℚ) - 1) * (limit.canonicalMatrix input 1).det +
        2 * ((shape.k : ℚ) + 1) * (limit.canonicalMatrix input 2).det = 0 :=
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
end DraismaVargas.LocalCases.W2M1kCommonBalance
