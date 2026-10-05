module

public import DraismaVargasCount.ColumnReceiptExport
public import DraismaVargas.LocalCases.NonTrivalentAnchorValency

@[expose] public section

/-!
# The valency-three split, read off an arbitrary incoming cover

**Source.**  Vargas, Part II (arXiv:2609.09109), the valency-three case of the count
(`subsec-case-v3`), Case `{v3-nd4}`, with Cases (r0)/(r1) of `prop-local` and `lem-rphi-nd`
as used there.  Builds on `ValencyThreeGeneral` (`AnchorIndices`, `Split`, `VType`,
`existsUnique`) and on the anchor machinery of `DraismaVargas.LocalCases`
(`NonTrivalentValencyThreeRigidity`, `NonTrivalentAnchorValency`, `PrunedFibreTree`).  The
results feed `ColumnReceiptExport.facetParity_of_metricUniqueness`, `ValencyThreeRigidity`
and `CensusAssembly`: this is part of the type-change step, step 3 of `Assembly`.

**Stages.**  Uniqueness at a valency-three metric limit is organised in five stages:
(1) every presenting regrowth carries the anchor input; (2) the split is determined by the
combinatorial type; (3) the type is the core's (`TypeMatch`); (4)--(5) the isomorphism extends
across the anchor and pins the core identification (`SplitRigidity`).  This file proves
stages 1 and 2 and the implication from stages 3--5 to uniqueness.

## What is proved

* **§1--§3, the shape of the anchor fibre, at an arbitrary incoming cover** (`shape`).  At a
  merged block `A` of surviving valency four over a trivalent wall, with the contraction
  forest and the valency split (`u` divalent of change one, `v` trivalent of change zero),
  the *pruned* fibre over `A` is exactly one of two pictures:
  `TwoPicture` (base tree `T₂`: `A_u` over `u` with ramification one, `A_v` over `v`, one
  internal occurrence `e₁`; both of surviving valency three) or `ThreePicture` (base tree
  `T_α`: `A_u` over `u` with ramification one and two internal occurrences `e₁ = A_u A_v`,
  `e' = A_u A'`; `A_v` of surviving valency three, `A'` of surviving valency two).  The proof
  is the source's, made general: no-return at the unramified constituents, all ramification
  over `u`, the pruned-fibre tree count, and the excess formula `ram_eq`.
* **§4, the local equations (b)** -- Case (r1) at `A_u` (`TwoPicture.r1`: `|A_u| = k₁ =
  k₂ + k₅`; `ThreePicture.r1`: `k_α = |A_u| = k₁ + |e'|`), Case (r0) at `A'`
  (`ThreePicture.r0_Z`: `|e'| = |A'| = k_δ`), Case (r0) at `A_v` (`TwoPicture.r0`,
  `ThreePicture.r0_Y`: `2|A_v| + 1 = k₁ + k_β + k_γ`), no-return at `A_v` (`Y_distinct`) and
  the sheet accounting `|A_v| + |A'| ≤ |A|` (`ThreePicture.size_Y_add_size_Z`).
* **§5, labelled limit anchors.**  `AnchorLabelling D A` (the survivors `e₂, …, e₅` of Part
  II's Case `{v3-nd4}` as four named occurrences of the *limit*), `AnchorLabelling.indices`
  (the `AnchorIndices` of `ValencyThreeGeneral`, with `(⊞)` from the excess formula),
  `transport` along a geometric isomorphism of limits and `indices_transport`;
  `nonempty_of_four`.
* **§6--§7, reading the split (a) and its validity (c).**  `Reads L u s` (base₂ when `e₂, e₅`
  meet one constituent over `u`; `simple α4 δ5` when `e_α` meets one over `u` and `e_δ` meets
  a divalent one).  **`existsUnique_reads`**: at every cover with `AnchorInput`, relative to
  every labelling, exactly one split is read and it is `AnchorIndices.Valid` for the limit's
  indices (`k_δ < k_α` from (r1)+(r0); `k_β + k_δ ≤ |A|` from harmonicity and sheet
  accounting).  `nonempty_anchorLabelling` (a labelling always exists),
  `eq_limA_of_nonDanglingValency_eq_four` (the anchor is the limit's only vertex of surviving
  valency four), and **`paired_iff`**: the read split's type is the intrinsic combinatorial
  type -- `e₂` lies at one incoming stable vertex exactly with `typePartner s.type`
  (`Paired`).  `reads_base₂_of_edgePartition_eq`: the base-`T₂` criterion.
* **§8, split determination (stage 2).**  `split_eq_of_indices_eq`, **`split_eq_of_limitIso`**
  (two covers, labels transported along *any* geometric isomorphism of the limits, same type
  ⇒ same split), **`split_eq_of_paired`** (same pairing of `e₂` ⇒ same split),
  `exists_transport`.
* **§9, stage 1 at regrowths.**  `RegrowthAnchor`; **`exists_regrowthAnchor`**: every
  regrowth at a facet point of a non-loop slot whose limit's merged target vertex is trivalent
  has the full anchor input (forest from the single vanishing row's simple end,
  `hasSimpleEnd_of_ident`; `nd(A) = 4` from `nonDanglingValency_eq_four_of_row_facet_threeStar`);
  `sourceVertexEquiv_limA`; **`regrowth_split_eq`**.
* **§10, stages 3--5 as hypotheses, and the implication.**  `IsMetricIso`
  (`sameMetricLimit_iff`), `TypeMatch` / `PairingMatch` (stage 3, with an *existential*
  labelled-metric isomorphism; `typeMatch_iff_pairingMatch`), `SplitRigidity` (stages 4--5),
  `V3Limit` (`v3Limit_of_facetPoint`).  **`split_eq_of_same_metric_limit`** (two classes
  specialising to one labelled metric limit with a common type have one split, class form),
  **`huniqL_of_stages`**, `huniqL_of_stages_of_rest`, `huniqR_of_stages_of_rest`,
  **`facetParity_of_stages`** (into `ColumnReceiptExport.facetParity_of_metricUniqueness`).
* **§11, label-moving automorphisms.**  `swapIso`: a sheet swap over a discrete target
  occurrence, related at both ends, is a geometric automorphism fixing every target vertex and
  occurrence (`swapIso_targetEdge`) that moves a source occurrence (`swapIso_moves`).
* **§12, `cat_step`.**  `tail_ne_head_of_sharedContractionSlot` (a shared contraction slot is
  not a loop), and four facts about the ballot data of `cat_step`: `ballot_edgePartition_eq`
  (the contracted spine edge `h₁` has the sheet partition of its root end `u₁`, the base-`T₂`
  criterion), `ballot_divEnd` (`u₁` is the divalent end of `h₁`), and `ballot_leaf_discrete`,
  `ballot_rel_zero_one` (the hypotheses of `swapIso` for the swap `0 ↔ 1` over the root leaf
  edge `u₁ v₁`).

## Three tempting inferences, checked

* **(i) "The split is read off the member's local tree over the anchor, as a partition of the
  `|A|` sheets."**  It holds in modified form.  The indices are the member's source-edge
  indices, and the split is read off the member's local tree over the anchor -- but off the
  **pruned** fibre, not off the `|A|` sheets: the fibre over `A` carries dangling
  constituents, so the split is not a partition of `|A|`.  At `cat_step` (checked by hand from
  the `BallotDatum` table): all five limits have base tree `T₂` (the criterion
  `edgePartition h₁ = vertexPartition u₁` of `reads_base₂_of_edgePartition_eq` holds there,
  `ballot_edgePartition_eq`); for the three sequences with `s₂ = 3`, `|A| = 3` while
  `|A_u| = k₂ + k₅ = 2`, so the `u₁` side of the fibre has a dangling one-sheet block inside
  `A`.  In general the pruned fibre is a tree of two or three constituents (`shape`), not a
  single genus-zero cover of the star.
* **(ii) "Split determination needs the labelled metric limit, which fixes the split."**  This
  does not hold as stated.  Split determination (stage 2) needs no metric:
  `split_eq_of_limitIso` takes *any* geometric isomorphism of the limits, anchor-to-anchor is
  automatic (`sourceVertexEquiv_limA`), and the anchor indices are invariants of the
  unlabelled limit (`indices_transport`).  The type, `α` and `δ` are read off the **cover**,
  not the limit.  Nor does the labelled metric limit fix `δ`: `e₂` and `e₅` lie over one
  target edge, so they carry the same surviving length and the same slot-aligned column, and
  the limit can have a labelled-metric automorphism exchanging them.  At every `cat_step`
  limit the sheet swap `0 ↔ 1` over the root leaf edge `u₁ v₁` is such an automorphism
  (`swapIso`, with hypotheses `ballot_leaf_discrete` and `ballot_rel_zero_one`), and it moves
  the occurrence of sheet `0` (`swapIso_moves`); by the `BallotDatum` table (not re-proved
  here: it needs the danglingness of the ballot source) the occurrences of sheets `0` and `1`
  over `u₁ v₁` are exactly the anchor's doubled-direction survivors `e₂, e₅` (the loop at
  `v₁`).
  Consequence for stage 3: along such an automorphism a cover with a `simple` split reads the
  other `δ`, hence the other of Types I, II, against itself; so `TypeMatch` must quantify the
  metric isomorphism existentially (as stated), not universally.  What the metric limit is
  for is stage 3 (matching the type to the core), which is not attempted here.
* **(iii) "Split determination is local at the anchor."**  This holds.  Stage 2 uses only the
  incoming datum over the closed star of the contracted occurrence (the partitions at `u`, `v`
  and `t₁` inside the merged block), which occurrences dangle, and the full-dimensional
  package's local properties (trivalence, no-glue, validity, change-minimality) with the
  forest.  The member's coordinates enter only stage 1 (`exists_regrowthAnchor`: the forest
  and `nd(A) = 4`).  Stage 4 (extending the isomorphism across the anchor) is local in the
  same sense; stage 5 (pinning the core identification) is global.

## Hypotheses of the implication, and where they are discharged

* `huniqL`/`huniqR` are not proved in this file.  `huniqL_of_stages` and
  `facetParity_of_stages` take:
  * `TypeMatch` (stage 3, equivalently `PairingMatch`): two odd near-side classes at one
    labelled metric limit pair `e₂` with the same survivor, along *some* labelled-metric
    isomorphism.  The universal form (along *every* such isomorphism) fails wherever a
    label-moving automorphism of §11 meets a `simple` split.  `TypeMatch` is proved at every
    facet point of a core with no slot parallel to `e₀`
    (`ValencyThreeCoreSlots.typeMatch_of_noParallel`).  Beyond that, the count uses the
    census form (equal *counts*, rather than the uniqueness form above): wherever a loop
    presenter exists (`ValencyThreeLoopMerge.metricCensus_clause_of_presented`), and at a
    generic `y₀` chosen for each step (`ValencyThreeDigon.exists_facetDatum_v3Clause_of_step`,
    at every step).
  * `SplitRigidity` (stages 4--5): two odd classes at one labelled metric limit with the same
    split are equal.  Proved at every facet request over a connected core with `3 ≤ n`
    (`ValencyThreeResolutionMatch.splitRigidity`, from `resolutionMatch`, which has no
    hypothesis).
  * `hrest`, `hrest'`: uniqueness at the metric limits that are not `V3Limit` (valency two and
    four).  See the caution before `huniqL_of_stages_of_rest`: at valency four this is not
    available.
  * `V3Limit` is discharged by `v3Limit_of_facetPoint` given the trivalence of each presenting
    regrowth's merged target vertex (what "valency-three limit" means) and the non-loop slot
    (`tail_ne_head_of_sharedContractionSlot` at a facet datum).  The trivalence is supplied by
    `CensusAssembly.valency_trichotomy`, which places every metric facet limit in exactly one
    of `V2Limit`, `V3Limit`, `V4Limit` once one presenting regrowth's valency is known
    (`CensusAssembly.limitValency_iff_exists`).
* The new `Prop`s: `AnchorInput` (interface: the hypotheses of
  `NonTrivalentValencyThreeRigidity.threeBranchAnchor`; produced by `exists_regrowthAnchor`);
  `Reads` (strict: exactly one split satisfies it, `existsUnique_reads`); `Paired`
  (characterised by `paired_iff`); `IsMetricIso` (interface: `sameMetricLimit_iff`);
  `TypeMatch`, `PairingMatch` (equivalent, `typeMatch_iff_pairingMatch`; consumer
  `huniqL_of_stages`); `SplitRigidity` (consumer `huniqL_of_stages`); `V3Limit` (interface:
  anchor inputs for every presenting regrowth; producer `v3Limit_of_facetPoint`).
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.ValencyThreeSplit

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification
open W4StableSource WallDegeneration FullDimensionalSource PrunedFibreValency PrunedFibreTree
  FullContractionFibre

/-! ## 1.  Local vocabulary at one incoming source vertex -/

section Local

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-- The surviving (non-dangling) source occurrences at a source vertex. -/
noncomputable def ndAt (X : data.SourceVertex) : Finset data.SourceEdge := by
  classical
  exact Finset.univ.filter fun e ↦ ¬ IsDangling data e ∧ Incident data e X

@[simp] theorem mem_ndAt (X : data.SourceVertex) (e : data.SourceEdge) :
    e ∈ ndAt data X ↔ ¬ IsDangling data e ∧ Incident data e X := by
  classical
  simp [ndAt]

theorem card_ndAt (X : data.SourceVertex) : (ndAt data X).card = nonDanglingValency data X := by
  classical
  rw [PrunedSource.nonDanglingValency_eq_card_filter]
  unfold ndAt
  congr 1

/-- The local degree `|X|` of a source vertex. -/
def size (X : data.SourceVertex) : ℕ := (data.vertexPartition X.1.1).blockCard X.1.2

/-- The local ramification `r(X)` of a source vertex. -/
def ram (X : data.SourceVertex) : ℤ := data.localRamification X.1.1 ⟨X.1.2, X.2⟩

/-- The target occurrence under a source occurrence at `X` is incident to `X`'s target
vertex. -/
theorem target_mem_incidentEdges {X : data.SourceVertex} {e : data.SourceEdge}
    (h : Incident data e X) : e.1.1 ∈ GluingDatum.incidentEdges X.1.1 :=
  ((incident_iff_target_mem_and_rel data e X).mp h).1

/-- **The non-dangling excess formula** (Part II `lem-rphi-nd`):
`r(X) = nd(X) - 2 + 2|X| - Σ_{surviving e ∋ X} k(e)`. -/
theorem ram_eq (hNoGlue : DanglingEdgeNoGlue data) (X : data.SourceVertex) :
    ram data X = (nonDanglingValency data X : ℤ) - 2 + 2 * (size data X : ℤ) -
      ∑ e ∈ ndAt data X, (data.sourceEdgeIndex e : ℤ) := by
  classical
  have h := StableLocalProperties.localRamification_eq_nonDangling_form data hNoGlue X
  rw [ram, h]
  congr 1
  refine Finset.sum_bij (fun edge _ ↦ edge.1) ?_ ?_ ?_ ?_
  · intro edge hEdge
    rw [mem_ndAt]
    exact ⟨(Finset.mem_filter.mp hEdge).2, edge.2⟩
  · intro first _ second _ hEq
    exact Subtype.ext hEq
  · intro e he
    rw [mem_ndAt] at he
    exact ⟨⟨e, he.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.1⟩, rfl⟩
  · intro _ _
    rfl

/-- **Harmonicity in one direction, exact form**: the indices of all source occurrences at
`X` over one incident target occurrence add up to `|X|`. -/
theorem sum_over_eq_size (X : data.SourceVertex) (t : target.edges)
    (ht : t ∈ GluingDatum.incidentEdges X.1.1) :
    (∑ e ∈ Finset.univ.filter (fun e : data.SourceEdge ↦ Incident data e X ∧ e.1.1 = t),
      (data.sourceEdgeIndex e : ℤ)) = size data X := by
  classical
  have h := W2R1SourceProfile.sum_sourceEdgeIndex_target data X t ht
  have h' : (∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data X)).filter
      (fun edge ↦ edge.1.1.1 = t), (data.sourceEdgeIndex edge.1 : ℤ)) = size data X := by
    rw [Finset.sum_filter]
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun edge _ ↦ ?_
    by_cases hT : edge.1.1.1 = t <;> simp [hT]
  rw [← h']
  symm
  refine Finset.sum_bij (fun edge _ ↦ edge.1) ?_ ?_ ?_ ?_
  · intro edge hEdge
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, edge.2, (Finset.mem_filter.mp hEdge).2⟩
  · intro first _ second _ hEq
    exact Subtype.ext hEq
  · intro e he
    obtain ⟨-, hInc, hT⟩ := Finset.mem_filter.mp he
    exact ⟨⟨e, hInc⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩, rfl⟩
  · intro _ _
    rfl

/-- **Harmonicity in one direction**: any set of source occurrences at `X` over one
incident target occurrence has total index at most `|X|`. -/
theorem sum_le_size (X : data.SourceVertex) (S : Finset data.SourceEdge) (t : target.edges)
    (hS : ∀ e ∈ S, Incident data e X ∧ e.1.1 = t) :
    (∑ e ∈ S, (data.sourceEdgeIndex e : ℤ)) ≤ size data X := by
  classical
  by_cases hEmpty : S = ∅
  · subst hEmpty
    simp
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have ht : t ∈ GluingDatum.incidentEdges X.1.1 := by
    have := target_mem_incidentEdges data (hS e₀ he₀).1
    rwa [(hS e₀ he₀).2] at this
  rw [← sum_over_eq_size data X t ht]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS e he⟩
  · intro _ _ _
    positivity

/-- The indices of a set of source occurrences add up to at least its size. -/
theorem card_le_sum_index (S : Finset data.SourceEdge) :
    (S.card : ℤ) ≤ ∑ e ∈ S, (data.sourceEdgeIndex e : ℤ) := by
  have h : ∑ _e ∈ S, (1 : ℤ) ≤ ∑ e ∈ S, (data.sourceEdgeIndex e : ℤ) :=
    Finset.sum_le_sum fun e _ ↦ by
      exact_mod_cast StableLocalProperties.sourceEdgeIndex_pos data e
  simpa using h

end Local

/-! ## 2.  The anchor fibre: vocabulary -/

section FibreVocabulary

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

include fd in
theorem ram_nonneg (X : data.SourceVertex) : 0 ≤ ram data X :=
  data.localRamification_nonneg X.1.1 (fd.valid.2 X.1.1) ⟨X.1.2, X.2⟩

include fd in
/-- A source vertex carries at most the change of its target vertex. -/
theorem ram_le_targetChange (X : data.SourceVertex) : ram data X ≤ data.targetChange X.1.1 := by
  classical
  have hLe := Finset.single_le_sum
    (f := data.localRamification X.1.1)
    (fun other _ ↦ data.localRamification_nonneg X.1.1 (fd.valid.2 X.1.1) other)
    (Finset.mem_univ (⟨X.1.2, X.2⟩ : (data.vertexPartition X.1.1).Blocks))
  exact hLe

include fd in
/-- **No-return** at an unramified source vertex: two surviving occurrences over one target
occurrence coincide. -/
theorem eq_of_ram_zero {X : data.SourceVertex} (hZero : ram data X = 0)
    {e e' : data.SourceEdge} (he : e ∈ ndAt data X) (he' : e' ∈ ndAt data X)
    (hT : e.1.1 = e'.1.1) : e = e' := by
  rw [mem_ndAt] at he he'
  exact NonTrivalentValencyThreeRigidity.sourceEdge_eq_of_same_target_of_localRamification_zero
    data fd X hZero e e' he.1 he'.1 he.2 he'.2 hT

include fd in
theorem nonDanglingValency_two_le {X : data.SourceVertex} (h : nonDanglingValency data X ≠ 0) :
    2 ≤ nonDanglingValency data X := by
  rcases fd.nonDanglingValency_trichotomy X with h0 | h2 | h3 <;> omega

/-- The internal degree of a source vertex: its surviving occurrences over the contracted
target occurrence. -/
noncomputable def ndOver (X : data.SourceVertex) (t : target.edges) : Finset data.SourceEdge := by
  classical
  exact (ndAt data X).filter fun e ↦ e.1.1 = t

@[simp] theorem mem_ndOver (X : data.SourceVertex) (t : target.edges) (e : data.SourceEdge) :
    e ∈ ndOver data X t ↔ e ∈ ndAt data X ∧ e.1.1 = t := by
  classical
  simp [ndOver]

/-- The anchor fibre, pruned: its active vertices. -/
noncomputable abbrev fib (block : (mergedPartition data a b).Blocks) : Finset data.SourceVertex :=
  activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)

/-- The anchor fibre's surviving internal occurrences. -/
noncomputable abbrev intl (block : (mergedPartition data a b).Blocks) : Finset data.SourceEdge :=
  internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)

variable (block : (mergedPartition data a b).Blocks)

theorem mem_fib_iff (X : data.SourceVertex) :
    X ∈ fib data hc hab hOne block ↔
      (X.1.1 = a ∨ X.1.1 = b) ∧ (mergedPartition data a b).repr X.1.2 = block.1 ∧
        nonDanglingValency data X ≠ 0 := by
  rw [fib, mem_activeFibreVertices, ← mem_fibreVertices,
    mem_fibreVertices_mergedVertex_iff, and_assoc]

/-- A surviving occurrence over the contracted target at an active fibre vertex is internal. -/
theorem mem_intl_of_ndAt {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {e : data.SourceEdge} (he : e ∈ ndAt data X) (hT : e.1.1 = contracted) :
    e ∈ intl data hc hab hOne block := by
  rw [mem_ndAt] at he
  rw [intl, mem_internalEdges]
  refine ⟨he.1, hT, ?_⟩
  have hMap := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e hT
  have hXmap := ((mem_activeFibreVertices data hc hab hOne _ X).mp hX).1
  rcases he.2 with h | h
  · rw [h]; exact hXmap
  · rw [hMap, h]; exact hXmap

/-- An internal occurrence is surviving at both its ends, which are active fibre vertices. -/
theorem intl_ends {e : data.SourceEdge} (he : e ∈ intl data hc hab hOne block) :
    (data.sourceEnds e).1 ∈ fib data hc hab hOne block ∧
      (data.sourceEnds e).2 ∈ fib data hc hab hOne block ∧
      e ∈ ndAt data (data.sourceEnds e).1 ∧ e ∈ ndAt data (data.sourceEnds e).2 ∧
      e.1.1 = contracted ∧ (data.sourceEnds e).1.1.1 = a ∧ (data.sourceEnds e).2.1.1 = b := by
  have hEnds := (sourceEnds_mem_activeFibre_iff data hc hab hOne _ e).mpr he
  obtain ⟨hSurv, hT, -⟩ := (mem_internalEdges data hc hab hOne _ e).mp he
  obtain ⟨ha, hb, -⟩ := W4IncomingPrunedFibre.internalEdge_endpoints data hc hab hOne _ e he
  exact ⟨hEnds.1, hEnds.2, (mem_ndAt data _ e).mpr ⟨hSurv, Or.inl rfl⟩,
    (mem_ndAt data _ e).mpr ⟨hSurv, Or.inr rfl⟩, hT, ha, hb⟩

/-- The end of a source occurrence lying over the target vertex `w` (meaningful for an
internal occurrence, whose ends lie over `a` and `b`). -/
noncomputable def endOn (e : data.SourceEdge) (w : target.V) : data.SourceVertex := by
  classical
  exact if (data.sourceEnds e).1.1.1 = w then (data.sourceEnds e).1 else (data.sourceEnds e).2

theorem endOn_spec {e : data.SourceEdge} (he : e ∈ intl data hc hab hOne block) {w : target.V}
    (hw : w = a ∨ w = b) :
    endOn data e w ∈ fib data hc hab hOne block ∧ (endOn data e w).1.1 = w ∧
      e ∈ ndAt data (endOn data e w) := by
  classical
  obtain ⟨h1, h2, hn1, hn2, -, ha, hb⟩ := intl_ends data hc hab hOne block he
  by_cases hwa : (data.sourceEnds e).1.1.1 = w
  · have hE : endOn data e w = (data.sourceEnds e).1 := by simp [endOn, hwa]
    rw [hE]
    exact ⟨h1, hwa, hn1⟩
  · have hE : endOn data e w = (data.sourceEnds e).2 := by simp [endOn, hwa]
    rw [hE]
    refine ⟨h2, ?_, hn2⟩
    rcases hw with rfl | rfl
    · exact absurd ha hwa
    · exact hb

/-- **Counting internal occurrences from one side.**  Every internal occurrence has exactly
one end over each endpoint of the contracted target occurrence. -/
theorem card_intl_eq_sum {w : target.V} (hw : w = a ∨ w = b) :
    (intl data hc hab hOne block).card =
      ∑ X ∈ (fib data hc hab hOne block).filter (fun X ↦ X.1.1 = w),
        ((intl data hc hab hOne block).filter (fun e ↦ endOn data e w = X)).card := by
  classical
  apply Finset.card_eq_sum_card_fiberwise
  intro e he
  obtain ⟨hF, hW, -⟩ := endOn_spec data hc hab hOne block he hw
  exact Finset.mem_filter.mpr ⟨hF, hW⟩

theorem card_filter_endOn_le {w : target.V} (hw : w = a ∨ w = b) (X : data.SourceVertex) :
    ((intl data hc hab hOne block).filter (fun e ↦ endOn data e w = X)).card ≤
      (ndOver data X contracted).card := by
  classical
  apply Finset.card_le_card
  intro e he
  obtain ⟨he, hX⟩ := Finset.mem_filter.mp he
  obtain ⟨-, -, hnd⟩ := endOn_spec data hc hab hOne block he hw
  rw [hX] at hnd
  exact (mem_ndOver data X contracted e).mpr ⟨hnd, (intl_ends data hc hab hOne block he).2.2.2.2.1⟩

/-- The pruned fibre splits into its two sides. -/
theorem card_fib_split {u v : target.V} (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    ((fib data hc hab hOne block).filter (fun X ↦ X.1.1 = u)).card +
      ((fib data hc hab hOne block).filter (fun X ↦ X.1.1 = v)).card =
        (fib data hc hab hOne block).card := by
  classical
  have huv' : u ≠ v := by rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hab; exact hab.symm]
  rw [← Finset.card_filter_add_card_filter_not (s := fib data hc hab hOne block)
    (p := fun X : data.SourceVertex ↦ X.1.1 = u)]
  congr 1
  apply congrArg Finset.card
  ext X
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hX, hv⟩
    exact ⟨hX, by rw [hv]; exact huv'.symm⟩
  · rintro ⟨hX, hu⟩
    refine ⟨hX, ?_⟩
    rcases ((mem_fib_iff data hc hab hOne block X).mp hX).1 with h | h <;>
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd h hu
    · exact h
    · exact h
    · exact absurd h hu

end FibreVocabulary

theorem side_of_huv {α : Type*} {a b u v : α} (hab : a ≠ b)
    (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    (u = a ∨ u = b) ∧ (v = a ∨ v = b) ∧ u ≠ v := by
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Or.inl rfl, Or.inr rfl, hab⟩
  · exact ⟨Or.inr rfl, Or.inl rfl, hab.symm⟩

/-! ## 3.  The shape of the anchor fibre (Part II, Case `{v3-nd4}`, Cases (r0)/(r1)) -/

section Shape

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)
  (u v : target.V)

include fd in
/-- **A ramification-one vertex over a divalent target vertex is not a pure fibre vertex**:
not all of its surviving occurrences lie over the contracted target occurrence. -/
theorem card_ndOver_lt (R : data.SourceVertex) (hR : nonDanglingValency data R ≠ 0)
    (hram : ram data R ≤ 1) :
    (ndOver data R contracted).card < nonDanglingValency data R := by
  classical
  by_contra hge
  have hge : nonDanglingValency data R ≤ (ndOver data R contracted).card := not_lt.mp hge
  have hsub : ndOver data R contracted ⊆ ndAt data R := Finset.filter_subset _ _
  have heq : ndOver data R contracted = ndAt data R :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_ndAt]; exact hge)
  have hsumle := sum_le_size data R (ndAt data R) contracted (fun e he ↦ by
    have he' := he
    rw [← heq, mem_ndOver] at he'
    exact ⟨((mem_ndAt data R e).mp he).2, he'.2⟩)
  have hsumge := card_le_sum_index data (ndAt data R)
  rw [card_ndAt] at hsumge
  have hram' := ram_eq data fd.danglingEdgeNoGlue R
  have h2 := nonDanglingValency_two_le data fd hR
  omega

/-- **The anchor fibre with base tree `T₂`** (Part II, Case `{v3-nd4}`): two active constituents,
`A_u = R` over the divalent endpoint `u` (ramification one) and `A_v = Y` over the trivalent
endpoint `v`, joined by one surviving internal occurrence `e₁`. -/
structure TwoPicture where
  R : data.SourceVertex
  Y : data.SourceVertex
  e₁ : data.SourceEdge
  fib_eq : fib data hc hab hOne block = {R, Y}
  intl_eq : intl data hc hab hOne block = {e₁}
  R_over : R.1.1 = u
  Y_over : Y.1.1 = v
  R_nd : nonDanglingValency data R = 3
  Y_nd : nonDanglingValency data Y = 3
  R_ram : ram data R = 1
  Y_ram : ram data Y = 0
  e₁_R : e₁ ∈ ndAt data R
  e₁_Y : e₁ ∈ ndAt data Y

/-- **The anchor fibre with base tree `T_α`** (Part II, Case `{v3-nd4}`): three active constituents,
`A_u = R` over `u` (ramification one), and `A_v = Y`, `A' = Z` over `v` (unramified,
surviving valencies three and two), joined by `e₁ = R Y` and `e' = R Z`. -/
structure ThreePicture where
  R : data.SourceVertex
  Y : data.SourceVertex
  Z : data.SourceVertex
  e₁ : data.SourceEdge
  e' : data.SourceEdge
  fib_eq : fib data hc hab hOne block = {R, Y, Z}
  intl_eq : intl data hc hab hOne block = {e₁, e'}
  Y_ne_Z : Y ≠ Z
  e₁_ne : e₁ ≠ e'
  R_over : R.1.1 = u
  Y_over : Y.1.1 = v
  Z_over : Z.1.1 = v
  R_nd : nonDanglingValency data R = 3
  Y_nd : nonDanglingValency data Y = 3
  Z_nd : nonDanglingValency data Z = 2
  R_ram : ram data R = 1
  Y_ram : ram data Y = 0
  Z_ram : ram data Z = 0
  e₁_R : e₁ ∈ ndAt data R
  e₁_Y : e₁ ∈ ndAt data Y
  e'_R : e' ∈ ndAt data R
  e'_Z : e' ∈ ndAt data Z

include fd in
/-- **The anchor fibre is one of the two pictures.**  Inputs: the contraction forest, the
dangling compatibility, `nd(A) = 4` at the merged block, and the valency split of the wall
(`u` divalent of change one, `v` of change zero). -/
theorem shape (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hNd : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 4)
    (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (hu2 : (GluingDatum.incidentEdges u).card = 2)
    (hchu : data.targetChange u = 1) (hchv : data.targetChange v = 0) :
    Nonempty (TwoPicture data hc hab hOne block u v) ∨
      Nonempty (ThreePicture data hc hab hOne block u v) := by
  classical
  obtain ⟨huw, hvw, huv'⟩ := side_of_huv hab huv
  set F := fib data hc hab hOne block with hFdef
  set I := intl data hc hab hOne block with hIdef
  set Fu := F.filter (fun X ↦ X.1.1 = u) with hFudef
  set Fv := F.filter (fun X ↦ X.1.1 = v) with hFvdef
  have hNe : F.Nonempty := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero
    data hc hab hOne hCompat _ (by rw [hNd]; norm_num)
  have hTree : I.card + 1 = F.card :=
    internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne hForest block hNe
  have hSum : ∑ X ∈ F, nonDanglingValency data X = 4 + 2 * I.card := by
    rw [hFdef, fib, sum_nonDanglingValency_activeFibre data hc hab hOne hCompat, hNd]
  have hLe3 : ∑ X ∈ F, nonDanglingValency data X ≤ ∑ _X ∈ F, 3 :=
    Finset.sum_le_sum fun X _ ↦ fd.trivalent X
  rw [Finset.sum_const, smul_eq_mul] at hLe3
  have hI1 : 1 ≤ I.card := by omega
  have hmemF : ∀ X ∈ F, (X.1.1 = a ∨ X.1.1 = b) ∧ nonDanglingValency data X ≠ 0 := fun X hX ↦
    ⟨((mem_fib_iff data hc hab hOne block X).mp hX).1,
      ((mem_fib_iff data hc hab hOne block X).mp hX).2.2⟩
  have hvram : ∀ X ∈ Fv, ram data X = 0 := fun X hX ↦
    W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd X
      (by rw [(Finset.mem_filter.mp hX).2]; exact hchv)
  have hdeg0 : ∀ X, ram data X = 0 → (ndOver data X contracted).card ≤ 1 := fun X h0 ↦
    Finset.card_le_one.mpr fun e he e' he' ↦ by
      rw [mem_ndOver] at he he'
      exact eq_of_ram_zero data fd h0 he.1 he'.1 (he.2.trans he'.2.symm)
  have hcntv : ∀ X ∈ Fv, (I.filter (fun e ↦ endOn data e v = X)).card ≤ 1 := fun X hX ↦
    (card_filter_endOn_le data hc hab hOne block hvw X).trans (hdeg0 X (hvram X hX))
  have hIv : I.card ≤ Fv.card := by
    rw [hIdef, card_intl_eq_sum data hc hab hOne block hvw]
    calc _ ≤ ∑ _X ∈ Fv, 1 := Finset.sum_le_sum hcntv
      _ = Fv.card := by simp
  have hSplit : Fu.card + Fv.card = F.card := card_fib_split data hc hab hOne block huv
  obtain ⟨e0, he0⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hR0F, hR0u, -⟩ := endOn_spec data hc hab hOne block he0 huw
  set R := endOn data e0 u with hRdef
  have hRFu : R ∈ Fu := Finset.mem_filter.mpr ⟨hR0F, hR0u⟩
  have hFu : Fu = {R} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr ⟨hRFu, fun X hX ↦ ?_⟩
    exact Finset.card_le_one.mp (by omega) X hX R hRFu
  have hFuv : Fv.card = I.card := by rw [hFu, Finset.card_singleton] at hSplit; omega
  have hIu : I.card ≤ (ndOver data R contracted).card := by
    rw [hIdef, card_intl_eq_sum data hc hab hOne block huw]
    rw [← hFudef, hFu, Finset.sum_singleton]
    exact card_filter_endOn_le data hc hab hOne block huw R
  have hRnd0 := (hmemF R hR0F).2
  have hRram_le : ram data R ≤ 1 :=
    (ram_le_targetChange data fd R).trans (by rw [hR0u, hchu])
  have hRlt := card_ndOver_lt data fd (contracted := contracted) R hRnd0 hRram_le
  have hR3 := fd.trivalent R
  have hRram0 := ram_nonneg data fd R
  -- every fibre vertex lies on one side
  have hFmem : ∀ X, X ∈ F ↔ X = R ∨ X ∈ Fv := by
    intro X
    constructor
    · intro hX
      by_cases hXu : X.1.1 = u
      · left
        have : X ∈ Fu := Finset.mem_filter.mpr ⟨hX, hXu⟩
        rw [hFu] at this
        exact Finset.mem_singleton.mp this
      · right
        refine Finset.mem_filter.mpr ⟨hX, ?_⟩
        rcases (hmemF X hX).1 with h | h <;> rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd h hXu
        · exact h
        · exact h
        · exact absurd h hXu
    · rintro (rfl | hX)
      · exact hR0F
      · exact (Finset.mem_filter.mp hX).1
  have hRnotFv : R ∉ Fv := fun h ↦ huv' (hR0u.symm.trans (Finset.mem_filter.mp h).2)
  have hFeq : F = insert R Fv := by
    ext X; rw [hFmem, Finset.mem_insert]
  have hSumSplit : ∑ X ∈ F, nonDanglingValency data X =
      nonDanglingValency data R + ∑ X ∈ Fv, nonDanglingValency data X := by
    rw [hFeq, Finset.sum_insert hRnotFv]
  have hvnd : ∀ X ∈ Fv, 2 ≤ nonDanglingValency data X ∧ nonDanglingValency data X ≤ 3 :=
    fun X hX ↦ ⟨nonDanglingValency_two_le data fd (hmemF X (Finset.mem_filter.mp hX).1).2,
      fd.trivalent X⟩
  -- the internal occurrences all end at `R` on the `u` side
  have hIendR : ∀ e ∈ I, endOn data e u = R := by
    intro e he
    obtain ⟨hF', hu', -⟩ := endOn_spec data hc hab hOne block he huw
    have : endOn data e u ∈ Fu := Finset.mem_filter.mpr ⟨hF', hu'⟩
    rw [hFu] at this
    exact Finset.mem_singleton.mp this
  have hcases : I.card = 1 ∨ I.card = 2 := by omega
  rcases hcases with h1 | h2
  · -- two-vertex picture
    left
    obtain ⟨Y, hFvY⟩ := Finset.card_eq_one.mp (hFuv.trans h1)
    obtain ⟨e₁, hIe⟩ := Finset.card_eq_one.mp h1
    have hYFv : Y ∈ Fv := by rw [hFvY]; exact Finset.mem_singleton_self Y
    have hYnd := hvnd Y hYFv
    rw [hFvY, Finset.sum_singleton] at hSumSplit
    have he₁ : e₁ ∈ I := by rw [hIe]; exact Finset.mem_singleton_self e₁
    obtain ⟨-, -, he₁R⟩ := endOn_spec data hc hab hOne block he₁ huw
    obtain ⟨hYF', hYv', he₁Y⟩ := endOn_spec data hc hab hOne block he₁ hvw
    rw [hIendR e₁ he₁] at he₁R
    have hYend : endOn data e₁ v = Y := by
      have : endOn data e₁ v ∈ Fv := Finset.mem_filter.mpr ⟨hYF', hYv'⟩
      rw [hFvY] at this
      exact Finset.mem_singleton.mp this
    rw [hYend] at he₁Y
    have hRnd : nonDanglingValency data R = 3 := by omega
    have hRram : ram data R = 1 := by
      by_contra hne
      have h0 : ram data R = 0 := by omega
      have hle := NonDanglingValency.nonDanglingValency_le_of_localRamification_zero data R h0
      rw [hR0u, hu2] at hle
      push_cast at hle
      omega
    exact ⟨{
      R := R, Y := Y, e₁ := e₁
      fib_eq := by rw [← hFdef, hFeq, hFvY]
      intl_eq := hIe
      R_over := hR0u
      Y_over := (Finset.mem_filter.mp hYFv).2
      R_nd := hRnd
      Y_nd := by omega
      R_ram := hRram
      Y_ram := hvram Y hYFv
      e₁_R := he₁R
      e₁_Y := he₁Y }⟩
  · -- three-vertex picture
    right
    have hRdeg : (ndOver data R contracted).card = 2 := by omega
    have hRnd : nonDanglingValency data R = 3 := by omega
    have hRram : ram data R = 1 := by
      by_contra hne
      have := hdeg0 R (by omega)
      omega
    have hFv2 : Fv.card = 2 := hFuv.trans h2
    have hcnt : ∀ X, (I.filter (fun e ↦ endOn data e v = X)).card = 1 →
        ∃ e ∈ I, endOn data e v = X := by
      intro X hX
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hX
      have hmem : e ∈ I.filter (fun e ↦ endOn data e v = X) := by
        rw [he]; exact Finset.mem_singleton_self e
      exact ⟨e, (Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2⟩
    have build : ∀ Y Z : data.SourceVertex, Fv = {Y, Z} → Y ≠ Z →
        nonDanglingValency data Y = 3 → nonDanglingValency data Z = 2 →
        Nonempty (ThreePicture data hc hab hOne block u v) := by
      intro Y Z hFvYZ hYZ hY3 hZ2
      have hYFv : Y ∈ Fv := by rw [hFvYZ]; simp
      have hZFv : Z ∈ Fv := by rw [hFvYZ]; simp
      have hIsum : I.card = (I.filter (fun e ↦ endOn data e v = Y)).card +
          (I.filter (fun e ↦ endOn data e v = Z)).card := by
        rw [hIdef, card_intl_eq_sum data hc hab hOne block hvw, ← hIdef, ← hFdef, ← hFvdef,
          hFvYZ, Finset.sum_pair hYZ]
      have hcY := hcntv Y hYFv
      have hcZ := hcntv Z hZFv
      obtain ⟨e₁, he₁I, he₁v⟩ := hcnt Y (by omega)
      obtain ⟨e', he'I, he'v⟩ := hcnt Z (by omega)
      have hne : e₁ ≠ e' := fun h ↦ hYZ (he₁v.symm.trans (h ▸ he'v))
      have hIeq : I = {e₁, e'} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact he₁I
          · rw [Finset.mem_singleton.mp he]; exact he'I
        · rw [Finset.card_pair hne, h2]
      obtain ⟨-, -, he₁R⟩ := endOn_spec data hc hab hOne block he₁I huw
      obtain ⟨-, -, he'R⟩ := endOn_spec data hc hab hOne block he'I huw
      obtain ⟨-, -, he₁Y⟩ := endOn_spec data hc hab hOne block he₁I hvw
      obtain ⟨-, -, he'Z⟩ := endOn_spec data hc hab hOne block he'I hvw
      rw [hIendR e₁ he₁I] at he₁R
      rw [hIendR e' he'I] at he'R
      rw [he₁v] at he₁Y
      rw [he'v] at he'Z
      exact ⟨{
        R := R, Y := Y, Z := Z, e₁ := e₁, e' := e'
        fib_eq := by rw [← hFdef, hFeq, hFvYZ]
        intl_eq := hIeq
        Y_ne_Z := hYZ
        e₁_ne := hne
        R_over := hR0u
        Y_over := (Finset.mem_filter.mp hYFv).2
        Z_over := (Finset.mem_filter.mp hZFv).2
        R_nd := hRnd
        Y_nd := hY3
        Z_nd := hZ2
        R_ram := hRram
        Y_ram := hvram Y hYFv
        Z_ram := hvram Z hZFv
        e₁_R := he₁R
        e₁_Y := he₁Y
        e'_R := he'R
        e'_Z := he'Z }⟩
    obtain ⟨Y', Z', hYZ', hFvYZ'⟩ := Finset.card_eq_two.mp hFv2
    have hY'Fv : Y' ∈ Fv := by rw [hFvYZ']; simp
    have hZ'Fv : Z' ∈ Fv := by rw [hFvYZ']; simp
    rw [hFvYZ', Finset.sum_pair hYZ'] at hSumSplit
    have hY' := hvnd Y' hY'Fv
    have hZ' := hvnd Z' hZ'Fv
    by_cases hY3 : nonDanglingValency data Y' = 3
    · exact build Y' Z' hFvYZ' hYZ' hY3 (by omega)
    · exact build Z' Y' (by rw [hFvYZ', Finset.pair_comm]) hYZ'.symm (by omega) (by omega)

end Shape

/-! ## 4.  Boundary occurrences and the local equations (Cases (r0)/(r1)) -/

section Boundary

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)
  {u v : target.V}

/-- The surviving occurrences at `X` that are not over the contracted target occurrence: at
a fibre vertex these are its boundary occurrences, the ones that survive in the limit. -/
noncomputable def bdAt (contracted : target.edges) (X : data.SourceVertex) :
    Finset data.SourceEdge := by
  classical
  exact (ndAt data X).filter fun e ↦ e.1.1 ≠ contracted

@[simp] theorem mem_bdAt (X : data.SourceVertex) (e : data.SourceEdge) :
    e ∈ bdAt data contracted X ↔ e ∈ ndAt data X ∧ e.1.1 ≠ contracted := by
  classical
  simp [bdAt]

theorem sum_ndAt_split (X : data.SourceVertex) (f : data.SourceEdge → ℤ) :
    ∑ e ∈ ndAt data X, f e = ∑ e ∈ ndOver data X contracted, f e +
      ∑ e ∈ bdAt data contracted X, f e := by
  classical
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem card_ndAt_split (X : data.SourceVertex) :
    nonDanglingValency data X = (ndOver data X contracted).card +
      (bdAt data contracted X).card := by
  classical
  rw [← card_ndAt]
  exact (Finset.card_filter_add_card_filter_not _).symm

include hc in
theorem contracted_mem_incidentEdges {w : target.V} (hw : w = a ∨ w = b) :
    contracted ∈ GluingDatum.incidentEdges w := by
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hc]
  rcases hw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

include hc in
/-- At a vertex over the divalent endpoint all boundary occurrences lie over the one
non-contracted target occurrence there. -/
theorem bdAt_target_eq_of_divalent {X : data.SourceVertex} (hX : X.1.1 = u)
    (hu : u = a ∨ u = b) (hu2 : (GluingDatum.incidentEdges u).card = 2)
    {e f : data.SourceEdge} (he : e ∈ bdAt data contracted X) (hf : f ∈ bdAt data contracted X) :
    e.1.1 = f.1.1 := by
  classical
  rw [mem_bdAt, mem_ndAt] at he hf
  have hce := target_mem_incidentEdges data he.1.2
  have hcf := target_mem_incidentEdges data hf.1.2
  rw [hX] at hce hcf
  have hcc := contracted_mem_incidentEdges hc hu
  obtain ⟨x, y, hxy, hxyEq⟩ := Finset.card_eq_two.mp hu2
  rw [hxyEq] at hce hcf hcc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hce hcf hcc
  have hne := he.2
  have hnf := hf.2
  rcases hcc with h | h <;> rcases hce with h' | h' <;> rcases hcf with h'' | h'' <;>
    first
    | exact h'.trans h''.symm
    | exact absurd (h'.trans h.symm) hne
    | exact absurd (h''.trans h.symm) hnf

include hc hab hOne in
/-- A non-contracted target occurrence at one endpoint of the contracted occurrence does not
meet the other endpoint (the contracted occurrence is the only one joining them). -/
theorem not_mem_incidentEdges_other (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    {t : target.edges} (ht : t ∈ GluingDatum.incidentEdges u) (hne : t ≠ contracted) :
    t ∉ GluingDatum.incidentEdges v := by
  intro htv
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at ht htv
  have hmem : (t : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  obtain ⟨-, -, huv'⟩ := side_of_huv hab huv
  have hloop : (t : target.V × target.V).1 ≠ (t : target.V × target.V).2 := by
    intro h
    apply target.loopless (t : target.V × target.V).1
    have hpair : (t : target.V × target.V) =
        ((t : target.V × target.V).1, (t : target.V × target.V).2) := rfl
    rw [hpair, ← h] at hmem
    exact hmem
  have hpairs : (t : target.V × target.V) = (u, v) ∨ (t : target.V × target.V) = (v, u) := by
    rcases ht with h1 | h1 <;> rcases htv with h2 | h2
    · exact absurd (h1.symm.trans h2) huv'
    · left; exact Prod.ext h1 h2
    · right; exact Prod.ext h2 h1
    · exact absurd (h1.symm.trans h2) huv'
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hpairs with h | h
  · exact hne (eq_contracted_of_coe_eq_pair hc hOne h)
  · exact notMem_swapped hc hab hOne (h ▸ hmem)
  · exact notMem_swapped hc hab hOne (h ▸ hmem)
  · exact hne (eq_contracted_of_coe_eq_pair hc hOne h)

include hc in
/-- At a trivalent endpoint the non-contracted target occurrences are exactly two. -/
theorem eq_or_eq_of_card_three {w : target.V} (hw : w = a ∨ w = b)
    (hw3 : (GluingDatum.incidentEdges w).card = 3) {t₁ t₂ t : target.edges}
    (h₁ : t₁ ∈ GluingDatum.incidentEdges w) (h₂ : t₂ ∈ GluingDatum.incidentEdges w)
    (ht : t ∈ GluingDatum.incidentEdges w) (hn₁ : t₁ ≠ contracted) (hn₂ : t₂ ≠ contracted)
    (hn : t ≠ contracted) (h12 : t₁ ≠ t₂) : t = t₁ ∨ t = t₂ := by
  classical
  have hcc := contracted_mem_incidentEdges hc hw
  have hsub : ({contracted, t₁, t₂} : Finset target.edges) ⊆ GluingDatum.incidentEdges w := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hcc
    · exact h₁
    · exact h₂
  have hcard : ({contracted, t₁, t₂} : Finset target.edges).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h12]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hn₁.symm, hn₂.symm⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hw3])
  rw [← heq] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with h | h | h
  · exact absurd h hn
  · exact Or.inl h
  · exact Or.inr h

/-- A source occurrence cannot meet two distinct source vertices over one target vertex:
its ends lie over the two distinct ends of its target occurrence. -/
theorem not_incident_both {e : data.SourceEdge} {X Y : data.SourceVertex} (hXY : X ≠ Y)
    (hside : X.1.1 = Y.1.1) (hX : Incident data e X) (hY : Incident data e Y) : False := by
  have hloop : (e.1.1 : target.V × target.V).1 = (e.1.1 : target.V × target.V).2 := by
    have h1 : (data.sourceEnds e).1.1.1 = (e.1.1 : target.V × target.V).1 := rfl
    have h2 : (data.sourceEnds e).2.1.1 = (e.1.1 : target.V × target.V).2 := rfl
    rcases hX with hX | hX <;> rcases hY with hY | hY
    · exact absurd (hX.symm.trans hY) hXY
    · rw [← h1, ← h2, hX, hY, hside]
    · rw [← h1, ← h2, hX, hY, hside]
    · exact absurd (hX.symm.trans hY) hXY
  apply target.loopless (e.1.1 : target.V × target.V).1
  have hmem : (e.1.1 : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  have hpair : (e.1.1 : target.V × target.V) =
      ((e.1.1 : target.V × target.V).1, (e.1.1 : target.V × target.V).2) := rfl
  rw [hpair, ← hloop] at hmem
  exact hmem

/-- An internal occurrence incident to a fibre vertex over `w` ends there on the `w` side. -/
theorem endOn_eq_of_incident {e : data.SourceEdge} (he : e ∈ intl data hc hab hOne block)
    {X : data.SourceVertex} (hInc : Incident data e X) {w : target.V} (hXw : X.1.1 = w) :
    endOn data e w = X := by
  classical
  obtain ⟨-, -, -, -, -, ha, hb⟩ := intl_ends data hc hab hOne block he
  rcases hInc with h | h
  · have hwa : (data.sourceEnds e).1.1.1 = w := by rw [h]; exact hXw
    have hE : endOn data e w = (data.sourceEnds e).1 := by simp [endOn, hwa]
    rw [hE, h]
  · have hwb : (data.sourceEnds e).1.1.1 ≠ w := by
      rw [ha]
      intro haw
      have : X.1.1 = b := by rw [← h]; exact hb
      exact hab (haw.trans (hXw.symm.trans this))
    have hE : endOn data e w = (data.sourceEnds e).2 := by simp [endOn, hwb]
    rw [hE, h]

/-- The size `|A|` of the merged anchor block. -/
noncomputable abbrev anchorSize : ℕ := (mergedPartition data a b).blockCard block.1

/-- The sheets of a fibre vertex lie in the merged block. -/
theorem block_subset_of_mem_fib {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    (data.vertexPartition X.1.1).block X.1.2 ⊆ (mergedPartition data a b).block block.1 := by
  obtain ⟨hw, hrepr, -⟩ := (mem_fib_iff data hc hab hOne block X).mp hX
  intro j hj
  rw [SheetPartition.mem_block_iff] at hj ⊢
  have hRef : (data.vertexPartition X.1.1).Refines (mergedPartition data a b) := by
    rcases hw with h | h
    · rw [h]; exact SheetPartition.left_refines_join _ _
    · rw [h]; exact SheetPartition.right_refines_join _ _
  have hRel := hRef.rel hj
  rw [SheetPartition.rel_iff] at hRel ⊢
  rw [← hRel, hrepr, block.2]

theorem size_le_anchorSize {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    size data X ≤ anchorSize data block :=
  Finset.card_le_card (block_subset_of_mem_fib data hc hab hOne block hX)

/-- **Sheet accounting on one side**: two distinct fibre vertices over the same endpoint
have disjoint sheet blocks inside the merged block. -/
theorem size_add_size_le {X Y : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) (hXY : X ≠ Y) (hside : X.1.1 = Y.1.1) :
    size data X + size data Y ≤ anchorSize data block := by
  classical
  have hdisj : Disjoint ((data.vertexPartition X.1.1).block X.1.2)
      ((data.vertexPartition Y.1.1).block Y.1.2) := by
    rw [Finset.disjoint_left]
    intro j hjX hjY
    rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff] at hjX hjY
    apply hXY
    apply Subtype.ext
    apply Prod.ext hside
    have h1 := X.2
    have h2 := Y.2
    rw [hside] at hjX h1
    exact h1.symm.trans (hjX.trans (hjY.symm.trans h2))
  unfold size SheetPartition.blockCard
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card (Finset.union_subset
    (block_subset_of_mem_fib data hc hab hOne block hX)
    (block_subset_of_mem_fib data hc hab hOne block hY))

/-- A surviving occurrence at `X` has index at most `|X|`. -/
theorem index_le_size {X : data.SourceVertex} {e : data.SourceEdge} (he : e ∈ ndAt data X) :
    (data.sourceEdgeIndex e : ℤ) ≤ size data X := by
  have h := sum_le_size data X {e} e.1.1 (fun f hf ↦ by
    rw [Finset.mem_singleton.mp hf]; exact ⟨((mem_ndAt data _ _).mp he).2, rfl⟩)
  simpa using h

namespace TwoPicture

variable {data hc hab hOne block}
variable (P : TwoPicture data hc hab hOne block u v)

theorem R_mem : P.R ∈ fib data hc hab hOne block := by rw [P.fib_eq]; simp
theorem Y_mem : P.Y ∈ fib data hc hab hOne block := by rw [P.fib_eq]; simp

theorem ndOver_R : ndOver data P.R contracted = {P.e₁} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_ndOver data _ _ _).mpr
    ⟨P.e₁_R, (intl_ends data hc hab hOne block (by rw [P.intl_eq]; simp)).2.2.2.2.1⟩, ?_⟩
  intro e he
  rw [mem_ndOver] at he
  have := mem_intl_of_ndAt data hc hab hOne block P.R_mem he.1 he.2
  rw [P.intl_eq] at this
  exact Finset.mem_singleton.mp this

theorem ndOver_Y : ndOver data P.Y contracted = {P.e₁} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_ndOver data _ _ _).mpr
    ⟨P.e₁_Y, (intl_ends data hc hab hOne block (by rw [P.intl_eq]; simp)).2.2.2.2.1⟩, ?_⟩
  intro e he
  rw [mem_ndOver] at he
  have := mem_intl_of_ndAt data hc hab hOne block P.Y_mem he.1 he.2
  rw [P.intl_eq] at this
  exact Finset.mem_singleton.mp this

theorem card_bdAt_R : (bdAt data contracted P.R).card = 2 := by
  have h := card_ndAt_split data (contracted := contracted) P.R
  rw [P.R_nd, P.ndOver_R, Finset.card_singleton] at h
  omega

theorem card_bdAt_Y : (bdAt data contracted P.Y).card = 2 := by
  have h := card_ndAt_split data (contracted := contracted) P.Y
  rw [P.Y_nd, P.ndOver_Y, Finset.card_singleton] at h
  omega

include fd in
/-- **Case (r1) at `A_u`** (base tree `T₂`): `|A_u| = k₁ = k₂ + k₅`. -/
theorem r1 (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (hu2 : (GluingDatum.incidentEdges u).card = 2) :
    (data.sourceEdgeIndex P.e₁ : ℤ) = size data P.R ∧
      ∑ e ∈ bdAt data contracted P.R, (data.sourceEdgeIndex e : ℤ) = size data P.R := by
  classical
  obtain ⟨huw, -, -⟩ := side_of_huv hab huv
  have hex := ram_eq data fd.danglingEdgeNoGlue P.R
  rw [P.R_ram, P.R_nd, sum_ndAt_split data (contracted := contracted), P.ndOver_R,
    Finset.sum_singleton] at hex
  have h1 := sum_le_size data P.R {P.e₁} contracted (fun e he ↦ by
    rw [Finset.mem_singleton.mp he]
    exact ⟨((mem_ndAt data _ _).mp P.e₁_R).2,
      (intl_ends data hc hab hOne block (by rw [P.intl_eq]; simp)).2.2.2.2.1⟩)
  rw [Finset.sum_singleton] at h1
  obtain ⟨e0, he0⟩ : (bdAt data contracted P.R).Nonempty :=
    Finset.card_pos.mp (by rw [P.card_bdAt_R]; norm_num)
  have h2 := sum_le_size data P.R (bdAt data contracted P.R) e0.1.1 (fun e he ↦
    ⟨((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp he).1).2,
      bdAt_target_eq_of_divalent data hc P.R_over huw hu2 he he0⟩)
  push_cast at hex
  constructor <;> linarith

include fd in
/-- **Case (r0) at `A_v`** (base tree `T₂`): `2|A_v| + 1 = k₁ + k₃ + k₄`. -/
theorem r0 :
    2 * (size data P.Y : ℤ) + 1 =
      data.sourceEdgeIndex P.e₁ + ∑ e ∈ bdAt data contracted P.Y, (data.sourceEdgeIndex e : ℤ) := by
  classical
  have hex := ram_eq data fd.danglingEdgeNoGlue P.Y
  rw [P.Y_ram, P.Y_nd, sum_ndAt_split data (contracted := contracted), P.ndOver_Y,
    Finset.sum_singleton] at hex
  push_cast at hex
  linarith

include fd in
/-- The two boundary occurrences at `A_v` lie over distinct target occurrences (no-return). -/
theorem Y_distinct {e f : data.SourceEdge} (he : e ∈ bdAt data contracted P.Y)
    (hf : f ∈ bdAt data contracted P.Y) (hT : e.1.1 = f.1.1) : e = f :=
  eq_of_ram_zero data fd P.Y_ram ((mem_bdAt data _ _).mp he).1 ((mem_bdAt data _ _).mp hf).1 hT

end TwoPicture

namespace ThreePicture

variable {data hc hab hOne block}
variable (P : ThreePicture data hc hab hOne block u v)

theorem R_mem : P.R ∈ fib data hc hab hOne block := by rw [P.fib_eq]; simp
theorem Y_mem : P.Y ∈ fib data hc hab hOne block := by rw [P.fib_eq]; simp
theorem Z_mem : P.Z ∈ fib data hc hab hOne block := by rw [P.fib_eq]; simp
theorem e₁_mem : P.e₁ ∈ intl data hc hab hOne block := by rw [P.intl_eq]; simp
theorem e'_mem : P.e' ∈ intl data hc hab hOne block := by rw [P.intl_eq]; simp

theorem e₁_target : P.e₁.1.1 = contracted :=
  (intl_ends data hc hab hOne block P.e₁_mem).2.2.2.2.1
theorem e'_target : P.e'.1.1 = contracted :=
  (intl_ends data hc hab hOne block P.e'_mem).2.2.2.2.1

theorem ndOver_R : ndOver data P.R contracted = {P.e₁, P.e'} := by
  classical
  ext e
  rw [mem_ndOver]
  constructor
  · rintro ⟨he, hT⟩
    rw [← P.intl_eq]
    exact mem_intl_of_ndAt data hc hab hOne block P.R_mem he hT
  · intro he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨P.e₁_R, P.e₁_target⟩
    · rw [Finset.mem_singleton.mp he]; exact ⟨P.e'_R, P.e'_target⟩

theorem ndOver_Y : ndOver data P.Y contracted = {P.e₁} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_ndOver data _ _ _).mpr
    ⟨P.e₁_Y, P.e₁_target⟩, ?_⟩
  intro e he
  rw [mem_ndOver] at he
  have hI := mem_intl_of_ndAt data hc hab hOne block P.Y_mem he.1 he.2
  rw [P.intl_eq] at hI
  rcases Finset.mem_insert.mp hI with h | h
  · exact h
  · have he' := Finset.mem_singleton.mp h
    subst he'
    exfalso
    apply P.Y_ne_Z
    have h1 := endOn_eq_of_incident data hc hab hOne block P.e'_mem
      ((mem_ndAt data _ _).mp he.1).2 P.Y_over
    have h2 := endOn_eq_of_incident data hc hab hOne block P.e'_mem
      ((mem_ndAt data _ _).mp P.e'_Z).2 P.Z_over
    exact h1.symm.trans h2

theorem ndOver_Z : ndOver data P.Z contracted = {P.e'} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_ndOver data _ _ _).mpr
    ⟨P.e'_Z, P.e'_target⟩, ?_⟩
  intro e he
  rw [mem_ndOver] at he
  have hI := mem_intl_of_ndAt data hc hab hOne block P.Z_mem he.1 he.2
  rw [P.intl_eq] at hI
  rcases Finset.mem_insert.mp hI with h | h
  · subst h
    exfalso
    apply P.Y_ne_Z
    have h1 := endOn_eq_of_incident data hc hab hOne block P.e₁_mem
      ((mem_ndAt data _ _).mp he.1).2 P.Z_over
    have h2 := endOn_eq_of_incident data hc hab hOne block P.e₁_mem
      ((mem_ndAt data _ _).mp P.e₁_Y).2 P.Y_over
    exact h2.symm.trans h1
  · exact Finset.mem_singleton.mp h

theorem card_bdAt_R : (bdAt data contracted P.R).card = 1 := by
  have h := card_ndAt_split data (contracted := contracted) P.R
  rw [P.R_nd, P.ndOver_R, Finset.card_pair P.e₁_ne] at h
  omega

theorem card_bdAt_Y : (bdAt data contracted P.Y).card = 2 := by
  have h := card_ndAt_split data (contracted := contracted) P.Y
  rw [P.Y_nd, P.ndOver_Y, Finset.card_singleton] at h
  omega

theorem card_bdAt_Z : (bdAt data contracted P.Z).card = 1 := by
  have h := card_ndAt_split data (contracted := contracted) P.Z
  rw [P.Z_nd, P.ndOver_Z, Finset.card_singleton] at h
  omega

include fd in
/-- **Case (r1) at `A_u`** (base tree `T_α`): `k_α = |A_u| = k₁ + |e'|`. -/
theorem r1 :
    (data.sourceEdgeIndex P.e₁ : ℤ) + data.sourceEdgeIndex P.e' = size data P.R ∧
      ∑ e ∈ bdAt data contracted P.R, (data.sourceEdgeIndex e : ℤ) = size data P.R := by
  classical
  have hex := ram_eq data fd.danglingEdgeNoGlue P.R
  rw [P.R_ram, P.R_nd, sum_ndAt_split data (contracted := contracted), P.ndOver_R,
    Finset.sum_pair P.e₁_ne] at hex
  have h1 := sum_le_size data P.R {P.e₁, P.e'} contracted (fun e he ↦ by
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨((mem_ndAt data _ _).mp P.e₁_R).2, P.e₁_target⟩
    · rw [Finset.mem_singleton.mp he]
      exact ⟨((mem_ndAt data _ _).mp P.e'_R).2, P.e'_target⟩)
  rw [Finset.sum_pair P.e₁_ne] at h1
  obtain ⟨bR, hbR⟩ := Finset.card_eq_one.mp P.card_bdAt_R
  have hbRm : bR ∈ bdAt data contracted P.R := by rw [hbR]; exact Finset.mem_singleton_self _
  have h2 := index_le_size data ((mem_bdAt data _ _).mp hbRm).1
  rw [hbR, Finset.sum_singleton] at hex ⊢
  push_cast at hex
  constructor <;> linarith

include fd in
/-- **Case (r0) at `A'`** (base tree `T_α`): `|e'| = |A'| = k_δ`. -/
theorem r0_Z :
    (data.sourceEdgeIndex P.e' : ℤ) = size data P.Z ∧
      ∑ e ∈ bdAt data contracted P.Z, (data.sourceEdgeIndex e : ℤ) = size data P.Z := by
  classical
  have hex := ram_eq data fd.danglingEdgeNoGlue P.Z
  rw [P.Z_ram, P.Z_nd, sum_ndAt_split data (contracted := contracted), P.ndOver_Z,
    Finset.sum_singleton] at hex
  have h1 := index_le_size data P.e'_Z
  obtain ⟨bZ, hbZ⟩ := Finset.card_eq_one.mp P.card_bdAt_Z
  have hbZm : bZ ∈ bdAt data contracted P.Z := by rw [hbZ]; exact Finset.mem_singleton_self _
  have h2 := index_le_size data ((mem_bdAt data _ _).mp hbZm).1
  rw [hbZ, Finset.sum_singleton] at hex ⊢
  push_cast at hex
  constructor <;> linarith

include fd in
/-- **Case (r0) at `A_v`** (base tree `T_α`): `2|A_v| + 1 = k₁ + k_β + k_γ`. -/
theorem r0_Y :
    2 * (size data P.Y : ℤ) + 1 =
      data.sourceEdgeIndex P.e₁ + ∑ e ∈ bdAt data contracted P.Y, (data.sourceEdgeIndex e : ℤ) := by
  classical
  have hex := ram_eq data fd.danglingEdgeNoGlue P.Y
  rw [P.Y_ram, P.Y_nd, sum_ndAt_split data (contracted := contracted), P.ndOver_Y,
    Finset.sum_singleton] at hex
  push_cast at hex
  linarith

include fd in
theorem Y_distinct {e f : data.SourceEdge} (he : e ∈ bdAt data contracted P.Y)
    (hf : f ∈ bdAt data contracted P.Y) (hT : e.1.1 = f.1.1) : e = f :=
  eq_of_ram_zero data fd P.Y_ram ((mem_bdAt data _ _).mp he).1 ((mem_bdAt data _ _).mp hf).1 hT

/-- **Sheet accounting at `v`**: `|A_v| + |A'| ≤ |A|`. -/
theorem size_Y_add_size_Z :
    size data P.Y + size data P.Z ≤ anchorSize data block :=
  size_add_size_le data hc hab hOne block P.Y_mem P.Z_mem P.Y_ne_Z (P.Y_over.trans P.Z_over.symm)

end ThreePicture

end Boundary

/-! ## 5.  The limit anchor: its survivors, labelled -/

section Labelling

variable {T : CFGraph} {degree : ℕ} (D : GluingDatum T degree) (A : D.SourceVertex)

/-- **A labelling of the four survivors at a valency-three anchor** (Part II, Case `{v3-nd4}`):
`e 0, e 3` are `e₂, e₅` over the doubled target direction with `k₂ ≤ k₅`; `e 1, e 2` are
`e₃, e₄` over the two simple directions with `k₃ ≤ k₄`.  With ties the labelling is a
choice; every statement below is relative to it, and a geometric isomorphism of limits
transports it (`AnchorLabelling.transport`). -/
structure AnchorLabelling where
  e : Fin 4 → D.SourceEdge
  mem : ∀ i, e i ∈ ndAt D A
  inj : Function.Injective e
  dir25 : (e 0).1.1 = (e 3).1.1
  dir3 : (e 1).1.1 ≠ (e 0).1.1
  dir4 : (e 2).1.1 ≠ (e 0).1.1
  dir34 : (e 1).1.1 ≠ (e 2).1.1
  ord25 : D.sourceEdgeIndex (e 0) ≤ D.sourceEdgeIndex (e 3)
  ord34 : D.sourceEdgeIndex (e 1) ≤ D.sourceEdgeIndex (e 2)

namespace AnchorLabelling

variable {D A} (L : AnchorLabelling D A)

theorem ndAt_eq (hnd : nonDanglingValency D A = 4) :
    ndAt D A = Finset.univ.image L.e := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro f hf
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hf
    exact L.mem i
  · rw [card_ndAt, hnd, Finset.card_image_of_injective _ L.inj]
    simp

theorem sum_ndAt (hnd : nonDanglingValency D A = 4) :
    ∑ f ∈ ndAt D A, (D.sourceEdgeIndex f : ℤ) =
      D.sourceEdgeIndex (L.e 0) + D.sourceEdgeIndex (L.e 1) + D.sourceEdgeIndex (L.e 2) +
        D.sourceEdgeIndex (L.e 3) := by
  classical
  rw [L.ndAt_eq hnd, Finset.sum_image (fun i _ j _ h ↦ L.inj h), Fin.sum_univ_four]

/-- **The anchor indices of a labelled valency-three anchor**
(`ValencyThreeGeneral.Split7.AnchorIndices`): `|A|` is the anchor's local degree, `(⊞)` is
the excess formula at ramification one and surviving valency four, and the three bounds are
harmonicity in each direction. -/
def indices (hNoGlue : DanglingEdgeNoGlue D) (hram : ram D A = 1)
    (hnd : nonDanglingValency D A = 4) : ValencyThreeGeneral.Split7.AnchorIndices where
  A := size D A
  k₂ := D.sourceEdgeIndex (L.e 0)
  k₃ := D.sourceEdgeIndex (L.e 1)
  k₄ := D.sourceEdgeIndex (L.e 2)
  k₅ := D.sourceEdgeIndex (L.e 3)
  h25 := L.ord25
  h34 := L.ord34
  tri := by
    have h := ram_eq D hNoGlue A
    rw [hram, hnd, L.sum_ndAt hnd] at h
    push_cast at h
    omega
  doubled := by
    classical
    have hne : L.e 0 ≠ L.e 3 := fun h ↦ absurd (L.inj h) (by decide)
    have h := sum_le_size D A {L.e 0, L.e 3} (L.e 0).1.1 (fun f hf ↦ by
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨((mem_ndAt D _ _).mp (L.mem 0)).2, rfl⟩
      · rw [Finset.mem_singleton.mp hf]
        exact ⟨((mem_ndAt D _ _).mp (L.mem 3)).2, L.dir25.symm⟩)
    rw [Finset.sum_pair hne] at h
    omega
  simple₃ := by have := index_le_size D (L.mem 1); omega
  simple₄ := by have := index_le_size D (L.mem 2); omega

@[simp] theorem indices_A (hNoGlue : DanglingEdgeNoGlue D) (hram : ram D A = 1)
    (hnd : nonDanglingValency D A = 4) : (L.indices hNoGlue hram hnd).A = size D A := rfl

/-- Anchor indices are determined by their five numbers. -/
theorem _root_.DraismaVargas.Count.ValencyThreeSplit.anchorIndices_ext
    {x y : ValencyThreeGeneral.Split7.AnchorIndices} (hA : x.A = y.A) (h2 : x.k₂ = y.k₂)
    (h3 : x.k₃ = y.k₃) (h4 : x.k₄ = y.k₄) (h5 : x.k₅ = y.k₅) : x = y := by
  obtain ⟨A, k₂, k₃, k₄, k₅, _, _, _, _, _, _⟩ := x
  obtain ⟨A', k₂', k₃', k₄', k₅', _, _, _, _, _, _⟩ := y
  simp only at hA h2 h3 h4 h5
  subst hA h2 h3 h4 h5
  rfl

variable {T₂ : CFGraph} {D₂ : GluingDatum T₂ degree}

/-- **Transport of a labelling along a geometric isomorphism of limits.** -/
def transport (ψ : GeometricDatumIso D D₂) (hConn : D.Connected) :
    AnchorLabelling D₂ (ψ.sourceVertexEquiv A) where
  e i := ψ.sourceEdgeEquiv (L.e i)
  mem i := by
    have h := (mem_ndAt D _ _).mp (L.mem i)
    rw [mem_ndAt, ψ.isDangling_map_iff hConn, ψ.incident_map_iff]
    exact h
  inj i j h := L.inj (ψ.sourceEdgeEquiv.injective h)
  dir25 := congrArg ψ.targetEdge L.dir25
  dir3 h := L.dir3 (ψ.targetEdge.injective h)
  dir4 h := L.dir4 (ψ.targetEdge.injective h)
  dir34 h := L.dir34 (ψ.targetEdge.injective h)
  ord25 := by rw [ψ.sourceEdgeIndex_map, ψ.sourceEdgeIndex_map]; exact L.ord25
  ord34 := by rw [ψ.sourceEdgeIndex_map, ψ.sourceEdgeIndex_map]; exact L.ord34

theorem size_map (ψ : GeometricDatumIso D D₂) (X : D.SourceVertex) :
    size D₂ (ψ.sourceVertexEquiv X) = size D X := by
  change (D₂.vertexPartition (ψ.targetVertex X.1.1)).blockCard (ψ.vertexPerm X.1.1 X.1.2) = _
  rw [ψ.vertexPartition X.1.1]
  exact SheetPartition.relabel_blockCard _ _ _

/-- **A geometric isomorphism of limits preserves the anchor indices** of a transported
labelling. -/
theorem indices_transport (ψ : GeometricDatumIso D D₂) (hConn : D.Connected)
    (hNoGlue : DanglingEdgeNoGlue D) (hram : ram D A = 1) (hnd : nonDanglingValency D A = 4)
    (hNoGlue₂ : DanglingEdgeNoGlue D₂) (hram₂ : ram D₂ (ψ.sourceVertexEquiv A) = 1)
    (hnd₂ : nonDanglingValency D₂ (ψ.sourceVertexEquiv A) = 4) :
    (L.transport ψ hConn).indices hNoGlue₂ hram₂ hnd₂ = L.indices hNoGlue hram hnd :=
  anchorIndices_ext (size_map ψ A) (ψ.sourceEdgeIndex_map _) (ψ.sourceEdgeIndex_map _)
    (ψ.sourceEdgeIndex_map _) (ψ.sourceEdgeIndex_map _)

/-- A labelling from four explicit survivors, already in order. -/
def ofFour (x₀ x₁ x₂ x₃ : D.SourceEdge) (m₀ : x₀ ∈ ndAt D A) (m₁ : x₁ ∈ ndAt D A)
    (m₂ : x₂ ∈ ndAt D A) (m₃ : x₃ ∈ ndAt D A) (h03 : x₀ ≠ x₃)
    (d03 : x₀.1.1 = x₃.1.1) (d10 : x₁.1.1 ≠ x₀.1.1) (d20 : x₂.1.1 ≠ x₀.1.1)
    (d12 : x₁.1.1 ≠ x₂.1.1)
    (o03 : D.sourceEdgeIndex x₀ ≤ D.sourceEdgeIndex x₃)
    (o12 : D.sourceEdgeIndex x₁ ≤ D.sourceEdgeIndex x₂) : AnchorLabelling D A where
  e := ![x₀, x₁, x₂, x₃]
  mem i := by fin_cases i <;> assumption
  inj := by
    have h01 : x₀ ≠ x₁ := fun h ↦ d10 (by rw [h])
    have h02 : x₀ ≠ x₂ := fun h ↦ d20 (by rw [h])
    have h12 : x₁ ≠ x₂ := fun h ↦ d12 (by rw [h])
    have h13 : x₁ ≠ x₃ := fun h ↦ d10 (by rw [h, d03])
    have h23 : x₂ ≠ x₃ := fun h ↦ d20 (by rw [h, d03])
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  dir25 := d03
  dir3 := d10
  dir4 := d20
  dir34 := d12
  ord25 := o03
  ord34 := o12

/-- A labelling exists as soon as four survivors show the `2 + 1 + 1` pattern: sort each
pair by index. -/
theorem nonempty_of_four (x₀ x₁ x₂ x₃ : D.SourceEdge) (m₀ : x₀ ∈ ndAt D A)
    (m₁ : x₁ ∈ ndAt D A) (m₂ : x₂ ∈ ndAt D A) (m₃ : x₃ ∈ ndAt D A) (h03 : x₀ ≠ x₃)
    (d03 : x₀.1.1 = x₃.1.1) (d10 : x₁.1.1 ≠ x₀.1.1) (d20 : x₂.1.1 ≠ x₀.1.1)
    (d12 : x₁.1.1 ≠ x₂.1.1) : Nonempty (AnchorLabelling D A) := by
  by_cases o03 : D.sourceEdgeIndex x₀ ≤ D.sourceEdgeIndex x₃
  · by_cases o12 : D.sourceEdgeIndex x₁ ≤ D.sourceEdgeIndex x₂
    · exact ⟨ofFour x₀ x₁ x₂ x₃ m₀ m₁ m₂ m₃ h03 d03 d10 d20 d12 o03 o12⟩
    · exact ⟨ofFour x₀ x₂ x₁ x₃ m₀ m₂ m₁ m₃ h03 d03 d20 d10 (Ne.symm d12) o03 (by omega)⟩
  · by_cases o12 : D.sourceEdgeIndex x₁ ≤ D.sourceEdgeIndex x₂
    · exact ⟨ofFour x₃ x₁ x₂ x₀ m₃ m₁ m₂ m₀ (Ne.symm h03) d03.symm (d03 ▸ d10)
        (d03 ▸ d20) d12 (by omega) o12⟩
    · exact ⟨ofFour x₃ x₂ x₁ x₀ m₃ m₂ m₁ m₀ (Ne.symm h03) d03.symm (d03 ▸ d20)
        (d03 ▸ d10) (Ne.symm d12) (by omega) (by omega)⟩

end AnchorLabelling

end Labelling

/-! ## 6.  Reading the split off the incoming cover -/

section Reading

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)

/-- The anchor of the limit: the merged block, as a source vertex of the contracted datum. -/
noncomputable abbrev limA : (contractDatum data hc hab hOne).SourceVertex :=
  mergedVertex data hc hab hOne block

theorem size_limA :
    size (contractDatum data hc hab hOne) (limA data hc hab hOne block) =
      anchorSize data block := by
  change ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard block.1 = _
  rw [contractDatum_vertexPartition_merge]

variable {data hc hab hOne block}

/-- A boundary occurrence at an active fibre vertex survives at the limit anchor. -/
theorem sourceEdgeMap_mem_ndAt (hCompat : DanglingCompatible data hc hab hOne)
    {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {e : data.SourceEdge} (he : e ∈ bdAt data contracted X) :
    sourceEdgeMap data hc hab hOne ⟨e, ((mem_bdAt data X e).mp he).2⟩ ∈
      ndAt (contractDatum data hc hab hOne) (limA data hc hab hOne block) := by
  obtain ⟨hnd', hT⟩ := (mem_bdAt data X e).mp he
  obtain ⟨hSurv, hInc⟩ := (mem_ndAt data X e).mp hnd'
  rw [mem_ndAt]
  refine ⟨fun hBad ↦ hSurv (hCompat.2 ⟨e, hT⟩ hBad), ?_⟩
  have hXmap := ((mem_activeFibreVertices data hc hab hOne _ X).mp hX).1
  unfold Incident
  rw [sourceEnds_sourceEdgeMap]
  rcases hInc with h | h
  · left; rw [h]; exact hXmap
  · right; rw [h]; exact hXmap

omit [Fintype coordinate] [DecidableEq coordinate] in
theorem sourceEdgeMap_target_eq_iff (e f : {e : data.SourceEdge // e.1.1 ≠ contracted}) :
    (sourceEdgeMap data hc hab hOne e).1.1 = (sourceEdgeMap data hc hab hOne f).1.1 ↔
      e.1.1.1 = f.1.1.1 := by
  change foldEdge hc hab hOne ⟨e.1.1.1, e.2⟩ = foldEdge hc hab hOne ⟨f.1.1.1, f.2⟩ ↔ _
  constructor
  · intro h
    exact congrArg Subtype.val (foldEdge_injective hc hab hOne h)
  · intro h
    exact congrArg _ (Subtype.ext h)

variable (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- The incoming boundary occurrence carrying the limit survivor `L.e i`. -/
noncomputable def lift (i : Fin 4) : data.SourceEdge :=
  ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)).1

theorem lift_ne (i : Fin 4) : (lift L i).1.1 ≠ contracted :=
  ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)).2

theorem sourceEdgeMap_lift (i : Fin 4) :
    sourceEdgeMap data hc hab hOne ⟨lift L i, lift_ne L i⟩ = L.e i :=
  (ContractionFibre.sourceEdgeEquiv data hc hab hOne).apply_symm_apply (L.e i)

theorem index_lift (i : Fin 4) :
    data.sourceEdgeIndex (lift L i) = (contractDatum data hc hab hOne).sourceEdgeIndex (L.e i) :=
  ContractionFibre.sourceEdgeIndex_symm_sourceEdgeEquiv data hc hab hOne (L.e i)

theorem lift_injective : Function.Injective (lift L) := by
  intro i j h
  apply L.inj
  have h' : ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)) =
      ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e j)) := Subtype.ext h
  exact (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm.injective h'

theorem lift_target_eq_iff (i j : Fin 4) :
    (lift L i).1.1 = (lift L j).1.1 ↔ (L.e i).1.1 = (L.e j).1.1 := by
  rw [← sourceEdgeMap_lift L i, ← sourceEdgeMap_lift L j]
  change _ ↔ foldEdge hc hab hOne ⟨(lift L i).1.1, lift_ne L i⟩ =
    foldEdge hc hab hOne ⟨(lift L j).1.1, lift_ne L j⟩
  constructor
  · intro h
    exact congrArg _ (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (foldEdge_injective hc hab hOne h)

/-- **The only two labels over one target direction are `e₂` and `e₅`.** -/
theorem label_pair_of_target_eq {i j : Fin 4} (hij : i ≠ j)
    (h : (L.e i).1.1 = (L.e j).1.1) : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) := by
  have d25 := L.dir25
  have d3 := L.dir3
  have d4 := L.dir4
  have d34 := L.dir34
  fin_cases i <;> fin_cases j <;> simp_all

include hc in
/-- A boundary occurrence at an active fibre vertex is the lift of a label, and conversely. -/
theorem exists_lift_eq (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne)
      (limA data hc hab hOne block) = 4)
    {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {e : data.SourceEdge} (he : e ∈ bdAt data contracted X) : ∃ i, lift L i = e := by
  classical
  obtain ⟨hnd', hT⟩ := (mem_bdAt data X e).mp he
  obtain ⟨hSurv, hInc⟩ := (mem_ndAt data X e).mp hnd'
  have hmem : sourceEdgeMap data hc hab hOne ⟨e, hT⟩ ∈
      ndAt (contractDatum data hc hab hOne) (limA data hc hab hOne block) := by
    rw [mem_ndAt]
    refine ⟨fun hBad ↦ hSurv (hCompat.2 ⟨e, hT⟩ hBad), ?_⟩
    have hXmap := ((mem_activeFibreVertices data hc hab hOne _ X).mp hX).1
    unfold Incident
    rw [sourceEnds_sourceEdgeMap]
    rcases hInc with h | h
    · left; rw [h]; exact hXmap
    · right; rw [h]; exact hXmap
  rw [L.ndAt_eq hnd] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_⟩
  have h2 : (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i) = ⟨e, hT⟩ := by
    rw [hi]; exact (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm_apply_apply _
  exact congrArg Subtype.val h2

include hc in
theorem exists_fib_of_lift (hCompat : DanglingCompatible data hc hab hOne) (i : Fin 4) :
    ∃ X ∈ fib data hc hab hOne block, lift L i ∈ bdAt data contracted X := by
  classical
  have hm := (mem_ndAt _ _ _).mp (L.mem i)
  rw [← sourceEdgeMap_lift L i] at hm
  obtain ⟨hSurv, hInc⟩ := hm
  have hSurv' : ¬ IsDangling data (lift L i) := fun hBad ↦ hSurv (hCompat.1 ⟨_, lift_ne L i⟩ hBad)
  unfold Incident at hInc
  rw [sourceEnds_sourceEdgeMap] at hInc
  rcases hInc with h | h
  · refine ⟨(data.sourceEnds (lift L i)).1, ?_, ?_⟩
    · rw [fib, mem_activeFibreVertices]
      exact ⟨h, ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurv' (Or.inl rfl)⟩
    · exact (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨hSurv', Or.inl rfl⟩, lift_ne L i⟩
  · refine ⟨(data.sourceEnds (lift L i)).2, ?_, ?_⟩
    · rw [fib, mem_activeFibreVertices]
      exact ⟨h, ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurv' (Or.inr rfl)⟩
    · exact (mem_bdAt data _ _).mpr ⟨(mem_ndAt data _ _).mpr ⟨hSurv', Or.inr rfl⟩, lift_ne L i⟩

open ValencyThreeGeneral.Split7 in
/-- The label of `e_α` in `Split.simple α4 δ5` (`e₄` if `α4`, else `e₃`). -/
def alphaIdx (α4 : Bool) : Fin 4 := if α4 then 2 else 1
/-- The label of `e_β`, the other simple survivor. -/
def betaIdx (α4 : Bool) : Fin 4 := if α4 then 1 else 2
/-- The label of `e_δ` (`e₅` if `δ5`, else `e₂`). -/
def deltaIdx (δ5 : Bool) : Fin 4 := if δ5 then 3 else 0

open ValencyThreeGeneral.Split7 in
/-- **The split an incoming cover realises** (Part II, Case `{v3-nd4}`), read off its anchor fibre
relative to a labelling `L` of the limit's survivors: base tree `T₂` when `e₂` and `e₅` meet
one constituent over the divalent endpoint `u`; base tree `T_α` with survivor `e_δ` when `e_α`
meets a constituent over `u` and `e_δ` meets a constituent of surviving valency two (the
vertex `A'`). -/
def Reads (u : target.V) : Split → Prop
  | .base₂ => ∃ X ∈ fib data hc hab hOne block, X.1.1 = u ∧ lift L 0 ∈ ndAt data X ∧
      lift L 3 ∈ ndAt data X
  | .simple α4 δ5 => (∃ X ∈ fib data hc hab hOne block, X.1.1 = u ∧
      lift L (alphaIdx α4) ∈ ndAt data X) ∧
      ∃ Z ∈ fib data hc hab hOne block, nonDanglingValency data Z = 2 ∧
        lift L (deltaIdx δ5) ∈ ndAt data Z

section Indices

variable (hNoGlue : DanglingEdgeNoGlue (contractDatum data hc hab hOne))
  (hram : ram (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 1)
  (hnd : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4)

theorem kα_eq (α4 : Bool) :
    (L.indices hNoGlue hram hnd).kα α4 = data.sourceEdgeIndex (lift L (alphaIdx α4)) := by
  cases α4 <;> simp [ValencyThreeGeneral.Split7.AnchorIndices.kα, alphaIdx,
    AnchorLabelling.indices, index_lift]

theorem kβ_eq (α4 : Bool) :
    (L.indices hNoGlue hram hnd).kβ α4 = data.sourceEdgeIndex (lift L (betaIdx α4)) := by
  cases α4 <;> simp [ValencyThreeGeneral.Split7.AnchorIndices.kβ, betaIdx,
    AnchorLabelling.indices, index_lift]

theorem kδ_eq (δ5 : Bool) :
    (L.indices hNoGlue hram hnd).kδ δ5 = data.sourceEdgeIndex (lift L (deltaIdx δ5)) := by
  cases δ5 <;> simp [ValencyThreeGeneral.Split7.AnchorIndices.kδ, deltaIdx,
    AnchorLabelling.indices, index_lift]

theorem A_eq : (L.indices hNoGlue hram hnd).A = anchorSize data block :=
  size_limA data hc hab hOne block

end Indices

variable {u v : target.V}

/-- **Base tree `T₂` is read as `Split.base₂`.** -/
theorem reads_two (P : TwoPicture data hc hab hOne block u v)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4)
    (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) (hu2 : (GluingDatum.incidentEdges u).card = 2) :
    Reads L u .base₂ := by
  classical
  obtain ⟨huw, -, -⟩ := side_of_huv hab huv
  obtain ⟨x, y, hxy, hxyEq⟩ := Finset.card_eq_two.mp P.card_bdAt_R
  have hx : x ∈ bdAt data contracted P.R := by rw [hxyEq]; simp
  have hy : y ∈ bdAt data contracted P.R := by rw [hxyEq]; simp
  obtain ⟨i, hi⟩ := exists_lift_eq L hCompat hnd P.R_mem hx
  obtain ⟨j, hj⟩ := exists_lift_eq L hCompat hnd P.R_mem hy
  have hij : i ≠ j := fun h ↦ hxy (hi.symm.trans (h ▸ hj))
  have hT : (L.e i).1.1 = (L.e j).1.1 := by
    rw [← lift_target_eq_iff, hi, hj]
    exact bdAt_target_eq_of_divalent data hc P.R_over huw hu2 hx hy
  have hmem : ∀ k, lift L k = x ∨ lift L k = y → lift L k ∈ ndAt data P.R := by
    rintro k (h | h)
    · rw [h]; exact ((mem_bdAt data _ _).mp hx).1
    · rw [h]; exact ((mem_bdAt data _ _).mp hy).1
  refine ⟨P.R, P.R_mem, P.R_over, ?_, ?_⟩
  · rcases label_pair_of_target_eq L hij hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem 0 (Or.inl hi)
    · exact hmem 0 (Or.inr hj)
  · rcases label_pair_of_target_eq L hij hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem 3 (Or.inr hj)
    · exact hmem 3 (Or.inl hi)

include fd in
/-- The labels of the boundary occurrences in the three-vertex picture: `A_u`'s is simple,
`A'`'s is over the doubled direction. -/
theorem ThreePicture.labels (P : ThreePicture data hc hab hOne block u v)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4)
    (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) (hv3 : (GluingDatum.incidentEdges v).card = 3) :
    ∃ i j : Fin 4, bdAt data contracted P.R = {lift L i} ∧ bdAt data contracted P.Z = {lift L j} ∧
      (i = 1 ∨ i = 2) ∧ (j = 0 ∨ j = 3) := by
  classical
  obtain ⟨-, hvw, -⟩ := side_of_huv hab huv
  obtain ⟨bR, hbR⟩ := Finset.card_eq_one.mp P.card_bdAt_R
  obtain ⟨bZ, hbZ⟩ := Finset.card_eq_one.mp P.card_bdAt_Z
  have hbRm : bR ∈ bdAt data contracted P.R := by rw [hbR]; exact Finset.mem_singleton_self _
  have hbZm : bZ ∈ bdAt data contracted P.Z := by rw [hbZ]; exact Finset.mem_singleton_self _
  obtain ⟨i, hi⟩ := exists_lift_eq L hCompat hnd P.R_mem hbRm
  obtain ⟨j, hj⟩ := exists_lift_eq L hCompat hnd P.Z_mem hbZm
  refine ⟨i, j, by rw [hbR, hi], by rw [hbZ, hj], ?_, ?_⟩
  · -- `A_u`'s survivor is alone over its direction
    by_contra hbad
    have hi03 : i = 0 ∨ i = 3 := by omega
    set p : Fin 4 := if i = 0 then 3 else 0 with hp
    have hpi : p ≠ i := by rcases hi03 with rfl | rfl <;> simp [hp]
    have hT : (L.e p).1.1 = (L.e i).1.1 := by
      rcases hi03 with rfl | rfl
      · simp only [hp, ite_true]; exact L.dir25.symm
      · simp only [hp]; exact L.dir25
    obtain ⟨X, hX, hpX⟩ := exists_fib_of_lift L hCompat p
    rw [P.fib_eq] at hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    have htR : (lift L i).1.1 ∈ GluingDatum.incidentEdges u := by
      rw [← P.R_over, hi]
      exact target_mem_incidentEdges data ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hbRm).1).2
    have hTl : (lift L p).1.1 = (lift L i).1.1 := (lift_target_eq_iff L p i).mpr hT
    rcases hX with rfl | rfl | rfl
    · rw [hbR, ← hi] at hpX
      exact hpi (lift_injective L (Finset.mem_singleton.mp hpX))
    · have := target_mem_incidentEdges data ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hpX).1).2
      rw [P.Y_over, hTl] at this
      exact not_mem_incidentEdges_other hc hab hOne huv htR (lift_ne L i) this
    · have := target_mem_incidentEdges data ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hpX).1).2
      rw [P.Z_over, hTl] at this
      exact not_mem_incidentEdges_other hc hab hOne huv htR (lift_ne L i) this
  · -- `A'`'s survivor shares its direction with one of `A_v`'s
    obtain ⟨y₁, y₂, hy12, hyEq⟩ := Finset.card_eq_two.mp P.card_bdAt_Y
    have hy₁ : y₁ ∈ bdAt data contracted P.Y := by rw [hyEq]; simp
    have hy₂ : y₂ ∈ bdAt data contracted P.Y := by rw [hyEq]; simp
    have hin : ∀ {X : data.SourceVertex} {e : data.SourceEdge}, e ∈ bdAt data contracted X →
        X.1.1 = v → e.1.1 ∈ GluingDatum.incidentEdges v := fun he hXv ↦ by
      have := target_mem_incidentEdges data ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp he).1).2
      rwa [hXv] at this
    have hT12 : y₁.1.1 ≠ y₂.1.1 := fun h ↦ hy12 (P.Y_distinct fd hy₁ hy₂ h)
    have hcases := eq_or_eq_of_card_three hc hvw hv3 (hin hy₁ P.Y_over) (hin hy₂ P.Y_over)
      (hin hbZm P.Z_over) ((mem_bdAt data _ _).mp hy₁).2 ((mem_bdAt data _ _).mp hy₂).2
      ((mem_bdAt data _ _).mp hbZm).2 hT12
    -- an occurrence at both `A_v` and `A'` would be a loop over `v`
    have hnotboth : ∀ e, e ∈ bdAt data contracted P.Y → e ∈ bdAt data contracted P.Z → False := by
      intro e heY heZ
      have hIY := ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp heY).1).2
      have hIZ := ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp heZ).1).2
      have hloop : (e.1.1 : target.V × target.V).1 = (e.1.1 : target.V × target.V).2 := by
        have h1 : (data.sourceEnds e).1.1.1 = (e.1.1 : target.V × target.V).1 := rfl
        have h2 : (data.sourceEnds e).2.1.1 = (e.1.1 : target.V × target.V).2 := rfl
        rcases hIY with hY | hY <;> rcases hIZ with hZ | hZ
        · exact absurd (hY.symm.trans hZ) P.Y_ne_Z
        · rw [← h1, ← h2, hY, hZ, P.Y_over, P.Z_over]
        · rw [← h1, ← h2, hY, hZ, P.Y_over, P.Z_over]
        · exact absurd (hY.symm.trans hZ) P.Y_ne_Z
      exact target.loopless _ (by
        have hmem : (e.1.1 : target.V × target.V) ∈ target.edges := Multiset.coe_mem
        have hpair : (e.1.1 : target.V × target.V) =
            ((e.1.1 : target.V × target.V).1, (e.1.1 : target.V × target.V).2) := rfl
        rw [hpair, hloop] at hmem
        exact hmem)
    have key : ∀ y, y ∈ bdAt data contracted P.Y → bZ.1.1 = y.1.1 → j = 0 ∨ j = 3 := by
      intro y hy hT
      obtain ⟨j', hj'⟩ := exists_lift_eq L hCompat hnd P.Y_mem hy
      have hne : j ≠ j' := by
        intro h
        subst h
        exact hnotboth bZ (hj ▸ hj' ▸ hy) hbZm
      have hTl : (L.e j).1.1 = (L.e j').1.1 := by
        rw [← lift_target_eq_iff, hj, hj']; exact hT
      rcases label_pair_of_target_eq L hne hTl with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    rcases hcases with h | h
    · exact key y₁ hy₁ h
    · exact key y₂ hy₂ h

open ValencyThreeGeneral.Split7 in
include fd in
/-- **Base tree `T_α` is read as `Split.simple α4 δ5`, and that split is realisable**
(Part II, Case `{v3-nd4}`): `k_δ < k_α` from Case (r1) at `A_u` and Case (r0) at `A'`, and
`k_β + k_δ ≤ |A|` from harmonicity at `A_v` and the sheet accounting at `v`. -/
theorem reads_three (P : ThreePicture data hc hab hOne block u v)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum data hc hab hOne))
    (hram : ram (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 1)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4)
    (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) (hv3 : (GluingDatum.incidentEdges v).card = 3) :
    ∃ α4 δ5 : Bool, Reads L u (.simple α4 δ5) ∧
      (L.indices hNoGlue hram hnd).Valid (.simple α4 δ5) := by
  classical
  obtain ⟨i, j, hR, hZ, hi, hj⟩ := P.labels fd L hCompat hnd huv hv3
  set α4 : Bool := decide (i = 2) with hα4
  set δ5 : Bool := decide (j = 3) with hδ5
  have hαi : alphaIdx α4 = i := by
    rcases hi with rfl | rfl <;> simp [hα4, alphaIdx]
  have hδj : deltaIdx δ5 = j := by
    rcases hj with rfl | rfl <;> simp [hδ5, deltaIdx]
  have hβ : betaIdx α4 ≠ i ∧ betaIdx α4 ≠ j ∧ (betaIdx α4 = 1 ∨ betaIdx α4 = 2) := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp [hα4, betaIdx]
  have hαR : lift L (alphaIdx α4) ∈ bdAt data contracted P.R := by
    rw [hR, hαi]; exact Finset.mem_singleton_self _
  have hδZ : lift L (deltaIdx δ5) ∈ bdAt data contracted P.Z := by
    rw [hZ, hδj]; exact Finset.mem_singleton_self _
  -- `e_β` sits at `A_v`
  have hβY : lift L (betaIdx α4) ∈ bdAt data contracted P.Y := by
    obtain ⟨X, hX, hβX⟩ := exists_fib_of_lift L hCompat (betaIdx α4)
    rw [P.fib_eq] at hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · rw [hR] at hβX
      exact absurd (lift_injective L (Finset.mem_singleton.mp hβX)) hβ.1
    · exact hβX
    · rw [hZ] at hβX
      exact absurd (lift_injective L (Finset.mem_singleton.mp hβX)) hβ.2.1
  refine ⟨α4, δ5, ⟨⟨P.R, P.R_mem, P.R_over, ((mem_bdAt data _ _).mp hαR).1⟩,
    P.Z, P.Z_mem, P.Z_nd, ((mem_bdAt data _ _).mp hδZ).1⟩, ?_⟩
  -- the local equations
  obtain ⟨hr1a, hr1b⟩ := P.r1 fd
  obtain ⟨hr0a, hr0b⟩ := P.r0_Z fd
  rw [hR, Finset.sum_singleton, ← hαi] at hr1b
  rw [hZ, Finset.sum_singleton, ← hδj] at hr0b
  have hpos := StableLocalProperties.sourceEdgeIndex_pos data P.e₁
  have hβle := index_le_size data ((mem_bdAt data _ _).mp hβY).1
  have hsheets := P.size_Y_add_size_Z
  change (L.indices hNoGlue hram hnd).kδ δ5 < (L.indices hNoGlue hram hnd).kα α4 ∧
    (L.indices hNoGlue hram hnd).kβ α4 + (L.indices hNoGlue hram hnd).kδ δ5 ≤
      (L.indices hNoGlue hram hnd).A
  rw [kα_eq, kβ_eq, kδ_eq, A_eq]
  constructor
  · have : (data.sourceEdgeIndex (lift L (deltaIdx δ5)) : ℤ) <
        data.sourceEdgeIndex (lift L (alphaIdx α4)) := by
      linarith
    exact_mod_cast this
  · have : (data.sourceEdgeIndex (lift L (betaIdx α4)) : ℤ) +
        data.sourceEdgeIndex (lift L (deltaIdx δ5)) ≤ anchorSize data block := by
      have hs : ((size data P.Y + size data P.Z : ℕ) : ℤ) ≤ anchorSize data block := by
        exact_mod_cast hsheets
      push_cast at hs
      linarith
    exact_mod_cast this

theorem alphaIdx_injective : Function.Injective alphaIdx := by
  intro x y h; cases x <;> cases y <;> simp_all [alphaIdx]

theorem deltaIdx_injective : Function.Injective deltaIdx := by
  intro x y h; cases x <;> cases y <;> simp_all [deltaIdx]

open ValencyThreeGeneral.Split7 in
/-- In the two-vertex picture the only reading is `base₂`. -/
theorem TwoPicture.reads_eq (P : TwoPicture data hc hab hOne block u v) {s : Split}
    (hs : Reads L u s) : s = .base₂ := by
  rcases s with _ | ⟨α4, δ5⟩
  · rfl
  · exfalso
    obtain ⟨-, Z, hZ, hZ2, -⟩ := hs
    rw [P.fib_eq] at hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · rw [P.R_nd] at hZ2; exact absurd hZ2 (by norm_num)
    · rw [P.Y_nd] at hZ2; exact absurd hZ2 (by norm_num)

open ValencyThreeGeneral.Split7 in
include fd in
/-- In the three-vertex picture the reading is unique. -/
theorem ThreePicture.reads_eq (P : ThreePicture data hc hab hOne block u v)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4)
    (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) (hv3 : (GluingDatum.incidentEdges v).card = 3)
    {s s' : Split} (hs : Reads L u s) (hs' : Reads L u s') : s = s' := by
  classical
  obtain ⟨-, -, huv'⟩ := side_of_huv hab huv
  obtain ⟨i, j, hR, hZ, -, -⟩ := P.labels fd L hCompat hnd huv hv3
  -- a constituent over `u` is `A_u`
  have hXu : ∀ X ∈ fib data hc hab hOne block, X.1.1 = u → X = P.R := by
    intro X hX hXu
    rw [P.fib_eq] at hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · rfl
    · exact absurd (hXu.symm.trans P.Y_over) huv'
    · exact absurd (hXu.symm.trans P.Z_over) huv'
  -- a divalent constituent is `A'`
  have hX2 : ∀ X ∈ fib data hc hab hOne block, nonDanglingValency data X = 2 → X = P.Z := by
    intro X hX hX2
    rw [P.fib_eq] at hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · rw [P.R_nd] at hX2; exact absurd hX2 (by norm_num)
    · rw [P.Y_nd] at hX2; exact absurd hX2 (by norm_num)
    · rfl
  have hbd : ∀ (X : data.SourceVertex) (k : Fin 4), lift L k ∈ ndAt data X →
      lift L k ∈ bdAt data contracted X := fun X k h ↦ (mem_bdAt data _ _).mpr ⟨h, lift_ne L k⟩
  have hαR : ∀ α4 δ5, Reads L u (.simple α4 δ5) → alphaIdx α4 = i ∧ deltaIdx δ5 = j := by
    rintro α4 δ5 ⟨⟨X, hX, hXu', hαX⟩, Z, hZm, hZ2, hδZ⟩
    rw [hXu X hX hXu'] at hαX
    rw [hX2 Z hZm hZ2] at hδZ
    have h1 := hbd _ _ hαX
    have h2 := hbd _ _ hδZ
    rw [hR] at h1
    rw [hZ] at h2
    exact ⟨lift_injective L (Finset.mem_singleton.mp h1),
      lift_injective L (Finset.mem_singleton.mp h2)⟩
  have hnot₂ : ¬ Reads L u .base₂ := by
    rintro ⟨X, hX, hXu', h0, h3⟩
    rw [hXu X hX hXu'] at h0 h3
    have h0' := hbd _ _ h0
    have h3' := hbd _ _ h3
    rw [hR] at h0' h3'
    have := lift_injective L ((Finset.mem_singleton.mp h0').trans (Finset.mem_singleton.mp h3').symm)
    exact absurd this (by decide)
  rcases s with _ | ⟨α4, δ5⟩
  · exact absurd hs hnot₂
  rcases s' with _ | ⟨α4', δ5'⟩
  · exact absurd hs' hnot₂
  obtain ⟨ha, hd⟩ := hαR α4 δ5 hs
  obtain ⟨ha', hd'⟩ := hαR α4' δ5' hs'
  rw [alphaIdx_injective (ha.trans ha'.symm), deltaIdx_injective (hd.trans hd'.symm)]

end Reading

/-! ## 7.  The split of a cover, and its determination by the type -/

section Determination

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)

/-- **The inputs of the anchor analysis at one incoming cover.**

Interface: exactly the hypotheses of `NonTrivalentValencyThreeRigidity.threeBranchAnchor`
(the `ThreeStar` replaced by its defining cardinality, `ThreeStar.of_card`); every field is
an existing predicate, and at an actual facet `nd4` is produced by
`NonTrivalentAnchorValency.exists_wallBlock_nonDanglingValency_eq_four_of_threeStar`. -/
structure AnchorInput : Prop where
  forest : ContractionForest data a b contracted
  valency : (GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩).card = 3
  nd4 : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4

/-- The divalent endpoint `u` of the contracted occurrence. -/
noncomputable def divEnd (a b : target.V) : target.V := by
  classical
  exact if (GluingDatum.incidentEdges a).card = 2 then a else b

/-- The trivalent endpoint `v`. -/
noncomputable def triEnd (a b : target.V) : target.V := by
  classical
  exact if (GluingDatum.incidentEdges a).card = 2 then b else a

namespace AnchorInput

variable {data hc hab hOne block}

theorem compat (H : AnchorInput data hc hab hOne block) : DanglingCompatible data hc hab hOne :=
  WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne H.forest

/-- The trivalent wall's star. -/
noncomputable def star (H : AnchorInput data hc hab hOne block) :
    ThirdEquation.ThreeStar (contract target hab hOne) ⟨a, hab⟩ :=
  ThirdEquation.ThreeStar.of_card H.valency

theorem noGlue (H : AnchorInput data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    DanglingEdgeNoGlue (contractDatum data hc hab hOne) :=
  danglingEdgeNoGlue_contractDatum data H.compat.2 fd.danglingEdgeNoGlue

/-- `lemma-above-w0`: the anchor carries the unit of ramification. -/
theorem ram_one (H : AnchorInput data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    ram (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 1 :=
  NonTrivalentValencyThreeRigidity.localRamification_eq_one data fd hc hab hOne H.forest
    H.compat H.star block H.nd4

/-- The valency split of the wall: `u` divalent with change one, `v` trivalent with change
zero. -/
theorem sides (H : AnchorInput data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    ((divEnd a b = a ∧ triEnd a b = b) ∨ (divEnd a b = b ∧ triEnd a b = a)) ∧
      (GluingDatum.incidentEdges (divEnd a b)).card = 2 ∧
      (GluingDatum.incidentEdges (triEnd a b)).card = 3 ∧
      data.targetChange (divEnd a b) = 1 ∧ data.targetChange (triEnd a b) = 0 := by
  classical
  rcases ThirdEquation.valencySplit_of_threeStar data hc hab hOne fd.valid fd.changeMinimal
    H.star with ⟨h2, h3, h1, h0⟩ | ⟨h3, h2, h0, h1⟩
  · have hu : divEnd a b = a := by simp only [divEnd, h2, ite_true]
    have hv : triEnd a b = b := by simp only [triEnd, h2, ite_true]
    rw [hu, hv]
    exact ⟨Or.inl ⟨rfl, rfl⟩, h2, h3, h1, h0⟩
  · have hne : (GluingDatum.incidentEdges a).card ≠ 2 := by omega
    have hu : divEnd a b = b := by simp only [divEnd, hne, ite_false]
    have hv : triEnd a b = a := by simp only [triEnd, hne, ite_false]
    rw [hu, hv]
    exact ⟨Or.inr ⟨rfl, rfl⟩, h2, h3, h1, h0⟩

end AnchorInput

variable (fd : FullDimensionalSourcePresentation data coordinate)
variable {data hc hab hOne block}

open ValencyThreeGeneral.Split7 in
/-- **Stages 1 and 2, joined: the split of an arbitrary incoming cover.**  At every incoming
cover of a valency-three anchor, relative to any labelling `L` of the limit's survivors,
exactly one split is read off the cover (`Reads`), and it is realisable for the limit's anchor
indices (`AnchorIndices.Valid`). -/
theorem existsUnique_reads (H : AnchorInput data hc hab hOne block)
    (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block)) :
    ∃ s : Split, Reads L (divEnd a b) s ∧
      (L.indices (H.noGlue fd) (H.ram_one fd) H.nd4).Valid s ∧
      ∀ s', Reads L (divEnd a b) s' → s' = s := by
  classical
  obtain ⟨huv, hu2, hv3, hchu, hchv⟩ := H.sides fd
  rcases shape data fd hc hab hOne block (divEnd a b) (triEnd a b) H.forest H.compat H.nd4 huv
    hu2 hchu hchv with ⟨⟨P⟩⟩ | ⟨⟨P⟩⟩
  · exact ⟨.base₂, reads_two L P H.compat H.nd4 huv hu2, trivial,
      fun s' hs' ↦ P.reads_eq L hs'⟩
  · obtain ⟨α4, δ5, hr, hv⟩ := reads_three fd L P H.compat (H.noGlue fd) (H.ram_one fd) H.nd4
      huv hv3
    exact ⟨.simple α4 δ5, hr, hv, fun s' hs' ↦ P.reads_eq fd L H.compat H.nd4 huv hv3 hs' hr⟩

open ValencyThreeGeneral.Split7 in
/-- Every split read off a cover is realisable. -/
theorem valid_of_reads (H : AnchorInput data hc hab hOne block)
    (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    {s : Split} (hs : Reads L (divEnd a b) s) :
    (L.indices (H.noGlue fd) (H.ram_one fd) H.nd4).Valid s := by
  obtain ⟨s₀, -, hv, huniq⟩ := existsUnique_reads fd H L
  rw [huniq s hs]
  exact hv

/-- The anchor as a wall block of the limit. -/
def anchorWallBlock : W4Assembly.WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩ :=
  ⟨block.1, by rw [contractDatum_vertexPartition_merge]; exact block.2⟩

theorem sourceVertex_anchorWallBlock :
    WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ (anchorWallBlock (hc := hc) (hab := hab) (hOne := hOne) (block := block)) =
      limA data hc hab hOne block := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (anchorWallBlock (hc := hc) (hab := hab) (hOne := hOne) (block := block)).2

include fd in
/-- **The anchor is the limit's only vertex of surviving valency four** (Part II, subsection
*Combinatorial setup and local determinants*):
another wall block is rigid (`lemma-above-w0`), and a vertex away from the wall keeps its
incoming surviving valency. -/
theorem eq_limA_of_nonDanglingValency_eq_four (H : AnchorInput data hc hab hOne block)
    (X : (contractDatum data hc hab hOne).SourceVertex)
    (hX : nonDanglingValency (contractDatum data hc hab hOne) X = 4) :
    X = limA data hc hab hOne block := by
  classical
  by_cases hXw : X.1.1 = ⟨a, hab⟩
  · have hrepr : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).repr X.1.2 = X.1.2 := by
      have := X.2
      rw [hXw] at this
      exact this
    let B : W4Assembly.WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩ := ⟨X.1.2, hrepr⟩
    have hB : WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ B = X := by
      apply Subtype.ext
      apply Prod.ext
      · exact hXw.symm
      · exact hrepr
    by_cases hRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
        (anchorWallBlock (hc := hc) (hab := hab) (hOne := hOne) (block := block)).1 B.1
    · rw [SheetPartition.rel_iff, (anchorWallBlock (hc := hc) (hab := hab) (hOne := hOne) (block := block)).2, hrepr] at hRel
      apply Subtype.ext
      apply Prod.ext
      · exact hXw
      · exact hRel.symm
    · exfalso
      have hle := NonTrivalentAnchorValency.nonDanglingValency_wallBlock_le_three_of_threeStar
        data fd hc hab hOne H.star H.forest (anchorWallBlock (hc := hc) (hab := hab) (hOne := hOne) (block := block))
        (by rw [sourceVertex_anchorWallBlock]; exact H.nd4) B hRel
      rw [hB, hX] at hle
      omega
  · exfalso
    obtain ⟨Y, rfl⟩ := sourceVertexMap_surjective data hc hab hOne X
    have hYa : Y.1.1 ≠ a := fun h ↦ hXw (ContractionFibre.fold_eq_of_eq_or hab (Or.inl h))
    have hYb : Y.1.1 ≠ b := fun h ↦ hXw (ContractionFibre.fold_eq_of_eq_or hab (Or.inr h))
    rw [nonDanglingValency_sourceVertexMap data H.compat Y hYa hYb] at hX
    have := fd.trivalent Y
    omega

include fd in
/-- **A labelling of the limit's survivors exists** at every valency-three anchor of an
incoming cover (the `2 + 1 + 1` pattern, read off the two pictures). -/
theorem nonempty_anchorLabelling (H : AnchorInput data hc hab hOne block) :
    Nonempty (AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block)) := by
  classical
  obtain ⟨huv, hu2, hv3, hchu, hchv⟩ := H.sides fd
  obtain ⟨huw, hvw, -⟩ := side_of_huv hab huv
  have hT : ∀ {X : data.SourceVertex} {e : data.SourceEdge}, e ∈ bdAt data contracted X →
      e.1.1 ∈ GluingDatum.incidentEdges X.1.1 := fun he ↦
    target_mem_incidentEdges data ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp he).1).2
  have hN : ∀ {X : data.SourceVertex} {e : data.SourceEdge}, e ∈ bdAt data contracted X →
      e.1.1 ≠ contracted := fun he ↦ ((mem_bdAt data _ _).mp he).2
  -- a `u`-side target is never a `v`-side target
  have hUV : ∀ {X Y : data.SourceVertex} {e f : data.SourceEdge}, X.1.1 = divEnd a b →
      Y.1.1 = triEnd a b → e ∈ bdAt data contracted X → f ∈ bdAt data contracted Y →
      f.1.1 ≠ e.1.1 := by
    intro X Y e f hX hY he hf hEq
    have h1 := hT he
    have h2 := hT hf
    rw [hX] at h1
    rw [hY, hEq] at h2
    exact not_mem_incidentEdges_other hc hab hOne huv h1 (hN he) h2
  have img : ∀ {X : data.SourceVertex} {e : data.SourceEdge}, X ∈ fib data hc hab hOne block →
      (he : e ∈ bdAt data contracted X) →
      sourceEdgeMap data hc hab hOne ⟨e, hN he⟩ ∈
        ndAt (contractDatum data hc hab hOne) (limA data hc hab hOne block) :=
    fun hX he ↦ sourceEdgeMap_mem_ndAt H.compat hX he
  have hne : ∀ {e f : data.SourceEdge} (he : e.1.1 ≠ contracted) (hf : f.1.1 ≠ contracted),
      e ≠ f → sourceEdgeMap data hc hab hOne ⟨e, he⟩ ≠ sourceEdgeMap data hc hab hOne ⟨f, hf⟩ :=
    fun he hf h h' ↦ h (congrArg Subtype.val (sourceEdgeMap_injective data hc hab hOne h'))
  rcases shape data fd hc hab hOne block (divEnd a b) (triEnd a b) H.forest H.compat H.nd4 huv
    hu2 hchu hchv with ⟨⟨P⟩⟩ | ⟨⟨P⟩⟩
  · obtain ⟨x, y, hxy, hxyEq⟩ := Finset.card_eq_two.mp P.card_bdAt_R
    obtain ⟨p, q, hpq, hpqEq⟩ := Finset.card_eq_two.mp P.card_bdAt_Y
    have hx : x ∈ bdAt data contracted P.R := by rw [hxyEq]; simp
    have hy : y ∈ bdAt data contracted P.R := by rw [hxyEq]; simp
    have hp : p ∈ bdAt data contracted P.Y := by rw [hpqEq]; simp
    have hq : q ∈ bdAt data contracted P.Y := by rw [hpqEq]; simp
    exact AnchorLabelling.nonempty_of_four _ _ _ _ (img P.R_mem hx) (img P.Y_mem hp)
      (img P.Y_mem hq) (img P.R_mem hy) (hne _ _ hxy)
      ((sourceEdgeMap_target_eq_iff _ _).mpr
        (bdAt_target_eq_of_divalent data hc P.R_over huw hu2 hx hy))
      (fun h ↦ hUV P.R_over P.Y_over hx hp ((sourceEdgeMap_target_eq_iff _ _).mp h))
      (fun h ↦ hUV P.R_over P.Y_over hx hq ((sourceEdgeMap_target_eq_iff _ _).mp h))
      (fun h ↦ hpq (P.Y_distinct fd hp hq ((sourceEdgeMap_target_eq_iff _ _).mp h)))
  · obtain ⟨bR, hbR⟩ := Finset.card_eq_one.mp P.card_bdAt_R
    obtain ⟨bZ, hbZ⟩ := Finset.card_eq_one.mp P.card_bdAt_Z
    obtain ⟨y₁, y₂, hy12, hyEq⟩ := Finset.card_eq_two.mp P.card_bdAt_Y
    have hbRm : bR ∈ bdAt data contracted P.R := by rw [hbR]; exact Finset.mem_singleton_self _
    have hbZm : bZ ∈ bdAt data contracted P.Z := by rw [hbZ]; exact Finset.mem_singleton_self _
    have hy₁ : y₁ ∈ bdAt data contracted P.Y := by rw [hyEq]; simp
    have hy₂ : y₂ ∈ bdAt data contracted P.Y := by rw [hyEq]; simp
    have hTv : ∀ {X : data.SourceVertex} {e : data.SourceEdge}, X.1.1 = triEnd a b →
        e ∈ bdAt data contracted X → e.1.1 ∈ GluingDatum.incidentEdges (triEnd a b) :=
      fun hX he ↦ hX ▸ hT he
    have hT12 : y₁.1.1 ≠ y₂.1.1 := fun h ↦ hy12 (P.Y_distinct fd hy₁ hy₂ h)
    have hZY : ∀ {y : data.SourceEdge}, y ∈ bdAt data contracted P.Y → bZ ≠ y := by
      intro y hy h
      subst h
      exact not_incident_both data P.Y_ne_Z (P.Y_over.trans P.Z_over.symm)
        ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hy).1).2
        ((mem_ndAt data _ _).mp ((mem_bdAt data _ _).mp hbZm).1).2
    have build : ∀ γ β : data.SourceEdge, γ ∈ bdAt data contracted P.Y →
        β ∈ bdAt data contracted P.Y → γ.1.1 ≠ β.1.1 → bZ.1.1 = γ.1.1 →
        Nonempty (AnchorLabelling (contractDatum data hc hab hOne)
          (limA data hc hab hOne block)) := by
      intro γ β hγ hβ hγβ hZγ
      exact AnchorLabelling.nonempty_of_four _ _ _ _ (img P.Z_mem hbZm) (img P.R_mem hbRm)
        (img P.Y_mem hβ) (img P.Y_mem hγ) (hne _ _ (hZY hγ))
        ((sourceEdgeMap_target_eq_iff _ _).mpr hZγ)
        (fun h ↦ hUV P.R_over P.Z_over hbRm hbZm ((sourceEdgeMap_target_eq_iff _ _).mp h).symm)
        (fun h ↦ hγβ (hZγ.symm.trans ((sourceEdgeMap_target_eq_iff _ _).mp h).symm))
        (fun h ↦ hUV P.R_over P.Y_over hbRm hβ ((sourceEdgeMap_target_eq_iff _ _).mp h).symm)
    rcases eq_or_eq_of_card_three hc hvw hv3 (hTv P.Y_over hy₁) (hTv P.Y_over hy₂)
      (hTv P.Z_over hbZm) (hN hy₁) (hN hy₂) (hN hbZm) hT12 with h | h
    · exact build y₁ y₂ hy₁ hy₂ hT12 h
    · exact build y₂ y₁ hy₂ hy₁ (Ne.symm hT12) h

open ValencyThreeGeneral.Split7 in
include fd in
/-- **The base-`T₂` criterion.**  If the contracted occurrence's sheet partition is the
divalent endpoint's vertex partition, every constituent over `u` carries exactly one
occurrence over the contracted target occurrence; the three-vertex picture is impossible, and
the cover reads `base₂` (type III). -/
theorem reads_base₂_of_edgePartition_eq (H : AnchorInput data hc hab hOne block)
    (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (hEq : data.edgePartition contracted = data.vertexPartition (divEnd a b)) :
    Reads L (divEnd a b) .base₂ := by
  classical
  obtain ⟨huv, hu2, hv3, hchu, hchv⟩ := H.sides fd
  rcases shape data fd hc hab hOne block (divEnd a b) (triEnd a b) H.forest H.compat H.nd4 huv
    hu2 hchu hchv with ⟨⟨P⟩⟩ | ⟨⟨P⟩⟩
  · exact reads_two L P H.compat H.nd4 huv hu2
  · exfalso
    have key : ∀ e, e ∈ ndAt data P.R → e.1.1 = contracted → e.1.2 = P.R.1.2 := by
      intro e he hT
      have hRel := ((incident_iff_target_mem_and_rel data e P.R).mp
        ((mem_ndAt data _ _).mp he).2).2
      have hrep : (data.vertexPartition (divEnd a b)).repr e.1.2 = e.1.2 := by
        rw [← hEq, ← hT]; exact e.2
      rw [P.R_over, SheetPartition.rel_iff, hrep] at hRel
      have hR := P.R.2
      rw [P.R_over] at hR
      rw [← hRel, hR]
    apply P.e₁_ne
    apply Subtype.ext
    apply Prod.ext
    · exact P.e₁_target.trans P.e'_target.symm
    · exact (key _ P.e₁_R P.e₁_target).trans (key _ P.e'_R P.e'_target).symm

/-! ### The type, intrinsically: which survivor `e₂` is paired with -/

/-- **Two labelled survivors lie at one vertex of the incoming stable graph** at the anchor:
at one active constituent, or at two joined by a surviving internal occurrence with a divalent
end (smoothed away in the stable graph).  This is the combinatorial type `H_{2,β}` of Part
II's Case `{v3-nd4}`: `e₂` is paired with `e_β`. -/
def Paired (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (i j : Fin 4) : Prop :=
  ∃ X ∈ fib data hc hab hOne block, ∃ X' ∈ fib data hc hab hOne block,
    lift L i ∈ ndAt data X ∧ lift L j ∈ ndAt data X' ∧
      (X = X' ∨ ∃ e ∈ intl data hc hab hOne block, e ∈ ndAt data X ∧ e ∈ ndAt data X' ∧
        (nonDanglingValency data X = 2 ∨ nonDanglingValency data X' = 2))

open ValencyThreeGeneral.Split7 in
/-- The label paired with `e₂` in each type: `e₃`, `e₄`, `e₅` for Types I, II, III. -/
def typePartner : VType → Fin 4
  | .I => 1
  | .II => 2
  | .III => 3

open ValencyThreeGeneral.Split7 in
theorem typePartner_injective : Function.Injective typePartner := by
  intro x y h; cases x <;> cases y <;> simp_all [typePartner]

open ValencyThreeGeneral.Split7 in
theorem typePartner_ne_zero (t : VType) : typePartner t ≠ 0 := by
  cases t <;> decide

include hc hab hOne in
/-- **A boundary occurrence has one home in the fibre**: its other end lies over a vertex
off the contracted occurrence. -/
theorem home_unique {e : data.SourceEdge} (hT : e.1.1 ≠ contracted) {X X' : data.SourceVertex}
    (hX : X ∈ fib data hc hab hOne block) (hX' : X' ∈ fib data hc hab hOne block)
    (hi : Incident data e X) (hi' : Incident data e X') : X = X' := by
  classical
  by_contra hne
  obtain ⟨hXw, -, -⟩ := (mem_fib_iff data hc hab hOne block X).mp hX
  obtain ⟨hX'w, -, -⟩ := (mem_fib_iff data hc hab hOne block X').mp hX'
  have h1 : (data.sourceEnds e).1.1.1 = (e.1.1 : target.V × target.V).1 := rfl
  have h2 : (data.sourceEnds e).2.1.1 = (e.1.1 : target.V × target.V).2 := rfl
  have hends : ((e.1.1 : target.V × target.V).1 = X.1.1 ∧ (e.1.1 : target.V × target.V).2 = X'.1.1) ∨
      ((e.1.1 : target.V × target.V).1 = X'.1.1 ∧ (e.1.1 : target.V × target.V).2 = X.1.1) := by
    rcases hi with h | h <;> rcases hi' with h' | h'
    · exact absurd (h.symm.trans h') hne
    · left; rw [← h1, ← h2, h, h']; exact ⟨rfl, rfl⟩
    · right; rw [← h1, ← h2, h, h']; exact ⟨rfl, rfl⟩
    · exact absurd (h.symm.trans h') hne
  have hmem : (e.1.1 : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  have hloop : (e.1.1 : target.V × target.V).1 ≠ (e.1.1 : target.V × target.V).2 := by
    intro h
    apply target.loopless (e.1.1 : target.V × target.V).1
    have hpair : (e.1.1 : target.V × target.V) =
        ((e.1.1 : target.V × target.V).1, (e.1.1 : target.V × target.V).2) := rfl
    rw [hpair, ← h] at hmem
    exact hmem
  have hpair : (e.1.1 : target.V × target.V) = (a, b) ∨ (e.1.1 : target.V × target.V) = (b, a) := by
    have hp : (e.1.1 : target.V × target.V) =
        ((e.1.1 : target.V × target.V).1, (e.1.1 : target.V × target.V).2) := rfl
    rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hXw with hx | hx <;> rcases hX'w with hy | hy
    · exact absurd (e1.trans (hx.trans (hy.symm.trans e2.symm))) hloop
    · left; rw [hp, e1, e2, hx, hy]
    · right; rw [hp, e1, e2, hx, hy]
    · exact absurd (e1.trans (hx.trans (hy.symm.trans e2.symm))) hloop
    · exact absurd (e1.trans (hy.trans (hx.symm.trans e2.symm))) hloop
    · right; rw [hp, e1, e2, hx, hy]
    · left; rw [hp, e1, e2, hx, hy]
    · exact absurd (e1.trans (hy.trans (hx.symm.trans e2.symm))) hloop
  rcases hpair with h | h
  · exact hT (eq_contracted_of_coe_eq_pair hc hOne h)
  · exact notMem_swapped hc hab hOne (h ▸ hmem)

open ValencyThreeGeneral.Split7 in
include fd in
/-- **The type is the pairing of `e₂`** (Part II, Case `{v3-nd4}`): for the split read off a cover,
`e₂` lies at one incoming stable vertex with exactly the survivor `typePartner s.type`
(`e₃`, `e₄`, `e₅` for Types I, II, III).  So "same type" in `split_eq_of_limitIso` is the
intrinsic combinatorial type `H_{2,β}` of the incoming stable graph at the anchor, read on
transported labels. -/
theorem paired_iff (H : AnchorInput data hc hab hOne block)
    (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    {s : Split} (hs : Reads L (divEnd a b) s) (k : Fin 4) (hk : k ≠ 0) :
    Paired L 0 k ↔ k = typePartner s.type := by
  classical
  obtain ⟨huv, hu2, hv3, hchu, hchv⟩ := H.sides fd
  obtain ⟨-, -, huv'⟩ := side_of_huv hab huv
  have hbd : ∀ {X : data.SourceVertex} {m : Fin 4}, lift L m ∈ ndAt data X →
      lift L m ∈ bdAt data contracted X := fun h ↦ (mem_bdAt data _ _).mpr ⟨h, lift_ne L _⟩
  -- the home of a label is unique
  have hhome : ∀ {X X' : data.SourceVertex} {m : Fin 4}, X ∈ fib data hc hab hOne block →
      X' ∈ fib data hc hab hOne block → lift L m ∈ ndAt data X → lift L m ∈ ndAt data X' →
      X = X' := fun hX hX' h h' ↦ home_unique (lift_ne L _) hX hX'
        ((mem_ndAt data _ _).mp h).2 ((mem_ndAt data _ _).mp h').2
  rcases shape data fd hc hab hOne block (divEnd a b) (triEnd a b) H.forest H.compat H.nd4 huv
    hu2 hchu hchv with ⟨⟨P⟩⟩ | ⟨⟨P⟩⟩
  · -- base tree `T₂`: `e₂, e₅` at `A_u`, `e₃, e₄` at `A_v`
    obtain rfl := P.reads_eq L hs
    obtain ⟨X, hX, hXu, h0, h3⟩ := reads_two L P H.compat H.nd4 huv hu2
    have hXR : X = P.R := by
      rw [P.fib_eq] at hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl
      · rfl
      · exact absurd (hXu.symm.trans P.Y_over) huv'
    rw [hXR] at h0 h3
    have hne03 : lift L 0 ≠ lift L 3 := fun h ↦ absurd (lift_injective L h) (by decide)
    have hbdR : bdAt data contracted P.R = {lift L 0, lift L 3} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hbd h0
        · rw [Finset.mem_singleton.mp he]; exact hbd h3
      · rw [P.card_bdAt_R, Finset.card_pair hne03]
    have hatR : ∀ m, lift L m ∈ ndAt data P.R → m = 0 ∨ m = 3 := by
      intro m hm
      have := hbd hm
      rw [hbdR] at this
      rcases Finset.mem_insert.mp this with h | h
      · exact Or.inl (lift_injective L h)
      · exact Or.inr (lift_injective L (Finset.mem_singleton.mp h))
    change Paired L 0 k ↔ k = 3
    constructor
    · rintro ⟨X₁, hX₁, X₂, hX₂, h₁, h₂, hj⟩
      have h1R := hhome hX₁ P.R_mem h₁ h0
      subst h1R
      rcases hj with rfl | ⟨e, -, -, -, hdiv⟩
      · rcases hatR k h₂ with h | h
        · exact absurd h hk
        · exact h
      · exfalso
        rw [P.fib_eq] at hX₂
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX₂
        rcases hX₂ with rfl | rfl <;> rcases hdiv with h | h
        all_goals first
          | (rw [P.R_nd] at h; exact absurd h (by norm_num))
          | (rw [P.Y_nd] at h; exact absurd h (by norm_num))
    · intro hk3
      rw [hk3]
      exact ⟨P.R, P.R_mem, P.R, P.R_mem, h0, h3, Or.inl rfl⟩
  · -- base tree `T_α`
    obtain ⟨i, j₀, hR, hZ, hi, hj₀⟩ := P.labels fd L H.compat H.nd4 huv hv3
    have hatR : ∀ m, lift L m ∈ ndAt data P.R → m = i := by
      intro m hm
      have := hbd hm
      rw [hR] at this
      exact lift_injective L (Finset.mem_singleton.mp this)
    have hatZ : ∀ m, lift L m ∈ ndAt data P.Z → m = j₀ := by
      intro m hm
      have := hbd hm
      rw [hZ] at this
      exact lift_injective L (Finset.mem_singleton.mp this)
    have hatY : ∀ m, m ≠ i → m ≠ j₀ → lift L m ∈ ndAt data P.Y := by
      intro m hmi hmj
      obtain ⟨X, hX, hmX⟩ := exists_fib_of_lift L H.compat m
      have hmX' := ((mem_bdAt data _ _).mp hmX).1
      rw [P.fib_eq] at hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      rcases hX with rfl | rfl | rfl
      · exact absurd (hatR m hmX') hmi
      · exact hmX'
      · exact absurd (hatZ m hmX') hmj
    have hYZ : ∀ e, e ∈ ndAt data P.Y → e ∈ ndAt data P.Z → False := fun e hY hZ' ↦
      not_incident_both data P.Y_ne_Z (P.Y_over.trans P.Z_over.symm)
        ((mem_ndAt data _ _).mp hY).2 ((mem_ndAt data _ _).mp hZ').2
    -- the read split
    have hsR : Reads L (divEnd a b) (.simple (decide (i = 2)) (decide (j₀ = 3))) := by
      refine ⟨⟨P.R, P.R_mem, P.R_over, ?_⟩, P.Z, P.Z_mem, P.Z_nd, ?_⟩
      · have : alphaIdx (decide (i = 2)) = i := by rcases hi with rfl | rfl <;> simp [alphaIdx]
        rw [this]
        exact ((mem_bdAt data _ _).mp (by rw [hR]; exact Finset.mem_singleton_self _)).1
      · have : deltaIdx (decide (j₀ = 3)) = j₀ := by
          rcases hj₀ with rfl | rfl <;> simp [deltaIdx]
        rw [this]
        exact ((mem_bdAt data _ _).mp (by rw [hZ]; exact Finset.mem_singleton_self _)).1
    obtain rfl := P.reads_eq fd L H.compat H.nd4 huv hv3 hs hsR
    rcases hj₀ with rfl | rfl
    · -- `δ = 2`: `e₂` at `A'`, paired with `e_α` across `e'`
      have h0Z : lift L 0 ∈ ndAt data P.Z := by
        exact ((mem_bdAt data _ _).mp (by rw [hZ]; exact Finset.mem_singleton_self _)).1
      have hpart : typePartner (Split.simple (decide (i = 2)) (decide ((0 : Fin 4) = 3))).type = i := by
        rcases hi with rfl | rfl <;> rfl
      rw [hpart]
      constructor
      · rintro ⟨X₁, hX₁, X₂, hX₂, h₁, h₂, hj⟩
        have h1Z := hhome hX₁ P.Z_mem h₁ h0Z
        subst h1Z
        rw [P.fib_eq] at hX₂
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX₂
        rcases hX₂ with rfl | rfl | rfl
        · exact hatR k h₂
        · exfalso
          rcases hj with h | ⟨e, -, heZ, heY, -⟩
          · exact P.Y_ne_Z h.symm
          · exact hYZ e heY heZ
        · exact absurd (hatZ k h₂) hk
      · intro hki
        rw [hki]
        have hiR : lift L i ∈ ndAt data P.R :=
          ((mem_bdAt data _ _).mp (by rw [hR]; exact Finset.mem_singleton_self _)).1
        exact ⟨P.Z, P.Z_mem, P.R, P.R_mem, h0Z, hiR,
          Or.inr ⟨P.e', P.e'_mem, P.e'_Z, P.e'_R, Or.inl P.Z_nd⟩⟩
    · -- `δ = 5`: `e₂ = e_γ` at `A_v`, paired with `e_β` there
      have hi0 : (0 : Fin 4) ≠ i := by rcases hi with rfl | rfl <;> decide
      have h0Y : lift L 0 ∈ ndAt data P.Y := hatY 0 hi0 (by decide)
      set β : Fin 4 := if i = 1 then 2 else 1 with hβ
      have hβi : β ≠ i := by rcases hi with rfl | rfl <;> decide
      have hβ3 : β ≠ 3 := by rcases hi with rfl | rfl <;> decide
      have hβY : lift L β ∈ ndAt data P.Y := hatY β hβi hβ3
      have hpart : typePartner (Split.simple (decide (i = 2)) (decide ((3 : Fin 4) = 3))).type = β := by
        rcases hi with rfl | rfl <;> rfl
      rw [hpart]
      have hne0β : lift L 0 ≠ lift L β := fun h ↦ by
        have := lift_injective L h
        rcases hi with rfl | rfl <;> simp [hβ] at this
      have hbdY : bdAt data contracted P.Y = {lift L 0, lift L β} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact hbd h0Y
          · rw [Finset.mem_singleton.mp he]; exact hbd hβY
        · rw [P.card_bdAt_Y, Finset.card_pair hne0β]
      constructor
      · rintro ⟨X₁, hX₁, X₂, hX₂, h₁, h₂, hj⟩
        have h1Y := hhome hX₁ P.Y_mem h₁ h0Y
        subst h1Y
        rcases hj with rfl | ⟨e, -, heY, heX, hdiv⟩
        · have := hbd h₂
          rw [hbdY] at this
          rcases Finset.mem_insert.mp this with h | h
          · exact absurd (lift_injective L h) hk
          · exact lift_injective L (Finset.mem_singleton.mp h)
        · exfalso
          rw [P.fib_eq] at hX₂
          simp only [Finset.mem_insert, Finset.mem_singleton] at hX₂
          rcases hX₂ with rfl | rfl | rfl
          · rcases hdiv with h | h
            · rw [P.Y_nd] at h; exact absurd h (by norm_num)
            · rw [P.R_nd] at h; exact absurd h (by norm_num)
          · rcases hdiv with h | h <;> (rw [P.Y_nd] at h; exact absurd h (by norm_num))
          · exact hYZ e heY heX
      · intro hkβ
        rw [hkβ]
        exact ⟨P.Y, P.Y_mem, P.Y, P.Y_mem, h0Y, hβY, Or.inl rfl⟩

end Determination

/-! ## 8.  Split determination across two covers with the same labelled limit -/

section TwoCovers

open ValencyThreeGeneral.Split7

variable {degree : ℕ} {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {target₁ target₂ : CFGraph}
  {data₁ : GluingDatum target₁ degree} {data₂ : GluingDatum target₂ degree}
  (fd₁ : FullDimensionalSourcePresentation data₁ coordinate)
  (fd₂ : FullDimensionalSourcePresentation data₂ coordinate)
  {a₁ b₁ : target₁.V} {contracted₁ : target₁.edges}
  {hc₁ : (contracted₁ : target₁.V × target₁.V) = (a₁, b₁)} {hab₁ : a₁ ≠ b₁}
  {hOne₁ : num_edges target₁ a₁ b₁ = 1} {block₁ : (mergedPartition data₁ a₁ b₁).Blocks}
  {a₂ b₂ : target₂.V} {contracted₂ : target₂.edges}
  {hc₂ : (contracted₂ : target₂.V × target₂.V) = (a₂, b₂)} {hab₂ : a₂ ≠ b₂}
  {hOne₂ : num_edges target₂ a₂ b₂ = 1} {block₂ : (mergedPartition data₂ a₂ b₂).Blocks}

/-- **Split determination (stage 2), cover form.**  Two incoming covers of valency-three
anchors whose labelled limits have the same anchor indices, and whose read splits have the
same type, have the same split.  This is `ValencyThreeGeneral`'s `existsUnique` applied to the two covers'
read splits, which are realisable by `existsUnique_reads`. -/
theorem split_eq_of_indices_eq (H₁ : AnchorInput data₁ hc₁ hab₁ hOne₁ block₁)
    (H₂ : AnchorInput data₂ hc₂ hab₂ hOne₂ block₂)
    (L₁ : AnchorLabelling (contractDatum data₁ hc₁ hab₁ hOne₁) (limA data₁ hc₁ hab₁ hOne₁ block₁))
    (L₂ : AnchorLabelling (contractDatum data₂ hc₂ hab₂ hOne₂) (limA data₂ hc₂ hab₂ hOne₂ block₂))
    (hidx : L₁.indices (H₁.noGlue fd₁) (H₁.ram_one fd₁) H₁.nd4 =
      L₂.indices (H₂.noGlue fd₂) (H₂.ram_one fd₂) H₂.nd4)
    {s₁ s₂ : Split} (h₁ : Reads L₁ (divEnd a₁ b₁) s₁) (h₂ : Reads L₂ (divEnd a₂ b₂) s₂)
    (htype : s₁.type = s₂.type) : s₁ = s₂ := by
  have hv₁ := valid_of_reads fd₁ H₁ L₁ h₁
  have hv₂ := valid_of_reads fd₂ H₂ L₂ h₂
  rw [← hidx] at hv₂
  exact (existsUnique (L₁.indices (H₁.noGlue fd₁) (H₁.ram_one fd₁) H₁.nd4) s₂.type).unique
    ⟨hv₁, htype⟩ ⟨hv₂, rfl⟩

include fd₁ fd₂ in
/-- **Split determination along an isomorphism of limits**: labels transported along a
geometric isomorphism of the two limits carrying anchor to anchor give equal anchor indices,
hence equal splits for equal types. -/
theorem split_eq_of_limitIso (H₁ : AnchorInput data₁ hc₁ hab₁ hOne₁ block₁)
    (H₂ : AnchorInput data₂ hc₂ hab₂ hOne₂ block₂)
    (ψ : GeometricDatumIso (contractDatum data₁ hc₁ hab₁ hOne₁) (contractDatum data₂ hc₂ hab₂ hOne₂))
    (hψ : ψ.sourceVertexEquiv (limA data₁ hc₁ hab₁ hOne₁ block₁) = limA data₂ hc₂ hab₂ hOne₂ block₂)
    (L₁ : AnchorLabelling (contractDatum data₁ hc₁ hab₁ hOne₁) (limA data₁ hc₁ hab₁ hOne₁ block₁))
    (L₂ : AnchorLabelling (contractDatum data₂ hc₂ hab₂ hOne₂) (limA data₂ hc₂ hab₂ hOne₂ block₂))
    (hL : ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i))
    {s₁ s₂ : Split} (h₁ : Reads L₁ (divEnd a₁ b₁) s₁) (h₂ : Reads L₂ (divEnd a₂ b₂) s₂)
    (htype : s₁.type = s₂.type) : s₁ = s₂ := by
  refine split_eq_of_indices_eq fd₁ fd₂ H₁ H₂ L₁ L₂ ?_ h₁ h₂ htype
  refine anchorIndices_ext ?_ ?_ ?_ ?_ ?_
  · change size _ _ = size _ _
    rw [← hψ, AnchorLabelling.size_map]
  all_goals
    change _ = (contractDatum data₂ hc₂ hab₂ hOne₂).sourceEdgeIndex (L₂.e _)
    rw [hL, ψ.sourceEdgeIndex_map]
    rfl

include fd₁ fd₂ in
/-- **Split determination, intrinsic form**: two covers whose incoming stable graphs pair
`e₂` with the same survivor (same combinatorial type `H_{2,β}`, on transported labels) have
the same split. -/
theorem split_eq_of_paired (H₁ : AnchorInput data₁ hc₁ hab₁ hOne₁ block₁)
    (H₂ : AnchorInput data₂ hc₂ hab₂ hOne₂ block₂)
    (ψ : GeometricDatumIso (contractDatum data₁ hc₁ hab₁ hOne₁) (contractDatum data₂ hc₂ hab₂ hOne₂))
    (hψ : ψ.sourceVertexEquiv (limA data₁ hc₁ hab₁ hOne₁ block₁) = limA data₂ hc₂ hab₂ hOne₂ block₂)
    (L₁ : AnchorLabelling (contractDatum data₁ hc₁ hab₁ hOne₁) (limA data₁ hc₁ hab₁ hOne₁ block₁))
    (L₂ : AnchorLabelling (contractDatum data₂ hc₂ hab₂ hOne₂) (limA data₂ hc₂ hab₂ hOne₂ block₂))
    (hL : ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i))
    {s₁ s₂ : Split} (h₁ : Reads L₁ (divEnd a₁ b₁) s₁) (h₂ : Reads L₂ (divEnd a₂ b₂) s₂)
    (j : Fin 4) (hj : j ≠ 0) (hp₁ : Paired L₁ 0 j) (hp₂ : Paired L₂ 0 j) : s₁ = s₂ := by
  have e₁ := (paired_iff fd₁ H₁ L₁ h₁ j hj).mp hp₁
  have e₂ := (paired_iff fd₂ H₂ L₂ h₂ j hj).mp hp₂
  exact split_eq_of_limitIso fd₁ fd₂ H₁ H₂ ψ hψ L₁ L₂ hL h₁ h₂
    (typePartner_injective (e₁.symm.trans e₂))

/-- The transported labelling exists. -/
theorem exists_transport
    (ψ : GeometricDatumIso (contractDatum data₁ hc₁ hab₁ hOne₁) (contractDatum data₂ hc₂ hab₂ hOne₂))
    (hψ : ψ.sourceVertexEquiv (limA data₁ hc₁ hab₁ hOne₁ block₁) = limA data₂ hc₂ hab₂ hOne₂ block₂)
    (hConn : (contractDatum data₁ hc₁ hab₁ hOne₁).Connected)
    (L₁ : AnchorLabelling (contractDatum data₁ hc₁ hab₁ hOne₁) (limA data₁ hc₁ hab₁ hOne₁ block₁)) :
    ∃ L₂ : AnchorLabelling (contractDatum data₂ hc₂ hab₂ hOne₂) (limA data₂ hc₂ hab₂ hOne₂ block₂),
      ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i) := by
  rw [← hψ]
  exact ⟨L₁.transport ψ hConn, fun _ ↦ rfl⟩

end TwoCovers

/-! ## 9.  Regrowths: stage 1 (anchor localization) at every facet regrowth -/

section Regrowth

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The anchor input of a regrowth** at a merged block of its limit: `AnchorInput` for the
regrowth's own contraction (`Regrowth.limit` is `contractDatum` of this contraction). -/
abbrev RegrowthAnchor (w : Regrowth core y degree)
    (block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks) :
    Prop :=
  AnchorInput w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) block

example (w : Regrowth core y degree) :
    w.limit = contractDatum w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) := rfl

/-- A non-loop core slot gives its stable path a simple end (the `HasSimpleEnd` input of the
single-row forest), through the core identification. -/
theorem hasSimpleEnd_of_ident (k : Frame core degree) (e₀ : Fin p)
    (hloop : core.tail e₀ ≠ core.head e₀) :
    SingleRowForest.HasSimpleEnd k.data (k.ident.row.symm e₀) := by
  refine ⟨k.ident.vertex.symm (core.tail e₀), ?_⟩
  rw [k.ident.incidence, Equiv.apply_symm_apply]
  simp [coreIncidence, hloop.symm]

/-- **Stage 1, anchor localization, at every facet regrowth.**  A regrowth at a facet point
(one request coordinate zero, at a non-loop core slot) whose limit's merged target vertex is
trivalent has a merged block carrying the full anchor input: the contraction forest (the
single vanishing row has a simple end), and `nd(A) = 4` (the receipt-free producer
`nonDanglingValency_eq_four_of_row_facet_threeStar`). -/
theorem exists_regrowthAnchor (w : Regrowth core y degree) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop : core.tail e₀ ≠ core.head e₀)
    (hval : (GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
      ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
        fst_ne_snd (w.frame.edgeOf w.column)⟩).card = 3) :
    ∃ block, RegrowthAnchor w block := by
  classical
  set k := w.frame with hk
  set facet : Fin p := k.slot.symm e₀ with hfacet
  have hmul : ∀ row, (GluingDatum.LengthMatrixPresentation.matrix
      k.fullDim.labelling.presentation).mulVec (k.coordsAt y) row = y (k.slot row) :=
    fun row ↦ congrFun (k.mulVec_coordsAt y) row
  have hRows : ∀ row, row ≠ facet → (GluingDatum.LengthMatrixPresentation.matrix
      k.fullDim.labelling.presentation).mulVec (k.coordsAt y) row ≠ 0 := by
    intro row hrow
    rw [hmul]
    refine ne_of_gt (hpt.2 _ ?_)
    intro h
    apply hrow
    rw [hfacet, ← h, Equiv.symm_apply_apply]
  have hFacetZero : (GluingDatum.LengthMatrixPresentation.matrix
      k.fullDim.labelling.presentation).mulVec (k.coordsAt y) facet = 0 := by
    rw [hmul, hfacet, Equiv.apply_symm_apply]
    exact hpt.1
  have hZero : k.coordsAt y (k.fullDim.labelling.targetEdge.symm (k.edgeOf w.column)) = 0 :=
    InheritedLimitRows.zero_coordinate w
  have hcol : k.fullDim.labelling.targetEdge.symm (k.edgeOf w.column) = w.column := by
    simp [Frame.edgeOf]
  have hPos : ∀ column, column ≠ k.fullDim.labelling.targetEdge.symm (k.edgeOf w.column) →
      0 < k.coordsAt y column := by
    intro column hne
    rw [hcol] at hne
    exact w.degenerate.2 column hne
  have hNonneg : ∀ column, 0 ≤ k.coordsAt y column := by
    intro column
    by_cases h : column = w.column
    · rw [h, ← hcol, hZero]
    · exact le_of_lt (w.degenerate.2 column h)
  have hEnd : SingleRowForest.HasSimpleEnd k.data (k.fullDim.labelling.row.symm facet) := by
    have : k.fullDim.labelling.row.symm facet = k.ident.row.symm e₀ := by
      rw [hfacet]
      simp [Frame.slot]
    rw [this]
    exact hasSimpleEnd_of_ident k e₀ hloop
  have hForest : ContractionForest k.data _ _ (k.edgeOf w.column) :=
    SingleRowForest.contractionForest_of_single_row k.fullDim.labelling (k.coordsAt y) hNonneg
      facet hRows hEnd rfl hZero
  have star : ThirdEquation.ThreeStar
      (contract k.target (fst_ne_snd (k.edgeOf w.column)) (k.numEdges_edgeOf w.column))
      ⟨_, fst_ne_snd (k.edgeOf w.column)⟩ := ThirdEquation.ThreeStar.of_card hval
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep (k.fullDim.labelling.row.symm facet)
  have hRow : k.fullDim.labelling.row edge.stablePath = facet := by
    show k.fullDim.labelling.row (Quot.mk _ edge) = facet
    rw [hEdge, Equiv.apply_symm_apply]
  obtain ⟨block, -, hFour⟩ := NonTrivalentAnchorValency.nonDanglingValency_eq_four_of_row_facet_threeStar
    k.data k.fullDim rfl (fst_ne_snd (k.edgeOf w.column)) (k.numEdges_edgeOf w.column) star
    hForest (k.coordsAt y) facet hRows hZero hPos hFacetZero edge hRow
  exact ⟨block, hForest, hval, hFour⟩

/-- The limit of a regrowth is connected. -/
theorem connected_limit (w : Regrowth core y degree) : w.limit.Connected :=
  connected_contractDatum w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) w.frame.fullDim.valid.1

variable {c₂ : Core n p}

/-- **An isomorphism of regrowth limits carries anchor to anchor**: the image of one anchor
has surviving valency four, and the anchor is the only such vertex. -/
theorem sourceVertexEquiv_limA (w₁ : Regrowth core y degree) (w₂ : Regrowth c₂ y degree)
    {block₁} {block₂} (H₁ : RegrowthAnchor w₁ block₁) (H₂ : RegrowthAnchor w₂ block₂)
    (ψ : GeometricDatumIso w₁.limit w₂.limit) :
    ψ.sourceVertexEquiv (limA w₁.frame.data rfl (fst_ne_snd (w₁.frame.edgeOf w₁.column))
        (w₁.frame.numEdges_edgeOf w₁.column) block₁) =
      limA w₂.frame.data rfl (fst_ne_snd (w₂.frame.edgeOf w₂.column))
        (w₂.frame.numEdges_edgeOf w₂.column) block₂ := by
  apply eq_limA_of_nonDanglingValency_eq_four w₂.frame.fullDim H₂
  exact (ψ.nonDanglingValency_map (connected_limit w₁) _).trans H₁.nd4

open ValencyThreeGeneral.Split7 in
/-- **Stage 2 at regrowths: split determination along a limit isomorphism.**  For two
regrowths (over any cores) with valency-three anchors and any geometric isomorphism of their
limits -- in particular the one a labelled metric limit provides -- a labelling of the first
limit transports to the second, and then two read splits of the same type are equal. -/
theorem regrowth_split_eq (w₁ : Regrowth core y degree) (w₂ : Regrowth c₂ y degree)
    {block₁} {block₂} (H₁ : RegrowthAnchor w₁ block₁) (H₂ : RegrowthAnchor w₂ block₂)
    (ψ : GeometricDatumIso w₁.limit w₂.limit)
    (L₁ : AnchorLabelling w₁.limit (limA w₁.frame.data rfl (fst_ne_snd (w₁.frame.edgeOf w₁.column))
        (w₁.frame.numEdges_edgeOf w₁.column) block₁)) :
    ∃ L₂ : AnchorLabelling w₂.limit (limA w₂.frame.data rfl
        (fst_ne_snd (w₂.frame.edgeOf w₂.column)) (w₂.frame.numEdges_edgeOf w₂.column) block₂),
      (∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i)) ∧
      ∀ s₁ s₂ : Split,
        Reads L₁ (divEnd (w₁.frame.edgeOf w₁.column : w₁.frame.target.V × w₁.frame.target.V).1
          (w₁.frame.edgeOf w₁.column : w₁.frame.target.V × w₁.frame.target.V).2) s₁ →
        Reads L₂ (divEnd (w₂.frame.edgeOf w₂.column : w₂.frame.target.V × w₂.frame.target.V).1
          (w₂.frame.edgeOf w₂.column : w₂.frame.target.V × w₂.frame.target.V).2) s₂ →
        s₁.type = s₂.type → s₁ = s₂ := by
  have hψ := sourceVertexEquiv_limA w₁ w₂ H₁ H₂ ψ
  obtain ⟨L₂, hL⟩ := exists_transport ψ hψ (connected_limit w₁) L₁
  exact ⟨L₂, hL, fun s₁ s₂ h₁ h₂ ht ↦
    split_eq_of_limitIso w₁.frame.fullDim w₂.frame.fullDim H₁ H₂ ψ hψ L₁ L₂ hL h₁ h₂ ht⟩

end Regrowth

/-! ## 10.  What stages 3 to 5 owe, and the implication to `huniqL` -/

section Stages

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyThreeGeneral (SameMetricLimit MetricFacetLimit MSpecializesLeft MSpecializesRight
  metricSwap slotColumn limitCol)
open ValencyThreeGeneral.Split7

variable {n p degree : ℕ}

/-- The divalent endpoint of a regrowth's contracted occurrence. -/
noncomputable abbrev uOf {core : Core n p} {y : Fin p → ℚ} (w : Regrowth core y degree) :
    w.frame.target.V :=
  divEnd (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1
    (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2

/-- The anchor of a regrowth's limit at a merged block. -/
noncomputable abbrev anchorOf {core : Core n p} {y : Fin p → ℚ} (w : Regrowth core y degree)
    (block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks) :
    w.limit.SourceVertex :=
  limA w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    block

/-- **A limit isomorphism is labelled-metric**: it preserves each surviving target length and
slot-aligned column.  This is exactly the witness shape of
`ValencyThreeGeneral.SameMetricLimit (Sum.inl w) (Sum.inl w')`
(`sameMetricLimit_iff`). -/
def IsMetricIso {core : Core n p} {y : Fin p → ℚ} (w w' : Regrowth core y degree)
    (ψ : GeometricDatumIso w.limit w'.limit) : Prop :=
  ∀ e, StarPilot.limitLength w' (ψ.targetEdge e) = StarPilot.limitLength w e ∧
    slotColumn w'.frame (limitCol w' (ψ.targetEdge e)) = slotColumn w.frame (limitCol w e)

theorem sameMetricLimit_iff {c c' : Core n p} {y : Fin p → ℚ} (w w' : Regrowth c y degree) :
    SameMetricLimit (c := c) (c' := c') (Sum.inl w) (Sum.inl w') ↔
      ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ :=
  Iff.rfl

/-- **Stage 3, matching the core type to the base tree.**  Two odd classes of one core at one
labelled metric limit with a valency-three anchor: *some* labelled-metric isomorphism of their
limits makes their read splits have the same type, for labellings transported along it.

The isomorphism is existential on purpose.  A labelled metric limit can have label-moving
automorphisms: `e₂` and `e₅` lie over one target edge, so an isomorphism fixing every target
edge and relabelling sheets there preserves every surviving length and slot-aligned column
while exchanging them (when `k₂ = k₅`); along such an automorphism a cover with a
`simple` split reads the other `δ`, hence the other of Types I, II, against itself.  So the
universal form ("every metric isomorphism") would be false wherever such a symmetry meets a
`simple` split, although uniqueness is not; the existential form is what uniqueness implies
(through the frame isomorphism's own limit isomorphism).

Interface: the statement "the type `H_{2,β}` of the incoming stable graph at the anchor is
the core's" (Part II, Case `{v3-nd4}`) in the labelled form `split_eq_of_limitIso` consumes;
equivalent to `PairingMatch` (`typeMatch_iff_pairingMatch`); not proved here. -/
def TypeMatch (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block'),
    (∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ) →
    (FrameClass.mk w.frame).IsOdd → (FrameClass.mk w'.frame).IsOdd →
    ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ ∧
      ∀ (L : AnchorLabelling w.limit (anchorOf w block))
        (L' : AnchorLabelling w'.limit (anchorOf w' block')),
        (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) →
        ∀ s s' : Split, Reads L (uOf w) s → Reads L' (uOf w') s' → s.type = s'.type

/-- **Stage 3, intrinsic form**: two odd classes of one core, at one labelled metric limit
with a valency-three anchor, have -- along some labelled-metric isomorphism -- incoming stable
graphs pairing `e₂` with the same survivor (one combinatorial type `H_{2,β}`).

Interface: equivalent to `TypeMatch` (`typeMatch_iff_pairingMatch`). -/
def PairingMatch (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block'),
    (∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ) →
    (FrameClass.mk w.frame).IsOdd → (FrameClass.mk w'.frame).IsOdd →
    ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ ∧
      ∀ (L : AnchorLabelling w.limit (anchorOf w block))
        (L' : AnchorLabelling w'.limit (anchorOf w' block')),
        (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) →
        ∀ j : Fin 4, j ≠ 0 → Paired L 0 j → Paired L' 0 j

theorem typeMatch_iff_pairingMatch (core : Core n p) (y : Fin p → ℚ) :
    TypeMatch core y degree ↔ PairingMatch core y degree := by
  constructor
  · intro h3 w w' block block' H H' hsame hx hx'
    obtain ⟨ψ, hψ, ht⟩ := h3 w w' block block' H H' hsame hx hx'
    refine ⟨ψ, hψ, fun L L' hL j hj hp ↦ ?_⟩
    obtain ⟨s, hs, -, -⟩ := existsUnique_reads w.frame.fullDim H L
    obtain ⟨s', hs', -, -⟩ := existsUnique_reads w'.frame.fullDim H' L'
    have hts := ht L L' hL s s' hs hs'
    have hj' := (paired_iff w.frame.fullDim H L hs j hj).mp hp
    exact (paired_iff w'.frame.fullDim H' L' hs' j hj).mpr (hj'.trans (congrArg typePartner hts))
  · intro h3 w w' block block' H H' hsame hx hx'
    obtain ⟨ψ, hψ, hp⟩ := h3 w w' block block' H H' hsame hx hx'
    refine ⟨ψ, hψ, fun L L' hL s s' hs hs' ↦ ?_⟩
    have h0 := (paired_iff w.frame.fullDim H L hs _ (typePartner_ne_zero _)).mpr rfl
    have h1 := hp L L' hL _ (typePartner_ne_zero _) h0
    exact typePartner_injective ((paired_iff w'.frame.fullDim H' L' hs' _
      (typePartner_ne_zero _)).mp h1)

/-- **Stages 4 and 5, extending the isomorphism across the anchor and pinning the
identifications.**  Two odd classes of one core at one labelled metric limit with a
valency-three anchor, reading the same split for transported labellings, are equal.

Interface: "the limit, the split and the core identification determine the frame class"
(Part II's Case `{v3-nd4}` read as a reconstruction); not proved here. -/
def SplitRigidity (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ →
    ∀ (L : AnchorLabelling w.limit (anchorOf w block))
      (L' : AnchorLabelling w'.limit (anchorOf w' block')),
      (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) →
      (FrameClass.mk w.frame).IsOdd → (FrameClass.mk w'.frame).IsOdd →
      ∀ s : Split, Reads L (uOf w) s → Reads L' (uOf w') s →
        FrameClass.mk w.frame = FrameClass.mk w'.frame

/-- **A valency-three metric facet limit** (near side): every near-side regrowth presenting
it carries the anchor input.  Interface: discharged at every facet regrowth whose limit's
merged target vertex is trivalent (`exists_regrowthAnchor`, `v3Limit_of_facetPoint`). -/
def V3Limit {c c' : Core n p} {y : Fin p → ℚ} (m : MetricFacetLimit c c' y degree) : Prop :=
  ∀ w : Regrowth c y degree, MetricFacetLimit.ofLeft (c' := c') w = m →
    ∃ block, RegrowthAnchor w block

/-- `V3Limit` at a facet point of a non-loop slot reduces to the trivalence of the merged
target vertex of each presenting regrowth. -/
theorem v3Limit_of_facetPoint {c c' : Core n p} {y : Fin p → ℚ}
    (m : MetricFacetLimit c c' y degree) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop : c.tail e₀ ≠ c.head e₀)
    (hval : ∀ w : Regrowth c y degree, MetricFacetLimit.ofLeft (c' := c') w = m →
      (GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
        ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
          fst_ne_snd (w.frame.edgeOf w.column)⟩).card = 3) :
    V3Limit m :=
  fun w hw ↦ exists_regrowthAnchor w e₀ hpt hloop (hval w hw)

/-- **Two classes specialising to one labelled metric limit with a
valency-three anchor, with the same type, have the same split.**  Presenting regrowths,
their anchor inputs, a labelling transported along the labelled-metric isomorphism, and the
two read splits exist; the splits are equal as soon as their types are, equivalently as soon
as the two incoming stable graphs pair `e₂` with the same survivor (`paired_iff`). -/
theorem split_eq_of_same_metric_limit {c c' : Core n p} {y : Fin p → ℚ}
    {m : MetricFacetLimit c c' y degree} (hm : V3Limit m) {x x' : FrameClass c degree}
    (hs : MSpecializesLeft x m) (hs' : MSpecializesLeft x' m) :
    ∃ (w w' : Regrowth c y degree) (block : _) (block' : _) (H : RegrowthAnchor w block)
      (_H' : RegrowthAnchor w' block') (ψ : GeometricDatumIso w.limit w'.limit)
      (L : AnchorLabelling w.limit (anchorOf w block))
      (L' : AnchorLabelling w'.limit (anchorOf w' block')) (sp sp' : Split),
      FrameClass.mk w.frame = x ∧ FrameClass.mk w'.frame = x' ∧ IsMetricIso w w' ψ ∧
      (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) ∧
      Reads L (uOf w) sp ∧ Reads L' (uOf w') sp' ∧
      (L.indices (H.noGlue w.frame.fullDim) (H.ram_one w.frame.fullDim) H.nd4).Valid sp ∧
      (sp.type = sp'.type → sp = sp') := by
  obtain ⟨w, hx, hw⟩ := hs
  obtain ⟨w', hx', hw'⟩ := hs'
  obtain ⟨block, H⟩ := hm w hw
  obtain ⟨block', H'⟩ := hm w' hw'
  have hsame : SameMetricLimit (c := c) (c' := c') (Sum.inl w) (Sum.inl w') :=
    Quotient.exact (hw.trans hw'.symm)
  obtain ⟨ψ, hψ⟩ := (sameMetricLimit_iff w w').mp hsame
  obtain ⟨L⟩ := nonempty_anchorLabelling w.frame.fullDim H
  obtain ⟨L', hL, hsplit⟩ := regrowth_split_eq w w' H H' ψ L
  obtain ⟨sp, hsR, hv, -⟩ := existsUnique_reads w.frame.fullDim H L
  obtain ⟨sp', hsR', -, -⟩ := existsUnique_reads w'.frame.fullDim H' L'
  exact ⟨w, w', block, block', H, H', ψ, L, L', sp, sp', hx, hx', hψ, hL, hsR, hsR', hv,
    hsplit sp sp' hsR hsR'⟩

/-- **Stages 1--5 give `huniqL` at every valency-three metric limit.** -/
theorem huniqL_of_stages {c c' : Core n p} {y : Fin p → ℚ}
    (h3 : TypeMatch c y degree) (h45 : SplitRigidity c y degree)
    (m : MetricFacetLimit c c' y degree) (hm : V3Limit m)
    (x x' : FrameClass c degree) (hx : x.IsOdd) (hs : MSpecializesLeft x m)
    (hx' : x'.IsOdd) (hs' : MSpecializesLeft x' m) : x = x' := by
  obtain ⟨w, rfl, hw⟩ := hs
  obtain ⟨w', rfl, hw'⟩ := hs'
  obtain ⟨block, H⟩ := hm w hw
  obtain ⟨block', H'⟩ := hm w' hw'
  have hsame : SameMetricLimit (c := c) (c' := c') (Sum.inl w) (Sum.inl w') :=
    Quotient.exact (hw.trans hw'.symm)
  obtain ⟨ψ, hψ, htype⟩ := h3 w w' block block' H H' ((sameMetricLimit_iff w w').mp hsame) hx hx'
  obtain ⟨L⟩ := nonempty_anchorLabelling w.frame.fullDim H
  obtain ⟨L', hL, hsplit⟩ := regrowth_split_eq w w' H H' ψ L
  obtain ⟨s, hsR, -, -⟩ := existsUnique_reads w.frame.fullDim H L
  obtain ⟨s', hsR', -, -⟩ := existsUnique_reads w'.frame.fullDim H' L'
  have ht := htype L L' hL s s' hsR hsR'
  have hss : s = s' := hsplit s s' hsR hsR' ht
  subst hss
  exact h45 w w' block block' H H' ψ hψ L L' hL hx hx' s hsR hsR'

/-! **Caution: the at-most-one-odd-class hypotheses consumed below fail at valency-four
`K`-family metric limits.**  Part II gives `min(k₂-1, |A|-k₅)+1` members per type, two at
`(|A|; k) = (3; 2,2,2,2)` and `(4; 2,2,3,3)` in degree four, and such limits occur in genus
six.  The implication stands but cannot be discharged at every step; in particular `hrest`'s
"at most one odd class" hypothesis below is not dischargeable at valency four, so
`huniqL_of_stages_of_rest` is not the route the count uses.  The count uses instead a census
inside each labelled metric limit with equal counts through an index: `FacetCensus.MetricCensus`
and `CensusAssembly.metricCensus_of_resolved`, with `K` as the valency-four index
(`ValencyFourRigidity`, `ValencyFourRealisation`); this is step 3 of `Assembly`. -/
/-- **The full `huniqL`**: stages 1--5 at the valency-three metric limits, and uniqueness
supplied at the others (valency two and four). -/
theorem huniqL_of_stages_of_rest {c c' : Core n p} {y : Fin p → ℚ}
    (h3 : TypeMatch c y degree) (h45 : SplitRigidity c y degree)
    (hrest : ∀ m : MetricFacetLimit c c' y degree, ¬ V3Limit m →
      ∀ x x' : FrameClass c degree,
        x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x')
    (m : MetricFacetLimit c c' y degree) (x x' : FrameClass c degree) (hx : x.IsOdd)
    (hs : MSpecializesLeft x m) (hx' : x'.IsOdd) (hs' : MSpecializesLeft x' m) : x = x' := by
  by_cases hm : V3Limit m
  · exact huniqL_of_stages h3 h45 m hm x x' hx hs hx' hs'
  · exact hrest m hm x x' hx hs hx' hs'

/-- **The far side, by exchanging the two cores**: `huniqR` from the stages over the far
core. -/
theorem huniqR_of_stages_of_rest {c c' : Core n p} {y : Fin p → ℚ}
    (h3 : TypeMatch c' y degree) (h45 : SplitRigidity c' y degree)
    (hrest : ∀ m : MetricFacetLimit c' c y degree, ¬ V3Limit m →
      ∀ x x' : FrameClass c' degree,
        x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x')
    (m : MetricFacetLimit c c' y degree) (x x' : FrameClass c' degree) (hx : x.IsOdd)
    (hs : MSpecializesRight x m) (hx' : x'.IsOdd) (hs' : MSpecializesRight x' m) : x = x' :=
  huniqL_of_stages_of_rest h3 h45 hrest (metricSwap m) x x' hx
    (ValencyThreeGeneral.mSpecializesRight_swap_iff.mp hs) hx'
    (ValencyThreeGeneral.mSpecializesRight_swap_iff.mp hs')

section Composite

open FacetAdapterPilot FacetMachine
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **`FacetParity` at a Whitehead step from stages 3--5 on both sides**, with stage 1
(`V3Limit`) at the valency-three metric limits and uniqueness supplied at the others.  This
feeds `ColumnReceiptExport.facetParity_of_metricUniqueness` (whose receipts
`ColumnReceiptExport` discharges). -/
theorem facetParity_of_stages (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (h3 : TypeMatch c.core y₀ degree) (h45 : SplitRigidity c.core y₀ degree)
    (h3' : TypeMatch (farCore m').core y₀ degree) (h45' : SplitRigidity (farCore m').core y₀ degree)
    (hrest : ∀ m : MetricFacetLimit c.core (farCore m').core y₀ degree, ¬ V3Limit m →
      ∀ x x' : FrameClass c.core degree,
        x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x')
    (hrest' : ∀ m : MetricFacetLimit (farCore m').core c.core y₀ degree, ¬ V3Limit m →
      ∀ x x' : FrameClass (farCore m').core degree,
        x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x') :
    FacetParity c.core (farCore m').core degree y₀ :=
  ColumnReceiptExport.facetParity_of_metricUniqueness m' hd hG hDegree
    (huniqL_of_stages_of_rest h3 h45 hrest) (huniqR_of_stages_of_rest h3' h45' hrest')

end Composite

end Stages

/-! ## 11.  Label-moving automorphisms of a limit -/

section LabelMoving

variable {T : CFGraph} {degree : ℕ} (D : GluingDatum T degree)

/-- **A sheet swap over a discrete target occurrence** whose two sheets are related at both
ends is a geometric automorphism of the datum fixing every target vertex and occurrence: the
datum does not tell the two source occurrences over that target occurrence apart. -/
noncomputable def swapIso (t : T.edges) (i j : Fin degree)
    (hdisc : ∀ k, (D.edgePartition t).repr k = k)
    (hrel : ∀ v, ((t : T.V × T.V).1 = v ∨ (t : T.V × T.V).2 = v) → (D.vertexPartition v).Rel i j) :
    GeometricDatumIso D D := by
  classical
  exact
  { targetVertex := Equiv.refl _
    targetEdge := Equiv.refl _
    ends := fun _ ↦ Or.inl rfl
    vertexPerm := fun _ ↦ Equiv.refl _
    edgePerm := fun e ↦ if e = t then Equiv.swap i j else Equiv.refl _
    vertexPartition := fun v ↦ (Transport.DatumIso.relabel_refl _).symm
    edgePartition := fun e ↦ by
      by_cases he : e = t
      · subst he
        simp only [ite_true, Equiv.refl_apply]
        apply SheetPartition.ext_repr
        funext k
        simp only [SheetPartition.relabel, hdisc, Equiv.apply_symm_apply]
      · simp only [he, ite_false, Equiv.refl_apply]
        exact (Transport.DatumIso.relabel_refl _).symm
    compatible := fun e v hv k ↦ by
      by_cases he : e = t
      · subst he
        simp only [ite_true, Equiv.refl_symm, Equiv.refl_apply]
        have h := hrel v hv
        by_cases hki : k = i
        · subst hki; rw [Equiv.swap_apply_left]; exact ((D.vertexPartition v).rel_iff _ _).mpr
            (((D.vertexPartition v).rel_iff _ _).mp h).symm
        · by_cases hkj : k = j
          · subst hkj; rw [Equiv.swap_apply_right]; exact h
          · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]; rfl
      · simp only [he, ite_false, Equiv.refl_symm, Equiv.refl_apply]
        rfl }

theorem swapIso_targetEdge (t : T.edges) (i j : Fin degree)
    (hdisc : ∀ k, (D.edgePartition t).repr k = k)
    (hrel : ∀ v, ((t : T.V × T.V).1 = v ∨ (t : T.V × T.V).2 = v) → (D.vertexPartition v).Rel i j)
    (e : T.edges) : (swapIso D t i j hdisc hrel).targetEdge e = e := rfl

/-- The swap moves the source occurrence of sheet `i` over `t` to that of sheet `j`. -/
theorem swapIso_moves (t : T.edges) (i j : Fin degree) (hij : i ≠ j)
    (hdisc : ∀ k, (D.edgePartition t).repr k = k)
    (hrel : ∀ v, ((t : T.V × T.V).1 = v ∨ (t : T.V × T.V).2 = v) → (D.vertexPartition v).Rel i j) :
    (swapIso D t i j hdisc hrel).sourceEdgeEquiv ⟨(t, i), hdisc i⟩ ≠ ⟨(t, i), hdisc i⟩ := by
  classical
  intro h
  have h2 := congrArg (fun f : D.SourceEdge ↦ f.1.2) h
  change (if t = t then Equiv.swap i j else Equiv.refl _) i = i at h2
  rw [ite_eq_left rfl, Equiv.swap_apply_left] at h2
  exact hij h2.symm

end LabelMoving

/-! ## 12.  `cat_step`: the ballot regrowths -/

section CatStep

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.FacetMachine
open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)
open DraismaVargas.Infrastructure.CaterpillarTree

theorem tail_ne_head_of_sharedContractionSlot {n p : ℕ} {c c' : Core n p} {e₀ : Fin p}
    (h : SharedContractionSlot c c' e₀) : c.tail e₀ ≠ c.head e₀ := by
  obtain ⟨v₀, v₁, hne, hends, -, -⟩ := h
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hne
  · rw [h1, h2]; exact hne.symm

variable {c' : Core (4 * 2 + 2) (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ} {ε : ℚ}

/-- At `cat_step` the contracted spine edge `h₁ = occ 2 1` has the sheet partition of its
root end `u₁` (the spine block and the bridge pair coincide, `s₁ = 2`). -/
theorem ballot_edgePartition_eq (s : Slopes (2 * (2 + 1))) :
    (BallotDatum.ballotDatum 2 s).edgePartition (occ 2 1) =
      (BallotDatum.ballotDatum 2 s).vertexPartition
        (((occ 2 1 : (catTree 2).edges) : (catTree 2).V × (catTree 2).V).1) := by
  rw [BallotDatum.ballotDatum_edgePart_occ, BallotDatum.ballotDatum_vertexPart_val]
  apply SheetPartition.ext_repr
  funext k
  simp only [BallotDatum.catStar, SheetPartition.sheetStar_repr]
  have e1 : ((1 : Fin (6 * 2 + 3)) : ℕ) = 1 := rfl
  have e0 : (((occ 2 1 : (catTree 2).edges) : (catTree 2).V × (catTree 2).V).1).val = 0 := rfl
  have h : BallotDatum.EdgePred 2 s ((1 : Fin (6 * 2 + 3)) : ℕ) k.val ↔
      BallotDatum.VertPred 2 s
        (((occ 2 1 : (catTree 2).edges) : (catTree 2).V × (catTree 2).V).1).val k.val := by
    rw [e1, e0]
    simp only [BallotDatum.EdgePred, BallotDatum.VertPred]
    norm_num
    exact Slopes.spineMem_one_iff_pairMem_one s k.val
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.mp h1) h2
  · exact absurd (h.mpr h2) h1
  · rfl

/-- At `cat_step` the divalent end of `h₁` is its root end `u₁`. -/
theorem ballot_divEnd :
    divEnd (((occ 2 1 : (catTree 2).edges) : (catTree 2).V × (catTree 2).V).1)
        (((occ 2 1 : (catTree 2).edges) : (catTree 2).V × (catTree 2).V).2) =
      ((occ 2 1 : (catTree 2).edges) : (catTree 2).V × (catTree 2).V).1 := by
  have h : (GluingDatum.incidentEdges
      (((occ 2 1 : (catTree 2).edges) : (catTree 2).V × (catTree 2).V).1)).card = 2 := by
    rw [card_incidentEdges]
    decide
  simp only [divEnd, h, ite_true]

theorem ballot_rel_zero_one (s : Slopes (2 * (2 + 1))) (v : (catTree 2).V)
    (hv : v.val = 0 ∨ v.val = 1) :
    ((BallotDatum.ballotDatum 2 s).vertexPartition v).Rel 0 1 := by
  rw [BallotDatum.ballotDatum_vertexPart_val, BallotDatum.catStar_rel_iff _
    (by simp [BallotDatum.VertPred, Slopes.pairMem_zero])]
  left
  have hP : ∀ k, BallotDatum.VertPred 2 s v.val k ↔ s.PairMem 1 k := by
    intro k
    rcases hv with h | h <;> rw [h] <;> simp [BallotDatum.VertPred, lolli]
  rw [hP, hP]
  refine ⟨Or.inl rfl, Or.inr ?_⟩
  rw [Slopes.cum_one]
  rfl

theorem ballot_leaf_discrete (s : Slopes (2 * (2 + 1))) (k : Fin (2 + 2)) :
    ((BallotDatum.ballotDatum 2 s).edgePartition (occ 2 0)).repr k = k := by
  rw [BallotDatum.ballotDatum_edgePart_occ]
  simp only [BallotDatum.catStar, SheetPartition.sheetStar_repr]
  have e0 : ((0 : Fin (6 * 2 + 3)) : ℕ) = 0 := rfl
  rw [e0]
  simp only [BallotDatum.EdgePred]
  norm_num
  intro h
  exact h.symm

end CatStep

end DraismaVargas.Count.ValencyThreeSplit
