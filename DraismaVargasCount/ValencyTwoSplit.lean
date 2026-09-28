import DraismaVargasCount.FacetCensus

/-!
# The valency-two split, read off an arbitrary incoming cover

**Source.**  Vargas, Part II (arXiv:2609.09109), the valency-two limits `{v2-nd4}`
(subsection `subsec-case-v2`): at a valency-two limit `φ₀` the four non-dangling edges at the
anchor `A` lie over the two target edges at `w₀`, split `2 + 2` (Configuration A) or `3 + 1`
(Configuration B), and in every subcase exactly one full-dimensional morphism of each of
Types I, II and III specializes to `φ₀`.  This module is the valency-two form of §1--§10 of
`DraismaVargasCount.ValencyThreeSplit`, feeding `FacetCensus.MetricCensus` (the type changes,
step 3 of `DraismaVargasCount.Assembly`).

## The five stages

As at valency three (`ValencyThreeSplit`), the census at a valency-two metric limit is proved
in five stages:

1. *anchor localization*: every regrowth presenting the limit carries the anchor input at a
   merged block of its limit (`exists_regrowthAnchor`, `V2Limit`);
2. *split determination*: two covers whose incoming stable graphs pair the labelled survivors
   in the same way read the same split (`split_eq_of_paired`);
3. *the pairing is the core's*: some labelled-metric isomorphism of the two limits matches the
   pairings (`PairingMatch`);
4. *extension across the anchor*: two classes reading the same split have column-compatible
   incoming data (`AnchorExtension`; the transport form `ResolutionMatch` implies it);
5. *pinning the core*: column-compatible data give a frame isomorphism over the core
   (`ValencyThreeRigidity.frameIso_of_columns`, which does not look at the anchor).

`SplitRigidity` is stages 4 and 5 together.  This module proves stages 1 and 2, obtains
`SplitRigidity` from stage 4 alone (`splitRigidity_of_anchorExtension`, stage 5 being
valency-free), and assembles the census clause from stages 3--5 (`censusAt_of_stages`).

## The result, in one paragraph

Contract one target edge `t₁ = (a, b)` of an incoming cover so that the merged target vertex is
divalent; the anchor `A` has `nd(A) = 4` and `r₀(A) = 2`.  The endpoints split `(2,2)` (both
divalent, change one each) or `(1,3)`/`(3,1)` (a leaf of change two and a trivalent vertex of
change zero; `SecondEquation.valencySplit_of_twoStar`).  **At `(2,2)`** the pruned anchor
fibre is: one trivalent constituent `A_a`, `A_b` over each endpoint, joined by a surviving
internal occurrence `e₁` (`exists_R`, `exists_join`), and at most one divalent pass-through over
each endpoint (`pass_unique`), hanging on the trivalent constituent over the other endpoint
(`nd_three_of_attach`); every occurrence at a constituent survives, so indices are sizes
(`survive`, `sum_bd`, `sum_ndOver`).  **At a leaf split** the constituents carrying boundary
survivors are two trivalent unramified constituents over the trivalent endpoint
(`LeafInput.nd_three`, `home`), each with one survivor in each of the two limit directions, of
index its size (`exists_partner`, `index_eq`; no dangling occurrence at the anchor because
`N(A) = r₀(A) + 2 = 4 = nd(A)`, `survive_bd`).  The **split** of a cover is whether it is a leaf
split, which labelled survivors pass through a divalent constituent, and which labelled
survivors are paired (`Split`, `Reads`, `existsUnique_reads`; the pairing must be part of the
split, because the two cross pairings of a leaf split -- Types I and II over Base I -- have the
same leaf flag and pass set, and a split without them would make `SplitRigidity` false).
**It is determined by the pairing** of the four survivors at the
incoming stable vertices (`Paired`, the body of `ValencyThreeSplit.Paired`), the limit
directions and the limit indices (`AnchorInput.reads_iff`): a survivor passes through exactly
when it is paired across the two directions with a survivor of strictly larger index
(`DivInput.nd_two_iff`, `pass_iff`), and the cover is a leaf split exactly when the pairing is
across the directions and nothing passes through (`leaf_iff`).  Hence **stage 2**:
two covers with the same pairing on transported labels read the same split
(`split_eq_of_paired`, `regrowth_split_eq`) -- no arithmetic beyond the order of indices.

## What is proved

* §1 `localRamification_add_le`, `ram_add_ram_le`, `not_isDangling_of_nd_eq`,
  `card_incident_of_divalent`, `not_isDangling_of_divalent`, `sum_ndOver_eq_size`,
  `index_eq_size_of_unique`.
* §2 **`mem_of_closed`** (the pruned fibre's connectivity in closed-set form, from
  `PrunedContractionFibre.sourceVertexMap_eq_iff_surviving_walk`), `PairedE`.
* §3 the `(2,2)` split (`DivInput`): `sum_excess` (`Σ (nd - 2) = 2`), `eq_of_nd_three`,
  **`exists_R`**, `ram_eq_nd`, **`survive`**, `sum_ndOver`, `sum_bd`, `pass_cards`,
  `bd_nonempty`, `eq_R`, `intl_unique`, `ends_mem_pair`, `exists_other_end`,
  **`exists_join`**, **`nd_three_of_attach`**, `bd_card_one`, `size_ge_two`, `index_of_single`,
  `ne_join`, `index_intl_of_pass`, `bd_target_ne`, **`nd_two_iff`** (the pass-through
  criterion), `bd_nonempty_of_two`, **`pass_unique`**.
* §4 the leaf split (`LeafInput`): `side`, **`survive_bd`**, `bd_empty_of_leaf`,
  **`nd_three`**, `home`, `index_eq`, `exists_partner`, `eq_of_pairedE`.
* §5 `Labelling` (four injectively labelled survivors, no direction constraint),
  `Labelling.ndAt_eq`, `Labelling.transport`, `nonempty_labelling`; `lift`, `lift_ne`,
  `index_lift`, `lift_injective`, `sourceEdgeMap_lift`, `lift_target_eq_iff`,
  `exists_lift_eq`, `exists_home`, `home_eq`, **`Paired`**, `PassAt`.
* §6 `Split` (leaf flag, pass set, pairs), `PassOf`, `LeafOf`, `splitOf`, `LeafCover`, **`Reads`**, `existsUnique_reads`,
  `dirOf`, `idxOf`, `reads_iff_eq_splitOf`.
* §7 `passAt_iff_home`, `paired_iff_home`, `dir_ne_iff`, **`DivInput.pass_iff`**,
  **`DivInput.leaf_iff`**, `LeafInput.not_passAt`, `LeafInput.not_passOf`,
  **`LeafInput.pass_iff`**, **`LeafInput.leaf_iff`**.
* §8 `AnchorInput` (forest, merged vertex divalent, `nd(A) = 4`), `AnchorInput.cases` (the
  three splits), `pass_iff`, `leaf_iff`, **`AnchorInput.reads_iff`**, `splitOf_congr`,
  **`split_eq_of_paired`** (stage 2).
* §9 `RegrowthAnchor`, **`exists_regrowthAnchor`** (stage 1 at every facet regrowth of a
  non-loop slot whose merged target vertex is divalent),
  **`eq_limA_of_nonDanglingValency_eq_four`** (the anchor is the limit's only four-valent
  vertex; no coordinates needed), `sourceVertexEquiv_limA`, `exists_transport`,
  **`regrowth_split_eq`**.
* §10 `anchorOf`, `PairingMatch` (stage 3), `SplitRigidity` (stages 4--5), `V2Limit`,
  `v2Limit_of_facetPoint`, **`eq_of_stages`** (uniqueness of **all** classes at a valency-two
  metric limit), `subsingleton_left`/`_right`, **`exists_mSpecializesRight`/`Left`** (the
  metric existence transfers of `ColumnReceiptExport` for every class, not only odd ones),
  `CensusAt`, `metricCensus_iff_forall_censusAt`, `censusAt_of_subsingleton`,
  **`censusAt_of_stages`** (the `MetricCensus` clause at a valency-two metric limit of a
  Whitehead step's facet datum, index `Unit`).
* §11 `AnchorExtension`, `splitRigidity_of_anchorExtension` / `anchorExtension_of_splitRigidity`
  (stage 5 is valency-free: `ValencyThreeRigidity.frameIso_of_columns` applies verbatim),
  `ResolutionMatch`, `anchorExtension_of_resolutionMatch`, **`splitRigidity_of_resolutionMatch`**,
  `splitRigidity_of_subsingleton`.
* §12 non-vacuity: `byPartner` and four `example`s -- `splitOf` produces exactly the four
  pictures (merge, `3 + 1`, split members, leaf); `CensusAt` inhabited at the genus-six
  caterpillar core.

## Remarks

* Part II's count of exactly one morphism of each type at a valency-two limit has a
  combinatorial half, proved here: per labelled limit and per pairing (= type) the split is
  unique (`split_eq_of_paired`).  The rest is stages 3--5.
* Compared with valency three, the pairing alone (with the index order) pins the split, so no
  analogue of the arithmetic `AnchorIndices.Valid` of `ValencyThreeGeneral` is needed;
  conversely the fibre is not one of two pictures but `{A_a, A_b}` plus at most one
  pass-through per side, or the leaf picture.
* No position is built: the equal-ranges half of the census is the link transfer
  `ColumnReceiptExport.metricLinkReceipts`, made whole-fibre in
  `exists_mSpecializesRight`/`Left`.
* `PairingMatch` is existential in the limit isomorphism because of a loop at the anchor (a
  core slot parallel to `e₀`), where two pairings can be read over one core
  (`ValencyThreeSplit.swapIso`).  Labelled-metric uniqueness at a valency-two limit implies
  `SplitRigidity` (`splitRigidity_of_subsingleton`).

## What is not proved here (every hypothesis, explicitly)

* **`PairingMatch c y degree`** (stage 3: some labelled-metric isomorphism preserves the
  pairing) on both cores is a hypothesis here.  It is proved at every resolved datum
  downstream, by `ValencyTwoPairing.pairingMatch_of_side` (hence `pairingMatchSupply`).
* **`SplitRigidity c y degree`** (stages 4--5): a hypothesis *here*, reduced to
  `ResolutionMatch` (§11); both are proved downstream, in
  `DraismaVargasCount.ValencyTwoResolutionMatch`.
* **`V2Limit m`, `V2Limit (metricSwap m)`**: stage 1 for every presenting regrowth; discharged
  by `v2Limit_of_facetPoint` modulo the divalence of each presenting regrowth's merged target
  vertex, and from `CensusAssembly.V2Limit` in `DraismaVargasCount.ValencyTwoCensus`
  (`v2Limit_of_limitValency`).
* `3 ≤ degree`, `FacetGeneric` (for the transfers of `ColumnReceiptExport`); `hconn`, `3 ≤ n`,
  `y e₀ = 0` (stage 5).
* No `FacetParity` or `MetricCensus` composite is stated: the valency-three and valency-four
  limits are treated in other modules.
* Non-vacuity of `PairingMatch`, `SplitRigidity`, `AnchorExtension`, `ResolutionMatch`,
  `V2Limit`: no valency-two facet regrowth over a literal gluing datum is constructed here (as
  for `NonTrivalentValencyTwoAnchor.TwoBranchAnchor`), so their antecedents are not inhabited
  at a concrete instance; §12 inhabits the split machinery and `CensusAt` only.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.ValencyTwoSplit

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification
open W4StableSource WallDegeneration FullDimensionalSource PrunedFibreValency PrunedFibreTree
  FullContractionFibre
open ValencyThreeSplit (ndAt mem_ndAt card_ndAt size ram ram_eq sum_over_eq_size sum_le_size
  card_le_sum_index ram_nonneg ram_le_targetChange eq_of_ram_zero nonDanglingValency_two_le
  ndOver mem_ndOver fib intl mem_fib_iff mem_intl_of_ndAt intl_ends endOn endOn_spec
  card_intl_eq_sum card_filter_endOn_le card_fib_split side_of_huv card_ndOver_lt bdAt mem_bdAt
  card_ndAt_split sum_ndAt_split contracted_mem_incidentEdges not_mem_incidentEdges_other
  not_incident_both endOn_eq_of_incident target_mem_incidentEdges index_le_size)

/-! ## 1.  Local vocabulary: ramification budgets, full survival, harmonicity -/

section Local

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-- Two distinct blocks over one target vertex share its change. -/
theorem localRamification_add_le (hValid : data.Valid) (w : target.V)
    (B B' : (data.vertexPartition w).Blocks) (hne : B ≠ B') :
    data.localRamification w B + data.localRamification w B' ≤ data.targetChange w := by
  classical
  unfold GluingDatum.targetChange
  rw [← Finset.sum_pair hne]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun blk _ _ ↦ data.localRamification_nonneg w (hValid.2 w) blk)

/-- **Two source vertices over one target vertex share its change**: their local
ramifications add up to at most the change there. -/
theorem ram_add_ram_le (hValid : data.Valid) {X X' : data.SourceVertex} (hne : X ≠ X')
    (hw : X.1.1 = X'.1.1) : ram data X + ram data X' ≤ data.targetChange X.1.1 := by
  classical
  rcases X with ⟨⟨w, i⟩, hi⟩
  rcases X' with ⟨⟨w', i'⟩, hi'⟩
  simp only at hw
  subst hw
  have hne' : (⟨i, hi⟩ : (data.vertexPartition w).Blocks) ≠ ⟨i', hi'⟩ := by
    intro h
    apply hne
    have : i = i' := congrArg Subtype.val h
    subst this
    rfl
  exact localRamification_add_le data hValid w ⟨i, hi⟩ ⟨i', hi'⟩ hne'

/-- **Full survival**: when the surviving valency is the whole valency, every incident
occurrence survives. -/
theorem not_isDangling_of_nd_eq (X : data.SourceVertex)
    (hEq : nonDanglingValency data X = Fintype.card (IncidentSourceEdge data X))
    {e : data.SourceEdge} (he : Incident data e X) : ¬ IsDangling data e := by
  classical
  intro hd
  have hcard := StableLocalProperties.card_filter_not_isDangling_eq_nonDanglingValency data X
  have hlt : ((Finset.univ : Finset (IncidentSourceEdge data X)).filter
      (fun edge ↦ ¬ IsDangling data edge.1)).card <
      (Finset.univ : Finset (IncidentSourceEdge data X)).card :=
    Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨⟨e, he⟩, Finset.mem_univ _, by simpa using hd⟩)
  rw [hcard, Finset.card_univ, hEq] at hlt
  exact lt_irrefl _ hlt

/-- The valency at a source vertex over a divalent target vertex is `r + 2`. -/
theorem card_incident_of_divalent (X : data.SourceVertex)
    (h2 : (GluingDatum.incidentEdges X.1.1).card = 2) :
    (Fintype.card (IncidentSourceEdge data X) : ℤ) = ram data X + 2 := by
  have h := NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data X
  rw [h2] at h
  unfold ram
  rw [h]
  ring

/-- At a source vertex over a divalent target vertex with `nd = r + 2`, every incident
occurrence survives. -/
theorem not_isDangling_of_divalent (X : data.SourceVertex)
    (h2 : (GluingDatum.incidentEdges X.1.1).card = 2)
    (hnd : (nonDanglingValency data X : ℤ) = ram data X + 2)
    {e : data.SourceEdge} (he : Incident data e X) : ¬ IsDangling data e := by
  refine not_isDangling_of_nd_eq data X ?_ he
  have := card_incident_of_divalent data X h2
  omega

/-- **Harmonicity, surviving form**: if every occurrence at `X` over `t` survives, the
surviving ones over `t` have total index `|X|`. -/
theorem sum_ndOver_eq_size (X : data.SourceVertex) (t : target.edges)
    (ht : t ∈ GluingDatum.incidentEdges X.1.1)
    (hsurv : ∀ e : data.SourceEdge, Incident data e X → e.1.1 = t → ¬ IsDangling data e) :
    ∑ e ∈ ndOver data X t, (data.sourceEdgeIndex e : ℤ) = size data X := by
  classical
  rw [← sum_over_eq_size data X t ht]
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  ext e
  simp only [mem_ndOver, mem_ndAt, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨-, hi⟩, hT⟩
    exact ⟨hi, hT⟩
  · rintro ⟨hi, hT⟩
    exact ⟨⟨hsurv e hi hT, hi⟩, hT⟩

/-- The occurrence over one target edge at an unramified vertex, when all of them survive:
there is exactly one surviving occurrence there once there is one, and its index is `|X|`. -/
theorem index_eq_size_of_unique {X : data.SourceVertex}
    (hNoRet : ∀ e e' : data.SourceEdge, e ∈ ndAt data X →
      e' ∈ ndAt data X → e.1.1 = e'.1.1 → e = e')
    {e : data.SourceEdge} (he : e ∈ ndAt data X)
    (hsurv : ∀ f : data.SourceEdge, Incident data f X → f.1.1 = e.1.1 → ¬ IsDangling data f) :
    (data.sourceEdgeIndex e : ℤ) = size data X := by
  classical
  have ht := target_mem_incidentEdges data ((mem_ndAt data _ _).mp he).2
  rw [← sum_ndOver_eq_size data X e.1.1 ht hsurv]
  have hsing : ndOver data X e.1.1 = {e} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr ⟨(mem_ndOver data _ _ _).mpr ⟨he, rfl⟩, ?_⟩
    intro f hf
    rw [mem_ndOver] at hf
    exact hNoRet f e hf.1 he hf.2
  rw [hsing, Finset.sum_singleton]

end Local

/-! ## 2.  Closed sets of the pruned fibre: connectivity in usable form -/

section Closure

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)

/-- **The pruned fibre is connected, closed-set form.**  A set of source vertices closed under
the surviving internal occurrences (an internal occurrence has both ends in it or neither)
and meeting the pruned fibre contains all of it. -/
theorem mem_of_closed (S : Finset data.SourceVertex)
    (hS : ∀ e ∈ intl data hc hab hOne block,
      ((data.sourceEnds e).1 ∈ S ↔ (data.sourceEnds e).2 ∈ S))
    {X Y : data.SourceVertex} (hXS : X ∈ S) (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) : Y ∈ S := by
  classical
  have hXi := (mem_activeFibreVertices data hc hab hOne _ X).mp hX
  have hYi := (mem_activeFibreVertices data hc hab hOne _ Y).mp hY
  have hWalk := (PrunedContractionFibre.sourceVertexMap_eq_iff_surviving_walk data hc hab hOne hXi.2 hYi.2).mp
    (hXi.1.trans hYi.1.symm)
  suffices h : ∀ Z, Relation.ReflTransGen (PrunedContractionFibre.SurvivingFibreStep data contracted) X Z →
      Z ∈ fib data hc hab hOne block ∧ Z ∈ S from (h Y hWalk).2
  intro Z hZ
  induction hZ with
  | refl => exact ⟨hX, hXS⟩
  | @tail M Z _ hStep ih =>
    obtain ⟨hMf, hMS⟩ := ih
    obtain ⟨edge, hT, hSurv, hEnds⟩ := hStep
    have hMmap := ((mem_activeFibreVertices data hc hab hOne _ M).mp hMf).1
    have hMap := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne edge hT
    have hI : edge ∈ intl data hc hab hOne block := by
      rw [intl, mem_internalEdges]
      refine ⟨hSurv, hT, ?_⟩
      rcases hEnds with h | h
      · rw [h]; exact hMmap
      · rw [h] at hMap ⊢; rw [hMap]; exact hMmap
    have hZmap : sourceVertexMap data hc hab hOne Z = mergedVertex data hc hab hOne block := by
      rcases hEnds with h | h
      · rw [h] at hMap; rw [← hMap]; exact hMmap
      · rw [h] at hMap; rw [hMap]; exact hMmap
    have hZf : Z ∈ fib data hc hab hOne block := by
      rw [fib, mem_activeFibreVertices]
      exact ⟨hZmap, ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurv
        (incident_of_sourceEnds data hEnds.symm)⟩
    refine ⟨hZf, ?_⟩
    have := hS edge hI
    rcases hEnds with h | h
    · rw [h] at this; exact this.mp hMS
    · rw [h] at this; exact this.mpr hMS

/-- **Two constituents are one vertex of the incoming stable graph**: equal, or joined by a
surviving internal occurrence one of whose ends is divalent (smoothed away).  The edge form
of `ValencyThreeSplit.Paired`. -/
def PairedE (X Y : data.SourceVertex) : Prop :=
  X = Y ∨ ∃ e ∈ intl data hc hab hOne block, e ∈ ndAt data X ∧ e ∈ ndAt data Y ∧
    (nonDanglingValency data X = 2 ∨ nonDanglingValency data Y = 2)

end Closure

/-! ## 3.  The `(2,2)` split: both endpoints divalent, change one each -/

section Divalent

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)

/-- The inputs of the anchor analysis at an incoming cover whose contracted occurrence joins
two divalent target vertices (Part II §5.4, the `(2,2)` split of
`SecondEquation.valencySplit_of_twoStar`). -/
structure DivInput : Prop where
  forest : ContractionForest data a b contracted
  nd4 : nonDanglingValency (contractDatum data hc hab hOne) (mergedVertex data hc hab hOne block) = 4
  a2 : (GluingDatum.incidentEdges a).card = 2
  b2 : (GluingDatum.incidentEdges b).card = 2
  cha : data.targetChange a = 1
  chb : data.targetChange b = 1

namespace DivInput

variable {data hc hab hOne block}
variable (H : DivInput data hc hab hOne block)
include H

theorem compat : DanglingCompatible data hc hab hOne :=
  WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne H.forest

omit H in
theorem side {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    X.1.1 = a ∨ X.1.1 = b :=
  ((mem_fib_iff data hc hab hOne block X).mp hX).1

theorem div2 {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    (GluingDatum.incidentEdges X.1.1).card = 2 := by
  rcases side hX with h | h <;> rw [h]
  · exact H.a2
  · exact H.b2

theorem ch1 {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    data.targetChange X.1.1 = 1 := by
  rcases side hX with h | h <;> rw [h]
  · exact H.cha
  · exact H.chb

omit H in
include fd in
theorem nd_bounds {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    2 ≤ nonDanglingValency data X ∧ nonDanglingValency data X ≤ 3 :=
  ⟨nonDanglingValency_two_le data fd ((mem_fib_iff data hc hab hOne block X).mp hX).2.2,
    fd.trivalent X⟩

theorem nd_sub_le_ram {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    (nonDanglingValency data X : ℤ) - 2 ≤ ram data X :=
  NonTrivalentValencyTwoRigidity.nonDanglingValency_sub_two_le_localRamification_of_divalent
    data X (H.div2 hX)

include fd in
theorem ram_le_one {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    ram data X ≤ 1 := by
  have := ram_le_targetChange data fd X
  rw [H.ch1 hX] at this
  exact this

/-- `Σ (nd - 2) = 2` over the pruned fibre: the tree count and the occurrence accounting. -/
theorem sum_excess :
    ∑ X ∈ fib data hc hab hOne block, ((nonDanglingValency data X : ℤ) - 2) = 2 := by
  classical
  have hNe : (fib data hc hab hOne block).Nonempty :=
    activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne H.compat _
      (by rw [H.nd4]; norm_num)
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne
    H.forest block hNe
  have hSum := sum_nonDanglingValency_activeFibre data hc hab hOne H.compat
    (mergedVertex data hc hab hOne block)
  rw [H.nd4] at hSum
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hSum' : ∑ X ∈ fib data hc hab hOne block, (nonDanglingValency data X : ℤ) =
      4 + 2 * ((internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)).card : ℤ) := by
    exact_mod_cast hSum
  rw [hSum', fib, ← hTree]
  push_cast
  ring

include fd in
/-- **Two trivalent constituents on one side are impossible**: each carries ramification at
least one, and the side's change is one. -/
theorem eq_of_nd_three {X Y : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) (hX3 : nonDanglingValency data X = 3)
    (hY3 : nonDanglingValency data Y = 3) (hside : X.1.1 = Y.1.1) : X = Y := by
  by_contra hne
  have h := ram_add_ram_le data fd.valid hne hside
  have h1 := H.nd_sub_le_ram hX
  have h2 := H.nd_sub_le_ram hY
  rw [H.ch1 hX, hX3] at *
  rw [hY3] at h2
  push_cast at h1 h2
  omega

include fd in
/-- **The two trivalent constituents** `A_a`, `A_b`: exactly one over each endpoint. -/
theorem exists_R : ∃ Ra Rb : data.SourceVertex, Ra ∈ fib data hc hab hOne block ∧
    Rb ∈ fib data hc hab hOne block ∧ Ra.1.1 = a ∧ Rb.1.1 = b ∧
    nonDanglingValency data Ra = 3 ∧ nonDanglingValency data Rb = 3 := by
  classical
  set F := fib data hc hab hOne block
  set T := F.filter (fun X ↦ nonDanglingValency data X = 3) with hTdef
  have hT : T.card = 2 := by
    have h := H.sum_excess
    have h' : ∑ X ∈ F, ((nonDanglingValency data X : ℤ) - 2) =
        ∑ X ∈ F, (if nonDanglingValency data X = 3 then (1 : ℤ) else 0) := by
      refine Finset.sum_congr rfl fun X hX ↦ ?_
      have := nd_bounds fd hX
      split_ifs with h3
      · rw [h3]; norm_num
      · have : nonDanglingValency data X = 2 := by omega
        rw [this]; norm_num
    rw [h', Finset.sum_boole] at h
    exact_mod_cast h
  obtain ⟨X, Y, hXY, hTXY⟩ := Finset.card_eq_two.mp hT
  have hXT : X ∈ T := by rw [hTXY]; simp
  have hYT : Y ∈ T := by rw [hTXY]; simp
  obtain ⟨hXF, hX3⟩ := Finset.mem_filter.mp hXT
  obtain ⟨hYF, hY3⟩ := Finset.mem_filter.mp hYT
  have hside : X.1.1 ≠ Y.1.1 := fun h ↦ hXY (H.eq_of_nd_three fd hXF hYF hX3 hY3 h)
  rcases side hXF with hXa | hXb
  · have hYb : Y.1.1 = b := by
      rcases side hYF with h | h
      · exact absurd (hXa.trans h.symm) hside
      · exact h
    exact ⟨X, Y, hXF, hYF, hXa, hYb, hX3, hY3⟩
  · have hYa : Y.1.1 = a := by
      rcases side hYF with h | h
      · exact h
      · exact absurd (hXb.trans h.symm) hside
    exact ⟨Y, X, hYF, hXF, hYa, hXb, hY3, hX3⟩

include fd in
/-- The ramification of a fibre constituent is its surviving excess `nd - 2`. -/
theorem ram_eq_nd {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    ram data X = (nonDanglingValency data X : ℤ) - 2 := by
  classical
  have hb := nd_bounds fd hX
  have hle := H.nd_sub_le_ram hX
  have hr1 := H.ram_le_one fd hX
  by_cases h3 : nonDanglingValency data X = 3
  · rw [h3] at hle ⊢; push_cast at hle ⊢; omega
  · have h2 : nonDanglingValency data X = 2 := by omega
    rw [h2]
    obtain ⟨Ra, Rb, hRa, hRb, hRaa, hRbb, hRa3, hRb3⟩ := H.exists_R fd
    -- the trivalent constituent on `X`'s side
    have key : ∀ R, R ∈ fib data hc hab hOne block → nonDanglingValency data R = 3 →
        R.1.1 = X.1.1 → ram data X = 0 := by
      intro R hR hR3 hside
      have hne : X ≠ R := fun h ↦ h3 (h ▸ hR3)
      have hsum := ram_add_ram_le data fd.valid hne hside.symm
      rw [H.ch1 hX] at hsum
      have hR1 := H.nd_sub_le_ram hR
      rw [hR3] at hR1
      have := ram_nonneg data fd X
      push_cast at hR1
      omega
    rcases side hX with h | h
    · rw [key Ra hRa hRa3 (hRaa.trans h.symm)]; norm_num
    · rw [key Rb hRb hRb3 (hRbb.trans h.symm)]; norm_num

include fd in
/-- **Every occurrence at a fibre constituent survives** in the `(2,2)` split. -/
theorem survive {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {e : data.SourceEdge} (he : Incident data e X) : ¬ IsDangling data e :=
  not_isDangling_of_divalent data X (H.div2 hX) (by rw [H.ram_eq_nd fd hX]; ring) he

include fd in
theorem sum_ndOver {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    ∑ e ∈ ndOver data X contracted, (data.sourceEdgeIndex e : ℤ) = size data X :=
  sum_ndOver_eq_size data X contracted (contracted_mem_incidentEdges hc (side hX))
    (fun _ he _ ↦ H.survive fd hX he)

include fd in
theorem sum_bd {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    ∑ e ∈ bdAt data contracted X, (data.sourceEdgeIndex e : ℤ) = size data X := by
  have h := ram_eq data fd.danglingEdgeNoGlue X
  rw [H.ram_eq_nd fd hX, sum_ndAt_split data (contracted := contracted), H.sum_ndOver fd hX] at h
  linarith

include fd in
/-- **A divalent constituent is a pass-through**: one internal and one boundary survivor. -/
theorem pass_cards {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (h2 : nonDanglingValency data X = 2) :
    (ndOver data X contracted).card = 1 ∧ (bdAt data contracted X).card = 1 := by
  classical
  have hram0 : ram data X = 0 := by rw [H.ram_eq_nd fd hX, h2]; norm_num
  have hover : (ndOver data X contracted).card ≤ 1 := Finset.card_le_one.mpr fun e he e' he' ↦ by
    rw [mem_ndOver] at he he'
    exact eq_of_ram_zero data fd hram0 he.1 he'.1 (he.2.trans he'.2.symm)
  have hbd : (bdAt data contracted X).card ≤ 1 := Finset.card_le_one.mpr fun e he e' he' ↦ by
    have hT := ValencyThreeSplit.bdAt_target_eq_of_divalent data hc rfl (side hX) (H.div2 hX)
      he he'
    rw [mem_bdAt] at he he'
    exact eq_of_ram_zero data fd hram0 he.1 he'.1 hT
  have := card_ndAt_split data (contracted := contracted) X
  omega

include fd in
/-- A trivalent constituent carries a boundary survivor. -/
theorem bd_nonempty {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (h3 : nonDanglingValency data X = 3) : (bdAt data contracted X).Nonempty := by
  have hlt := card_ndOver_lt data fd (contracted := contracted) X (by omega) (H.ram_le_one fd hX)
  have := card_ndAt_split data (contracted := contracted) X
  exact Finset.card_pos.mp (by omega)

include fd in
/-- The trivalent constituent over the endpoint of a trivalent constituent is itself. -/
theorem eq_R {Ra Rb X : data.SourceVertex} (hRa : Ra ∈ fib data hc hab hOne block)
    (hRb : Rb ∈ fib data hc hab hOne block) (hRaa : Ra.1.1 = a) (hRbb : Rb.1.1 = b)
    (hRa3 : nonDanglingValency data Ra = 3) (hRb3 : nonDanglingValency data Rb = 3)
    (hX : X ∈ fib data hc hab hOne block) (hX3 : nonDanglingValency data X = 3) :
    X = Ra ∨ X = Rb := by
  rcases side hX with h | h
  · exact Or.inl (H.eq_of_nd_three fd hX hRa hX3 hRa3 (h.trans hRaa.symm))
  · exact Or.inr (H.eq_of_nd_three fd hX hRb hX3 hRb3 (h.trans hRbb.symm))

include fd in
/-- A pass-through has one internal occurrence. -/
theorem intl_unique {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (h2 : nonDanglingValency data X = 2) {e e' : data.SourceEdge}
    (he : e ∈ intl data hc hab hOne block) (he' : e' ∈ intl data hc hab hOne block)
    (heX : e ∈ ndAt data X) (he'X : e' ∈ ndAt data X) : e = e' := by
  have hc1 := (H.pass_cards fd hX h2).1
  exact Finset.card_le_one.mp (le_of_eq hc1) e
    ((mem_ndOver data _ _ _).mpr ⟨heX, (intl_ends data hc hab hOne block he).2.2.2.2.1⟩) e'
    ((mem_ndOver data _ _ _).mpr ⟨he'X, (intl_ends data hc hab hOne block he').2.2.2.2.1⟩)

omit H in
/-- The two ends of an occurrence incident to two distinct vertices are those vertices. -/
theorem ends_mem_pair {e : data.SourceEdge} {P Q : data.SourceVertex} (hPQ : P ≠ Q)
    (hP : Incident data e P) (hQ : Incident data e Q) :
    (data.sourceEnds e).1 ∈ ({P, Q} : Finset data.SourceVertex) ∧
      (data.sourceEnds e).2 ∈ ({P, Q} : Finset data.SourceVertex) := by
  rcases hP with h | h <;> rcases hQ with h' | h'
  · exact absurd (h.symm.trans h') hPQ
  · rw [h, h']; simp
  · rw [h, h']; simp
  · exact absurd (h.symm.trans h') hPQ

omit H in
/-- An internal occurrence has an end on the other side of each of its ends. -/
theorem exists_other_end {e : data.SourceEdge} (he : e ∈ intl data hc hab hOne block)
    {X : data.SourceVertex} (hX : Incident data e X) :
    ∃ Q ∈ fib data hc hab hOne block, e ∈ ndAt data Q ∧ Q.1.1 ≠ X.1.1 ∧ Q ≠ X := by
  obtain ⟨h1, h2, n1, n2, -, ha, hb⟩ := intl_ends data hc hab hOne block he
  rcases hX with h | h
  · refine ⟨(data.sourceEnds e).2, h2, n2, ?_, ?_⟩
    · rw [← h, ha, hb]; exact hab.symm
    · intro hEq; rw [← h] at hEq; rw [hEq, ha] at hb; exact hab hb
  · refine ⟨(data.sourceEnds e).1, h1, n1, ?_, ?_⟩
    · rw [← h, ha, hb]; exact hab
    · intro hEq; rw [← h] at hEq; rw [hEq, hb] at ha; exact hab ha.symm

include fd in
/-- **Connectivity at a `(2,2)` split**: the two trivalent constituents are joined by a
surviving internal occurrence.  Otherwise `A_a` and the pass-throughs hanging on it would be a
closed proper subset of the pruned fibre. -/
theorem exists_join {Ra Rb : data.SourceVertex} (hRa : Ra ∈ fib data hc hab hOne block)
    (hRb : Rb ∈ fib data hc hab hOne block) (hRaa : Ra.1.1 = a) (hRbb : Rb.1.1 = b)
    (hRb3 : nonDanglingValency data Rb = 3) :
    ∃ e₁ ∈ intl data hc hab hOne block, e₁ ∈ ndAt data Ra ∧ e₁ ∈ ndAt data Rb := by
  classical
  by_contra hno
  simp only [not_exists, not_and] at hno
  set S : Finset data.SourceVertex := insert Ra ((fib data hc hab hOne block).filter
    fun X ↦ ∃ e ∈ intl data hc hab hOne block, e ∈ ndAt data X ∧ e ∈ ndAt data Ra) with hSdef
  have hinc : ∀ {e X}, e ∈ ndAt data X → Incident data e X := fun h ↦ ((mem_ndAt data _ _).mp h).2
  have hS : ∀ e ∈ intl data hc hab hOne block,
      ((data.sourceEnds e).1 ∈ S ↔ (data.sourceEnds e).2 ∈ S) := by
    intro e he
    obtain ⟨h1, h2, n1, n2, -, ha, hb⟩ := intl_ends data hc hab hOne block he
    constructor
    · intro hm
      have hE1 : (data.sourceEnds e).1 = Ra := by
        rcases Finset.mem_insert.mp hm with h | h
        · exact h
        · obtain ⟨-, e', he', he'1, he'R⟩ := Finset.mem_filter.mp h
          by_contra hne
          exact not_incident_both data hne (ha.trans hRaa.symm) (hinc he'1) (hinc he'R)
      refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h2, e, he, n2, ?_⟩)
      rw [← hE1]; exact n1
    · intro hm
      have hne : (data.sourceEnds e).2 ≠ Ra := by
        intro h; rw [h, hRaa] at hb; exact hab hb
      obtain ⟨-, e', he', he'2, he'R⟩ :=
        Finset.mem_filter.mp ((Finset.mem_insert.mp hm).resolve_left hne)
      have h2nd : nonDanglingValency data (data.sourceEnds e).2 = 2 := by
        have hb3 := nd_bounds fd h2
        by_contra h3
        have h3' : nonDanglingValency data (data.sourceEnds e).2 = 3 := by omega
        have hEq := H.eq_of_nd_three fd h2 hRb h3' hRb3 (hb.trans hRbb.symm)
        rw [hEq] at he'2
        exact hno e' he' he'R he'2
      have hee' := H.intl_unique fd h2 h2nd he he' n2 he'2
      subst hee'
      have hE1 : (data.sourceEnds e).1 = Ra := by
        by_contra hne'
        exact not_incident_both data hne' (ha.trans hRaa.symm) (hinc n1) (hinc he'R)
      rw [hE1]; exact Finset.mem_insert_self _ _
  have hRbS := mem_of_closed data hc hab hOne block S hS (Finset.mem_insert_self _ _) hRa hRb
  rcases Finset.mem_insert.mp hRbS with h | h
  · rw [h, hRaa] at hRbb; exact hab hRbb
  · obtain ⟨-, e', he', he'b, he'a⟩ := Finset.mem_filter.mp h
    exact hno e' he' he'a he'b

include fd in
/-- **A pass-through hangs on a trivalent constituent**: the other end of its internal
occurrence has surviving valency three. -/
theorem nd_three_of_attach {P Q : data.SourceVertex} (hP : P ∈ fib data hc hab hOne block)
    (hP2 : nonDanglingValency data P = 2) (hQ : Q ∈ fib data hc hab hOne block)
    {e : data.SourceEdge} (he : e ∈ intl data hc hab hOne block) (heP : e ∈ ndAt data P)
    (heQ : e ∈ ndAt data Q) (hPQ : P ≠ Q) : nonDanglingValency data Q = 3 := by
  classical
  by_contra h3
  have hQ2 : nonDanglingValency data Q = 2 := by
    have := nd_bounds fd hQ; omega
  have hinc : ∀ {e X}, e ∈ ndAt data X → Incident data e X := fun h ↦ ((mem_ndAt data _ _).mp h).2
  have hS : ∀ e' ∈ intl data hc hab hOne block,
      ((data.sourceEnds e').1 ∈ ({P, Q} : Finset data.SourceVertex) ↔
        (data.sourceEnds e').2 ∈ ({P, Q} : Finset data.SourceVertex)) := by
    intro e' he'
    obtain ⟨-, -, n1, n2, -, -, -⟩ := intl_ends data hc hab hOne block he'
    have key : ∀ X, X ∈ ({P, Q} : Finset data.SourceVertex) → e' ∈ ndAt data X → e' = e := by
      intro X hX hX'
      rcases Finset.mem_insert.mp hX with rfl | hX
      · exact H.intl_unique fd hP hP2 he' he hX' heP
      · rw [Finset.mem_singleton.mp hX] at hX'
        exact H.intl_unique fd hQ hQ2 he' he hX' heQ
    have hpair := ends_mem_pair hPQ (hinc heP) (hinc heQ)
    constructor
    · intro hm; rw [key _ hm n1]; exact hpair.2
    · intro hm; rw [key _ hm n2]; exact hpair.1
  obtain ⟨Ra, Rb, hRa, hRb, -, -, hRa3, -⟩ := H.exists_R fd
  have hRaS := mem_of_closed data hc hab hOne block {P, Q} hS (Finset.mem_insert_self _ _) hP hRa
  rcases Finset.mem_insert.mp hRaS with h | h
  · rw [h] at hRa3; omega
  · rw [Finset.mem_singleton.mp h] at hRa3; omega

include fd in
/-- A trivalent constituent with two internal occurrences has a single boundary survivor. -/
theorem bd_card_one {X : data.SourceVertex} (hX3 : nonDanglingValency data X = 3)
    {e e' : data.SourceEdge} (he : e ∈ ndOver data X contracted)
    (he' : e' ∈ ndOver data X contracted) (hne : e ≠ e') (hX : X ∈ fib data hc hab hOne block) :
    (bdAt data contracted X).card = 1 := by
  classical
  have h2 : 2 ≤ (ndOver data X contracted).card := by
    have : ({e, e'} : Finset data.SourceEdge) ⊆ ndOver data X contracted := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact he
      · rw [Finset.mem_singleton.mp hx]; exact he'
    have := Finset.card_le_card this
    rwa [Finset.card_pair hne] at this
  have hne' := (H.bd_nonempty fd hX hX3).card_pos
  have := card_ndAt_split data (contracted := contracted) X
  omega

include fd in
/-- Two internal occurrences at a constituent bound its size from below. -/
theorem size_ge_two {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {e e' : data.SourceEdge} (he : e ∈ ndOver data X contracted)
    (he' : e' ∈ ndOver data X contracted) (hne : e ≠ e') :
    (data.sourceEdgeIndex e : ℤ) + 1 ≤ size data X := by
  classical
  rw [← H.sum_ndOver fd hX]
  have hsub : ({e, e'} : Finset data.SourceEdge) ⊆ ndOver data X contracted := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact he
    · rw [Finset.mem_singleton.mp hx]; exact he'
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun f ↦ (data.sourceEdgeIndex f : ℤ))
    hsub (fun _ _ _ ↦ by positivity)
  rw [Finset.sum_pair hne] at hle
  have := StableLocalProperties.sourceEdgeIndex_pos data e'
  omega

include fd in
/-- The index of the only boundary survivor, and of the only internal occurrence, of a
constituent is its size. -/
theorem index_of_single {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {f : data.SourceEdge} (hf : f ∈ bdAt data contracted X)
    (h1 : (bdAt data contracted X).card = 1) : (data.sourceEdgeIndex f : ℤ) = size data X := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h1
  rw [hg, Finset.mem_singleton] at hf
  subst hf
  rw [← H.sum_bd fd hX, hg, Finset.sum_singleton]

omit H in
/-- An occurrence at a pass-through is not the join of the two trivalent constituents. -/
theorem ne_join {Ra Rb Z : data.SourceVertex} (hRa3 : nonDanglingValency data Ra = 3)
    (hRb3 : nonDanglingValency data Rb = 3) (hRaa : Ra.1.1 = a) (hRbb : Rb.1.1 = b)
    (hZ : Z ∈ fib data hc hab hOne block) (hZ2 : nonDanglingValency data Z = 2)
    {e e₁ : data.SourceEdge} (heZ : e ∈ ndAt data Z) (he₁a : e₁ ∈ ndAt data Ra)
    (he₁b : e₁ ∈ ndAt data Rb) : e ≠ e₁ := by
  rintro rfl
  have hinc : ∀ {e X}, e ∈ ndAt data X → Incident data e X := fun h ↦ ((mem_ndAt data _ _).mp h).2
  rcases side hZ with h | h
  · have : Z = Ra := by
      by_contra hne
      exact not_incident_both data hne (h.trans hRaa.symm) (hinc heZ) (hinc he₁a)
    rw [this, hRa3] at hZ2; omega
  · have : Z = Rb := by
      by_contra hne
      exact not_incident_both data hne (h.trans hRbb.symm) (hinc heZ) (hinc he₁b)
    rw [this, hRb3] at hZ2; omega

include fd in
/-- The internal occurrence of a pass-through has index its size. -/
theorem index_intl_of_pass {Z : data.SourceVertex} (hZ : Z ∈ fib data hc hab hOne block)
    (hZ2 : nonDanglingValency data Z = 2) {e : data.SourceEdge}
    (he : e ∈ ndOver data Z contracted) : (data.sourceEdgeIndex e : ℤ) = size data Z := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp (H.pass_cards fd hZ hZ2).1
  rw [hg, Finset.mem_singleton] at he
  subst he
  rw [← H.sum_ndOver fd hZ, hg, Finset.sum_singleton]

omit H in
/-- Boundary survivors over different endpoints lie over different target occurrences. -/
theorem bd_target_ne {X Y : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hY : Y ∈ fib data hc hab hOne block) (hXY : X.1.1 ≠ Y.1.1) {f g : data.SourceEdge}
    (hf : f ∈ bdAt data contracted X) (hg : g ∈ bdAt data contracted Y) : g.1.1 ≠ f.1.1 := by
  intro hEq
  have huv : (X.1.1 = a ∧ Y.1.1 = b) ∨ (X.1.1 = b ∧ Y.1.1 = a) := by
    rcases side hX with h | h <;> rcases side hY with h' | h'
    · exact absurd (h.trans h'.symm) hXY
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩
    · exact absurd (h.trans h'.symm) hXY
  obtain ⟨hf1, hf2⟩ := (mem_bdAt data _ _).mp hf
  obtain ⟨hg1, -⟩ := (mem_bdAt data _ _).mp hg
  have hfX := target_mem_incidentEdges data ((mem_ndAt data _ _).mp hf1).2
  have hgY := target_mem_incidentEdges data ((mem_ndAt data _ _).mp hg1).2
  rw [hEq] at hgY
  exact not_mem_incidentEdges_other hc hab hOne huv hfX hf2 hgY

include fd in
/-- **The pass-through criterion at a `(2,2)` split.**  A boundary survivor `f` lies at a
divalent constituent exactly when it is paired, across the two target directions, with a
boundary survivor of strictly larger index.  (At a pass-through `P` hanging on `A_s`,
`k(f) = |P| < |A_s| = k(g)` for the survivor `g` at `A_s`; at a trivalent constituent every
partner is either at the same vertex, in the same direction, or at a pass-through, of smaller
index.) -/
theorem nd_two_iff {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {f : data.SourceEdge} (hf : f ∈ bdAt data contracted X) :
    nonDanglingValency data X = 2 ↔ ∃ Y ∈ fib data hc hab hOne block,
      ∃ g ∈ bdAt data contracted Y, PairedE data hc hab hOne block X Y ∧ g.1.1 ≠ f.1.1 ∧
        data.sourceEdgeIndex f < data.sourceEdgeIndex g := by
  classical
  have hinc : ∀ {e X}, e ∈ ndAt data X → Incident data e X := fun h ↦ ((mem_ndAt data _ _).mp h).2
  obtain ⟨Ra, Rb, hRa, hRb, hRaa, hRbb, hRa3, hRb3⟩ := H.exists_R fd
  obtain ⟨e₁, he₁, he₁a, he₁b⟩ := H.exists_join fd hRa hRb hRaa hRbb hRb3
  have he₁T := (intl_ends data hc hab hOne block he₁).2.2.2.2.1
  have hjoin : ∀ {Q}, Q ∈ fib data hc hab hOne block → nonDanglingValency data Q = 3 →
      e₁ ∈ ndOver data Q contracted := by
    intro Q hQ hQ3
    rcases H.eq_R fd hRa hRb hRaa hRbb hRa3 hRb3 hQ hQ3 with rfl | rfl
    · exact (mem_ndOver data _ _ _).mpr ⟨he₁a, he₁T⟩
    · exact (mem_ndOver data _ _ _).mpr ⟨he₁b, he₁T⟩
  constructor
  · intro h2
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp (H.pass_cards fd hX h2).1
    have heO : e ∈ ndOver data X contracted := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨heX, heT⟩ := (mem_ndOver data _ _ _).mp heO
    have heI := mem_intl_of_ndAt data hc hab hOne block hX heX heT
    obtain ⟨Q, hQ, heQ, hQside, hQX⟩ := exists_other_end heI (hinc heX)
    have hQ3 := H.nd_three_of_attach fd hX h2 hQ heI heX heQ hQX.symm
    have hne := ne_join hRa3 hRb3 hRaa hRbb hX h2 heX he₁a he₁b
    have heOQ : e ∈ ndOver data Q contracted := (mem_ndOver data _ _ _).mpr ⟨heQ, heT⟩
    have hbd1 := H.bd_card_one fd hQ3 heOQ (hjoin hQ hQ3) hne hQ
    obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hbd1
    have hgQ : g ∈ bdAt data contracted Q := by rw [hg]; exact Finset.mem_singleton_self g
    refine ⟨Q, hQ, g, hgQ, Or.inr ⟨e, heI, heX, heQ, Or.inl h2⟩,
      bd_target_ne hX hQ hQside.symm hf hgQ, ?_⟩
    have i1 := H.index_of_single fd hQ hgQ hbd1
    have i2 := H.size_ge_two fd hQ heOQ (hjoin hQ hQ3) hne
    have i3 := H.index_intl_of_pass fd hX h2 heO
    have i4 := H.index_of_single fd hX hf (H.pass_cards fd hX h2).2
    have : (data.sourceEdgeIndex f : ℤ) < data.sourceEdgeIndex g := by omega
    exact_mod_cast this
  · rintro ⟨Y, hY, g, hg, hP, hdir, hlt⟩
    by_contra h2
    have hX3 : nonDanglingValency data X = 3 := by have := nd_bounds fd hX; omega
    rcases hP with rfl | ⟨e, heI, heX, heY, hnd⟩
    · exact hdir (ValencyThreeSplit.bdAt_target_eq_of_divalent data hc rfl (side hX)
        (H.div2 hX) hg hf)
    · have hY2 : nonDanglingValency data Y = 2 := hnd.resolve_left h2
      have heT := (intl_ends data hc hab hOne block heI).2.2.2.2.1
      have hne := ne_join hRa3 hRb3 hRaa hRbb hY hY2 heY he₁a he₁b
      have heOX : e ∈ ndOver data X contracted := (mem_ndOver data _ _ _).mpr ⟨heX, heT⟩
      have hbd1 := H.bd_card_one fd hX3 heOX (hjoin hX hX3) hne hX
      have i1 := H.index_of_single fd hX hf hbd1
      have i2 := H.size_ge_two fd hX heOX (hjoin hX hX3) hne
      have i3 := H.index_intl_of_pass fd hY hY2 ((mem_ndOver data _ _ _).mpr ⟨heY, heT⟩)
      have i4 := H.index_of_single fd hY hg (H.pass_cards fd hY hY2).2
      have : (data.sourceEdgeIndex g : ℤ) < data.sourceEdgeIndex f := by omega
      exact absurd hlt (not_lt.mpr (le_of_lt (by exact_mod_cast this)))

include fd in
/-- A pass-through carries a boundary survivor. -/
theorem bd_nonempty_of_two {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (h2 : nonDanglingValency data X = 2) : (bdAt data contracted X).Nonempty :=
  Finset.card_pos.mp (by rw [(H.pass_cards fd hX h2).2]; norm_num)

include fd in
/-- **At most one pass-through over each endpoint**: two would hang on the trivalent
constituent over the other endpoint, which already carries the join `e₁`, giving it three
internal occurrences. -/
theorem pass_unique {P P' : data.SourceVertex} (hP : P ∈ fib data hc hab hOne block)
    (hP' : P' ∈ fib data hc hab hOne block) (hP2 : nonDanglingValency data P = 2)
    (hP'2 : nonDanglingValency data P' = 2) (hside : P.1.1 = P'.1.1) : P = P' := by
  classical
  by_contra hne
  have hinc : ∀ {e X}, e ∈ ndAt data X → Incident data e X := fun h ↦ ((mem_ndAt data _ _).mp h).2
  obtain ⟨Ra, Rb, hRa, hRb, hRaa, hRbb, hRa3, hRb3⟩ := H.exists_R fd
  obtain ⟨e₁, he₁, he₁a, he₁b⟩ := H.exists_join fd hRa hRb hRaa hRbb hRb3
  have he₁T := (intl_ends data hc hab hOne block he₁).2.2.2.2.1
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp (H.pass_cards fd hP hP2).1
  obtain ⟨e', he'⟩ := Finset.card_eq_one.mp (H.pass_cards fd hP' hP'2).1
  have heO : e ∈ ndOver data P contracted := by rw [he]; exact Finset.mem_singleton_self e
  have he'O : e' ∈ ndOver data P' contracted := by rw [he']; exact Finset.mem_singleton_self e'
  obtain ⟨heP, heT⟩ := (mem_ndOver data _ _ _).mp heO
  obtain ⟨he'P, he'T⟩ := (mem_ndOver data _ _ _).mp he'O
  have heI := mem_intl_of_ndAt data hc hab hOne block hP heP heT
  have he'I := mem_intl_of_ndAt data hc hab hOne block hP' he'P he'T
  obtain ⟨Q, hQ, heQ, hQs, hQP⟩ := exists_other_end heI (hinc heP)
  obtain ⟨Q', hQ', he'Q', hQ's, hQ'P⟩ := exists_other_end he'I (hinc he'P)
  have hQ3 := H.nd_three_of_attach fd hP hP2 hQ heI heP heQ hQP.symm
  have hQ'3 := H.nd_three_of_attach fd hP' hP'2 hQ' he'I he'P he'Q' hQ'P.symm
  have hQQ' : Q = Q' := by
    refine H.eq_of_nd_three fd hQ hQ' hQ3 hQ'3 ?_
    rcases side hQ with h | h <;> rcases side hQ' with h' | h'
    · exact h.trans h'.symm
    · exfalso; rcases side hP with hp | hp
      · exact hQs (h.trans hp.symm)
      · rw [hside] at hp; exact hQ's (h'.trans hp.symm)
    · exfalso; rcases side hP with hp | hp
      · rw [hside] at hp; exact hQ's (h'.trans hp.symm)
      · exact hQs (h.trans hp.symm)
    · exact h.trans h'.symm
  subst hQQ'
  have hee' : e ≠ e' := by
    rintro rfl
    exact hne (by
      by_contra hne'
      exact not_incident_both data hne' hside (hinc heP) (hinc he'P))
  have hne₁ := ne_join hRa3 hRb3 hRaa hRbb hP hP2 heP he₁a he₁b
  have hne₁' := ne_join hRa3 hRb3 hRaa hRbb hP' hP'2 he'P he₁a he₁b
  have hsub : ({e, e', e₁} : Finset data.SourceEdge) ⊆ ndOver data Q contracted := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (mem_ndOver data _ _ _).mpr ⟨heQ, heT⟩
    · exact (mem_ndOver data _ _ _).mpr ⟨he'Q', he'T⟩
    · rcases H.eq_R fd hRa hRb hRaa hRbb hRa3 hRb3 hQ hQ3 with rfl | rfl
      · exact (mem_ndOver data _ _ _).mpr ⟨he₁a, he₁T⟩
      · exact (mem_ndOver data _ _ _).mpr ⟨he₁b, he₁T⟩
  have hcard3 : ({e, e', e₁} : Finset data.SourceEdge).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne₁']
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hee', hne₁⟩
  have hlt := card_ndOver_lt data fd (contracted := contracted) Q (by omega) (H.ram_le_one fd hQ)
  have := Finset.card_le_card hsub
  omega

end DivInput

end Divalent

/-! ## 4.  The leaf split: one endpoint a target leaf (change two), the other trivalent -/

section Leaf

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)
  (u v : target.V)

/-- The inputs of the anchor analysis at an incoming cover whose contracted occurrence joins a
target leaf `u` (change two) to a trivalent vertex `v` (change zero): the `(1,3)`/`(3,1)`
splits of `SecondEquation.valencySplit_of_twoStar`. -/
structure LeafInput : Prop where
  forest : ContractionForest data a b contracted
  nd4 : nonDanglingValency (contractDatum data hc hab hOne) (mergedVertex data hc hab hOne block) = 4
  valency : (GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩).card = 2
  huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  u1 : (GluingDatum.incidentEdges u).card = 1
  v3 : (GluingDatum.incidentEdges v).card = 3
  chu : data.targetChange u = 2
  chv : data.targetChange v = 0

namespace LeafInput

variable {data hc hab hOne block u v}
variable (H : LeafInput data hc hab hOne block u v)
include H

theorem compat : DanglingCompatible data hc hab hOne :=
  WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne H.forest

theorem side {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block) :
    X.1.1 = u ∨ X.1.1 = v := by
  rcases ((mem_fib_iff data hc hab hOne block X).mp hX).1 with h | h <;>
    rcases H.huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr h
  · exact Or.inl h

include fd in
/-- **No dangling occurrence at the anchor**: `N(A) = r₀(A) + 2 = 4 = nd(A)`, so every
non-contracted occurrence at a fibre constituent survives. -/
theorem survive_bd {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {e : data.SourceEdge} (he : Incident data e X) (hT : e.1.1 ≠ contracted) :
    ¬ IsDangling data e := by
  classical
  have hram := NonTrivalentValencyTwoRigidity.localRamification_eq_two data fd hc hab hOne
    H.forest H.compat (W2R1Target.TwoStar.of_card H.valency) block H.nd4
  have hN := NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form
    (contractDatum data hc hab hOne) (mergedVertex data hc hab hOne block)
  have hval : (GluingDatum.incidentEdges (mergedVertex data hc hab hOne block).1.1).card = 2 :=
    H.valency
  rw [hval] at hN
  have hEq : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) =
      Fintype.card (IncidentSourceEdge (contractDatum data hc hab hOne)
        (mergedVertex data hc hab hOne block)) := by
    have hr : (contractDatum data hc hab hOne).localRamification
        (mergedVertex data hc hab hOne block).1.1
        ⟨(mergedVertex data hc hab hOne block).1.2, (mergedVertex data hc hab hOne block).2⟩ =
        2 := hram
    rw [hr] at hN
    rw [H.nd4]
    push_cast at hN
    omega
  intro hBad
  have hmap := ((mem_activeFibreVertices data hc hab hOne _ X).mp hX).1
  have hInc : Incident (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne ⟨e, hT⟩)
      (mergedVertex data hc hab hOne block) := by
    unfold Incident
    rw [sourceEnds_sourceEdgeMap]
    rcases he with h | h
    · left; rw [h]; exact hmap
    · right; rw [h]; exact hmap
  exact not_isDangling_of_nd_eq _ _ hEq hInc (H.compat.1 ⟨e, hT⟩ hBad)

/-- A constituent over the leaf has no boundary survivor. -/
theorem bd_empty_of_leaf {X : data.SourceVertex} (hXu : X.1.1 = u) :
    bdAt data contracted X = ∅ := by
  classical
  ext f
  simp only [Finset.notMem_empty, iff_false]
  intro hf
  obtain ⟨hf1, hf2⟩ := (mem_bdAt data _ _).mp hf
  have hfu := target_mem_incidentEdges data ((mem_ndAt data _ _).mp hf1).2
  rw [hXu] at hfu
  have hcu := contracted_mem_incidentEdges hc (side_of_huv hab H.huv).1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp H.u1
  rw [ht, Finset.mem_singleton] at hfu hcu
  exact hf2 (hfu.trans hcu.symm)

include fd in
/-- **The leaf fibre** (Part II, the Base I picture): every constituent over the trivalent
endpoint has surviving valency three.  (One ramification-two constituent `L` of surviving
valency two over the leaf, joined to exactly two constituents `Y`, `Z` over `v`.) -/
theorem nd_three {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hXv : X.1.1 = v) : nonDanglingValency data X = 3 := by
  classical
  obtain ⟨huw, hvw, huv'⟩ := side_of_huv hab H.huv
  set F := fib data hc hab hOne block with hFdef
  set I := intl data hc hab hOne block with hIdef
  set Fu := F.filter (fun X ↦ X.1.1 = u) with hFudef
  set Fv := F.filter (fun X ↦ X.1.1 = v) with hFvdef
  have hNe : F.Nonempty := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero
    data hc hab hOne H.compat _ (by rw [H.nd4]; norm_num)
  have hTree : I.card + 1 = F.card :=
    internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne H.forest block hNe
  have hSum : ∑ X ∈ F, nonDanglingValency data X = 4 + 2 * I.card := by
    rw [hFdef, fib, sum_nonDanglingValency_activeFibre data hc hab hOne H.compat, H.nd4]
  have hSplit : Fu.card + Fv.card = F.card := card_fib_split data hc hab hOne block H.huv
  have hFv_eq : F.filter (fun X ↦ ¬ X.1.1 = u) = Fv := by
    ext Y
    simp only [hFvdef, Finset.mem_filter]
    constructor
    · rintro ⟨hY, hYu⟩; exact ⟨hY, (H.side hY).resolve_left hYu⟩
    · rintro ⟨hY, hYv⟩; exact ⟨hY, fun h ↦ huv' (h.symm.trans hYv)⟩
  have hSumSplit : ∑ X ∈ F, nonDanglingValency data X =
      ∑ X ∈ Fu, nonDanglingValency data X + ∑ X ∈ Fv, nonDanglingValency data X := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun X ↦ X.1.1 = u), hFv_eq]
  -- over the leaf: at most one active constituent, of surviving valency two
  have hram2 : ∀ Y ∈ Fu, 2 ≤ ram data Y := fun Y hY ↦ by
    obtain ⟨hYF, hYu⟩ := Finset.mem_filter.mp hY
    exact NonTrivalentValencyTwoRigidity.two_le_localRamification_of_target_leaf data fd.connected
      Y (by rw [hYu]; exact H.u1) ((mem_fib_iff data hc hab hOne block Y).mp hYF).2.2
  have hFu1 : Fu.card ≤ 1 := Finset.card_le_one.mpr fun Y hY Y' hY' ↦ by
    by_contra hne
    have h := ram_add_ram_le data fd.valid hne
      ((Finset.mem_filter.mp hY).2.trans (Finset.mem_filter.mp hY').2.symm)
    rw [(Finset.mem_filter.mp hY).2, H.chu] at h
    have := hram2 Y hY
    have := hram2 Y' hY'
    omega
  have hnd2 : ∀ Y ∈ Fu, nonDanglingValency data Y = 2 := fun Y hY ↦ by
    obtain ⟨hYF, hYu⟩ := Finset.mem_filter.mp hY
    have hN := NonDanglingValency.card_incidentSourceEdge_eq_localRamification_form data Y
    have hLe := StableLocalProperties.card_incidentSourceEdge_le_blockCard_of_target_leaf data Y
      (by rw [hYu]; exact H.u1)
    have hnd := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge data Y
    have hr := ram_le_targetChange data fd Y
    rw [hYu, H.chu] at hr
    have hcard : (GluingDatum.incidentEdges Y.1.1).card = 1 := by rw [hYu]; exact H.u1
    rw [hcard] at hN
    have hN' : (Fintype.card (IncidentSourceEdge data Y) : ℤ) =
        ram data Y + 2 - ((data.vertexPartition Y.1.1).blockCard Y.1.2 : ℤ) := by
      rw [hN]; unfold ram; push_cast; ring
    have h2 := nonDanglingValency_two_le data fd ((mem_fib_iff data hc hab hOne block Y).mp hYF).2.2
    have : (nonDanglingValency data Y : ℤ) ≤ Fintype.card (IncidentSourceEdge data Y) := by
      exact_mod_cast hnd
    omega
  -- over the trivalent endpoint: unramified, at most one internal occurrence each
  have hvram : ∀ Y ∈ Fv, ram data Y = 0 := fun Y hY ↦
    W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd Y
      (by rw [(Finset.mem_filter.mp hY).2]; exact H.chv)
  have hcntv : ∀ Y ∈ Fv, (I.filter (fun e ↦ endOn data e v = Y)).card ≤ 1 := fun Y hY ↦
    (card_filter_endOn_le data hc hab hOne block hvw Y).trans
      (Finset.card_le_one.mpr fun e he e' he' ↦ by
        rw [mem_ndOver] at he he'
        exact eq_of_ram_zero data fd (hvram Y hY) he.1 he'.1 (he.2.trans he'.2.symm))
  have hIv : I.card ≤ Fv.card := by
    rw [hIdef, card_intl_eq_sum data hc hab hOne block hvw]
    calc _ ≤ ∑ _X ∈ Fv, 1 := Finset.sum_le_sum hcntv
      _ = Fv.card := by simp
  have hIu : I.card ≤ 2 * Fu.card := by
    rw [hIdef, card_intl_eq_sum data hc hab hOne block huw, ← hIdef, ← hFdef, ← hFudef]
    calc _ ≤ ∑ _X ∈ Fu, 2 := Finset.sum_le_sum fun Y hY ↦ by
          refine (card_filter_endOn_le data hc hab hOne block huw Y).trans ?_
          rw [← hnd2 Y hY, ← card_ndAt]
          exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 * Fu.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hSumFu : ∑ Y ∈ Fu, nonDanglingValency data Y = 2 * Fu.card := by
    rw [Finset.sum_congr rfl hnd2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hFvle : ∀ Y ∈ Fv, nonDanglingValency data Y ≤ 3 := fun Y _ ↦ fd.trivalent Y
  have h3 : ∑ Y ∈ Fv, nonDanglingValency data Y ≤ 3 * Fv.card := by
    calc _ ≤ ∑ _Y ∈ Fv, 3 := Finset.sum_le_sum hFvle
      _ = 3 * Fv.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hFv2 : Fv.card = 2 := by omega
  have hFvsum : ∑ Y ∈ Fv, nonDanglingValency data Y = 6 := by omega
  obtain ⟨Y, Z, hYZ, hFvYZ⟩ := Finset.card_eq_two.mp hFv2
  have hXFv : X ∈ Fv := Finset.mem_filter.mpr ⟨hX, hXv⟩
  rw [hFvYZ, Finset.sum_pair hYZ] at hFvsum
  have hY3 := hFvle Y (by rw [hFvYZ]; simp)
  have hZ3 := hFvle Z (by rw [hFvYZ]; simp)
  rw [hFvYZ] at hXFv
  rcases Finset.mem_insert.mp hXFv with rfl | hXZ
  · omega
  · rw [Finset.mem_singleton.mp hXZ]; omega

include fd in
/-- The home of a boundary survivor at a leaf split: a trivalent, unramified constituent over
`v`. -/
theorem home {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {f : data.SourceEdge} (hf : f ∈ bdAt data contracted X) :
    X.1.1 = v ∧ nonDanglingValency data X = 3 ∧ ram data X = 0 := by
  have hXv : X.1.1 = v := by
    rcases H.side hX with h | h
    · rw [H.bd_empty_of_leaf h] at hf; simp at hf
    · exact h
  refine ⟨hXv, H.nd_three fd hX hXv, ?_⟩
  exact W4IncomingCensus.AnyWall.localRamification_eq_zero_at_endpoint data fd X
    (by rw [hXv]; exact H.chv)

include fd in
/-- **Equal indices at a leaf-split constituent**: both boundary survivors have index `|X|`. -/
theorem index_eq {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {f : data.SourceEdge} (hf : f ∈ bdAt data contracted X) :
    (data.sourceEdgeIndex f : ℤ) = size data X := by
  obtain ⟨-, -, hr⟩ := H.home fd hX hf
  obtain ⟨hf1, hf2⟩ := (mem_bdAt data _ _).mp hf
  exact index_eq_size_of_unique data (fun e e' he he' hT ↦ eq_of_ram_zero data fd hr he he' hT)
    hf1 (fun g hg hgT ↦ H.survive_bd fd hX hg (hgT ▸ hf2))

include fd in
/-- **The partner at a leaf-split constituent**: a second boundary survivor, in the other
direction. -/
theorem exists_partner {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {f : data.SourceEdge} (hf : f ∈ bdAt data contracted X) :
    ∃ g ∈ bdAt data contracted X, g.1.1 ≠ f.1.1 := by
  classical
  obtain ⟨-, h3, hr⟩ := H.home fd hX hf
  have hover : (ndOver data X contracted).card ≤ 1 := Finset.card_le_one.mpr fun e he e' he' ↦ by
    rw [mem_ndOver] at he he'
    exact eq_of_ram_zero data fd hr he.1 he'.1 (he.2.trans he'.2.symm)
  have hsplit := card_ndAt_split data (contracted := contracted) X
  have h2 : 1 < (bdAt data contracted X).card := by omega
  obtain ⟨g, hg, hgf⟩ := Finset.exists_mem_ne h2 f
  refine ⟨g, hg, fun hT ↦ hgf ?_⟩
  exact eq_of_ram_zero data fd hr ((mem_bdAt data _ _).mp hg).1 ((mem_bdAt data _ _).mp hf).1 hT

omit H in
/-- **Stable adjacency at a leaf split is equality** for constituents carrying boundary
survivors: both lie over `v`, and no internal occurrence joins two constituents over one
endpoint. -/
theorem eq_of_pairedE {X Y : data.SourceVertex} (hXv : X.1.1 = v) (hYv : Y.1.1 = v)
    (h : PairedE data hc hab hOne block X Y) : X = Y := by
  rcases h with h | ⟨e, -, heX, heY, -⟩
  · exact h
  · by_contra hne
    exact not_incident_both data hne (hXv.trans hYv.symm) ((mem_ndAt data _ _).mp heX).2
      ((mem_ndAt data _ _).mp heY).2

end LeafInput

end Leaf

/-! ## 5.  The limit anchor's four survivors, labelled, and their lifts -/

section Labelling

variable {T : CFGraph} {degree : ℕ} (D : GluingDatum T degree) (A : D.SourceVertex)

/-- **A labelling of the four survivors at a valency-two anchor**: no direction or order
constraint (the `2 + 2` / `3 + 1` distribution is read off the labels, never imposed). -/
structure Labelling where
  e : Fin 4 → D.SourceEdge
  mem : ∀ i, e i ∈ ndAt D A
  inj : Function.Injective e

namespace Labelling

variable {D A} (L : Labelling D A)

theorem ndAt_eq (hnd : nonDanglingValency D A = 4) : ndAt D A = Finset.univ.image L.e := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro f hf
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hf
    exact L.mem i
  · rw [card_ndAt, hnd, Finset.card_image_of_injective _ L.inj]
    simp

variable {T₂ : CFGraph} {D₂ : GluingDatum T₂ degree}

/-- **Transport of a labelling along a geometric isomorphism of limits.** -/
def transport (ψ : GeometricDatumIso D D₂) (hConn : D.Connected) :
    Labelling D₂ (ψ.sourceVertexEquiv A) where
  e i := ψ.sourceEdgeEquiv (L.e i)
  mem i := by
    have h := (mem_ndAt D _ _).mp (L.mem i)
    rw [mem_ndAt, ψ.isDangling_map_iff hConn, ψ.incident_map_iff]
    exact h
  inj i j h := L.inj (ψ.sourceEdgeEquiv.injective h)

end Labelling

/-- A labelling exists at every vertex of surviving valency four. -/
theorem nonempty_labelling (hnd : nonDanglingValency D A = 4) : Nonempty (Labelling D A) := by
  classical
  have hc : (ndAt D A).card = 4 := by rw [card_ndAt, hnd]
  let eq : Fin 4 ≃ ndAt D A := (Finset.equivFinOfCardEq hc).symm
  exact ⟨⟨fun i ↦ (eq i).1, fun i ↦ (eq i).2, fun i j h ↦ eq.injective (Subtype.ext h)⟩⟩

end Labelling

section Lifts

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

open ValencyThreeSplit (limA)

variable (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- The incoming boundary occurrence carrying the limit survivor `L.e i`. -/
noncomputable def lift (i : Fin 4) : data.SourceEdge :=
  ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)).1

theorem lift_ne (i : Fin 4) : (lift L i).1.1 ≠ contracted :=
  ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)).2

theorem index_lift (i : Fin 4) :
    data.sourceEdgeIndex (lift L i) = (contractDatum data hc hab hOne).sourceEdgeIndex (L.e i) :=
  ContractionFibre.sourceEdgeIndex_symm_sourceEdgeEquiv data hc hab hOne (L.e i)

theorem lift_injective : Function.Injective (lift L) := by
  intro i j h
  apply L.inj
  have h' : ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i)) =
      ((ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e j)) := Subtype.ext h
  exact (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm.injective h'

theorem sourceEdgeMap_lift (i : Fin 4) :
    sourceEdgeMap data hc hab hOne ⟨lift L i, lift_ne L i⟩ = L.e i :=
  (ContractionFibre.sourceEdgeEquiv data hc hab hOne).apply_symm_apply (L.e i)

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

/-- A boundary occurrence at an active fibre constituent is the lift of a label. -/
theorem exists_lift_eq (hCompat : DanglingCompatible data hc hab hOne)
    (hnd : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4)
    {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    {e : data.SourceEdge} (he : e ∈ bdAt data contracted X) : ∃ i, lift L i = e := by
  classical
  obtain ⟨hnd', hT⟩ := (mem_bdAt data X e).mp he
  have hmem := ValencyThreeSplit.sourceEdgeMap_mem_ndAt hCompat hX he
  rw [L.ndAt_eq hnd] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_⟩
  have h2 : (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm (L.e i) = ⟨e, hT⟩ := by
    rw [hi]; exact (ContractionFibre.sourceEdgeEquiv data hc hab hOne).symm_apply_apply _
  exact congrArg Subtype.val h2

/-- Every label has a home: an active fibre constituent where its lift is a boundary
survivor. -/
theorem exists_home (hCompat : DanglingCompatible data hc hab hOne) (i : Fin 4) :
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

/-- **The home of a label is unique.** -/
theorem home_eq {i : Fin 4} {X X' : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hX' : X' ∈ fib data hc hab hOne block) (hi : lift L i ∈ ndAt data X)
    (hi' : lift L i ∈ ndAt data X') : X = X' :=
  ValencyThreeSplit.home_unique (lift_ne L i) hX hX' ((mem_ndAt data _ _).mp hi).2
    ((mem_ndAt data _ _).mp hi').2

/-- **Two labelled survivors lie at one vertex of the incoming stable graph** (the valency-two
form of `ValencyThreeSplit.Paired`, with the same body). -/
def Paired (i j : Fin 4) : Prop :=
  ∃ X ∈ fib data hc hab hOne block, ∃ X' ∈ fib data hc hab hOne block,
    lift L i ∈ ndAt data X ∧ lift L j ∈ ndAt data X' ∧ PairedE data hc hab hOne block X X'

/-- **The label passes through a divalent constituent** (a pass-through vertex of the incoming
cover, smoothed away in its stable graph). -/
def PassAt (i : Fin 4) : Prop :=
  ∃ X ∈ fib data hc hab hOne block, nonDanglingValency data X = 2 ∧ lift L i ∈ ndAt data X

end Lifts

/-! ## 6.  The split of a cover, and what the limit and the pairing say about it -/

section Split

/-- **The split of an incoming cover at a valency-two anchor**: whether the contracted
occurrence has a leaf end (the `(1,3)`/`(3,1)` splits: Part II's base tree with the fold over
the leaf), which labelled survivors pass through a divalent constituent, and the pairing of the
labelled survivors at the incoming stable vertices (the combinatorial type, Types I--III).
With the labelled limit this is the whole combinatorial picture of the pruned anchor fibre:
the `(2,2)` split with no pass-through (the `2 + 2` merge, a same-direction pairing), one
pass-through (the `3 + 1` distribution), two pass-throughs (the `2 + 2` split members), or the
leaf.  The pairing is part of the split because at a leaf split it is not determined by the
other two fields (both cross pairings read `leaf = true`, `pass = ∅`: Part II's two Base I
morphisms of subcase `{v2-nd4-t3-k2=k4}`, Types I and II). -/
@[ext] structure Split where
  leaf : Bool
  pass : Finset (Fin 4)
  pairs : Finset (Fin 4 × Fin 4)

/-- The limit-side test for a pass-through: a partner at the same stable vertex, in the other
target direction, of strictly larger index. -/
def PassOf (P : Fin 4 → Fin 4 → Prop) {E : Type*} (dir : Fin 4 → E) (idx : Fin 4 → ℕ)
    (i : Fin 4) : Prop :=
  ∃ j, j ≠ i ∧ P i j ∧ dir i ≠ dir j ∧ idx i < idx j

/-- The limit-side test for a leaf split: `e₀` is paired across the two directions and nothing
passes through. -/
def LeafOf (P : Fin 4 → Fin 4 → Prop) {E : Type*} (dir : Fin 4 → E) (idx : Fin 4 → ℕ) : Prop :=
  (∃ j, j ≠ 0 ∧ P 0 j ∧ dir 0 ≠ dir j) ∧ ∀ i, ¬ PassOf P dir idx i

open Classical in
/-- The split that the pairing, the directions and the indices determine. -/
noncomputable def splitOf (P : Fin 4 → Fin 4 → Prop) {E : Type*} (dir : Fin 4 → E)
    (idx : Fin 4 → ℕ) : Split :=
  ⟨decide (LeafOf P dir idx), Finset.univ.filter (PassOf P dir idx),
    Finset.univ.filter fun ij ↦ P ij.1 ij.2⟩

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

open ValencyThreeSplit (limA)

/-- The contracted occurrence has a leaf end. -/
def LeafCover (a b : target.V) : Prop :=
  (GluingDatum.incidentEdges a).card = 1 ∨ (GluingDatum.incidentEdges b).card = 1

/-- **The split an incoming cover reads**, relative to a labelling of the limit's
survivors. -/
def Reads (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (s : Split) : Prop :=
  (s.leaf = true ↔ LeafCover a b) ∧ (∀ i, i ∈ s.pass ↔ PassAt L i) ∧
    ∀ i j, (i, j) ∈ s.pairs ↔ Paired L i j

/-- Exactly one split is read (the reading is a function of the cover). -/
theorem existsUnique_reads
    (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block)) :
    ∃! s : Split, Reads L s := by
  classical
  refine ⟨⟨decide (LeafCover a b), Finset.univ.filter (PassAt L),
    Finset.univ.filter fun ij ↦ Paired L ij.1 ij.2⟩,
    ⟨by simp, fun i ↦ by simp, fun i j ↦ by simp⟩, fun s hs ↦ ?_⟩
  ext1
  · rw [Bool.eq_iff_iff, hs.1]; simp
  · ext i; rw [hs.2.1 i]; simp
  · ext ⟨i, j⟩; rw [hs.2.2 i j]; simp

/-- The limit direction of a label. -/
noncomputable abbrev dirOf (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (i : Fin 4) : (contract target hab hOne).edges :=
  (L.e i).1.1

/-- The index of a label. -/
noncomputable abbrev idxOf (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (i : Fin 4) : ℕ :=
  (contractDatum data hc hab hOne).sourceEdgeIndex (L.e i)

/-- **A read split is the one the pairing determines**, as soon as the two characterisations
hold. -/
theorem reads_iff_eq_splitOf
    (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (hpass : ∀ i, PassAt L i ↔ PassOf (Paired L) (dirOf L) (idxOf L) i)
    (hleaf : LeafCover a b ↔ LeafOf (Paired L) (dirOf L) (idxOf L)) (s : Split) :
    Reads L s ↔ s = splitOf (Paired L) (dirOf L) (idxOf L) := by
  classical
  constructor
  · rintro ⟨h1, h2, h3⟩
    ext1
    · simp only [splitOf]
      rw [Bool.eq_iff_iff, h1, hleaf]; simp
    · ext i; simp only [splitOf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h2 i, hpass i]
    · ext ⟨i, j⟩; simp only [splitOf, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h3 i j]
  · rintro rfl
    refine ⟨?_, fun i ↦ ?_, fun i j ↦ ?_⟩
    · simp only [splitOf, decide_eq_true_eq]; exact hleaf.symm
    · simp only [splitOf, Finset.mem_filter, Finset.mem_univ, true_and]; exact (hpass i).symm
    · simp only [splitOf, Finset.mem_filter, Finset.mem_univ, true_and]

end Split

/-! ## 7.  The characterisations, split by split -/

section Characterisation

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

open ValencyThreeSplit (limA)

variable (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

theorem nd_of_bd {X : data.SourceVertex} {e : data.SourceEdge}
    (h : e ∈ bdAt data contracted X) : e ∈ ndAt data X := ((mem_bdAt data _ _).mp h).1

theorem bd_of_lift {X : data.SourceVertex} {i : Fin 4} (h : lift L i ∈ ndAt data X) :
    lift L i ∈ bdAt data contracted X := (mem_bdAt data _ _).mpr ⟨h, lift_ne L i⟩

/-- `PassAt` is read at the home. -/
theorem passAt_iff_home {i : Fin 4} {X : data.SourceVertex} (hX : X ∈ fib data hc hab hOne block)
    (hi : lift L i ∈ bdAt data contracted X) : PassAt L i ↔ nonDanglingValency data X = 2 := by
  constructor
  · rintro ⟨X', hX', h2, hi'⟩
    rw [home_eq L hX hX' (nd_of_bd hi) hi']; exact h2
  · intro h2; exact ⟨X, hX, h2, nd_of_bd hi⟩

/-- `Paired` is read at the homes. -/
theorem paired_iff_home {i j : Fin 4} {X Y : data.SourceVertex}
    (hX : X ∈ fib data hc hab hOne block) (hY : Y ∈ fib data hc hab hOne block)
    (hi : lift L i ∈ bdAt data contracted X) (hj : lift L j ∈ bdAt data contracted Y) :
    Paired L i j ↔ PairedE data hc hab hOne block X Y := by
  constructor
  · rintro ⟨X₀, hX₀, Y₀, hY₀, hi0, hj0, hP⟩
    rw [home_eq L hX hX₀ (nd_of_bd hi) hi0, home_eq L hY hY₀ (nd_of_bd hj) hj0]; exact hP
  · intro hP; exact ⟨X, hX, Y, hY, nd_of_bd hi, nd_of_bd hj, hP⟩

theorem dir_ne_iff (i j : Fin 4) : dirOf L i ≠ dirOf L j ↔ (lift L j).1.1 ≠ (lift L i).1.1 := by
  rw [ne_comm, not_iff_not, lift_target_eq_iff]

section Div

variable (H : DivInput data hc hab hOne block)

include fd H in
/-- **The pass-through criterion, label form, at a `(2,2)` split.** -/
theorem DivInput.pass_iff (i : Fin 4) :
    PassAt L i ↔ PassOf (Paired L) (dirOf L) (idxOf L) i := by
  obtain ⟨X, hX, hi⟩ := exists_home L H.compat i
  rw [passAt_iff_home L hX hi, H.nd_two_iff fd hX hi]
  constructor
  · rintro ⟨Y, hY, g, hg, hP, hdir, hlt⟩
    obtain ⟨j, rfl⟩ := exists_lift_eq L H.compat H.nd4 hY hg
    refine ⟨j, fun h ↦ hdir (by rw [h]), (paired_iff_home L hX hY hi hg).mpr hP,
      (dir_ne_iff L i j).mpr hdir, ?_⟩
    rw [idxOf, idxOf, ← index_lift, ← index_lift]; exact hlt
  · rintro ⟨j, -, ⟨X₀, hX₀, Y₀, hY₀, hi0, hj0, hP⟩, hdir, hlt⟩
    rw [← home_eq L hX hX₀ (nd_of_bd hi) hi0] at hP
    refine ⟨Y₀, hY₀, lift L j, bd_of_lift L hj0, hP, (dir_ne_iff L i j).mp hdir, ?_⟩
    rw [index_lift, index_lift]; exact hlt

include fd H in
/-- **A `(2,2)` split is not a leaf split, and the limit-side test agrees**: with no
pass-through every constituent is trivalent, so paired survivors share a direction. -/
theorem DivInput.leaf_iff : LeafCover a b ↔ LeafOf (Paired L) (dirOf L) (idxOf L) := by
  constructor
  · rintro (h | h)
    · rw [H.a2] at h; exact absurd h (by norm_num)
    · rw [H.b2] at h; exact absurd h (by norm_num)
  · rintro ⟨⟨j, -, ⟨X₀, hX₀, Y₀, hY₀, hi0, hj0, hP⟩, hdir⟩, hno⟩
    exfalso
    have hall : ∀ X ∈ fib data hc hab hOne block, nonDanglingValency data X = 3 := by
      intro X hX
      by_contra h3
      have h2 : nonDanglingValency data X = 2 := by have := DivInput.nd_bounds fd hX; omega
      obtain ⟨f, hf⟩ := H.bd_nonempty_of_two fd hX h2
      obtain ⟨i, rfl⟩ := exists_lift_eq L H.compat H.nd4 hX hf
      exact hno i ((H.pass_iff fd L i).mp ⟨X, hX, h2, nd_of_bd hf⟩)
    have hXY : X₀ = Y₀ := by
      rcases hP with h | ⟨e, -, -, -, h2 | h2⟩
      · exact h
      · rw [hall X₀ hX₀] at h2; omega
      · rw [hall Y₀ hY₀] at h2; omega
    subst hXY
    apply (dir_ne_iff L 0 j).mp hdir
    exact ValencyThreeSplit.bdAt_target_eq_of_divalent data hc rfl (DivInput.side hX₀)
      (H.div2 hX₀) (bd_of_lift L hj0) (bd_of_lift L hi0)

end Div

section LeafCase

variable {u v : target.V} (H : LeafInput data hc hab hOne block u v)

include fd H in
theorem LeafInput.not_passAt (i : Fin 4) : ¬ PassAt L i := by
  rintro ⟨X, hX, h2, hi⟩
  have := (H.home fd hX (bd_of_lift L hi)).2.1
  omega

include fd H in
theorem LeafInput.not_passOf (i : Fin 4) : ¬ PassOf (Paired L) (dirOf L) (idxOf L) i := by
  rintro ⟨j, -, ⟨X₀, hX₀, Y₀, hY₀, hi0, hj0, hP⟩, -, hlt⟩
  have hXv := (H.home fd hX₀ (bd_of_lift L hi0)).1
  have hYv := (H.home fd hY₀ (bd_of_lift L hj0)).1
  have hXY := LeafInput.eq_of_pairedE hXv hYv hP
  subst hXY
  have h1 := H.index_eq fd hX₀ (bd_of_lift L hi0)
  have h2 := H.index_eq fd hX₀ (bd_of_lift L hj0)
  rw [idxOf, idxOf, ← index_lift, ← index_lift] at hlt
  have : (data.sourceEdgeIndex (lift L i) : ℤ) = data.sourceEdgeIndex (lift L j) := by omega
  omega

include fd H in
theorem LeafInput.pass_iff (i : Fin 4) :
    PassAt L i ↔ PassOf (Paired L) (dirOf L) (idxOf L) i :=
  ⟨fun h ↦ absurd h (H.not_passAt fd L i), fun h ↦ absurd h (H.not_passOf fd L i)⟩

include fd H in
/-- **A leaf split reads as one**: the survivors pair across the two directions (at each of
the two trivalent constituents over `v`) and nothing passes through. -/
theorem LeafInput.leaf_iff : LeafCover a b ↔ LeafOf (Paired L) (dirOf L) (idxOf L) := by
  constructor
  · rintro -
    refine ⟨?_, H.not_passOf fd L⟩
    obtain ⟨X, hX, h0⟩ := exists_home L H.compat 0
    obtain ⟨g, hg, hgT⟩ := H.exists_partner fd hX h0
    obtain ⟨j, rfl⟩ := exists_lift_eq L H.compat H.nd4 hX hg
    exact ⟨j, fun h ↦ hgT (by rw [h]), (paired_iff_home L hX hX h0 hg).mpr (Or.inl rfl),
      (dir_ne_iff L 0 j).mpr hgT⟩
  · rintro -
    rcases H.huv with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl H.u1
    · exact Or.inr H.u1

end LeafCase

end Characterisation

/-! ## 8.  The anchor input at a valency-two limit, and split determination -/

section Determination

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (block : (mergedPartition data a b).Blocks)

open ValencyThreeSplit (limA)

/-- **The inputs of the anchor analysis at one incoming cover of a valency-two limit.**

interface: the hypotheses of `NonTrivalentValencyTwoRigidity.twoBranchAnchor` (the `TwoStar`
replaced by its defining cardinality, `W2R1Target.TwoStar.of_card`); at an actual facet `nd4`
is produced by `NonTrivalentAnchorValency.nonDanglingValency_eq_four_of_row_facet_twoStar`
(`exists_regrowthAnchor`). -/
structure AnchorInput : Prop where
  forest : ContractionForest data a b contracted
  valency : (GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩).card = 2
  nd4 : nonDanglingValency (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 4

variable {data hc hab hOne block}

namespace AnchorInput

theorem compat (H : AnchorInput data hc hab hOne block) : DanglingCompatible data hc hab hOne :=
  WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne H.forest

/-- **The three splits** (`SecondEquation.valencySplit_of_twoStar`): `(2,2)`, or a leaf at `a`,
or a leaf at `b`. -/
theorem cases (H : AnchorInput data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    DivInput data hc hab hOne block ∨ LeafInput data hc hab hOne block a b ∨
      LeafInput data hc hab hOne block b a := by
  rcases SecondEquation.valencySplit_of_twoStar data hc hab hOne fd.valid fd.changeMinimal
    (W2R1Target.TwoStar.of_card H.valency) with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨H.forest, H.nd4, h1, h2, h3, h4⟩
  · exact Or.inr (Or.inl ⟨H.forest, H.nd4, H.valency, Or.inl ⟨rfl, rfl⟩, h1, h2, h3, h4⟩)
  · exact Or.inr (Or.inr ⟨H.forest, H.nd4, H.valency, Or.inr ⟨rfl, rfl⟩, h2, h1, h4, h3⟩)

variable (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

theorem pass_iff (H : AnchorInput data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) (i : Fin 4) :
    PassAt L i ↔ PassOf (Paired L) (dirOf L) (idxOf L) i := by
  rcases H.cases fd with H' | H' | H'
  · exact H'.pass_iff fd L i
  · exact H'.pass_iff fd L i
  · exact H'.pass_iff fd L i

theorem leaf_iff (H : AnchorInput data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) :
    LeafCover a b ↔ LeafOf (Paired L) (dirOf L) (idxOf L) := by
  rcases H.cases fd with H' | H' | H'
  · exact H'.leaf_iff fd L
  · exact H'.leaf_iff fd L
  · exact H'.leaf_iff fd L

/-- **Stages 1 and 2, joined, at valency two: the split of an arbitrary incoming cover is
the one its pairing determines.**  Relative to any labelling of the limit's survivors, the
unique split the cover reads (`existsUnique_reads`) is `splitOf` of the cover's pairing of the
survivors, their limit directions and their limit indices. -/
theorem reads_iff (H : AnchorInput data hc hab hOne block)
    (fd : FullDimensionalSourcePresentation data coordinate) (s : Split) :
    Reads L s ↔ s = splitOf (Paired L) (dirOf L) (idxOf L) :=
  reads_iff_eq_splitOf L (H.pass_iff L fd) (H.leaf_iff L fd) s

end AnchorInput

end Determination

section TwoCovers

/-- `splitOf` sees the pairing, the direction *pattern* and the indices only. -/
theorem splitOf_congr {P P' : Fin 4 → Fin 4 → Prop} {E E' : Type*} {d : Fin 4 → E}
    {d' : Fin 4 → E'} {k k' : Fin 4 → ℕ} (hP : ∀ i j, P i j ↔ P' i j)
    (hd : ∀ i j, d i = d j ↔ d' i = d' j) (hk : ∀ i, k i = k' i) :
    splitOf P d k = splitOf P' d' k' := by
  have hpass : ∀ i, PassOf P d k i ↔ PassOf P' d' k' i := fun i ↦ by
    simp only [PassOf, hP, ne_eq, hd, hk]
  have hleaf : LeafOf P d k ↔ LeafOf P' d' k' := by
    simp only [LeafOf, hP, ne_eq, hd, hpass]
  ext1
  · exact decide_eq_decide.mpr hleaf
  · ext i; simp only [splitOf, Finset.mem_filter, Finset.mem_univ, true_and, hpass]
  · ext ij; simp only [splitOf, Finset.mem_filter, Finset.mem_univ, true_and, hP]

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

open ValencyThreeSplit (limA)

include fd₁ fd₂ in
/-- **Split determination (stage 2) at valency two.**  Two incoming covers of valency-two
anchors, with labellings matched along a geometric isomorphism of their limits, whose
incoming stable graphs pair the labelled survivors in the same way, read the same split.
No arithmetic is needed beyond the order of the indices: the pairing fixes the merge (a
same-direction pairing), the `3 + 1` pass-through (the thick partner of the thin survivor),
and, for a cross pairing, the leaf (equal indices in each pair) versus the two pass-throughs
(the smaller member of each pair). -/
theorem split_eq_of_paired (H₁ : AnchorInput data₁ hc₁ hab₁ hOne₁ block₁)
    (H₂ : AnchorInput data₂ hc₂ hab₂ hOne₂ block₂)
    (ψ : GeometricDatumIso (contractDatum data₁ hc₁ hab₁ hOne₁) (contractDatum data₂ hc₂ hab₂ hOne₂))
    (L₁ : Labelling (contractDatum data₁ hc₁ hab₁ hOne₁) (limA data₁ hc₁ hab₁ hOne₁ block₁))
    (L₂ : Labelling (contractDatum data₂ hc₂ hab₂ hOne₂) (limA data₂ hc₂ hab₂ hOne₂ block₂))
    (hL : ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i))
    (hP : ∀ i j, Paired L₁ i j ↔ Paired L₂ i j)
    {s₁ s₂ : Split} (h₁ : Reads L₁ s₁) (h₂ : Reads L₂ s₂) : s₁ = s₂ := by
  rw [H₁.reads_iff L₁ fd₁] at h₁
  rw [H₂.reads_iff L₂ fd₂] at h₂
  rw [h₁, h₂]
  refine splitOf_congr hP (fun i j ↦ ?_) (fun i ↦ ?_)
  · change (L₁.e i).1.1 = (L₁.e j).1.1 ↔ (L₂.e i).1.1 = (L₂.e j).1.1
    rw [hL, hL]
    change _ ↔ ψ.targetEdge (L₁.e i).1.1 = ψ.targetEdge (L₁.e j).1.1
    exact ψ.targetEdge.apply_eq_iff_eq.symm
  · change _ = (contractDatum data₂ hc₂ hab₂ hOne₂).sourceEdgeIndex (L₂.e i)
    rw [hL, ψ.sourceEdgeIndex_map]

end TwoCovers

/-! ## 9.  Regrowths: stage 1 (anchor localization) at every valency-two facet regrowth -/

section Regrowth

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyThreeSplit (limA)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The valency-two anchor input of a regrowth** at a merged block of its limit. -/
abbrev RegrowthAnchor (w : Regrowth core y degree)
    (block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks) :
    Prop :=
  AnchorInput w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) block

/-- **Stage 1 at every valency-two facet regrowth.**  A regrowth at a facet point (one request
coordinate zero, at a non-loop core slot) whose limit's merged target vertex is divalent has a
merged block carrying the full anchor input: the contraction forest (the single vanishing row
has a simple end) and `nd(A) = 4` (`NonTrivalentAnchorValency`'s two-star producer). -/
theorem exists_regrowthAnchor (w : Regrowth core y degree) (e₀ : Fin p)
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop : core.tail e₀ ≠ core.head e₀)
    (hval : (GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
      ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
        fst_ne_snd (w.frame.edgeOf w.column)⟩).card = 2) :
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
    exact ValencyThreeSplit.hasSimpleEnd_of_ident k e₀ hloop
  have hForest : ContractionForest k.data _ _ (k.edgeOf w.column) :=
    SingleRowForest.contractionForest_of_single_row k.fullDim.labelling (k.coordsAt y) hNonneg
      facet hRows hEnd rfl hZero
  have star : W2R1Target.TwoStar
      (contract k.target (fst_ne_snd (k.edgeOf w.column)) (k.numEdges_edgeOf w.column))
      ⟨_, fst_ne_snd (k.edgeOf w.column)⟩ := W2R1Target.TwoStar.of_card hval
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep (k.fullDim.labelling.row.symm facet)
  have hRow : k.fullDim.labelling.row edge.stablePath = facet := by
    show k.fullDim.labelling.row (Quot.mk _ edge) = facet
    rw [hEdge, Equiv.apply_symm_apply]
  obtain ⟨block, -, hFour⟩ := NonTrivalentAnchorValency.nonDanglingValency_eq_four_of_row_facet_twoStar
    k.data k.fullDim rfl (fst_ne_snd (k.edgeOf w.column)) (k.numEdges_edgeOf w.column) star
    hForest (k.coordsAt y) facet hRows hZero hPos hFacetZero edge hRow
  exact ⟨block, hForest, hval, hFour⟩

/-- **The anchor is the limit's only vertex of surviving valency four** at a valency-two
limit: another block over the merged vertex is unramified (the anchor carries both units of
the change), so it has at most two occurrences; a vertex away from the wall keeps its incoming
surviving valency, at most three. -/
theorem eq_limA_of_nonDanglingValency_eq_four {target : CFGraph} {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate] {data : GluingDatum target degree}
    (fd : FullDimensionalSourcePresentation data coordinate) {a b : target.V}
    {contracted : target.edges} {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
    (H : AnchorInput data hc hab hOne block)
    (X : (contractDatum data hc hab hOne).SourceVertex)
    (hX : nonDanglingValency (contractDatum data hc hab hOne) X = 4) :
    X = limA data hc hab hOne block := by
  classical
  by_cases hXw : X.1.1 = ⟨a, hab⟩
  · by_contra hne
    have hstar := W2R1Target.TwoStar.of_card H.valency
    have hValidWall := valid_contractDatum data hc hab hOne H.forest fd.valid
    have hsum := ram_add_ram_le (contractDatum data hc hab hOne) hValidWall hne
      (hXw.trans rfl)
    rw [hXw, SecondEquation.targetChange_contractDatum_merge_eq_two data hc hab hOne fd.valid
      fd.changeMinimal H.forest hstar] at hsum
    have hA : ram (contractDatum data hc hab hOne) (limA data hc hab hOne block) = 2 :=
      NonTrivalentValencyTwoRigidity.localRamification_eq_two data fd hc hab hOne H.forest
        H.compat hstar block H.nd4
    have hcard := card_incident_of_divalent (contractDatum data hc hab hOne) X
      (by rw [hXw]; exact H.valency)
    have hle := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge
      (contractDatum data hc hab hOne) X
    rw [hX] at hle
    have : (4 : ℤ) ≤ Fintype.card (IncidentSourceEdge (contractDatum data hc hab hOne) X) := by
      exact_mod_cast hle
    omega
  · exfalso
    obtain ⟨Y, rfl⟩ := sourceVertexMap_surjective data hc hab hOne X
    have hYa : Y.1.1 ≠ a := fun h ↦ hXw (ContractionFibre.fold_eq_of_eq_or hab (Or.inl h))
    have hYb : Y.1.1 ≠ b := fun h ↦ hXw (ContractionFibre.fold_eq_of_eq_or hab (Or.inr h))
    rw [nonDanglingValency_sourceVertexMap data H.compat Y hYa hYb] at hX
    have := fd.trivalent Y
    omega

variable {c₂ : Core n p}

/-- **An isomorphism of regrowth limits carries anchor to anchor** at valency two. -/
theorem sourceVertexEquiv_limA (w₁ : Regrowth core y degree) (w₂ : Regrowth c₂ y degree)
    {block₁} {block₂} (H₁ : RegrowthAnchor w₁ block₁) (H₂ : RegrowthAnchor w₂ block₂)
    (ψ : GeometricDatumIso w₁.limit w₂.limit) :
    ψ.sourceVertexEquiv (limA w₁.frame.data rfl (fst_ne_snd (w₁.frame.edgeOf w₁.column))
        (w₁.frame.numEdges_edgeOf w₁.column) block₁) =
      limA w₂.frame.data rfl (fst_ne_snd (w₂.frame.edgeOf w₂.column))
        (w₂.frame.numEdges_edgeOf w₂.column) block₂ := by
  apply eq_limA_of_nonDanglingValency_eq_four w₂.frame.fullDim H₂
  exact (ψ.nonDanglingValency_map (ValencyThreeSplit.connected_limit w₁) _).trans H₁.nd4

/-- The divalent-limit labelling of a regrowth's anchor, transported along a limit
isomorphism. -/
theorem exists_transport (w₁ : Regrowth core y degree) (w₂ : Regrowth c₂ y degree)
    {block₁} {block₂} (H₁ : RegrowthAnchor w₁ block₁) (H₂ : RegrowthAnchor w₂ block₂)
    (ψ : GeometricDatumIso w₁.limit w₂.limit)
    (L₁ : Labelling w₁.limit (limA w₁.frame.data rfl (fst_ne_snd (w₁.frame.edgeOf w₁.column))
        (w₁.frame.numEdges_edgeOf w₁.column) block₁)) :
    ∃ L₂ : Labelling w₂.limit (limA w₂.frame.data rfl
        (fst_ne_snd (w₂.frame.edgeOf w₂.column)) (w₂.frame.numEdges_edgeOf w₂.column) block₂),
      ∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i) := by
  rw [← sourceVertexEquiv_limA w₁ w₂ H₁ H₂ ψ]
  exact ⟨L₁.transport ψ (ValencyThreeSplit.connected_limit w₁), fun _ ↦ rfl⟩

/-- **Stage 2 at regrowths: split determination along a limit isomorphism.**  For two
regrowths (over any cores) with valency-two anchors and any geometric isomorphism of their
limits, a labelling of the first limit transports to the second, and then two read splits are
equal as soon as the two covers pair the survivors in the same way. -/
theorem regrowth_split_eq (w₁ : Regrowth core y degree) (w₂ : Regrowth c₂ y degree)
    {block₁} {block₂} (H₁ : RegrowthAnchor w₁ block₁) (H₂ : RegrowthAnchor w₂ block₂)
    (ψ : GeometricDatumIso w₁.limit w₂.limit)
    (L₁ : Labelling w₁.limit (limA w₁.frame.data rfl (fst_ne_snd (w₁.frame.edgeOf w₁.column))
        (w₁.frame.numEdges_edgeOf w₁.column) block₁)) :
    ∃ L₂ : Labelling w₂.limit (limA w₂.frame.data rfl
        (fst_ne_snd (w₂.frame.edgeOf w₂.column)) (w₂.frame.numEdges_edgeOf w₂.column) block₂),
      (∀ i, L₂.e i = ψ.sourceEdgeEquiv (L₁.e i)) ∧
      ∀ s₁ s₂ : Split, Reads L₁ s₁ → Reads L₂ s₂ →
        (∀ i j, Paired L₁ i j ↔ Paired L₂ i j) → s₁ = s₂ := by
  obtain ⟨L₂, hL⟩ := exists_transport w₁ w₂ H₁ H₂ ψ L₁
  exact ⟨L₂, hL, fun s₁ s₂ h₁ h₂ hP ↦
    split_eq_of_paired w₁.frame.fullDim w₂.frame.fullDim H₁ H₂ ψ L₁ L₂ hL hP h₁ h₂⟩

end Regrowth

/-! ## 10.  What stages 3 to 5 owe at valency two, and the census clause -/

section Stages

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyThreeGeneral (SameMetricLimit MetricFacetLimit MSpecializesLeft MSpecializesRight
  metricSwap)
open ValencyThreeSplit (limA IsMetricIso sameMetricLimit_iff)

variable {n p degree : ℕ}

/-- The anchor of a regrowth's limit at a merged block. -/
noncomputable abbrev anchorOf {core : Core n p} {y : Fin p → ℚ} (w : Regrowth core y degree)
    (block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks) :
    w.limit.SourceVertex :=
  limA w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    block

/-- **Stage 3 at valency two, matching the pairing to the core.**  Two classes of one core at
one labelled metric limit with a valency-two anchor: *some* labelled-metric isomorphism of
their limits makes the two incoming stable graphs pair the transported survivors in the same
way.

The isomorphism is existential for the reason `ValencyThreeSplit.TypeMatch` records: a
labelled metric limit can have label-moving automorphisms (sheet swaps over one target
occurrence, `ValencyThreeSplit.swapIso`), along which a cover reads another pairing against
itself.

interface: the statement "the combinatorial type of the incoming stable graph at the anchor
is the core's" (Part II, `subsec-case-v2`: Types I, II, III are the three pairings of
`e₂, …, e₅`), in the labelled form `split_eq_of_paired` consumes; not proved here (it is
`ValencyTwoPairing.pairingMatch_of_side` downstream).  Unlike
`ValencyThreeSplit.TypeMatch` it is stated for **all** classes (the census counts the whole
fibres), not only odd ones. -/
def PairingMatch (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block'),
    (∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ) →
    ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ ∧
      ∀ (L : Labelling w.limit (anchorOf w block)) (L' : Labelling w'.limit (anchorOf w' block')),
        (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) → ∀ i j, Paired L i j ↔ Paired L' i j

/-- **Stages 4 and 5 at valency two: the split and the labelled limit determine the class.**
Two classes of one core at one labelled metric limit with a valency-two anchor, reading the
same split for transported labellings, are equal.

interface: "the limit, the split and the core identification determine the frame class"
(Part II, `subsec-case-v2`, read as a reconstruction: the pruned anchor fibre is fixed by the
split -- `DivInput.nd_two_iff`, `LeafInput.home` -- and the rest of the cover by the limit);
the valency-two analogue of `ValencyThreeSplit.SplitRigidity`, which is proved at valency
three (`ValencyThreeResolutionMatch.splitRigidity`); proved at valency two downstream
(`ValencyTwoResolutionMatch.splitRigidity`). -/
def SplitRigidity (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ →
    ∀ (L : Labelling w.limit (anchorOf w block)) (L' : Labelling w'.limit (anchorOf w' block')),
      (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) →
      ∀ s : Split, Reads L s → Reads L' s → FrameClass.mk w.frame = FrameClass.mk w'.frame

/-- **A valency-two metric facet limit** (near side): every near-side regrowth presenting it
carries the valency-two anchor input.  interface: discharged at every facet regrowth whose
limit's merged target vertex is divalent (`exists_regrowthAnchor`, `v2Limit_of_facetPoint`). -/
def V2Limit {c c' : Core n p} {y : Fin p → ℚ} (m : MetricFacetLimit c c' y degree) : Prop :=
  ∀ w : Regrowth c y degree, MetricFacetLimit.ofLeft (c' := c') w = m →
    ∃ block, RegrowthAnchor w block

/-- `V2Limit` at a facet point of a non-loop slot reduces to the divalence of the merged
target vertex of each presenting regrowth. -/
theorem v2Limit_of_facetPoint {c c' : Core n p} {y : Fin p → ℚ}
    (m : MetricFacetLimit c c' y degree) (e₀ : Fin p) (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop : c.tail e₀ ≠ c.head e₀)
    (hval : ∀ w : Regrowth c y degree, MetricFacetLimit.ofLeft (c' := c') w = m →
      (GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
        ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
          fst_ne_snd (w.frame.edgeOf w.column)⟩).card = 2) :
    V2Limit m :=
  fun w hw ↦ exists_regrowthAnchor w e₀ hpt hloop (hval w hw)

/-- **Stages 1--5 give uniqueness at every valency-two metric limit**, for all classes. -/
theorem eq_of_stages {c c' : Core n p} {y : Fin p → ℚ}
    (h3 : PairingMatch c y degree) (h45 : SplitRigidity c y degree)
    (m : MetricFacetLimit c c' y degree) (hm : V2Limit m)
    (x x' : FrameClass c degree) (hs : MSpecializesLeft x m) (hs' : MSpecializesLeft x' m) :
    x = x' := by
  obtain ⟨w, rfl, hw⟩ := hs
  obtain ⟨w', rfl, hw'⟩ := hs'
  obtain ⟨block, H⟩ := hm w hw
  obtain ⟨block', H'⟩ := hm w' hw'
  have hsame : SameMetricLimit (c := c) (c' := c') (Sum.inl w) (Sum.inl w') :=
    Quotient.exact (hw.trans hw'.symm)
  obtain ⟨ψ, hψ, hpair⟩ := h3 w w' block block' H H' ((sameMetricLimit_iff w w').mp hsame)
  obtain ⟨L⟩ := nonempty_labelling _ _ H.nd4
  obtain ⟨L', hL, hsplit⟩ := regrowth_split_eq w w' H H' ψ L
  obtain ⟨s, hsR, -⟩ := existsUnique_reads L
  obtain ⟨s', hsR', -⟩ := existsUnique_reads L'
  have hss : s = s' := hsplit s s' hsR hsR' (hpair L L' hL)
  subst hss
  exact h45 w w' block block' H H' ψ hψ L L' hL s hsR hsR'

/-- **At most one class of the near core at a valency-two metric limit.** -/
theorem subsingleton_left {c c' : Core n p} {y : Fin p → ℚ}
    (h3 : PairingMatch c y degree) (h45 : SplitRigidity c y degree)
    (m : MetricFacetLimit c c' y degree) (hm : V2Limit m) :
    Subsingleton {x : FrameClass c degree // MSpecializesLeft x m} :=
  ⟨fun a b ↦ Subtype.ext (eq_of_stages h3 h45 m hm a.1 b.1 a.2 b.2)⟩

/-- **At most one class of the far core**, by exchanging the two cores. -/
theorem subsingleton_right {c c' : Core n p} {y : Fin p → ℚ}
    (h3 : PairingMatch c' y degree) (h45 : SplitRigidity c' y degree)
    (m : MetricFacetLimit c c' y degree) (hm : V2Limit (metricSwap m)) :
    Subsingleton {x : FrameClass c' degree // MSpecializesRight x m} :=
  ⟨fun a b ↦ Subtype.ext (eq_of_stages h3 h45 (metricSwap m) hm a.1 b.1
    (ValencyThreeGeneral.mSpecializesRight_swap_iff.mp a.2)
    (ValencyThreeGeneral.mSpecializesRight_swap_iff.mp b.2))⟩

section Transfer

open FacetAdapterPilot FacetMachine
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **Metric existence transfer for every class, forward**
(`ColumnReceiptExport.exists_odd_mSpecializesRight` without the parity: the far regrowth of any
link presents the same labelled metric limit). -/
theorem exists_mSpecializesRight (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (x : FrameClass c.core degree)
    (hs : MSpecializesLeft x m) :
    ∃ x' : FrameClass (farCore m').core degree, MSpecializesRight x' m := by
  obtain ⟨w, rfl, rfl⟩ := hs
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member (w.frame.member y₀) hDegree
  obtain ⟨link, hlink⟩ := ColumnReceiptExport.metricLinkReceipts m' hd hG (by omega) w ms
  exact ⟨FrameClass.mk (farFrame m' hd hG (by omega) w ms link),
    farRegrowth m' hd hG (by omega) w ms link, rfl, (Quotient.sound hlink).symm⟩

/-- **Metric existence transfer for every class, reverse**, by the reversed move. -/
theorem exists_mSpecializesLeft (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree)
    (x' : FrameClass (farCore m').core degree) (hs : MSpecializesRight x' m) :
    ∃ x : FrameClass c.core degree, MSpecializesLeft x m := by
  have hback := farCore_revMove m'
  have key : ∀ {c₂ : CubicCore n p} (hb : farCore (revMove m') = c₂)
      (m₂ : MetricFacetLimit c₂.core (farCore m').core y₀ degree),
      MSpecializesRight x' m₂ → ∃ x : FrameClass c₂.core degree, MSpecializesLeft x m₂ := by
    rintro c₂ rfl m₂ hs₂
    obtain ⟨x, hx⟩ := exists_mSpecializesRight (revMove m') (facetDatum_rev m' hd) hG hDegree
      (metricSwap m₂) x' (ValencyThreeGeneral.mSpecializesRight_swap_iff.mp hs₂)
    refine ⟨x, ?_⟩
    have := ValencyThreeGeneral.mSpecializesRight_swap_iff.mp hx
    rwa [ValencyThreeGeneral.metricSwap_swap] at this
  exact key hback m hs

end Transfer

/-- **The census clause at one metric limit** (the body of `FacetCensus.MetricCensus`). -/
def CensusAt {c c' : Core n p} {y : Fin p → ℚ} (m : MetricFacetLimit c c' y degree) : Prop :=
  ∃ (ι : Type) (τL : {x : FrameClass c degree // MSpecializesLeft x m} → ι)
    (τR : {x : FrameClass c' degree // MSpecializesRight x m} → ι),
    Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR

/-- `MetricCensus` is `CensusAt` at every metric facet limit (definitional). -/
theorem metricCensus_iff_forall_censusAt {c c' : Core n p} {y : Fin p → ℚ} :
    FacetCensus.MetricCensus c c' degree y ↔ ∀ m : MetricFacetLimit c c' y degree, CensusAt m :=
  Iff.rfl

/-- **The index-`Unit` census clause**: at most one class on each side and existence both
ways. -/
theorem censusAt_of_subsingleton {c c' : Core n p} {y : Fin p → ℚ}
    {m : MetricFacetLimit c c' y degree}
    (hL : Subsingleton {x : FrameClass c degree // MSpecializesLeft x m})
    (hR : Subsingleton {x : FrameClass c' degree // MSpecializesRight x m})
    (hLR : (∃ x : FrameClass c degree, MSpecializesLeft x m) ↔
      ∃ x' : FrameClass c' degree, MSpecializesRight x' m) :
    CensusAt m := by
  refine ⟨Unit, fun _ ↦ (), fun _ ↦ (), fun a b _ ↦ Subsingleton.elim a b,
    fun a b _ ↦ Subsingleton.elim a b, ?_⟩
  ext u
  simp only [Set.mem_range, exists_const_iff, and_true]
  constructor
  · rintro ⟨x, hx⟩; exact ⟨hLR.mp ⟨x, hx⟩ |>.choose, (hLR.mp ⟨x, hx⟩).choose_spec⟩
  · rintro ⟨x, hx⟩; exact ⟨hLR.mpr ⟨x, hx⟩ |>.choose, (hLR.mpr ⟨x, hx⟩).choose_spec⟩

section Composite

open FacetAdapterPilot FacetMachine
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **The census clause at a valency-two metric limit of a Whitehead step's facet datum**,
index `Unit`, from stages 3--5 on both cores.  Stage 1 (`V2Limit`) is the valency dispatch;
stage 2 is `split_eq_of_paired` (proved); the existence halves are the link transfers of
`ColumnReceiptExport` without parity (`exists_mSpecializesRight`/`Left`, proved). -/
theorem censusAt_of_stages (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (h3 : PairingMatch c.core y₀ degree) (h45 : SplitRigidity c.core y₀ degree)
    (h3' : PairingMatch (farCore m').core y₀ degree)
    (h45' : SplitRigidity (farCore m').core y₀ degree)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (hm : V2Limit m)
    (hm' : V2Limit (metricSwap m)) : CensusAt m :=
  censusAt_of_subsingleton (subsingleton_left h3 h45 m hm) (subsingleton_right h3' h45' m hm')
    ⟨fun ⟨x, hx⟩ ↦ exists_mSpecializesRight m' hd hG hDegree m x hx,
      fun ⟨x', hx'⟩ ↦ exists_mSpecializesLeft m' hd hG hDegree m x' hx'⟩

end Composite

end Stages

/-! ## 11.  Stage 5 is valency-free: `SplitRigidity` reduced to stage 4 and to a transport -/

section Stage4

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyThreeSplit (IsMetricIso)
open ValencyThreeRigidity (ColumnIso IsPlacement resolutionOf endA colMap frameIso_of_columns
  columnIso_of_extendsMetric extendsMetric_of_transportFree)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Stage 4 at valency two, extending the isomorphism across the anchor**: two classes of
one core at one labelled metric limit with a valency-two anchor, reading the same split for
transported labellings, have column-compatible incoming data.

interface: equivalent to `SplitRigidity` at a facet over a connected core with `3 ≤ n`
(`splitRigidity_of_anchorExtension`, `anchorExtension_of_splitRigidity`); the valency-two
form of `ValencyThreeRigidity.AnchorExtension`, without its oddness binders. -/
def AnchorExtension (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ →
    ∀ (L : Labelling w.limit (anchorOf w block)) (L' : Labelling w'.limit (anchorOf w' block')),
      (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) →
      ∀ s : Split, Reads L s → Reads L' s → ColumnIso w w'

/-- **`SplitRigidity` from stage 4**: stage 5 (`ValencyThreeRigidity.frameIso_of_columns`)
never looks at the anchor, so it applies verbatim at valency two. -/
theorem splitRigidity_of_anchorExtension (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hy : y e₀ = 0) (h4 : AnchorExtension core y degree) : SplitRigidity core y degree := by
  intro w w' block block' H H' ψ hψ L L' hL s hs hs'
  obtain ⟨Φ, hcol⟩ := h4 w w' block block' H H' ψ hψ L L' hL s hs hs'
  exact FrameClass.mk_eq_mk_iff.mpr ⟨frameIso_of_columns w w'.frame hconn hn hy Φ hcol⟩

/-- Conversely `SplitRigidity` gives stage 4 (a frame isomorphism is column-compatible). -/
theorem anchorExtension_of_splitRigidity (h : SplitRigidity core y degree) :
    AnchorExtension core y degree := by
  intro w w' block block' H H' ψ hψ L L' hL s hs hs'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (h w w' block block' H H' ψ hψ L L' hL s hs hs')
  refine ⟨fi.datum, fun j _ ↦ ?_⟩
  have hc : colMap w.frame w'.frame fi.datum j = fi.column j := by
    simp [colMap, GeometricSegmentWalls.FrameIso.column]
  rw [hc]
  exact ValencyThreeGeneral.slotColumn_frameIso fi j

/-- **Stage 4 at valency two, in transport form**: two classes of one
core at one labelled metric limit with a valency-two anchor, reading the same split for
transported labellings, admit placements, a labelled-metric limit isomorphism and a decoupled
transport of their incoming resolutions.

interface: the valency-two form of `ValencyThreeRigidity.ResolutionMatch` (proved at valency
three, `ValencyThreeResolutionMatch.resolutionMatch`), without oddness binders;
implies `AnchorExtension` (`anchorExtension_of_resolutionMatch`); proved downstream
(`ValencyTwoResolutionMatch.resolutionMatch`). -/
def ResolutionMatch (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ →
    ∀ (L : Labelling w.limit (anchorOf w block)) (L' : Labelling w'.limit (anchorOf w' block')),
      (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) →
      ∀ s : Split, Reads L s → Reads L' s →
        ∃ (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second)
          (second' : (w'.frame.limitTarget w'.column).edges → Bool) (h' : IsPlacement w' second')
          (ψ' : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ' ∧
          Nonempty (ResolutionExpansionFree.TransportFree ψ'
            ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
            ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ second second'
            (resolutionOf w second h) (resolutionOf w' second' h'))

theorem anchorExtension_of_resolutionMatch (h : ResolutionMatch core y degree) :
    AnchorExtension core y degree := by
  intro w w' block block' H H' ψ hψ L L' hL s hs hs'
  obtain ⟨second, hp, second', hp', ψ', hψ', ⟨T⟩⟩ := h w w' block block' H H' ψ hψ L L' hL s hs hs'
  exact columnIso_of_extendsMetric
    (extendsMetric_of_transportFree w w' second hp second' hp' ψ' hψ' T)

/-- **`SplitRigidity` from the transport form** at a facet over a connected core with at
least three vertices. -/
theorem splitRigidity_of_resolutionMatch (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hy : y e₀ = 0) (h : ResolutionMatch core y degree) : SplitRigidity core y degree :=
  splitRigidity_of_anchorExtension hconn hn hy (anchorExtension_of_resolutionMatch h)

/-- **Interface half**: labelled-metric uniqueness of the near classes gives `SplitRigidity`
(so `SplitRigidity` is no stronger than the census clause it feeds). -/
theorem splitRigidity_of_subsingleton {c' : Core n p}
    (h : ∀ m : ValencyThreeGeneral.MetricFacetLimit core c' y degree,
      Subsingleton {x : FrameClass core degree // ValencyThreeGeneral.MSpecializesLeft x m}) :
    SplitRigidity core y degree := by
  intro w w' block block' H H' ψ hψ L L' hL s hs hs'
  have hm : ValencyThreeGeneral.MetricFacetLimit.ofLeft (c' := c') w' =
      ValencyThreeGeneral.MetricFacetLimit.ofLeft w :=
    (Quotient.sound ((ValencyThreeSplit.sameMetricLimit_iff (c' := c') w w').mpr ⟨ψ, hψ⟩)).symm
  have := (h (ValencyThreeGeneral.MetricFacetLimit.ofLeft (c' := c') w)).elim
    ⟨FrameClass.mk w.frame, w, rfl, rfl⟩ ⟨FrameClass.mk w'.frame, w', rfl, hm⟩
  exact congrArg Subtype.val this

end Stage4

/-! ## 12.  Non-vacuity: the four pictures are exactly what `splitOf` produces -/

section NonVacuity

/-- A pairing of the four labels by a partner function. -/
def byPartner (π : Fin 4 → Fin 4) : Fin 4 → Fin 4 → Prop := fun i j ↦ j = i ∨ j = π i

/-- The `(2,2)` merge: a same-direction pairing reads no leaf and no pass-through. -/
example : (splitOf (byPartner ![1, 0, 3, 2]) ![false, false, true, true] ![1, 1, 1, 1]).leaf =
      false ∧
    (splitOf (byPartner ![1, 0, 3, 2]) ![false, false, true, true] ![1, 1, 1, 1]).pass = ∅ := by
  refine ⟨?_, ?_⟩
  · simp [splitOf, LeafOf, PassOf, byPartner, Fin.exists_fin_succ, Fin.forall_fin_succ]
  · ext i; fin_cases i <;> simp [splitOf, PassOf, byPartner, Fin.exists_fin_succ]

/-- The `3 + 1` distribution: the thick survivor paired with the thin one passes through. -/
example : (splitOf (byPartner ![3, 2, 1, 0]) ![false, false, false, true] ![1, 1, 1, 3]).leaf =
      false ∧
    (splitOf (byPartner ![3, 2, 1, 0]) ![false, false, false, true] ![1, 1, 1, 3]).pass =
      {0} := by
  refine ⟨?_, ?_⟩
  · simp [splitOf, LeafOf, PassOf, byPartner, Fin.exists_fin_succ, Fin.forall_fin_succ]
  · ext i; fin_cases i <;> simp [splitOf, PassOf, byPartner, Fin.exists_fin_succ]

/-- The `(2,2)` split members: a cross pairing with unequal indices; the smaller member of
each pair passes through. -/
example : (splitOf (byPartner ![2, 3, 0, 1]) ![false, false, true, true] ![1, 2, 2, 1]).leaf =
      false ∧
    (splitOf (byPartner ![2, 3, 0, 1]) ![false, false, true, true] ![1, 2, 2, 1]).pass =
      {0, 3} := by
  refine ⟨?_, ?_⟩
  · simp [splitOf, LeafOf, PassOf, byPartner, Fin.exists_fin_succ, Fin.forall_fin_succ]
  · ext i; fin_cases i <;> simp [splitOf, PassOf, byPartner, Fin.exists_fin_succ]

/-- The leaf split: a cross pairing with equal indices in each pair. -/
example : (splitOf (byPartner ![2, 3, 0, 1]) ![false, false, true, true] ![1, 1, 1, 1]).leaf =
      true ∧
    (splitOf (byPartner ![2, 3, 0, 1]) ![false, false, true, true] ![1, 1, 1, 1]).pass = ∅ := by
  refine ⟨?_, ?_⟩
  · simp [splitOf, LeafOf, PassOf, byPartner, Fin.exists_fin_succ, Fin.forall_fin_succ]
  · ext i; fin_cases i <;> simp [splitOf, PassOf, byPartner, Fin.exists_fin_succ]

/-- **The pairing field is needed**: the two cross pairings of a leaf split (Part II's Base I
morphisms of Types I and II) have the same `leaf` and `pass` but are different splits. -/
example : splitOf (byPartner ![2, 3, 0, 1]) ![false, false, true, true] ![1, 1, 1, 1] ≠
    splitOf (byPartner ![3, 2, 1, 0]) ![false, false, true, true] ![1, 1, 1, 1] := by
  classical
  intro h
  have h1 : ((0 : Fin 4), (2 : Fin 4)) ∈
      (splitOf (byPartner ![2, 3, 0, 1]) ![false, false, true, true] ![1, 1, 1, 1]).pairs :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩
  have h2 : ((0 : Fin 4), (2 : Fin 4)) ∉
      (splitOf (byPartner ![3, 2, 1, 0]) ![false, false, true, true] ![1, 1, 1, 1]).pairs := by
    intro hm
    have := (Finset.mem_filter.mp hm).2
    simp only [byPartner] at this
    revert this
    decide
  rw [h] at h1
  exact h2 h1

/-- `CensusAt` is inhabited at a concrete genus-six instance (the caterpillar core paired with
itself, through `FacetCensus.metricCensus_self`). -/
example (y₀ : Fin (6 * 2 + 3) → ℚ)
    (m : ValencyThreeGeneral.MetricFacetLimit StepSupplyGenusSix.catCubicCore.core
      StepSupplyGenusSix.catCubicCore.core y₀ (2 + 2)) : CensusAt m :=
  FacetCensus.metricCensus_self m

end NonVacuity

end DraismaVargas.Count.ValencyTwoSplit
