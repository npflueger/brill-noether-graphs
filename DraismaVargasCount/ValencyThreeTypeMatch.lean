import DraismaVargasCount.ValencyThreeSplit
import DraismaVargasCount.NonTrivalentBalance

/-!
# Stage 3 of valency-three uniqueness: `TypeMatch` at valency-three anchors

**Source.**  Vargas, Part II (arXiv:2609.09109): Case `{v3-nd4}` of the valency-three case of
the count (`subsec-case-v3`: at a valency-three limit `φ₀` there is exactly one
full-dimensional morphism of each of Types I, II, III) and `lm:change-comb-type` (all of them
have the same signed multiplicity).  Builds on `ValencyThreeSplit` (`TypeMatch`, `Reads`,
`Paired`, `paired_iff`, `split_eq_of_limitIso`), `ValencyThreeGeneral` (§3 metric limits, §7
`Split7`), the geometric contraction functor (`GeometricContraction`,
`GeometricLimitTransport`) and the reciprocal-corner multiplicity comparison of
`NonTrivalentBalance`.  The stages are those of `ValencyThreeSplit`.

## What is proved

* **§1, contraction commutes with a geometric datum isomorphism** on source occurrences and
  source vertices: `sourceEdgeMap_comm`, `sourceVertexMap_comm` (the latter at a vertex whose
  target vertex carries a second occurrence, `HasOtherEdge`), for the induced
  `contractIso = GeometricContraction.contractDatumIso`.
* **§2, the fibre reading is transported**: `ndAt_map`, `fib_map`, `intl_map`, `lift_map`
  and **`paired_map`** -- the pairing `Paired L i j` read off the incoming cover's anchor
  fibre goes to the pairing for the transported labelling.
* **§3, `type_eq_of_map`**: the type of the split read off a cover is invariant under any
  geometric datum isomorphism carrying the contracted occurrence to the contracted
  occurrence, for labellings transported along the induced isomorphism of limits (under any
  name of the image occurrence, `contractDatumIsoOfEdgeEq`).  Both ends of the contracted
  occurrence carry a second occurrence at every anchor (`hasOtherEdge_of_anchorInput`).
* **§4, regrowths**: `isMetricIso_limitIso` (a frame isomorphism induces a labelled-metric
  isomorphism of the limits) and **`type_eq_of_frameIso`** (the read type is a frame-class
  invariant).
* **§5, the stages are exactly anchored uniqueness.**  `AnchoredUniqueness` (two odd classes
  of one core, presented by anchored regrowths with labelled-metric isomorphic limits, are
  equal); **`typeMatch_of_anchoredUniqueness`**, `splitRigidity_of_anchoredUniqueness`,
  `anchoredUniqueness_of_stages`, **`stages_iff_anchoredUniqueness`**
  (`TypeMatch ∧ SplitRigidity ↔ AnchoredUniqueness`); `anchoredUniqueness_of_metric`,
  **`typeMatch_of_metric`** (the labelled-metric `huniqL` implies stage 3),
  `anchoredUniqueness_of_coarse`, `huniqL_of_anchoredUniqueness`.
* **§6, the multiplicity is type-blind**: `bridge_pos`, `valid_chosen_all`,
  **`bridge_parity_differs`** (at `|A| = 4`, `(k₂,k₃,k₄,k₅) = (1,3,3,2)` the Type III split has
  `k₁ = 3`, the Type II split `k₁ = 2`), **`absMult_eq_of_splits`** (members whose contracted
  rows carry the corners `1/k₁` of two realisable splits of one anchor, of any types, have equal
  multiplicity).

## Three questions, checked

* **(i) Does oddness of the multiplicity see the type?**  No.  All three types are realisable
  at every anchor (`valid_chosen_all`, from `ValencyThreeGeneral`'s `existsUnique`), the only
  type-dependent number in a member's matrix is the corner `1/k₁` of the contracted row, and
  it cancels against the row denominator `d₁ = k₁` in `Mult = D_φ det A_φ / 2^{l(T)}` (Part II
  `lm:change-comb-type`(2); in Lean `absMult_eq_of_splits`, from
  `NonTrivalentBalance.absMult_eq_of_reciprocal_corners`).  The bridge `k₁` itself can change
  parity across types (`bridge_parity_differs`), so a `k₁`-weighted count *would* separate
  them; the true multiplicity does not.  Oddness alone therefore cannot give `TypeMatch`.
* **(ii) Do two odd classes at one labelled metric limit read the same type?**  The question
  is exactly uniqueness.  Two odd classes read the same type as soon as they are the same
  class (`type_eq_of_frameIso`), so a counterexample to `TypeMatch` is precisely two
  *distinct* odd classes of one core at one labelled metric limit reading different types --
  a counterexample to anchored uniqueness (`typeMatch_of_anchoredUniqueness`).  Computer
  experiments (not part of this library) find no valency-three labelled-metric uniqueness
  violation in genus four, and every valency-three coarse uniqueness violation they find in
  genus six is split `1 + 1` by the labelled metric limit.
  Where a counterexample would have to live (analysis, not proved in Lean): Part II gives one
  morphism of each type at `φ₀`, so two types over *one* core need two resolutions of the
  merged vertex that give the same labelled core, i.e. a core slot parallel to the contracted
  slot (a digon; the limit then has a loop at the anchor, on which two survivors lie).  There
  `TypeMatch` needs a label-moving automorphism of `φ₀` reversing that loop, as at the
  `cat_step` ballot limits (the sheet swap `ValencyThreeSplit.swapIso`); the far core of
  `cat_step` is exactly this case (`ValencyThreeCensus.not_noParallel_catLoop`).
* **(iii) Can `TypeMatch` fail?**  Only together with anchored uniqueness
  (`typeMatch_of_anchoredUniqueness`).  It holds at the near core of `cat_step`, which has no
  slot parallel to the contracted slot (`ValencyThreeCensus.noParallel_cat` and
  `ValencyThreeCoreSlots.typeMatch_of_noParallel`).  Its universal form (along *every*
  labelled-metric isomorphism) fails wherever a label-moving automorphism meets a `simple`
  split (`ValencyThreeSplit`, §11).

## Scope

* **`TypeMatch` in general.**  Here it is reduced to `AnchoredUniqueness` (equivalently, with
  `SplitRigidity`, to `huniqL` at valency-three limits).  A direct proof has to identify
  `Paired` with the core identification's incidence at the two ends of the contracted slot and
  show that some labelled-metric isomorphism preserves the core slots of the four survivors;
  `ValencyThreeCoreSlots.typeMatch_of_noParallel` does this at every core with no slot
  parallel to the contracted slot.  Where there is such a slot the count uses the census
  (equal-*counts*) form instead of uniqueness, as the digon analysis in (ii) suggests: the far
  core of `cat_step` has a loop at the merged vertex and is a loop presenter, so
  `ValencyThreeLoopMerge.metricCensus_clause_of_v3'` and `frameClass_eq_of_loopPresenter` give
  the `FacetCensus.MetricCensus` clause there via the label-moving automorphism of (ii), and
  every genus-six step, including the digon--digon steps, is covered by
  `ValencyThreeDigon.exists_facetDatum_v3Clause_of_step`.  Uniqueness at *coarse* (unlabelled)
  limits on the far side of `cat_step` is not needed: the count goes through the metric census
  (step 3 of `Assembly`).
* `absMult_eq_of_splits` carries the residues `hleaf`, `hother` of
  `NonTrivalentBalance.absMult_eq_of_reciprocal_corners` and the reciprocal-corner hypotheses;
  the Lean form of the answer to (i) is modulo those (Part II proves them).
* The digon analysis in (ii) is informal.
* `HasOtherEdge` is a hypothesis of §1--§2 only; it is discharged at every anchor
  (`hasOtherEdge_of_anchorInput`).
* The new `Prop`s: `AnchoredUniqueness` (interface: equivalent to `TypeMatch ∧ SplitRigidity`,
  `stages_iff_anchoredUniqueness`; consumer `huniqL_of_anchoredUniqueness`); `HasOtherEdge`
  (interface line in its docstring).
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.ValencyThreeTypeMatch

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open GraphContraction GluingContraction
open W4StableSource

/-! ## 1.  Contraction commutes with a geometric datum isomorphism -/

section Commute

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ}
  {D₁ : GluingDatum target₁ degree} {D₂ : GluingDatum target₂ degree}
  (ι : GeometricDatumIso D₁ D₂) (c₁ : target₁.edges)
  (hOne₁ : num_edges target₁ (c₁ : target₁.V × target₁.V).1 (c₁ : target₁.V × target₁.V).2 = 1)
  (hOne₂ : num_edges target₂ (ι.targetEdge c₁ : target₂.V × target₂.V).1
    (ι.targetEdge c₁ : target₂.V × target₂.V).2 = 1)

theorem targetEdge_ne {e : target₁.edges} (he : e ≠ c₁) : ι.targetEdge e ≠ ι.targetEdge c₁ :=
  fun h ↦ he (ι.targetEdge.injective h)

theorem contractEdgeEquiv_foldEdge (f : {f : target₁.edges // f ≠ c₁}) :
    GeometricContraction.contractEdgeEquiv ι c₁ hOne₁ hOne₂ (foldEdge rfl (fst_ne_snd c₁) hOne₁ f) =
      foldEdge rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ ⟨ι.targetEdge f.1, targetEdge_ne ι c₁ f.2⟩ := by
  have key : unfoldEdge rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂
      (GeometricContraction.contractEdgeEquiv ι c₁ hOne₁ hOne₂
        (foldEdge rfl (fst_ne_snd c₁) hOne₁ f)) = ι.targetEdge f.1 := by
    refine (GeometricContraction.unfoldEdge_contractEdgeEquiv ι c₁ hOne₁ hOne₂ _).trans ?_
    exact congrArg ι.targetEdge (unfoldEdge_foldEdge rfl (fst_ne_snd c₁) hOne₁ f)
  rw [← foldEdge_unfoldEdge rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂
    (GeometricContraction.contractEdgeEquiv ι c₁ hOne₁ hOne₂ (foldEdge rfl (fst_ne_snd c₁) hOne₁ f))
    (unfoldEdge_ne_contracted _ _ _ _)]
  exact congrArg _ (Subtype.ext key)

/-- The contraction isomorphism a geometric datum isomorphism induces
(`GeometricContraction.contractDatumIso`). -/
noncomputable abbrev contractIso : GeometricDatumIso (contractDatumAt D₁ c₁ hOne₁)
    (contractDatumAt D₂ (ι.targetEdge c₁) hOne₂) :=
  GeometricContraction.contractDatumIso ι c₁ hOne₁ hOne₂

/-- **Source occurrences commute with contraction.** -/
theorem sourceEdgeMap_comm (e : {e : D₁.SourceEdge // e.1.1 ≠ c₁}) :
    (contractIso ι c₁ hOne₁ hOne₂).sourceEdgeEquiv (sourceEdgeMap D₁ rfl (fst_ne_snd c₁) hOne₁ e) =
      sourceEdgeMap D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂
        ⟨ι.sourceEdgeEquiv e.1, targetEdge_ne ι c₁ e.2⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · exact contractEdgeEquiv_foldEdge ι c₁ hOne₁ hOne₂ ⟨e.1.1.1, e.2⟩
  · change ι.edgePerm (unfoldEdge rfl (fst_ne_snd c₁) hOne₁
        (foldEdge rfl (fst_ne_snd c₁) hOne₁ ⟨e.1.1.1, e.2⟩)) e.1.1.2 = ι.edgePerm e.1.1.1 e.1.1.2
    rw [unfoldEdge_foldEdge]

/-- **Source vertices commute with contraction**, at a vertex whose target vertex carries an
occurrence other than the contracted one. -/
theorem sourceVertexMap_comm (X : D₁.SourceVertex) (f : target₁.edges) (hf : f ≠ c₁)
    (hXf : (f : target₁.V × target₁.V).1 = X.1.1 ∨ (f : target₁.V × target₁.V).2 = X.1.1) :
    (contractIso ι c₁ hOne₁ hOne₂).sourceVertexEquiv (sourceVertexMap D₁ rfl (fst_ne_snd c₁) hOne₁ X) =
      sourceVertexMap D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ (ι.sourceVertexEquiv X) := by
  have hX : X = D₁.sourceEndpoint X.1.1 X.1.2 := by
    apply Subtype.ext
    exact Prod.ext rfl X.2.symm
  have hι : ι.sourceVertexEquiv X = D₂.sourceEndpoint (ι.targetVertex X.1.1) (ι.edgePerm f X.1.2) := by
    conv_lhs => rw [hX]
    exact (ι.sourceEndpoint_edge f X.1.1 hXf X.1.2).symm
  rw [hι]
  have hfold : (foldEdge rfl (fst_ne_snd c₁) hOne₁ ⟨f, hf⟩).1.1 =
        fold target₁ (fst_ne_snd c₁) X.1.1 ∨
      (foldEdge rfl (fst_ne_snd c₁) hOne₁ ⟨f, hf⟩).1.2 =
        fold target₁ (fst_ne_snd c₁) X.1.1 := by
    rcases hXf with h | h
    · left; rw [← h]; rfl
    · right; rw [← h]; rfl
  have hψ := (contractIso ι c₁ hOne₁ hOne₂).sourceEndpoint_edge (foldEdge rfl (fst_ne_snd c₁) hOne₁ ⟨f, hf⟩)
    (fold target₁ (fst_ne_snd c₁) X.1.1) hfold X.1.2
  change (contractIso ι c₁ hOne₁ hOne₂).sourceVertexEquiv
      ((contractDatumAt D₁ c₁ hOne₁).sourceEndpoint (fold target₁ (fst_ne_snd c₁) X.1.1) X.1.2) = _
  rw [← hψ]
  have h1 : (contractIso ι c₁ hOne₁ hOne₂).targetVertex (fold target₁ (fst_ne_snd c₁) X.1.1) =
      fold target₂ (fst_ne_snd (ι.targetEdge c₁)) (ι.targetVertex X.1.1) :=
    GeometricContraction.contractVertexEquiv_fold ι c₁ X.1.1
  have h2 : (contractIso ι c₁ hOne₁ hOne₂).edgePerm (foldEdge rfl (fst_ne_snd c₁) hOne₁ ⟨f, hf⟩) =
      ι.edgePerm f := by
    change ι.edgePerm (unfoldEdge rfl (fst_ne_snd c₁) hOne₁
      (foldEdge rfl (fst_ne_snd c₁) hOne₁ ⟨f, hf⟩)) = ι.edgePerm f
    rw [unfoldEdge_foldEdge]
  rw [h1, h2]
  exact sourceEndpoint_repr D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ _ _

end Commute

/-! ## 2.  Transport of the fibre reading -/

section Transport

open ValencyThreeSplit PrunedFibreValency PrunedFibreTree FullContractionFibre ContractionRamification

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ}
  {D₁ : GluingDatum target₁ degree} {D₂ : GluingDatum target₂ degree}
  (ι : GeometricDatumIso D₁ D₂) (c₁ : target₁.edges)
  (hOne₁ : num_edges target₁ (c₁ : target₁.V × target₁.V).1 (c₁ : target₁.V × target₁.V).2 = 1)
  (hOne₂ : num_edges target₂ (ι.targetEdge c₁ : target₂.V × target₂.V).1
    (ι.targetEdge c₁ : target₂.V × target₂.V).2 = 1)

/-- A target vertex carries an occurrence other than `c`.

interface: `∃ f ≠ c` incident to `w`; produced at both ends of the contracted occurrence of
every valency-three anchor by `hasOtherEdge_of_anchorInput`. -/
def HasOtherEdge {T : CFGraph} (c : T.edges) (w : T.V) : Prop :=
  ∃ f : T.edges, f ≠ c ∧ ((f : T.V × T.V).1 = w ∨ (f : T.V × T.V).2 = w)

theorem hasOtherEdge_of_two_le {T : CFGraph} (c : T.edges) (w : T.V)
    (h : 2 ≤ (GluingDatum.incidentEdges w).card) : HasOtherEdge c w := by
  classical
  by_contra hno
  have hsub : GluingDatum.incidentEdges w ⊆ {c} := by
    intro f hf
    rw [Finset.mem_singleton]
    by_contra hfc
    apply hno
    refine ⟨f, hfc, ?_⟩
    unfold GluingDatum.incidentEdges at hf
    exact (Finset.mem_filter.mp hf).2
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  omega

variable (hConn : D₁.Connected)
  (hEnds : HasOtherEdge c₁ (c₁ : target₁.V × target₁.V).1 ∧
    HasOtherEdge c₁ (c₁ : target₁.V × target₁.V).2)
  {block₁ : (mergedPartition D₁ (c₁ : target₁.V × target₁.V).1
    (c₁ : target₁.V × target₁.V).2).Blocks}
  {block₂ : (mergedPartition D₂ (ι.targetEdge c₁ : target₂.V × target₂.V).1
    (ι.targetEdge c₁ : target₂.V × target₂.V).2).Blocks}
  (hA : (contractIso ι c₁ hOne₁ hOne₂).sourceVertexEquiv (limA D₁ rfl (fst_ne_snd c₁) hOne₁ block₁) =
    limA D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ block₂)

include hConn in
theorem ndAt_map {X : D₁.SourceVertex} {e : D₁.SourceEdge} (he : e ∈ ndAt D₁ X) :
    ι.sourceEdgeEquiv e ∈ ndAt D₂ (ι.sourceVertexEquiv X) := by
  rw [mem_ndAt] at he ⊢
  rw [GeometricDatumIso.isDangling_map_iff ι hConn, ι.incident_map_iff]
  exact he

include hEnds in
theorem sourceVertexMap_comm_of_over {X : D₁.SourceVertex}
    (hX : X.1.1 = (c₁ : target₁.V × target₁.V).1 ∨ X.1.1 = (c₁ : target₁.V × target₁.V).2) :
    (contractIso ι c₁ hOne₁ hOne₂).sourceVertexEquiv (sourceVertexMap D₁ rfl (fst_ne_snd c₁) hOne₁ X) =
      sourceVertexMap D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ (ι.sourceVertexEquiv X) := by
  have hE : HasOtherEdge c₁ X.1.1 := by
    rcases hX with h | h <;> rw [h]
    exacts [hEnds.1, hEnds.2]
  obtain ⟨f, hf, hXf⟩ := hE
  exact sourceVertexMap_comm ι c₁ hOne₁ hOne₂ X f hf hXf

include hConn hEnds hA in
theorem fib_map {X : D₁.SourceVertex} (hX : X ∈ fib D₁ rfl (fst_ne_snd c₁) hOne₁ block₁) :
    ι.sourceVertexEquiv X ∈ fib D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ block₂ := by
  have hover := ((mem_fib_iff D₁ rfl (fst_ne_snd c₁) hOne₁ block₁ X).mp hX).1
  rw [fib, mem_activeFibreVertices] at hX ⊢
  refine ⟨?_, ?_⟩
  · rw [← sourceVertexMap_comm_of_over ι c₁ hOne₁ hOne₂ hEnds hover, hX.1]
    exact hA
  · rw [GeometricDatumIso.nonDanglingValency_map ι hConn]
    exact hX.2

include hConn hEnds hA in
theorem intl_map {e : D₁.SourceEdge} (he : e ∈ intl D₁ rfl (fst_ne_snd c₁) hOne₁ block₁) :
    ι.sourceEdgeEquiv e ∈ intl D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ block₂ := by
  obtain ⟨-, -, -, -, hT, ha, hb⟩ := intl_ends D₁ rfl (fst_ne_snd c₁) hOne₁ block₁ he
  rw [intl, mem_internalEdges] at he ⊢
  obtain ⟨hSurv, -, hMap⟩ := he
  refine ⟨?_, ?_, ?_⟩
  · rw [GeometricDatumIso.isDangling_map_iff ι hConn]; exact hSurv
  · change ι.targetEdge e.1.1 = ι.targetEdge c₁
    rw [hT]
  · have h1 := sourceVertexMap_comm_of_over ι c₁ hOne₁ hOne₂ hEnds (X := (D₁.sourceEnds e).1)
      (Or.inl ha)
    have h2 := sourceVertexMap_comm_of_over ι c₁ hOne₁ hOne₂ hEnds (X := (D₁.sourceEnds e).2)
      (Or.inr hb)
    have hsame := sourceVertexMap_sourceEnds_eq_of_contracted D₁ rfl (fst_ne_snd c₁) hOne₁ e hT
    rcases ι.sourceEnds_map e with h | h
    · have h' := congrArg Prod.fst h
      simp only at h'
      refine (congrArg _ h').trans ?_
      rw [← h1, hMap]; exact hA
    · have h' := congrArg Prod.fst h
      simp only at h'
      refine (congrArg _ h').trans ?_
      rw [← h2, ← hsame, hMap]; exact hA

variable (L₁ : AnchorLabelling (contractDatum D₁ rfl (fst_ne_snd c₁) hOne₁)
    (limA D₁ rfl (fst_ne_snd c₁) hOne₁ block₁))
  (L₂ : AnchorLabelling (contractDatum D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂)
    (limA D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ block₂))
  (hL : ∀ i, L₂.e i = (contractIso ι c₁ hOne₁ hOne₂).sourceEdgeEquiv (L₁.e i))

include hL in
/-- **Lifts of transported labels are transported lifts.** -/
theorem lift_map (i : Fin 4) : lift L₂ i = ι.sourceEdgeEquiv (lift L₁ i) := by
  have h := sourceEdgeMap_comm ι c₁ hOne₁ hOne₂ ⟨lift L₁ i, lift_ne L₁ i⟩
  have h2 : sourceEdgeMap D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂ ⟨lift L₂ i, lift_ne L₂ i⟩ =
      sourceEdgeMap D₂ rfl (fst_ne_snd (ι.targetEdge c₁)) hOne₂
        ⟨ι.sourceEdgeEquiv (lift L₁ i), targetEdge_ne ι c₁ (lift_ne L₁ i)⟩ := by
    rw [sourceEdgeMap_lift, hL, ← h, sourceEdgeMap_lift]
  exact congrArg Subtype.val (sourceEdgeMap_injective _ _ _ _ h2)

include hConn hEnds hA hL in
/-- **The pairing read off the fibre is transported.** -/
theorem paired_map {i j : Fin 4} (hp : Paired L₁ i j) : Paired L₂ i j := by
  obtain ⟨X, hX, X', hX', hi, hj, hor⟩ := hp
  refine ⟨ι.sourceVertexEquiv X, fib_map ι c₁ hOne₁ hOne₂ hConn hEnds hA hX,
    ι.sourceVertexEquiv X', fib_map ι c₁ hOne₁ hOne₂ hConn hEnds hA hX', ?_, ?_, ?_⟩
  · rw [lift_map ι c₁ hOne₁ hOne₂ L₁ L₂ hL]; exact ndAt_map ι hConn hi
  · rw [lift_map ι c₁ hOne₁ hOne₂ L₁ L₂ hL]; exact ndAt_map ι hConn hj
  · rcases hor with rfl | ⟨e, he, heX, heX', h2⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨ι.sourceEdgeEquiv e, intl_map ι c₁ hOne₁ hOne₂ hConn hEnds hA he,
        ndAt_map ι hConn heX, ndAt_map ι hConn heX', ?_⟩
      rw [GeometricDatumIso.nonDanglingValency_map ι hConn,
        GeometricDatumIso.nonDanglingValency_map ι hConn]
      exact h2

end Transport

/-! ## 3.  The read type is invariant -/

section TypeInvariance

open ValencyThreeSplit PrunedFibreValency PrunedFibreTree FullContractionFibre ContractionRamification
open ValencyThreeGeneral.Split7
open FullDimensionalSource

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {D₁ : GluingDatum target₁ degree} {D₂ : GluingDatum target₂ degree}

/-- At a valency-three anchor both endpoints of the contracted occurrence carry another
occurrence (the divalent end has valency two, the trivalent end three). -/
theorem hasOtherEdge_of_anchorInput (fd : FullDimensionalSourcePresentation D₁ coordinate)
    {c : target₁.edges}
    {hOne : num_edges target₁ (c : target₁.V × target₁.V).1 (c : target₁.V × target₁.V).2 = 1}
    {block : (mergedPartition D₁ (c : target₁.V × target₁.V).1
      (c : target₁.V × target₁.V).2).Blocks}
    (H : AnchorInput D₁ rfl (fst_ne_snd c) hOne block) :
    HasOtherEdge c (c : target₁.V × target₁.V).1 ∧ HasOtherEdge c (c : target₁.V × target₁.V).2 := by
  obtain ⟨huv, hu2, hv3, -, -⟩ := H.sides fd
  have h2 : 2 ≤ (GluingDatum.incidentEdges (divEnd (c : target₁.V × target₁.V).1
    (c : target₁.V × target₁.V).2)).card := le_of_eq hu2.symm
  have h3 : 2 ≤ (GluingDatum.incidentEdges (triEnd (c : target₁.V × target₁.V).1
    (c : target₁.V × target₁.V).2)).card := by rw [hv3]; omega
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hu] at h2; rw [hv] at h3
    exact ⟨hasOtherEdge_of_two_le c _ h2, hasOtherEdge_of_two_le c _ h3⟩
  · rw [hu] at h2; rw [hv] at h3
    exact ⟨hasOtherEdge_of_two_le c _ h3, hasOtherEdge_of_two_le c _ h2⟩

/-- **The read type is invariant under a datum isomorphism carrying the contracted occurrence
to the contracted occurrence**, for labellings transported along the induced contraction
isomorphism.  Stated for an arbitrary name `c₂` of the image occurrence. -/
theorem type_eq_of_map (fd₁ : FullDimensionalSourcePresentation D₁ coordinate)
    (fd₂ : FullDimensionalSourcePresentation D₂ coordinate)
    (ι : GeometricDatumIso D₁ D₂) (c₁ : target₁.edges) (c₂ : target₂.edges)
    (h : ι.targetEdge c₁ = c₂)
    (hOne₁ : num_edges target₁ (c₁ : target₁.V × target₁.V).1 (c₁ : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (c₂ : target₂.V × target₂.V).1 (c₂ : target₂.V × target₂.V).2 = 1)
    {block₁ : (mergedPartition D₁ (c₁ : target₁.V × target₁.V).1
      (c₁ : target₁.V × target₁.V).2).Blocks}
    {block₂ : (mergedPartition D₂ (c₂ : target₂.V × target₂.V).1
      (c₂ : target₂.V × target₂.V).2).Blocks}
    (H₁ : AnchorInput D₁ rfl (fst_ne_snd c₁) hOne₁ block₁)
    (H₂ : AnchorInput D₂ rfl (fst_ne_snd c₂) hOne₂ block₂)
    (hA : (GeometricLimitTransport.contractDatumIsoOfEdgeEq ι c₁ c₂ h hOne₁ hOne₂).sourceVertexEquiv
      (limA D₁ rfl (fst_ne_snd c₁) hOne₁ block₁) = limA D₂ rfl (fst_ne_snd c₂) hOne₂ block₂)
    (L₁ : AnchorLabelling (contractDatum D₁ rfl (fst_ne_snd c₁) hOne₁)
      (limA D₁ rfl (fst_ne_snd c₁) hOne₁ block₁))
    (L₂ : AnchorLabelling (contractDatum D₂ rfl (fst_ne_snd c₂) hOne₂)
      (limA D₂ rfl (fst_ne_snd c₂) hOne₂ block₂))
    (hL : ∀ i, L₂.e i =
      (GeometricLimitTransport.contractDatumIsoOfEdgeEq ι c₁ c₂ h hOne₁ hOne₂).sourceEdgeEquiv
        (L₁.e i))
    {s₁ s₂ : Split}
    (hs₁ : Reads L₁ (divEnd (c₁ : target₁.V × target₁.V).1 (c₁ : target₁.V × target₁.V).2) s₁)
    (hs₂ : Reads L₂ (divEnd (c₂ : target₂.V × target₂.V).1 (c₂ : target₂.V × target₂.V).2) s₂) :
    s₁.type = s₂.type := by
  subst h
  have hp₁ := (paired_iff fd₁ H₁ L₁ hs₁ (typePartner s₁.type) (typePartner_ne_zero _)).mpr rfl
  have hp₂ := paired_map ι c₁ hOne₁ hOne₂ fd₁.valid.1 (hasOtherEdge_of_anchorInput fd₁ H₁) hA
    L₁ L₂ hL hp₁
  exact typePartner_injective
    ((paired_iff fd₂ H₂ L₂ hs₂ (typePartner s₁.type) (typePartner_ne_zero _)).mp hp₂)

end TypeInvariance

/-! ## 4.  Regrowths: the read type is a frame-class invariant -/

section Regrowth

open ValencyThreeSplit
open ValencyThreeGeneral.Split7
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open GeometricLimitTransport (limitIso)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **A frame isomorphism induces a labelled-metric isomorphism of the limits.** -/
theorem isMetricIso_limitIso {w w' : Regrowth core y degree} (fi : FrameIso w.frame w'.frame) :
    IsMetricIso w w' (limitIso fi) := fun e ↦
  ⟨GeometricLimitTransport.limitLength_limitIso fi e, by
    rw [ValencyThreeGeneral.limitCol_limitIso fi e, ValencyThreeGeneral.slotColumn_frameIso]⟩

/-- **The read type is a frame-class invariant.** -/
theorem type_eq_of_frameIso {w w' : Regrowth core y degree} (fi : FrameIso w.frame w'.frame)
    {block block'} (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block')
    (L : AnchorLabelling w.limit (anchorOf w block))
    (L' : AnchorLabelling w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = (limitIso fi).sourceEdgeEquiv (L.e i))
    {s s' : Split} (hs : Reads L (uOf w) s) (hs' : Reads L' (uOf w') s') : s.type = s'.type :=
  type_eq_of_map w.frame.fullDim w'.frame.fullDim fi.datum (w.frame.edgeOf w.column)
    (w'.frame.edgeOf w'.column)
    (by rw [GeometricLimitTransport.targetEdge_edgeOf, GeometricLimitTransport.column_eq_of_frameIso fi])
    _ _ H H' (sourceVertexEquiv_limA w w' H H' (limitIso fi)) L L' hL hs hs'

end Regrowth

/-! ## 5.  Anchored uniqueness: what the stages are -/

section Stages

open ValencyThreeSplit
open ValencyThreeGeneral.Split7
open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft SameMetricLimit)
open FacetMachine (FacetLimit SpecializesLeft)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open GeometricLimitTransport (limitIso)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Anchored uniqueness**: two odd classes of one core, presented by regrowths with
valency-three anchors whose limits are labelled-metric isomorphic, are equal.  This is
`huniqL` at the valency-three limits, in the regrowth form `TypeMatch` and `SplitRigidity`
are stated in.

Interface: equivalent to `TypeMatch ∧ SplitRigidity` (`stages_iff_anchoredUniqueness`);
implied by the metric `huniqL` (`anchoredUniqueness_of_metric`) and by the coarse one
(`anchoredUniqueness_of_coarse`). -/
def AnchoredUniqueness (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block'),
    (∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ) →
    (FrameClass.mk w.frame).IsOdd → (FrameClass.mk w'.frame).IsOdd →
    FrameClass.mk w.frame = FrameClass.mk w'.frame

/-- **Stage 3 from uniqueness**: anchored uniqueness gives `TypeMatch`, with the isomorphism
the frame isomorphism induces on the limits. -/
theorem typeMatch_of_anchoredUniqueness (h : AnchoredUniqueness core y degree) :
    TypeMatch core y degree := by
  intro w w' block block' H H' hsame hx hx'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (h w w' block block' H H' hsame hx hx')
  exact ⟨limitIso fi, isMetricIso_limitIso fi, fun L L' hL _ _ hs hs' ↦
    type_eq_of_frameIso fi H H' L L' hL hs hs'⟩

theorem splitRigidity_of_anchoredUniqueness (h : AnchoredUniqueness core y degree) :
    SplitRigidity core y degree := by
  intro w w' block block' H H' ψ hψ _ _ _ hx hx' _ _ _
  exact h w w' block block' H H' ⟨ψ, hψ⟩ hx hx'

/-- **Stages 3--5 give anchored uniqueness** (the regrowth form of `huniqL_of_stages`). -/
theorem anchoredUniqueness_of_stages (h3 : TypeMatch core y degree)
    (h45 : SplitRigidity core y degree) : AnchoredUniqueness core y degree := by
  intro w w' block block' H H' hsame hx hx'
  obtain ⟨ψ, hψ, htype⟩ := h3 w w' block block' H H' hsame hx hx'
  obtain ⟨L⟩ := nonempty_anchorLabelling w.frame.fullDim H
  obtain ⟨L', hL, hsplit⟩ := regrowth_split_eq w w' H H' ψ L
  obtain ⟨s, hsR, -, -⟩ := existsUnique_reads w.frame.fullDim H L
  obtain ⟨s', hsR', -, -⟩ := existsUnique_reads w'.frame.fullDim H' L'
  have hss : s = s' := hsplit s s' hsR hsR' (htype L L' hL s s' hsR hsR')
  subst hss
  exact h45 w w' block block' H H' ψ hψ L L' hL hx hx' s hsR hsR'

/-- **The decomposition is exact**: stages 3 and 4--5 together are anchored uniqueness. -/
theorem stages_iff_anchoredUniqueness :
    TypeMatch core y degree ∧ SplitRigidity core y degree ↔ AnchoredUniqueness core y degree :=
  ⟨fun h ↦ anchoredUniqueness_of_stages h.1 h.2, fun h ↦
    ⟨typeMatch_of_anchoredUniqueness h, splitRigidity_of_anchoredUniqueness h⟩⟩

/-- The labelled-metric `huniqL` (the hypothesis of
`ValencyThreeGeneral.facetParity_of_metricUniqueness`) gives anchored uniqueness. -/
theorem anchoredUniqueness_of_metric {c' : Core n p}
    (huniqL : ∀ (m : MetricFacetLimit core c' y degree) (x x' : FrameClass core degree),
      x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x') :
    AnchoredUniqueness core y degree := by
  intro w w' _ _ _ _ hsame hx hx'
  have hm : ValencyThreeGeneral.MetricFacetLimit.ofLeft (c' := c') w =
      ValencyThreeGeneral.MetricFacetLimit.ofLeft w' :=
    Quotient.sound ((sameMetricLimit_iff (c' := c') w w').mpr hsame)
  exact huniqL _ _ _ hx ⟨w, rfl, rfl⟩ hx' ⟨w', rfl, hm.symm⟩

/-- The coarse `huniqL` gives anchored uniqueness. -/
theorem anchoredUniqueness_of_coarse {c' : Core n p}
    (huniqL : ∀ (l : FacetLimit core c' y degree) (x x' : FrameClass core degree),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x') :
    AnchoredUniqueness core y degree := by
  intro w w' _ _ _ _ hsame hx hx'
  obtain ⟨ψ, -⟩ := hsame
  have hl : FacetMachine.FacetLimit.ofLeft (c' := c') w = FacetMachine.FacetLimit.ofLeft w' :=
    Quotient.sound ⟨ψ⟩
  exact huniqL _ _ _ hx ⟨w, rfl, rfl⟩ hx' ⟨w', rfl, hl.symm⟩

/-- **Labelled-metric uniqueness gives stage 3 for free**: the labelled-metric `huniqL`
of `ValencyThreeGeneral.facetParity_of_metricUniqueness` implies `TypeMatch`. -/
theorem typeMatch_of_metric {c' : Core n p}
    (huniqL : ∀ (m : MetricFacetLimit core c' y degree) (x x' : FrameClass core degree),
      x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x') :
    TypeMatch core y degree :=
  typeMatch_of_anchoredUniqueness (anchoredUniqueness_of_metric huniqL)

/-- The consumer, through anchored uniqueness: `huniqL` at the valency-three metric limits. -/
theorem huniqL_of_anchoredUniqueness {c' : Core n p} (h : AnchoredUniqueness core y degree)
    (m : MetricFacetLimit core c' y degree) (hm : V3Limit m) (x x' : FrameClass core degree)
    (hx : x.IsOdd) (hs : MSpecializesLeft x m) (hx' : x'.IsOdd) (hs' : MSpecializesLeft x' m) :
    x = x' :=
  huniqL_of_stages (typeMatch_of_anchoredUniqueness h) (splitRigidity_of_anchoredUniqueness h)
    m hm x x' hx hs hx' hs'

end Stages

/-! ## 6.  The multiplicity is type-blind -/

section Weights

open ValencyThreeGeneral.Split7
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases.NonTrivalentLinkMatrix

/-- The bridge index `k₁` of a realisable split is positive. -/
theorem bridge_pos (a : AnchorIndices) {s : Split} (hv : a.Valid s) : 0 < a.bridge s := by
  obtain ⟨A, k₂, k₃, k₄, k₅, h25, h34, tri, dbl, s3, s4⟩ := a
  rcases s with _ | ⟨_ | _, _ | _⟩ <;>
    simp_all [AnchorIndices.bridge, AnchorIndices.Valid, AnchorIndices.kα, AnchorIndices.kδ,
      AnchorIndices.kβ]
  all_goals omega

/-- The three types always coexist: at every anchor, each type has a realisable split
(`ValencyThreeGeneral`'s `existsUnique`). -/
theorem valid_chosen_all (a : AnchorIndices) (t : VType) :
    a.Valid (chosen a.A a.k₂ a.k₄ t) ∧ (chosen a.A a.k₂ a.k₄ t).type = t :=
  ⟨valid_chosen a t, type_chosen _ _ _ t⟩

/-- The anchor indices `|A| = 4`, `(k₂, k₃, k₄, k₅) = (1, 3, 3, 2)` (`(⊞)`: `1+3+3+2 = 9`). -/
def exampleIndices : AnchorIndices where
  A := 4
  k₂ := 1
  k₃ := 3
  k₄ := 3
  k₅ := 2
  h25 := by decide
  h34 := by decide
  tri := by decide
  doubled := by decide
  simple₃ := by decide
  simple₄ := by decide

/-- **The bridge index does not have one parity across the types.**  At `exampleIndices` the Type III
split has `k₁ = 3` and the Type II split `k₁ = 2`.  A multiplicity weighted by `k₁` would
therefore separate the types by parity; the actual one is not (`absMult_eq_of_splits`). -/
theorem bridge_parity_differs :
    exampleIndices.Valid .base₂ ∧ exampleIndices.Valid (.simple true false) ∧ Split.base₂.type ≠ (Split.simple true false).type ∧
      exampleIndices.bridge .base₂ = 3 ∧ exampleIndices.bridge (.simple true false) = 2 := by
  refine ⟨trivial, ?_, by decide, rfl, rfl⟩
  simp only [AnchorIndices.Valid, AnchorIndices.kα, AnchorIndices.kβ, AnchorIndices.kδ, exampleIndices]
  decide

variable {targetIn targetOut : CFGraph} {degIn degOut : ℕ}
  {dataIn : GluingDatum targetIn degIn} {dataOut : GluingDatum targetOut degOut}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The multiplicity does not see the type**: two members specialising to one
non-trivalent limit, whose contracted rows carry the corners `1/k₁` of two realisable splits
of the same anchor -- of any two types -- have the same multiplicity (Part II
`lm:change-comb-type`(2): `d₁ = k₁` cancels the corner).  Parity therefore cannot tell the
types apart. -/
theorem absMult_eq_of_splits (a : AnchorIndices) {s s' : Split} (hv : a.Valid s)
    (hv' : a.Valid s')
    (pIn : dataIn.LengthMatrixPresentation coordinate)
    (pOut : dataOut.LengthMatrixPresentation coordinate) {row col : coordinate}
    (hagree : AgreeOffColumn (matrix pIn) (matrix pOut) col)
    (hrowIn : ∀ c, c ≠ col → matrix pIn row c = 0)
    (hrowOut : ∀ c, c ≠ col → matrix pOut row c = 0)
    (hcornerIn : matrix pIn row col = 1 / (a.bridge s : ℚ))
    (hcornerOut : matrix pOut row col = 1 / (a.bridge s' : ℚ))
    (hleaf : leafCount targetOut = leafCount targetIn)
    (hother : ∏ i ∈ Finset.univ.erase row, rowDenominator pOut i =
      ∏ i ∈ Finset.univ.erase row, rowDenominator pIn i) :
    absMult pOut = absMult pIn :=
  NonTrivalentBalance.absMult_eq_of_reciprocal_corners pIn pOut hagree hrowIn hrowOut
    (bridge_pos a hv) (bridge_pos a hv') hcornerIn hcornerOut hleaf hother

end Weights

end DraismaVargas.Count.ValencyThreeTypeMatch
