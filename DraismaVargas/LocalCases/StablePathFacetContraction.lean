import DraismaVargas.LocalCases.NonTrivalentUniqueFourValent
import DraismaVargas.LocalCases.PrunedFibreStablePath
import DraismaVargas.LocalCases.NonTrivalentValencyFourAnchor
import DraismaVargas.LocalCases.DivalentSourceLocal

/-!
# The stable-row dictionary across a one-zero-row facet

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1, labelling
convention (1) --

> Aside from `h_1^(q)`, the edges of `H^(q)` correspond bijectively to those of
> `H_0`, and for each `h ∈ E(H_0)` we denote by `h^(q)` the corresponding edge
> in `E(H^(q))`

-- together with Lemma `lm:change-comb-type`, where the wall matrix is read as
the common minor `A_{φ₀}` of the incoming matrices; and Draisma--Vargas Part I
(arXiv:1909.12924): the construction of the stable graph `H(M)` in Section 3,
and the edge labellings a limit inherits in Section 5 (the source/row
isomorphisms).

## What is proved

Let `M = data` be an incoming full-dimensional cover over a target tree `T`, let
`t₁ = contracted` be a target occurrence joining `a ≠ b`, and let
`M₀ = contractDatum M hc hab hOne` be the wall datum over `T₀ = contract T`.  At
a Part II open facet -- nonnegative wall metric `coordinates` whose only zero is
the contracted column, the stable row `facet` vanishing, no other row vanishing,
and the vanishing row carrying a simple end -- this file proves:

* **danglingness transport** (`isDangling_sourceEdgeMap_iff`,
  `isDangling_sourceEdgeEmbedding_iff`): danglingness is unchanged on the
  occurrences that survive the contraction, and `exists_sourceEdgeEmbedding_eq_iff`
  identifies those: an incoming occurrence has an image exactly when it does not
  lie over `t₁`.  The occurrences over `t₁` are deleted;
* **the merged-vertex valency comparison**
  (`nonDanglingValency_mergedVertex_of_no_contracted`,
  `nonDanglingValency_mergedVertex_eq_two_of_boundary_pair`): a fibre vertex with
  no surviving occurrence over `t₁` is the whole pruned fibre and the merged
  valency is unchanged; a surviving occurrence over `t₁` that is consecutive to
  two *distinct* retained occurrences has a two-vertex pruned fibre, so the
  merged vertex is again divalent.  Neither statement assumes a wall valency, a
  star, or an unramified anchor;
* **the row map** `StablePath M₀ → StablePath M` (`incomingRow`, which is
  `PrunedFibreStablePath.stablePathLift`) is injective (`incomingRow_injective`),
  misses exactly the vanishing row (`incomingRow_ne_facet`,
  `exists_incomingRow_eq`), and therefore gives the dictionary
  `rowEquiv : StablePath M₀ ≃ {row : StablePath M // row ≠ facet}` and its
  `Option`-valued inverse `wallRow`, with `wallRow facet = none`;
* **the occurrence sets** (`stablePath_descend_eq_iff`,
  `stablePath_nonDanglingEmbedding_eq_iff`, `mem_path_wallLabelling_iff`): a
  retained occurrence lies on a wall row exactly when it lies on the incoming
  row of that wall row, so the two occurrence lists differ precisely by the
  occurrences over `t₁`;
* **the square honest labelling** `wallLabelling` of `M₀` over
  `{column : coordinate // column ≠ targetEdge.symm contracted} ≃ T₀.edges`, and
  the `AgreeOffColumn`-shaped identity `matrix_wallLabelling`: its matrix agrees
  entrywise with the incoming matrix off the contracted column;
* **the count** `card_stablePath_wall_add_one`: `|E(H₀)| = |E(H)| - 1`, so the
  wall datum really does lose the contracting stable edge;
* `exists_wallLabelling_of_single_zero_row` and, at a four-valent wall,
  `exists_wallLabelling_of_single_zero_row_of_fourStar`, package the labelling,
  the dictionary and the matrix identity from the facet data alone, with the hypothesis list of
  `NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row` (the
  contraction forest and the dangling compatibility are *derived* from the simple
  end, not supplied).

## What is NOT proved

The chain argument needs one geometric input, isolated as the predicate
`NoContractedReturn data contracted`: at a surviving valency-two source vertex
there is at most one surviving occurrence over `t₁`.  Without it a stable class
could run along several occurrences over `t₁` in succession, and the two-vertex
fibre argument does not apply.  `noContractedReturn_of_nonleaf` discharges it
whenever **neither endpoint of `t₁` is a leaf of `T`**: change-minimality of a
full-dimensional cover then bounds the local ramification by one above `a` and
`b`, and `DivalentSourceLocal.sourceEdge_eq_of_same_target` applies.  Since a
Part II wall has `val(w₀) = val(u) + val(v) - 2`, this covers `val(w₀) = 4`
(3 + 3), `val(w₀) = 3` (2 + 3) and the `2 + 2` sub-case of `val(w₀) = 2`.  It
does **not** cover the `val(u) = 1, val(v) = 3` sub-case of `val(w₀) = 2`, where
the paper itself says the contracting stable edge runs up over `t₁` and back
above the leaf `u` ("the edge connecting `A_1^(q)` and `A_2^(q)` passes above
`u`", Section 5.1) -- exactly a contracted return.  That case is settled in
`DraismaVargas/LocalCases/LeafFacetNoReturn.lean`: `NoContractedReturn` really
is false there, but the weaker
`NoContractedReturnOffRow` -- two surviving occurrences over `t₁` at a divalent
vertex are equal or both on the vanishing row -- holds by `noReturn_off_facet`
(counting above the leaf via `leaf_block_dichotomy`), and the chain below is
re-run under it there.  At a four-valent wall the condition is free:
`noContractedReturn_of_fourStar` derives both endpoint valencies from the star
and change-minimality.

Nothing here constructs a `FullDimensionalSourcePresentation`, produces the wall
metric, or claims anything about the outgoing candidate.
`W4Bridge.auxR0SourceInput_of_contraction` is *not* used: its
`Nonempty (StablePath M₀ ≃ StablePath M)` is false at a Part II wall, and the
dictionary proved here is the correct replacement.

## Consumers

The `AgreeOffColumn` inputs of `NonTrivalentLinkMatrix`, the K = 0 row descent
of `NonTrivalentValencyFourRows`, and the common-minor half of Part II
`lm:change-comb-type`.
-/

namespace DraismaVargas.LocalCases.StablePathFacetContraction

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource WallDegeneration ClassInjectivity
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree
open FullDimensionalSource PresentationDecomposition

variable {target : CFGraph} {degree : ℕ}

section Transport

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- Danglingness is unchanged on occurrences away from the contracted target
occurrence. -/
theorem isDangling_sourceEdgeMap_iff (hCompat : DanglingCompatible data hc hab hOne)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) :
    IsDangling (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne e) ↔
      IsDangling data e.1 :=
  ⟨fun h ↦ hCompat.2 e h, fun h ↦ hCompat.1 e h⟩

/-- The same statement read on an occurrence of the wall datum. -/
theorem isDangling_sourceEdgeEmbedding_iff (hCompat : DanglingCompatible data hc hab hOne)
    (f : (contractDatum data hc hab hOne).SourceEdge) :
    IsDangling data (sourceEdgeEmbedding data hc hab hOne f) ↔
      IsDangling (contractDatum data hc hab hOne) f :=
  ⟨fun h ↦ hCompat.1.embedding f h, fun h ↦ hCompat.2.embedding f h⟩

/-- **What happens to the occurrences over the contracted target edge.**  An
incoming occurrence has an image in the wall datum exactly when it does not lie
over the contracted target occurrence; the occurrences over it are deleted. -/
theorem exists_sourceEdgeEmbedding_eq_iff (e : data.SourceEdge) :
    (∃ f : (contractDatum data hc hab hOne).SourceEdge,
        sourceEdgeEmbedding data hc hab hOne f = e) ↔ e.1.1 ≠ contracted := by
  constructor
  · rintro ⟨f, rfl⟩
    exact sourceEdgeEmbedding_ne_contracted data hc hab hOne f
  · exact exists_sourceEdgeEmbedding_eq data hc hab hOne

variable (hCompat : DanglingCompatible data hc hab hOne)

/-- A surviving incoming occurrence away from the contracted target occurrence,
read as a surviving occurrence of the wall datum. -/
noncomputable def descend (e : NonDanglingEdge data) (he : e.1.1.1 ≠ contracted) :
    NonDanglingEdge (contractDatum data hc hab hOne) :=
  ⟨sourceEdgeMap data hc hab hOne ⟨e.1, he⟩, fun hBad ↦ e.2 (hCompat.2 ⟨e.1, he⟩ hBad)⟩

@[simp] theorem nonDanglingEmbedding_descend (e : NonDanglingEdge data)
    (he : e.1.1.1 ≠ contracted) :
    nonDanglingEmbedding data hCompat.1 (descend data hc hab hOne hCompat e he) = e :=
  Subtype.ext (sourceEdgeEmbedding_sourceEdgeMap data hc hab hOne ⟨e.1, he⟩)

theorem descend_nonDanglingEmbedding (f : NonDanglingEdge (contractDatum data hc hab hOne))
    (hf : (nonDanglingEmbedding data hCompat.1 f).1.1.1 ≠ contracted) :
    descend data hc hab hOne hCompat (nonDanglingEmbedding data hCompat.1 f) hf = f := by
  apply Subtype.ext
  show sourceEdgeMap data hc hab hOne
      ⟨sourceEdgeEmbedding data hc hab hOne f.1, hf⟩ = f.1
  have hEq : (⟨sourceEdgeEmbedding data hc hab hOne f.1, hf⟩ :
      {e : data.SourceEdge // e.1.1 ≠ contracted}) =
      (sourceEdgeEquiv data hc hab hOne).symm f.1 := Subtype.ext rfl
  rw [hEq]
  exact (sourceEdgeEquiv data hc hab hOne).apply_symm_apply f.1

theorem descend_injective {e e' : NonDanglingEdge data} {he : e.1.1.1 ≠ contracted}
    {he' : e'.1.1.1 ≠ contracted}
    (h : descend data hc hab hOne hCompat e he = descend data hc hab hOne hCompat e' he') :
    e = e' := by
  have := congrArg (nonDanglingEmbedding data hCompat.1) h
  rwa [nonDanglingEmbedding_descend, nonDanglingEmbedding_descend] at this

theorem incident_descend {e : NonDanglingEdge data} (he : e.1.1.1 ≠ contracted)
    {v : data.SourceVertex} (hIncident : Incident data e.1 v) :
    Incident (contractDatum data hc hab hOne) (descend data hc hab hOne hCompat e he).1
      (sourceVertexMap data hc hab hOne v) :=
  incident_sourceEdgeMap data hc hab hOne ⟨e.1, he⟩ hIncident

end Transport


section Fibre

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- A surviving walk out of a vertex carrying no surviving occurrence over the
contracted target edge never leaves that vertex. -/
theorem eq_of_survivingWalk_of_no_contracted (v : data.SourceVertex)
    (hNone : ∀ e : data.SourceEdge, ¬ IsDangling data e → Incident data e v →
      e.1.1 ≠ contracted)
    {u : data.SourceVertex}
    (hWalk : Relation.ReflTransGen (SurvivingFibreStep data contracted) v u) : u = v := by
  induction hWalk with
  | refl => rfl
  | @tail middle last _ hStep ih =>
    obtain ⟨edge, hTarget, hSurvives, hEnds⟩ := hStep
    subst ih
    exact absurd hTarget (hNone edge hSurvives (incident_of_sourceEnds data hEnds))

/-- **An isolated fibre vertex.**  A source vertex carrying survivors but no
surviving occurrence over the contracted target edge is the whole pruned fibre
of its image. -/
theorem activeFibreVertices_eq_singleton_of_no_contracted (v : data.SourceVertex)
    (hActive : nonDanglingValency data v ≠ 0)
    (hNone : ∀ e : data.SourceEdge, ¬ IsDangling data e → Incident data e v →
      e.1.1 ≠ contracted) :
    activeFibreVertices data hc hab hOne (sourceVertexMap data hc hab hOne v) = {v} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨(mem_activeFibreVertices data hc hab hOne _ v).mpr ⟨rfl, hActive⟩, ?_⟩
  intro u hu
  obtain ⟨hMap, hUActive⟩ := (mem_activeFibreVertices data hc hab hOne _ u).mp hu
  exact eq_of_survivingWalk_of_no_contracted data v hNone
    ((sourceVertexMap_eq_iff_surviving_walk data hc hab hOne hActive hUActive).mp hMap.symm)

/-- The pruned fibre of such a vertex carries no internal occurrence. -/
theorem internalEdges_eq_empty_of_no_contracted (v : data.SourceVertex)
    (hActive : nonDanglingValency data v ≠ 0)
    (hNone : ∀ e : data.SourceEdge, ¬ IsDangling data e → Incident data e v →
      e.1.1 ≠ contracted) :
    internalEdges data hc hab hOne (sourceVertexMap data hc hab hOne v) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro edge hEdge
  obtain ⟨hFirst, hSecond⟩ :=
    (sourceEnds_mem_activeFibre_iff data hc hab hOne _ edge).mpr hEdge
  rw [activeFibreVertices_eq_singleton_of_no_contracted data hc hab hOne v hActive hNone,
    Finset.mem_singleton] at hFirst hSecond
  exact data.sourceEnds_ne edge (hFirst.trans hSecond.symm)

/-- **The merged valency at an isolated fibre vertex is unchanged.** -/
theorem nonDanglingValency_mergedVertex_of_no_contracted
    (hCompat : DanglingCompatible data hc hab hOne) (v : data.SourceVertex)
    (hActive : nonDanglingValency data v ≠ 0)
    (hNone : ∀ e : data.SourceEdge, ¬ IsDangling data e → Incident data e v →
      e.1.1 ≠ contracted) :
    nonDanglingValency (contractDatum data hc hab hOne)
        (sourceVertexMap data hc hab hOne v) = nonDanglingValency data v := by
  have hSum := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat
    (sourceVertexMap data hc hab hOne v)
  rw [activeFibreVertices_eq_singleton_of_no_contracted data hc hab hOne v hActive hNone,
    Finset.sum_singleton,
    internalEdges_eq_empty_of_no_contracted data hc hab hOne v hActive hNone,
    Finset.card_empty] at hSum
  omega

end Fibre


section Consecutive

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- At a surviving valency-two source vertex two distinct surviving incident
occurrences exhaust the incidences. -/
theorem eq_or_eq_of_nonDanglingValency_eq_two {v : data.SourceVertex}
    (hNd : nonDanglingValency data v = 2) {first second : data.SourceEdge}
    (hFirstSurvives : ¬ IsDangling data first) (hSecondSurvives : ¬ IsDangling data second)
    (hFirstInc : Incident data first v) (hSecondInc : Incident data second v)
    (hNe : first ≠ second) {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge v) : edge = first ∨ edge = second := by
  classical
  obtain ⟨other, hOtherNe, hPair⟩ :=
    nonDanglingIncident_eq_pair data hNd hFirstSurvives hFirstInc
  have hSecondMem : second ∈ nonDanglingIncident data v :=
    (mem_nonDanglingIncident data v second).mpr ⟨hSecondSurvives, hSecondInc⟩
  rw [hPair] at hSecondMem
  have hSecondOther : second = other := by
    rcases Finset.mem_insert.mp hSecondMem with h | h
    · exact absurd h hNe.symm
    · exact Finset.mem_singleton.mp h
  have hMem : edge ∈ nonDanglingIncident data v :=
    (mem_nonDanglingIncident data v edge).mpr ⟨hSurvives, hIncident⟩
  rw [hPair] at hMem
  rcases Finset.mem_insert.mp hMem with h | h
  · exact Or.inl h
  · exact Or.inr ((Finset.mem_singleton.mp h).trans hSecondOther.symm)

variable (hCompat : DanglingCompatible data hc hab hOne)

/-- **Stable adjacency descends off the contracted target occurrence.**  Two
consecutive surviving occurrences, neither over the contracted target edge,
meet at a divalent source vertex whose whole pruned fibre is that one vertex;
so the merged vertex is again divalent and their images are consecutive. -/
theorem consecutive_descend {x y : NonDanglingEdge data}
    (hx : x.1.1.1 ≠ contracted) (hy : y.1.1.1 ≠ contracted)
    (hCons : Consecutive data x y) :
    Consecutive (contractDatum data hc hab hOne)
      (descend data hc hab hOne hCompat x hx) (descend data hc hab hOne hCompat y hy) := by
  obtain ⟨hNe, v, hxv, hyv, hNd⟩ := hCons
  have hNeVal : x.1 ≠ y.1 := fun h ↦ hNe (Subtype.ext h)
  have hNone : ∀ e : data.SourceEdge, ¬ IsDangling data e → Incident data e v →
      e.1.1 ≠ contracted := by
    intro e hSurvives hIncident
    rcases eq_or_eq_of_nonDanglingValency_eq_two data hNd x.2 y.2 hxv hyv hNeVal
      hSurvives hIncident with h | h
    · rw [h]; exact hx
    · rw [h]; exact hy
  have hMerged := nonDanglingValency_mergedVertex_of_no_contracted data hc hab hOne hCompat v
    (by omega) hNone
  refine ⟨fun hEq ↦ hNe (descend_injective data hc hab hOne hCompat hEq),
    sourceVertexMap data hc hab hOne v, incident_descend data hc hab hOne hCompat hx hxv,
    incident_descend data hc hab hOne hCompat hy hyv, ?_⟩
  omega

end Consecutive


section Through

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (hCompat : DanglingCompatible data hc hab hOne)

include hCompat in
/-- **A stable class crossing the fibre forces a divalent merged vertex.**  If
one surviving occurrence over the contracted target edge is consecutive to two
*distinct* surviving occurrences away from it, then its pruned fibre is exactly
the two divalent meeting vertices joined by that one internal occurrence, so
the merged wall vertex again has surviving valency two. -/
theorem nonDanglingValency_mergedVertex_eq_two_of_boundary_pair
    {inner x z : NonDanglingEdge data} (hInner : inner.1.1.1 = contracted)
    (hx : x.1.1.1 ≠ contracted) (hz : z.1.1.1 ≠ contracted)
    (hcx : Consecutive data inner x) (hcz : Consecutive data inner z) (hxz : x ≠ z) :
    nonDanglingValency (contractDatum data hc hab hOne)
      (sourceVertexMap data hc hab hOne (data.sourceEnds inner.1).1) = 2 := by
  classical
  obtain ⟨-, v, hcv, hxv, hNdv⟩ := hcx
  obtain ⟨-, w, hcw, hzw, hNdw⟩ := hcz
  have hEndsMap : ∀ u : data.SourceVertex, Incident data inner.1 u →
      sourceVertexMap data hc hab hOne u =
        sourceVertexMap data hc hab hOne (data.sourceEnds inner.1).1 := by
    rintro u (h | h)
    · rw [← h]
    · rw [← h]
      exact (sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne inner.1 hInner).symm
  have hxNe : x.1 ≠ inner.1 := by intro h; rw [h] at hx; exact hx hInner
  have hzNe : z.1 ≠ inner.1 := by intro h; rw [h] at hz; exact hz hInner
  have hvw : v ≠ w := by
    rintro rfl
    rcases eq_or_eq_of_nonDanglingValency_eq_two data hNdv inner.2 x.2 hcv hxv
      (Ne.symm hxNe) z.2 hzw with h | h
    · exact hzNe h
    · exact hxz (Subtype.ext h.symm)
  have hAtV : ∀ e : data.SourceEdge, ¬ IsDangling data e → Incident data e v →
      e.1.1 = contracted → e = inner.1 := by
    intro e hs hi ht
    rcases eq_or_eq_of_nonDanglingValency_eq_two data hNdv inner.2 x.2 hcv hxv
      (Ne.symm hxNe) hs hi with h | h
    · exact h
    · rw [h] at ht; exact absurd ht hx
  have hAtW : ∀ e : data.SourceEdge, ¬ IsDangling data e → Incident data e w →
      e.1.1 = contracted → e = inner.1 := by
    intro e hs hi ht
    rcases eq_or_eq_of_nonDanglingValency_eq_two data hNdw inner.2 z.2 hcw hzw
      (Ne.symm hzNe) hs hi with h | h
    · exact h
    · rw [h] at ht; exact absurd ht hz
  have hEndsInPair : ∀ u : data.SourceVertex, Incident data inner.1 u → u = v ∨ u = w := by
    intro u hu
    rcases hcv with hv | hv <;> rcases hcw with hw | hw <;> rcases hu with hu | hu
    · exact absurd (hv.symm.trans hw) hvw
    · exact absurd (hv.symm.trans hw) hvw
    · exact Or.inl (hu.symm.trans hv)
    · exact Or.inr (hu.symm.trans hw)
    · exact Or.inr (hu.symm.trans hw)
    · exact Or.inl (hu.symm.trans hv)
    · exact absurd (hv.symm.trans hw) hvw
    · exact absurd (hv.symm.trans hw) hvw
  have hvMap := hEndsMap v hcv
  have hwMap := hEndsMap w hcw
  have hvActive : nonDanglingValency data v ≠ 0 := by omega
  have hwActive : nonDanglingValency data w ≠ 0 := by omega
  have hReach : ∀ u : data.SourceVertex,
      Relation.ReflTransGen (SurvivingFibreStep data contracted) v u → u = v ∨ u = w := by
    intro u hWalk
    induction hWalk with
    | refl => exact Or.inl rfl
    | @tail middle last _ hStep ih =>
      obtain ⟨edge, hTarget, hSurvives, hEnds⟩ := hStep
      have hEdge : edge = inner.1 := by
        rcases ih with h | h
        · subst h
          exact hAtV edge hSurvives (incident_of_sourceEnds data hEnds) hTarget
        · subst h
          exact hAtW edge hSurvives (incident_of_sourceEnds data hEnds) hTarget
      refine hEndsInPair last ?_
      rw [← hEdge]
      exact incident_of_sourceEnds data hEnds.symm
  have hFibre : activeFibreVertices data hc hab hOne
      (sourceVertexMap data hc hab hOne (data.sourceEnds inner.1).1) = {v, w} := by
    apply Finset.Subset.antisymm
    · intro u hu
      obtain ⟨hMap, hActive⟩ := (mem_activeFibreVertices data hc hab hOne _ u).mp hu
      have hWalk := (sourceVertexMap_eq_iff_surviving_walk data hc hab hOne
        hvActive hActive).mp (hvMap.trans hMap.symm)
      rcases hReach u hWalk with h | h <;> simp [h]
    · intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · exact (mem_activeFibreVertices data hc hab hOne _ u).mpr
          ⟨by rw [h]; exact hvMap, by rw [h]; exact hvActive⟩
      · have h' := Finset.mem_singleton.mp h
        exact (mem_activeFibreVertices data hc hab hOne _ u).mpr
          ⟨by rw [h']; exact hwMap, by rw [h']; exact hwActive⟩
  have hInternal : internalEdges data hc hab hOne
      (sourceVertexMap data hc hab hOne (data.sourceEnds inner.1).1) = {inner.1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨(mem_internalEdges data hc hab hOne _ inner.1).mpr ⟨inner.2, hInner, rfl⟩, ?_⟩
    intro e he
    obtain ⟨hs, ht, -⟩ := (mem_internalEdges data hc hab hOne _ e).mp he
    obtain ⟨hFst, hSnd⟩ := (sourceEnds_mem_activeFibre_iff data hc hab hOne _ e).mpr he
    rw [hFibre] at hFst hSnd
    have hIncV : Incident data e v := by
      rcases Finset.mem_insert.mp hFst with h | h
      · exact Or.inl h
      · rcases Finset.mem_insert.mp hSnd with h' | h'
        · exact Or.inr h'
        · exact absurd ((Finset.mem_singleton.mp h).trans
            (Finset.mem_singleton.mp h').symm) (data.sourceEnds_ne e)
    exact hAtV e hs hIncV ht
  have hSum := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat
    (sourceVertexMap data hc hab hOne (data.sourceEnds inner.1).1)
  rw [hFibre, Finset.sum_pair hvw, hInternal, Finset.card_singleton] at hSum
  omega

/-- The consequence used along a stable chain: the two boundary occurrences of
a crossed fibre have the same wall stable row. -/
theorem stablePath_descend_eq_of_boundary_pair
    {inner x z : NonDanglingEdge data} (hInner : inner.1.1.1 = contracted)
    (hx : x.1.1.1 ≠ contracted) (hz : z.1.1.1 ≠ contracted)
    (hcx : Consecutive data inner x) (hcz : Consecutive data inner z) :
    (descend data hc hab hOne hCompat x hx).stablePath =
      (descend data hc hab hOne hCompat z hz).stablePath := by
  by_cases hxz : x = z
  · subst hxz; rfl
  have hNd := nonDanglingValency_mergedVertex_eq_two_of_boundary_pair data hc hab hOne hCompat
    hInner hx hz hcx hcz hxz
  obtain ⟨-, v, hcv, hxv, -⟩ := hcx
  obtain ⟨-, w, hcw, hzw, -⟩ := hcz
  have hEndsMap : ∀ u : data.SourceVertex, Incident data inner.1 u →
      sourceVertexMap data hc hab hOne u =
        sourceVertexMap data hc hab hOne (data.sourceEnds inner.1).1 := by
    rintro u (h | h)
    · rw [← h]
    · rw [← h]
      exact (sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne inner.1 hInner).symm
  refine PrunedFibreStablePath.stablePath_eq_of_incident_divalent (contractDatum data hc hab hOne)
    _ _ (sourceVertexMap data hc hab hOne (data.sourceEnds inner.1).1) ?_ ?_ hNd
  · rw [← hEndsMap v hcv]
    exact incident_descend data hc hab hOne hCompat hx hxv
  · rw [← hEndsMap w hcw]
    exact incident_descend data hc hab hOne hCompat hz hzw

end Through


section NoReturn

/-- **No stable path returns to the contracted target occurrence.**  At a
surviving valency-two source vertex there is at most one surviving occurrence
over the contracted target edge. -/
def NoContractedReturn (data : GluingDatum target degree) (contracted : target.edges) : Prop :=
  ∀ vertex : data.SourceVertex, nonDanglingValency data vertex = 2 →
    ∀ first second : data.SourceEdge, first.1.1 = contracted → second.1.1 = contracted →
      ¬ IsDangling data first → ¬ IsDangling data second →
        Incident data first vertex → Incident data second vertex → first = second

/-- **Non-vacuity, and the only place the target valency enters.**  When
neither endpoint of the contracted target occurrence is a leaf of the target
tree, change-minimality of a full-dimensional cover bounds the local
ramification by one at every source vertex above them, and the divalent local
property then forbids a second surviving occurrence over the same target edge.
A leaf endpoint really can carry such a return -- that is the Part II
`val(u) = 1` sub-case of a valency-two wall. -/
theorem noContractedReturn_of_nonleaf {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b))
    (hLeft : 2 ≤ (GluingDatum.incidentEdges a).card)
    (hRight : 2 ≤ (GluingDatum.incidentEdges b).card) :
    NoContractedReturn data contracted := by
  intro vertex hNd first second hFirstT hSecondT hFirstS hSecondS hFirstI hSecondI
  have hAt := ((incident_iff_target_mem_and_rel data first vertex).mp hFirstI).1
  rw [hFirstT] at hAt
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hAt
  rw [hc] at hAt
  have hNonleaf : 2 ≤ (GluingDatum.incidentEdges (vertex.1.1 : target.V)).card := by
    rcases hAt with h | h
    · rw [← h]; exact hLeft
    · rw [← h]; exact hRight
  exact DivalentSourceLocal.sourceEdge_eq_of_same_target data fd.danglingEdgeNoGlue vertex hNd
    (DivalentSourceLocal.localRamification_le_one_of_nonleaf data fd.valid vertex
      (fd.changeMinimal (vertex.1.1 : target.V)) hNonleaf)
    first second hFirstS hSecondS hFirstI hSecondI (hFirstT.trans hSecondT.symm)

/-- **At a four-valent wall the non-leaf condition is automatic.**  Both
endpoints of the contracted target occurrence are trivalent there: the star
forces zero target change at each, and change-minimality then forces valency
three.  So the whole dictionary below is receipt-free at a Part II
`val(w₀) = 4` wall. -/
theorem noContractedReturn_of_fourStar {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩) :
    NoContractedReturn data contracted := by
  have hCard : ∀ place : target.V, place = a ∨ place = b →
      (GluingDatum.incidentEdges place).card = 3 := by
    intro place hPlace
    have hZero := W4IncomingCensus.changeZero_of_fourStar data fd hc hab hOne star place hPlace
    have hMin : data.targetChange place +
        ((GluingDatum.incidentEdges place).card : ℤ) - 3 = 0 := fd.changeMinimal place
    rw [hZero] at hMin
    omega
  exact noContractedReturn_of_nonleaf data fd hc
    (by rw [hCard a (Or.inl rfl)]; norm_num) (by rw [hCard b (Or.inr rfl)]; norm_num)

end NoReturn

section Chain

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (hCompat : DanglingCompatible data hc hab hOne)

/-- The invariant carried along a stable chain: an occurrence away from the
contracted target edge already has wall row `row`, and an occurrence over it
sends every consecutive retained occurrence to `row`. -/
def Anchored (row : StablePath (contractDatum data hc hab hOne))
    (x : NonDanglingEdge data) : Prop :=
  (∀ hx : x.1.1.1 ≠ contracted,
      (descend data hc hab hOne hCompat x hx).stablePath = row) ∧
  (x.1.1.1 = contracted → ∀ (y : NonDanglingEdge data) (hy : y.1.1.1 ≠ contracted),
      Consecutive data x y → (descend data hc hab hOne hCompat y hy).stablePath = row)

variable (hNoReturn : NoContractedReturn data contracted)

include hNoReturn in
/-- The invariant is closed under stable adjacency.  The four cases are: both
occurrences retained (`consecutive_descend`); a retained one followed by a
contracted one (`stablePath_descend_eq_of_boundary_pair`); a contracted one
followed by a retained one (the second clause); and two contracted ones, which
`NoContractedReturn` forbids. -/
theorem anchored_of_consecutive (row : StablePath (contractDatum data hc hab hOne))
    (first second : NonDanglingEdge data) (hCons : Consecutive data first second)
    (hFirst : Anchored data hc hab hOne hCompat row first) :
    Anchored data hc hab hOne hCompat row second := by
  by_cases hsT : second.1.1.1 = contracted
  · refine ⟨fun h ↦ absurd hsT h, ?_⟩
    intro _ z hz hCons2
    by_cases hfT : first.1.1.1 = contracted
    · exact absurd (Subtype.ext (hNoReturn hCons.2.choose
        hCons.2.choose_spec.2.2 first.1 second.1 hfT hsT first.2 second.2
        hCons.2.choose_spec.1 hCons.2.choose_spec.2.1)) hCons.1
    · refine Eq.trans ?_ (hFirst.1 hfT)
      exact stablePath_descend_eq_of_boundary_pair data hc hab hOne hCompat hsT hz hfT
        hCons2 (consecutive_symm hCons)
  · refine ⟨fun hst ↦ ?_, fun h ↦ absurd h hsT⟩
    by_cases hfT : first.1.1.1 = contracted
    · exact hFirst.2 hfT second hst hCons
    · rw [← stablePath_eq_of_consecutive
        (consecutive_descend data hc hab hOne hCompat hfT hst hCons)]
      exact hFirst.1 hfT

/-- Non-vacuity of the chain invariant: a retained occurrence is anchored at its
own wall row. -/
theorem anchored_self (e : NonDanglingEdge data) (he : e.1.1.1 ≠ contracted) :
    Anchored data hc hab hOne hCompat
      (descend data hc hab hOne hCompat e he).stablePath e :=
  ⟨fun _ ↦ rfl, fun hBad ↦ absurd hBad he⟩

include hNoReturn in
/-- **Retained occurrences of one incoming stable row descend to one wall stable
row.**  This is the injectivity half of the row dictionary. -/
theorem stablePath_descend_eq_of_stablePath_eq
    {x y : NonDanglingEdge data} (hx : x.1.1.1 ≠ contracted) (hy : y.1.1.1 ≠ contracted)
    (hEq : x.stablePath = y.stablePath) :
    (descend data hc hab hOne hCompat x hx).stablePath =
      (descend data hc hab hOne hCompat y hy).stablePath := by
  have hClosed := eqvGen_iff_of_closed
    (property := Anchored data hc hab hOne hCompat
      (descend data hc hab hOne hCompat x hx).stablePath)
    (anchored_of_consecutive data hc hab hOne hCompat hNoReturn _)
    ((stablePath_eq_iff x y).mp hEq)
  exact ((hClosed.mp (anchored_self data hc hab hOne hCompat x hx)).1 hy).symm

end Chain


section MatrixSum

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}

omit [Fintype coordinate] in
/-- **One entry of an honest stable length matrix, as a sum over occurrences.**
The entry in the column of `item` is the sum of the reciprocal ramification
indices of the surviving occurrences of that stable row lying over `item`. -/
theorem matrix_eq_sum_of_target (labelling : StableLengthMatrixLabelling data coordinate)
    (row : coordinate) (item : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
        (labelling.targetEdge.symm item) =
      ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
          (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
              labelling.row (NonDanglingEdge.stablePath
                (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) ∧ edge.1.1 = item),
        (1 : ℚ) / data.sourceEdgeIndex edge := by
  classical
  have hNodup : (labelling.path row).Nodup := by
    unfold StableLengthMatrixLabelling.path
    exact List.Nodup.filter _ (Finset.univ.nodup_toList)
  have hToFinset : (labelling.path row).toFinset =
      (Finset.univ : Finset data.SourceEdge).filter
        (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
          labelling.row (NonDanglingEdge.stablePath
            (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row) := by
    ext edge
    simp [List.mem_toFinset, labelling.mem_path_iff]
  calc
    GluingDatum.LengthMatrixPresentation.matrix labelling.presentation row
          (labelling.targetEdge.symm item)
        = ((labelling.path row).map fun edge ↦
            GluingDatum.LengthMatrixPresentation.coefficient
              labelling.presentation edge (labelling.targetEdge.symm item)).sum := rfl
    _ = ∑ edge ∈ (labelling.path row).toFinset,
          GluingDatum.LengthMatrixPresentation.coefficient
            labelling.presentation edge (labelling.targetEdge.symm item) :=
        (List.sum_toFinset _ hNodup).symm
    _ = ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
            (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
              labelling.row (NonDanglingEdge.stablePath
                (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row),
          GluingDatum.LengthMatrixPresentation.coefficient
            labelling.presentation edge (labelling.targetEdge.symm item) := by
        rw [hToFinset]
    _ = ∑ edge ∈ ((Finset.univ : Finset data.SourceEdge).filter
            (fun edge ↦ ∃ hSurvives : ¬ IsDangling data edge,
              labelling.row (NonDanglingEdge.stablePath
                (⟨edge, hSurvives⟩ : NonDanglingEdge data)) = row)).filter
            (fun edge ↦ edge.1.1 = item),
          (1 : ℚ) / data.sourceEdgeIndex edge := by
        conv_rhs => rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro edge _
        by_cases hCase : edge.1.1 = item
        · rw [if_pos hCase]
          simp [GluingDatum.LengthMatrixPresentation.coefficient,
            StableLengthMatrixLabelling.presentation, hCase]
        · rw [if_neg hCase]
          apply GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
          simp only [StableLengthMatrixLabelling.presentation, Equiv.apply_symm_apply]
          exact fun hEqual ↦ hCase hEqual.symm
    _ = _ := by rw [Finset.filter_filter]

end MatrixSum

section Labels

variable {coordinate : Type*} [DecidableEq coordinate]

/-- The transposition identifying the two punctured index sets. -/
noncomputable def punctureEquiv (first second : coordinate) :
    {column : coordinate // column ≠ first} ≃ {column : coordinate // column ≠ second} :=
  Equiv.subtypeEquiv (Equiv.swap first second) (fun column ↦ not_congr
    ⟨by rintro rfl; exact Equiv.swap_apply_left _ _,
      fun hSwap ↦ by
        have hApply := congrArg (Equiv.swap first second) hSwap
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at hApply⟩)

@[simp] theorem punctureEquiv_val (first second : coordinate)
    (column : {column : coordinate // column ≠ first}) :
    (punctureEquiv first second column).1 = Equiv.swap first second column.1 := rfl

variable {data : GluingDatum target degree} [Fintype coordinate]

/-- The wall columns: the incoming columns other than the contracted one,
matched with the target occurrences of the contracted target tree. -/
noncomputable def punctureTargetEquiv (labelling : StableLengthMatrixLabelling data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    {column : coordinate // column ≠ labelling.targetEdge.symm contracted} ≃
      (contract target hab hOne).edges :=
  (Equiv.subtypeEquiv labelling.targetEdge
      (fun _ ↦ not_congr (Equiv.eq_symm_apply labelling.targetEdge))).trans
    (foldEdgeEquiv hc hab hOne)

omit [DecidableEq coordinate] [Fintype coordinate] in
@[simp] theorem punctureTargetEquiv_apply
    (labelling : StableLengthMatrixLabelling data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (column : {column : coordinate // column ≠ labelling.targetEdge.symm contracted}) :
    punctureTargetEquiv labelling hc hab hOne column =
      foldEdge hc hab hOne ⟨labelling.targetEdge column.1,
        (not_congr (Equiv.eq_symm_apply labelling.targetEdge)).mp column.2⟩ := rfl

end Labels

section Facet

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  (hNoReturn : NoContractedReturn data contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hRows : ∀ row, row ≠ facet →
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates row ≠ 0)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

/-- The canonical incoming row of a wall row: the incoming row of any retained
occurrence.  This is `PrunedFibreStablePath.stablePathLift`, specialised to the
connectivity a full-dimensional incoming cover already provides. -/
noncomputable def incomingRow :
    StablePath (contractDatum data hc hab hOne) → StablePath data :=
  PrunedFibreStablePath.stablePathLift data hc hab hOne fd.connected hCompat hForest

@[simp] theorem incomingRow_descend (e : NonDanglingEdge data) (he : e.1.1.1 ≠ contracted) :
    incomingRow data fd hc hab hOne hCompat hForest
        (descend data hc hab hOne hCompat e he).stablePath = e.stablePath := by
  show (nonDanglingEmbedding data hCompat.1 (descend data hc hab hOne hCompat e he)).stablePath =
    e.stablePath
  rw [nonDanglingEmbedding_descend]

@[simp] theorem incomingRow_mk (g : NonDanglingEdge (contractDatum data hc hab hOne)) :
    incomingRow data fd hc hab hOne hCompat hForest g.stablePath =
      (nonDanglingEmbedding data hCompat.1 g).stablePath := rfl

include hNoReturn in
/-- **The row map is injective.** -/
theorem incomingRow_injective :
    Function.Injective (incomingRow data fd hc hab hOne hCompat hForest) := by
  intro first second hEq
  obtain ⟨f, rfl⟩ := Quot.exists_rep first
  obtain ⟨g, rfl⟩ := Quot.exists_rep second
  have hEmb : (nonDanglingEmbedding data hCompat.1 f).stablePath =
      (nonDanglingEmbedding data hCompat.1 g).stablePath := hEq
  have hDescend := stablePath_descend_eq_of_stablePath_eq data hc hab hOne hCompat hNoReturn
    (sourceEdgeEmbedding_ne_contracted data hc hab hOne f.1)
    (sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1) hEmb
  show NonDanglingEdge.stablePath f = NonDanglingEdge.stablePath g
  calc NonDanglingEdge.stablePath f
      = NonDanglingEdge.stablePath (descend data hc hab hOne hCompat
          (nonDanglingEmbedding data hCompat.1 f)
          (sourceEdgeEmbedding_ne_contracted data hc hab hOne f.1)) :=
        congrArg NonDanglingEdge.stablePath
          (descend_nonDanglingEmbedding data hc hab hOne hCompat f _).symm
    _ = NonDanglingEdge.stablePath (descend data hc hab hOne hCompat
          (nonDanglingEmbedding data hCompat.1 g)
          (sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1)) := hDescend
    _ = NonDanglingEdge.stablePath g :=
        congrArg NonDanglingEdge.stablePath
          (descend_nonDanglingEmbedding data hc hab hOne hCompat g _)

include hNoReturn in
/-- **The occurrence-level dictionary.**  A retained occurrence lies on the wall
row `row` exactly when it lies on the incoming row of `row`. -/
theorem stablePath_descend_eq_iff (e : NonDanglingEdge data) (he : e.1.1.1 ≠ contracted)
    (row : StablePath (contractDatum data hc hab hOne)) :
    (descend data hc hab hOne hCompat e he).stablePath = row ↔
      e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row := by
  constructor
  · rintro rfl
    exact (incomingRow_descend data fd hc hab hOne hCompat hForest e he).symm
  · intro hRow
    refine incomingRow_injective data fd hc hab hOne hCompat hForest hNoReturn ?_
    rw [incomingRow_descend]
    exact hRow

include fd hZeroCoord hPosCoord hFacetZero in
/-- **The vanishing row is not an incoming row of the wall.**  Every occurrence
of the vanishing row lies over the contracted target occurrence, and no such
occurrence survives the contraction. -/
theorem incomingRow_ne_facet (row : StablePath (contractDatum data hc hab hOne)) :
    incomingRow data fd hc hab hOne hCompat hForest row ≠ fd.labelling.row.symm facet := by
  obtain ⟨g, rfl⟩ := Quot.exists_rep row
  intro hBad
  refine sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1 ?_
  refine NonTrivalentUniqueFourValent.target_eq_contracted_of_row_eq_facet data fd
    coordinates facet hZeroCoord hPosCoord hFacetZero
    (nonDanglingEmbedding data hCompat.1 g) ?_
  show fd.labelling.row (incomingRow data fd hc hab hOne hCompat hForest (Quot.mk _ g)) = facet
  rw [hBad, Equiv.apply_symm_apply]

include fd hRows hZeroCoord in
/-- **Every retained row keeps an occurrence.**  A row other than the vanishing
one has positive length, so one of its occurrences lies over a target
occurrence other than the contracted one. -/
theorem exists_occurrence_ne_contracted (row : StablePath data)
    (hRow : fd.labelling.row row ≠ facet) :
    ∃ e : NonDanglingEdge data, e.stablePath = row ∧ e.1.1.1 ≠ contracted := by
  classical
  by_contra hNone
  apply hRows (fd.labelling.row row) hRow
  rw [GluingDatum.LengthMatrixPresentation.matrix_mulVec]
  unfold GluingDatum.sourcePathLength
  apply List.sum_eq_zero
  intro term hTerm
  obtain ⟨e, hMem, rfl⟩ := List.mem_map.mp hTerm
  obtain ⟨hSurvives, hRowEq⟩ := (mem_presentation_path_iff fd.labelling _ e).mp hMem
  have hPath : NonDanglingEdge.stablePath (⟨e, hSurvives⟩ : NonDanglingEdge data) = row :=
    fd.labelling.row.injective hRowEq
  have hTarget : e.1.1 = contracted :=
    not_not.mp (fun hBad ↦ hNone ⟨⟨e, hSurvives⟩, hPath, hBad⟩)
  show data.sourceEdgeLength
    (fun occurrence ↦ coordinates (fd.labelling.presentation.targetEdge.symm occurrence)) e = 0
  unfold GluingDatum.sourceEdgeLength
  rw [hTarget]
  show coordinates (fd.labelling.targetEdge.symm contracted) / _ = 0
  rw [hZeroCoord, zero_div]

include fd hRows hZeroCoord in
/-- **The row map is onto the retained rows.** -/
theorem exists_incomingRow_eq (row : StablePath data)
    (hRow : row ≠ fd.labelling.row.symm facet) :
    ∃ wallRow : StablePath (contractDatum data hc hab hOne),
      incomingRow data fd hc hab hOne hCompat hForest wallRow = row := by
  obtain ⟨e, hPath, hTarget⟩ := exists_occurrence_ne_contracted data fd coordinates facet
    hRows hZeroCoord row (fun hBad ↦ hRow (by rw [← hBad, Equiv.symm_apply_apply]))
  exact ⟨(descend data hc hab hOne hCompat e hTarget).stablePath,
    (incomingRow_descend data fd hc hab hOne hCompat hForest e hTarget).trans hPath⟩

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The row dictionary at a one-zero-row facet**, Part II Section 5.1
labelling convention (1): aside from the contracting stable edge, the
stable edges of the incoming cover correspond bijectively to those of the wall
datum. -/
noncomputable def rowEquiv :
    StablePath (contractDatum data hc hab hOne) ≃
      {row : StablePath data // row ≠ fd.labelling.row.symm facet} :=
  Equiv.ofBijective
    (fun wallRow ↦ ⟨incomingRow data fd hc hab hOne hCompat hForest wallRow,
      incomingRow_ne_facet data fd hc hab hOne hCompat hForest coordinates facet
        hZeroCoord hPosCoord hFacetZero wallRow⟩)
    ⟨fun first second hEq ↦ incomingRow_injective data fd hc hab hOne hCompat hForest
        hNoReturn (congrArg Subtype.val hEq),
      fun row ↦ by
        obtain ⟨wallRow, hWallRow⟩ := exists_incomingRow_eq data fd hc hab hOne hCompat
          hForest coordinates facet hRows hZeroCoord row.1 row.2
        exact ⟨wallRow, Subtype.ext hWallRow⟩⟩

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The Part II row map.**  The vanishing row goes to `none`; every other
incoming row goes to its wall row. -/
noncomputable def wallRow (row : StablePath data) :
    Option (StablePath (contractDatum data hc hab hOne)) :=
  if hFacet : row = fd.labelling.row.symm facet then none
  else some ((rowEquiv data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
    hRows hZeroCoord hPosCoord hFacetZero).symm ⟨row, hFacet⟩)

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
@[simp] theorem wallRow_facet :
    wallRow data fd hc hab hOne hCompat hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero (fd.labelling.row.symm facet) = none :=
  dif_pos rfl

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
@[simp] theorem wallRow_incomingRow (row : StablePath (contractDatum data hc hab hOne)) :
    wallRow data fd hc hab hOne hCompat hForest hNoReturn coordinates facet hRows
        hZeroCoord hPosCoord hFacetZero
        (incomingRow data fd hc hab hOne hCompat hForest row) = some row := by
  rw [wallRow, dif_neg (incomingRow_ne_facet data fd hc hab hOne hCompat hForest
    coordinates facet hZeroCoord hPosCoord hFacetZero row)]
  exact congrArg some (((rowEquiv data fd hc hab hOne hCompat hForest hNoReturn coordinates
    facet hRows hZeroCoord hPosCoord hFacetZero).symm_apply_eq).mpr (Subtype.ext rfl))

include hNoReturn in
/-- **The occurrence-set statement, on the wall datum's own occurrences.**  A
surviving wall occurrence lies on the wall row `row` exactly when the incoming
occurrence it comes from lies on the incoming row of `row`. -/
theorem stablePath_nonDanglingEmbedding_eq_iff
    (row : StablePath (contractDatum data hc hab hOne))
    (g : NonDanglingEdge (contractDatum data hc hab hOne)) :
    g.stablePath = row ↔
      (nonDanglingEmbedding data hCompat.1 g).stablePath =
        incomingRow data fd hc hab hOne hCompat hForest row := by
  constructor
  · rintro rfl; rfl
  · intro hRow
    refine incomingRow_injective data fd hc hab hOne hCompat hForest hNoReturn ?_
    exact hRow

/-! ### The square honest labelling of the wall datum -/

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- The wall rows, transported to the same index set by the transposition
exchanging the vanishing row's label with the contracted column's label. -/
noncomputable def wallRowIndex :
    StablePath (contractDatum data hc hab hOne) ≃
      {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} :=
  ((rowEquiv data fd hc hab hOne hCompat hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero).trans
    ((Equiv.subtypeEquiv fd.labelling.row
        (fun _ ↦ not_congr (Equiv.eq_symm_apply fd.labelling.row)) :
      {row : StablePath data // row ≠ fd.labelling.row.symm facet} ≃
        {column : coordinate // column ≠ facet}))).trans
    (punctureEquiv facet (fd.labelling.targetEdge.symm contracted))

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The wall datum's own square honest stable length-matrix labelling.**  Its
index set is the incoming coordinate set with the contracted column removed, so
it has exactly `|E(T)| - 1 = |E(T_0)|` rows and columns. -/
noncomputable def wallLabelling :
    StableLengthMatrixLabelling (contractDatum data hc hab hOne)
      {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted} where
  targetEdge := punctureTargetEquiv fd.labelling hc hab hOne
  row := wallRowIndex data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
    hRows hZeroCoord hPosCoord hFacetZero

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The wall matrix is the incoming matrix off the contracted column.**  This
is the `AgreeOffColumn`-shaped identity: after the row dictionary, every entry
of the wall datum's honest length matrix in a retained column equals the
corresponding entry of the incoming cover's honest length matrix.  Part II,
Lemma `lm:change-comb-type`, reads the wall matrix as the common minor
`A_{φ₀}` of the incoming matrices. -/
theorem matrix_wallLabelling
    (wallRowValue : StablePath (contractDatum data hc hab hOne))
    (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}) :
    GluingDatum.LengthMatrixPresentation.matrix
        (wallLabelling data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
          hRows hZeroCoord hPosCoord hFacetZero).presentation
        (wallRowIndex data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
          hRows hZeroCoord hPosCoord hFacetZero wallRowValue) column =
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
        (fd.labelling.row (incomingRow data fd hc hab hOne hCompat hForest wallRowValue))
        column.1 := by
  classical
  have hColT : fd.labelling.targetEdge column.1 ≠ contracted :=
    (not_congr (Equiv.eq_symm_apply fd.labelling.targetEdge)).mp column.2
  have hColSymm : (wallLabelling data fd hc hab hOne hCompat hForest hNoReturn coordinates
      facet hRows hZeroCoord hPosCoord hFacetZero).targetEdge.symm
        (foldEdge hc hab hOne ⟨fd.labelling.targetEdge column.1, hColT⟩) = column := by
    rw [Equiv.symm_apply_eq]
    rfl
  calc GluingDatum.LengthMatrixPresentation.matrix
        (wallLabelling data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
          hRows hZeroCoord hPosCoord hFacetZero).presentation
        (wallRowIndex data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
          hRows hZeroCoord hPosCoord hFacetZero wallRowValue) column
      = GluingDatum.LengthMatrixPresentation.matrix
          (wallLabelling data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
            hRows hZeroCoord hPosCoord hFacetZero).presentation
          (wallRowIndex data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
            hRows hZeroCoord hPosCoord hFacetZero wallRowValue)
          ((wallLabelling data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
            hRows hZeroCoord hPosCoord hFacetZero).targetEdge.symm
              (foldEdge hc hab hOne ⟨fd.labelling.targetEdge column.1, hColT⟩)) := by
        rw [hColSymm]
    _ = ∑ edge ∈ (Finset.univ :
          Finset (contractDatum data hc hab hOne).SourceEdge).filter
            (fun edge ↦ (∃ hSurvives : ¬ IsDangling (contractDatum data hc hab hOne) edge,
                (wallLabelling data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
                  hRows hZeroCoord hPosCoord hFacetZero).row
                  (NonDanglingEdge.stablePath
                    (⟨edge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne))) =
                  wallRowIndex data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
                    hRows hZeroCoord hPosCoord hFacetZero wallRowValue) ∧
              edge.1.1 = foldEdge hc hab hOne ⟨fd.labelling.targetEdge column.1, hColT⟩),
          (1 : ℚ) / (contractDatum data hc hab hOne).sourceEdgeIndex edge :=
        matrix_eq_sum_of_target _ _ _
    _ = ∑ edge ∈ (Finset.univ : Finset data.SourceEdge).filter
            (fun edge ↦ (∃ hSurvives : ¬ IsDangling data edge,
                fd.labelling.row (NonDanglingEdge.stablePath
                  (⟨edge, hSurvives⟩ : NonDanglingEdge data)) =
                  fd.labelling.row
                    (incomingRow data fd hc hab hOne hCompat hForest wallRowValue)) ∧
              edge.1.1 = fd.labelling.targetEdge column.1),
          (1 : ℚ) / data.sourceEdgeIndex edge := by
        refine Finset.sum_nbij (sourceEdgeEmbedding data hc hab hOne) ?_ ?_ ?_ ?_
        · intro wallEdge hWallEdge
          obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (Finset.mem_filter.mp hWallEdge).2
          have hDown : NonDanglingEdge.stablePath
              (⟨wallEdge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne)) =
              wallRowValue := (wallRowIndex data fd hc hab hOne hCompat hForest hNoReturn
                coordinates facet hRows hZeroCoord hPosCoord hFacetZero).injective hRow
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            ⟨(nonDanglingEmbedding data hCompat.1
              (⟨wallEdge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne))).2,
              congrArg fd.labelling.row
                ((stablePath_nonDanglingEmbedding_eq_iff data fd hc hab hOne hCompat hForest
                  hNoReturn wallRowValue ⟨wallEdge, hSurvives⟩).mp hDown)⟩, ?_⟩
          have hVal := congrArg Prod.fst
            (IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne wallEdge)
          rw [hVal, hTarget, unfoldEdge_foldEdge]
        · exact fun first _ second _ hEq ↦
            (sourceEdgeEmbedding data hc hab hOne).injective hEq
        · intro edge hEdge
          obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ :=
            (Finset.mem_filter.mp (by exact hEdge : edge ∈ _)).2
          have hNe : edge.1.1 ≠ contracted := by rw [hTarget]; exact hColT
          obtain ⟨wallEdge, hWallEdge⟩ := exists_sourceEdgeEmbedding_eq data hc hab hOne hNe
          have hVal : edge.1.1 = unfoldEdge hc hab hOne wallEdge.1.1 := by
            rw [← hWallEdge]
            exact congrArg Prod.fst
              (IncomingNormalizationRows.sourceEdgeEmbedding_val data hc hab hOne wallEdge)
          have hUnfold : unfoldEdge hc hab hOne wallEdge.1.1 ≠ contracted := by
            rw [← hVal]; exact hNe
          have hFold : foldEdge hc hab hOne ⟨fd.labelling.targetEdge column.1, hColT⟩ =
              wallEdge.1.1 := by
            rw [show (⟨fd.labelling.targetEdge column.1, hColT⟩ :
                {f : target.edges // f ≠ contracted}) =
              ⟨unfoldEdge hc hab hOne wallEdge.1.1, hUnfold⟩ from
                Subtype.ext (hTarget.symm.trans hVal)]
            exact foldEdge_unfoldEdge hc hab hOne wallEdge.1.1 hUnfold
          have hWallSurvives : ¬ IsDangling (contractDatum data hc hab hOne) wallEdge := by
            intro hBad
            exact hSurvives (hWallEdge ▸ hCompat.2.embedding wallEdge hBad)
          refine ⟨wallEdge, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            ⟨hWallSurvives, ?_⟩, hFold.symm⟩, hWallEdge⟩
          refine congrArg _ ((stablePath_nonDanglingEmbedding_eq_iff data fd hc hab hOne hCompat
            hForest hNoReturn wallRowValue ⟨wallEdge, hWallSurvives⟩).mpr ?_)
          refine Eq.trans ?_ (fd.labelling.row.injective hRow)
          exact congrArg NonDanglingEdge.stablePath (Subtype.ext hWallEdge)
        · intro wallEdge _
          rw [sourceEdgeIndex_sourceEdgeEmbedding]
    _ = GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
          (fd.labelling.row (incomingRow data fd hc hab hOne hCompat hForest wallRowValue))
          (fd.labelling.targetEdge.symm (fd.labelling.targetEdge column.1)) :=
        (matrix_eq_sum_of_target _ _ _).symm
    _ = _ := by rw [Equiv.symm_apply_apply]

include hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **The occurrence list of a wall row is the retained part of the occurrence
list of its incoming row.**  Combined with
`exists_sourceEdgeEmbedding_eq_iff` this says the two lists differ exactly by
the occurrences over the contracted target occurrence, which is why the two
matrix rows agree off the contracted column. -/
theorem mem_path_wallLabelling_iff
    (wallRowValue : StablePath (contractDatum data hc hab hOne))
    (edge : (contractDatum data hc hab hOne).SourceEdge) :
    edge ∈ (wallLabelling data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
        hRows hZeroCoord hPosCoord hFacetZero).path
        (wallRowIndex data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
          hRows hZeroCoord hPosCoord hFacetZero wallRowValue) ↔
      sourceEdgeEmbedding data hc hab hOne edge ∈
        fd.labelling.path (fd.labelling.row
          (incomingRow data fd hc hab hOne hCompat hForest wallRowValue)) := by
  rw [StableLengthMatrixLabelling.mem_path_iff, StableLengthMatrixLabelling.mem_path_iff]
  constructor
  · rintro ⟨hSurvives, hRow⟩
    have hDown : NonDanglingEdge.stablePath
        (⟨edge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne)) =
        wallRowValue := (wallRowIndex data fd hc hab hOne hCompat hForest hNoReturn
          coordinates facet hRows hZeroCoord hPosCoord hFacetZero).injective hRow
    exact ⟨(nonDanglingEmbedding data hCompat.1
        (⟨edge, hSurvives⟩ : NonDanglingEdge (contractDatum data hc hab hOne))).2,
      congrArg fd.labelling.row ((stablePath_nonDanglingEmbedding_eq_iff data fd hc hab hOne
        hCompat hForest hNoReturn wallRowValue ⟨edge, hSurvives⟩).mp hDown)⟩
  · rintro ⟨hSurvives, hRow⟩
    have hWallSurvives : ¬ IsDangling (contractDatum data hc hab hOne) edge :=
      fun hBad ↦ hSurvives (hCompat.2.embedding edge hBad)
    refine ⟨hWallSurvives, congrArg _ ?_⟩
    exact (stablePath_nonDanglingEmbedding_eq_iff data fd hc hab hOne hCompat hForest
      hNoReturn wallRowValue ⟨edge, hWallSurvives⟩).mpr (fd.labelling.row.injective hRow)

include hCompat hForest hNoReturn hRows hZeroCoord hPosCoord hFacetZero in
/-- **`|E(H₀)| = |E(H)| − 1`.**  The wall datum has exactly one stable row fewer
than the incoming cover: the contracting stable edge disappears.  This is why
`W4Bridge.auxR0SourceInput_of_contraction`'s
`Nonempty (StablePath M₀ ≃ StablePath M)` cannot hold at a Part II wall. -/
theorem card_stablePath_wall_add_one :
    Fintype.card (StablePath (contractDatum data hc hab hOne)) + 1 =
      Fintype.card (StablePath data) := by
  classical
  have hCongr := Fintype.card_congr (rowEquiv data fd hc hab hOne hCompat hForest hNoReturn
    coordinates facet hRows hZeroCoord hPosCoord hFacetZero)
  have hCompl := Fintype.card_subtype_compl
    (p := fun row : StablePath data ↦ row = fd.labelling.row.symm facet)
  have hPoint : Fintype.card {row : StablePath data // row = fd.labelling.row.symm facet} = 1 :=
    Fintype.card_subtype_eq _
  have hPos : 0 < Fintype.card (StablePath data) :=
    Fintype.card_pos_iff.mpr ⟨fd.labelling.row.symm facet⟩
  have hSub : Fintype.card {row : StablePath data // row ≠ fd.labelling.row.symm facet} =
      Fintype.card (StablePath data) - 1 := by rw [hCompl, hPoint]
  omega

end Facet

section Producer

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The Part II row dictionary and the common minor, from the facet data
alone.**  The hypotheses are exactly those
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row` carries --
an incoming full-dimensional cover, the nonnegative wall metric with only the
contracted target occurrence at zero, the single vanishing stable row and its
simple end -- together with the non-leaf condition on the two endpoints of the
contracted target occurrence, which is what `NoContractedReturn` needs.  No
contraction forest, dangling-compatibility or source receipt is supplied: the
forest comes from the simple end and the compatibility from the forest.

The conclusion is the wall datum's own square honest labelling, the row
dictionary of Part II convention (1), and the entrywise agreement of the two
honest matrices off the contracted column. -/
theorem exists_wallLabelling_of_noContractedReturn
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hNoReturn : NoContractedReturn data contracted)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm facet))
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    ∃ labelling : StableLengthMatrixLabelling (contractDatum data hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted},
      ∃ rowDictionary : StablePath (contractDatum data hc hab hOne) ≃
        {row : StablePath data // row ≠ fd.labelling.row.symm facet},
        ∀ (wallRowValue : StablePath (contractDatum data hc hab hOne))
          (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix labelling.presentation
              (labelling.row wallRowValue) column =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (rowDictionary wallRowValue).1) column.1 := by
  have hForest := SingleRowForest.contractionForest_of_single_row fd.labelling coordinates
    (NonTrivalentUniqueFourValent.coordinates_nonneg data fd coordinates hZeroCoord hPosCoord)
    facet hRows hEnd hc hZeroCoord
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest data hc hab hOne
    hForest
  exact ⟨wallLabelling data fd hc hab hOne hCompat hForest hNoReturn coordinates facet
      hRows hZeroCoord hPosCoord hFacetZero,
    rowEquiv data fd hc hab hOne hCompat hForest hNoReturn coordinates facet hRows
      hZeroCoord hPosCoord hFacetZero,
    fun wallRowValue column ↦ matrix_wallLabelling data fd hc hab hOne hCompat hForest
      hNoReturn coordinates facet hRows hZeroCoord hPosCoord hFacetZero wallRowValue column⟩

/-- **The row dictionary at a Part II open facet with non-leaf endpoints.**
Hypotheses exactly those of
`NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row`, plus the
non-leaf condition on the two endpoints of the contracted target occurrence. -/
theorem exists_wallLabelling_of_single_zero_row
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hLeft : 2 ≤ (GluingDatum.incidentEdges a).card)
    (hRight : 2 ≤ (GluingDatum.incidentEdges b).card)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm facet))
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    ∃ labelling : StableLengthMatrixLabelling (contractDatum data hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted},
      ∃ rowDictionary : StablePath (contractDatum data hc hab hOne) ≃
        {row : StablePath data // row ≠ fd.labelling.row.symm facet},
        ∀ (wallRowValue : StablePath (contractDatum data hc hab hOne))
          (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix labelling.presentation
              (labelling.row wallRowValue) column =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (rowDictionary wallRowValue).1) column.1 :=
  exists_wallLabelling_of_noContractedReturn data fd hc hab hOne
    (noContractedReturn_of_nonleaf data fd hc hLeft hRight) coordinates facet hRows hEnd
    hZeroCoord hPosCoord hFacetZero

/-- **The row dictionary at a Part II four-valent wall, receipt-free.**  The
non-leaf condition is discharged by the star, so the hypothesis list is exactly
that of `NonTrivalentValencyFourAnchor.fourBranchAnchor_of_single_zero_row`
together with the wall metric data already carried by
`NonTrivalentUniqueFourValent`. -/
theorem exists_wallLabelling_of_single_zero_row_of_fourStar
    (data : GluingDatum target degree)
    (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)
    (coordinates : coordinate → ℚ) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm facet))
    (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
    (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
      0 < coordinates column)
    (hFacetZero :
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates facet = 0) :
    ∃ labelling : StableLengthMatrixLabelling (contractDatum data hc hab hOne)
        {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted},
      ∃ rowDictionary : StablePath (contractDatum data hc hab hOne) ≃
        {row : StablePath data // row ≠ fd.labelling.row.symm facet},
        ∀ (wallRowValue : StablePath (contractDatum data hc hab hOne))
          (column : {column : coordinate // column ≠ fd.labelling.targetEdge.symm contracted}),
          GluingDatum.LengthMatrixPresentation.matrix labelling.presentation
              (labelling.row wallRowValue) column =
            GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
              (fd.labelling.row (rowDictionary wallRowValue).1) column.1 :=
  exists_wallLabelling_of_noContractedReturn data fd hc hab hOne
    (noContractedReturn_of_fourStar data fd hc hab hOne star) coordinates facet hRows hEnd
    hZeroCoord hPosCoord hFacetZero

end Producer

end DraismaVargas.LocalCases.StablePathFacetContraction
