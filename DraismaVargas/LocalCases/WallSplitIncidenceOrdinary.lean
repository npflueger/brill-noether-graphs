import DraismaVargas.LocalCases.WallSplitIncidence

/-!
# The incidence dictionary at an unramified wall block

Source: Draisma--Vargas Part I (arXiv:1909.12924): Lemma
`lemma-ndval-of-GqA0` in Section 6 (the surviving valency of a merged vertex is
`2` plus the sum of the excesses over its pruned fibre) and the construction of
the stable graph `H(M)` in Section 3; read through Vargas, Part II
(arXiv:2609.09109), Section 5.1, the labelling convention (1) and Lemma
`lm:change-comb-type`.

Setting.  As in `WallSplitIncidence`: `data = M` is an incoming cover over a
target tree, `contracted = t_1` joins `a <> b`, and
`M_0 = contractDatum M hc hab hOne` is the wall datum.  `WallSplitIncidence`
part (a) transports the row-filtered star at a source vertex lying over a
target vertex **other than** `a` and `b`, and part (b) splits it at a merged
anchor whose pruned fibre is a pair carrying a bridge **whose row has all its
occurrences over `t_1`**.  Neither applies at an *ordinary* wall block of a
non-trivalent wall: such a block lies over the merged target vertex, and its
internal occurrence (when it has one) is not on the vanishing row.  This module
covers exactly that case.

## What is proved

Everything is valency-agnostic and stated for a general facet contraction.

* `retainedStar`, `fibreStar`: the surviving occurrences of `M` on one incoming
  row that are *not* over `t_1`, at a single incoming vertex and at the whole
  pruned fibre of a wall vertex.
* `incidenceCount_eq_card_fibreStar`: the wall datum's row-filtered star at any
  wall source vertex is the retained star of the incoming row over the fibre.
  The bijection is `StablePathFacetContraction.descend`, and the only
  hypothesis is the injectivity of `incomingRow` (the same `hInj` as in
  `WallSplitIncidence`).
* `card_retainedStar_of_none`, `card_retainedStar_add_of_bridge`,
  `incidenceCount_divalent`: the three arithmetic facts -- a fibre vertex with
  no contracted survivor has retained star equal to its star; a fibre vertex
  whose only contracted survivor is `bridge` loses exactly the bridge, and only
  on the bridge's own row; a **divalent** fibre vertex sees only the bridge's
  row, twice.
* `incidenceCount_of_point`, `incidenceCount_of_internal`: the two shapes an
  unramified fibre can take, and
* `incidenceCount_unramified`: **the headline.**  If the pruned fibre of a wall
  source vertex carries at most one internal occurrence -- which is what
  vanishing local ramification gives -- and the wall vertex has surviving
  valency at most three while `u` in its fibre is a branch vertex, then
  `incidenceCount M_0 vertex r = incidenceCount M u (incomingRow r)` for every
  wall row `r`.  In the two-vertex case the identity is *not* a disjoint split:
  the divalent constituent contributes exactly the bridge occurrence that the
  branch constituent loses.

## Hypotheses left explicit here

1. `hInj`, `hCompat`, `hForest`, `fd`, `hConnected`: the standing inputs of the
   wall contraction, exactly as in `WallSplitIncidence`.
2. `hSubsingleton` (at most one internal occurrence in the fibre).  It is a
   consequence of vanishing local ramification -- at a valency-three wall
   `NonTrivalentValencyThreeRigidity.localRamification_eq_zero_of_ne_anchor`
   followed by `...localRamification_eq_zero_in_fibre` and
   `...internalEdges_subsingleton` -- but the ramification bookkeeping is
   valency-specific, so it is carried here as a hypothesis.
3. `hLeThree` (the wall vertex is trivalent) and `hTri` (the incoming cover is
   trivalent).  Both are used only to force the second fibre vertex to be
   divalent.

No structure is introduced.  The two `Finset` definitions are applied
throughout, and `incidenceCount_unramified` is instantiated at a point fibre by
`incidenceCount_of_point`.

## Consumers

The (T2) transport of the star count at every valency: the valency-three Type
III count (`NonTrivalentValencyThreeStarCount`), the valency-three Types I/II
count (`NonTrivalentValencyThreeSimpleStarCount`), the valency-two Base II count
(`NonTrivalentValencyTwoStarCount` / `NonTrivalentValencyTwoStarCountAll`), the
valency-two Base I count (`NonTrivalentValencyTwoBaseOneStarCount`) and the
valency-four count (`NonTrivalentValencyFourStarCount`) -- all via
`incidenceCount_unramified`, whose ordinary blocks are unramified for the same
reason at every valency.
-/

namespace DraismaVargas.LocalCases.WallSplitIncidenceOrdinary

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource WallDegeneration ClassInjectivity StablePathCount
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree FullContractionFibre
open FullDimensionalSource StableGraphIncidence StablePathFacetContraction

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  Retained stars at one incoming vertex -/

section Stars

variable (data : GluingDatum target degree) (contracted : target.edges)

/-- The surviving occurrences at `vertex` on the row `row` that do not lie over
the contracted target occurrence. -/
noncomputable def retainedStar (vertex : data.SourceVertex) (row : StablePath data) :
    Finset (NonDanglingEdge data) := by
  classical
  exact (incidentEdges data vertex).filter fun e ↦ e.1.1.1 ≠ contracted ∧ e.stablePath = row

theorem mem_retainedStar {vertex : data.SourceVertex} {row : StablePath data}
    (e : NonDanglingEdge data) :
    e ∈ retainedStar data contracted vertex row ↔
      (Incident data e.1 vertex ∧ e.1.1.1 ≠ contracted) ∧ e.stablePath = row := by
  classical
  rw [retainedStar, Finset.mem_filter, mem_incidentEdges]
  tauto

theorem retainedStar_subset (vertex : data.SourceVertex) (row : StablePath data) :
    retainedStar data contracted vertex row ⊆
      (incidentEdges data vertex).filter fun e ↦ e.stablePath = row := by
  classical
  intro e he
  rw [mem_retainedStar] at he
  exact Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr he.1.1, he.2⟩

/-- **No contracted survivor**: the retained star is the whole star. -/
theorem card_retainedStar_of_none (vertex : data.SourceVertex) (row : StablePath data)
    (hNone : ∀ e : NonDanglingEdge data, Incident data e.1 vertex → e.1.1.1 ≠ contracted) :
    (retainedStar data contracted vertex row).card = incidenceCount data vertex row := by
  classical
  unfold incidenceCount
  congr 1
  ext e
  rw [mem_retainedStar, Finset.mem_filter, mem_incidentEdges]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, hNone e h1⟩, h2⟩

/-- **One contracted survivor**: the retained star loses exactly `bridge`, and
only on the bridge's own row. -/
theorem card_retainedStar_add_of_bridge (vertex : data.SourceVertex) (row : StablePath data)
    (bridge : NonDanglingEdge data) (hBridgeInc : Incident data bridge.1 vertex)
    (hBridgeT : bridge.1.1.1 = contracted)
    (hUnique : ∀ e : NonDanglingEdge data, Incident data e.1 vertex →
      e.1.1.1 = contracted → e = bridge) :
    (retainedStar data contracted vertex row).card +
        (if bridge.stablePath = row then 1 else 0) = incidenceCount data vertex row := by
  classical
  have hDiff : ((incidentEdges data vertex).filter fun e ↦ e.stablePath = row) \
      retainedStar data contracted vertex row =
      if bridge.stablePath = row then {bridge} else ∅ := by
    ext e
    rw [Finset.mem_sdiff, Finset.mem_filter, mem_incidentEdges, mem_retainedStar]
    by_cases hb : bridge.stablePath = row
    · rw [if_pos hb, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hInc, hRow⟩, hNot⟩
        have hT : e.1.1.1 = contracted := by
          by_contra hT
          exact hNot ⟨⟨hInc, hT⟩, hRow⟩
        exact hUnique e hInc hT
      · rintro rfl
        refine ⟨⟨hBridgeInc, hb⟩, ?_⟩
        rintro ⟨⟨-, hT⟩, -⟩
        exact hT hBridgeT
    · rw [if_neg hb]
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨⟨hInc, hRow⟩, hNot⟩
      have hT : e.1.1.1 = contracted := by
        by_contra hT
        exact hNot ⟨⟨hInc, hT⟩, hRow⟩
      rw [hUnique e hInc hT] at hRow
      exact hb hRow
  have hCard := Finset.card_sdiff_add_card_eq_card
    (retainedStar_subset data contracted vertex row)
  rw [hDiff] at hCard
  unfold incidenceCount
  by_cases hb : bridge.stablePath = row
  · rw [if_pos hb] at hCard ⊢
    rw [Finset.card_singleton] at hCard
    omega
  · rw [if_neg hb] at hCard ⊢
    rw [Finset.card_empty] at hCard
    omega

/-- **A divalent vertex sees only one row.**  Its two surviving occurrences are
consecutive, so both lie on the row of any one of them. -/
theorem incidenceCount_divalent (vertex : data.SourceVertex) (row : StablePath data)
    (bridge : NonDanglingEdge data) (hBridgeInc : Incident data bridge.1 vertex)
    (hTwo : nonDanglingValency data vertex = 2) :
    incidenceCount data vertex row = 2 * (if bridge.stablePath = row then 1 else 0) := by
  classical
  have hAll : ∀ e ∈ incidentEdges data vertex, e.stablePath = bridge.stablePath := by
    intro e he
    by_cases hEq : e = bridge
    · rw [hEq]
    · exact stablePath_eq_of_consecutive
        ⟨hEq, vertex, (mem_incidentEdges _ _ _).mp he, hBridgeInc, hTwo⟩
  unfold incidenceCount
  by_cases hb : bridge.stablePath = row
  · rw [if_pos hb, mul_one,
      Finset.filter_true_of_mem (fun e he ↦ (hAll e he).trans hb),
      card_incidentEdges, hTwo]
  · rw [if_neg hb, mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hRow
    exact hb ((hAll e he).symm.trans hRow)

end Stars

/-! ## 2.  The retained star of a whole pruned fibre -/

section Fibre

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  (hInj : Function.Injective (incomingRow data fd hc hab hOne hCompat hForest))

/-- The retained occurrences of one incoming row meeting the pruned fibre of a
wall source vertex. -/
noncomputable def fibreStar (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (row : StablePath data) : Finset (NonDanglingEdge data) := by
  classical
  exact Finset.univ.filter fun e ↦ (e.1.1.1 ≠ contracted ∧ e.stablePath = row) ∧
    (sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1 = vertex ∨
      sourceVertexMap data hc hab hOne (data.sourceEnds e.1).2 = vertex)

theorem mem_fibreStar (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (row : StablePath data) (e : NonDanglingEdge data) :
    e ∈ fibreStar data hc hab hOne vertex row ↔
      (e.1.1.1 ≠ contracted ∧ e.stablePath = row) ∧
      (sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1 = vertex ∨
        sourceVertexMap data hc hab hOne (data.sourceEnds e.1).2 = vertex) := by
  classical
  rw [fibreStar, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ e)

include hInj in
/-- **The wall datum's row-filtered star is the fibre's retained star.**  The
bijection is `descend`; this is `WallSplitIncidence.incidenceCount_sourceVertexMap`
with the off-wall hypothesis removed and the answer left as a fibre count. -/
theorem incidenceCount_eq_card_fibreStar
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (row : StablePath (contractDatum data hc hab hOne)) :
    incidenceCount (contractDatum data hc hab hOne) vertex row =
      (fibreStar data hc hab hOne vertex
        (incomingRow data fd hc hab hOne hCompat hForest row)).card := by
  classical
  symm
  unfold incidenceCount
  refine Finset.card_bij (fun e he ↦ descend data hc hab hOne hCompat e
    (((mem_fibreStar data hc hab hOne vertex _ e).mp he).1.1)) ?_ ?_ ?_
  · intro e he
    obtain ⟨⟨hT, hRow⟩, hEnds⟩ := (mem_fibreStar data hc hab hOne vertex _ e).mp he
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr ?_, ?_⟩
    · show Incident (contractDatum data hc hab hOne)
        (sourceEdgeMap data hc hab hOne ⟨e.1, hT⟩) vertex
      unfold Incident
      rw [sourceEnds_sourceEdgeMap]
      exact hEnds
    · exact (WallSplitIncidence.stablePath_descend_eq_iff_of_injective data fd hc hab hOne
        hCompat hForest hInj e _ row).mpr hRow
  · intro e₁ he₁ e₂ he₂ hEq
    exact descend_injective data hc hab hOne hCompat hEq
  · intro g hg
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp hg
    have hIncidentDown := (mem_incidentEdges (contractDatum data hc hab hOne) _ g).mp hMem
    have heT : (nonDanglingEmbedding data hCompat.1 g).1.1.1 ≠ contracted :=
      sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1
    have hDescend : descend data hc hab hOne hCompat
        (nonDanglingEmbedding data hCompat.1 g) heT = g :=
      descend_nonDanglingEmbedding data hc hab hOne hCompat g heT
    have hVal : sourceEdgeMap data hc hab hOne
        ⟨(nonDanglingEmbedding data hCompat.1 g).1, heT⟩ = g.1 :=
      congrArg (fun w : NonDanglingEdge (contractDatum data hc hab hOne) ↦ w.1) hDescend
    have hEnds := sourceEnds_sourceEdgeMap data hc hab hOne
      ⟨(nonDanglingEmbedding data hCompat.1 g).1, heT⟩
    rw [hVal] at hEnds
    have hRowUp : (nonDanglingEmbedding data hCompat.1 g).stablePath =
        incomingRow data fd hc hab hOne hCompat hForest row :=
      (WallSplitIncidence.stablePath_descend_eq_iff_of_injective data fd hc hab hOne hCompat
        hForest hInj _ heT row).mp (by rw [hDescend]; exact hRow)
    refine ⟨nonDanglingEmbedding data hCompat.1 g,
      (mem_fibreStar data hc hab hOne vertex _ _).mpr ⟨⟨heT, hRowUp⟩, ?_⟩, hDescend⟩
    have hI : ((contractDatum data hc hab hOne).sourceEnds g.1).1 = vertex ∨
        ((contractDatum data hc hab hOne).sourceEnds g.1).2 = vertex := hIncidentDown
    rw [hEnds] at hI
    exact hI

/-- Two distinct fibre vertices carry no common retained occurrence: it would
be a loop of the wall datum. -/
theorem retainedStar_disjoint
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (u p : data.SourceVertex)
    (hNe : u ≠ p)
    (hMapU : sourceVertexMap data hc hab hOne u = vertex)
    (hMapP : sourceVertexMap data hc hab hOne p = vertex) (row : StablePath data) :
    Disjoint (retainedStar data contracted u row) (retainedStar data contracted p row) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro e heU heP
  obtain ⟨⟨hIncU, hT⟩, -⟩ := (mem_retainedStar data contracted e).mp heU
  obtain ⟨⟨hIncP, -⟩, -⟩ := (mem_retainedStar data contracted e).mp heP
  refine sourceVertexMap_sourceEnds_ne data hc hab hOne ⟨e.1, hT⟩ ?_
  rcases hIncU with h1 | h1 <;> rcases hIncP with h2 | h2
  · exact absurd (h1.symm.trans h2) hNe
  · rw [h1, h2, hMapU, hMapP]
  · rw [h1, h2, hMapP, hMapU]
  · exact absurd (h1.symm.trans h2) hNe

/-- A point fibre: the fibre star is the retained star of its only vertex. -/
theorem fibreStar_point (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (u : data.SourceVertex)
    (hFibre : activeFibreVertices data hc hab hOne vertex = {u}) (row : StablePath data) :
    fibreStar data hc hab hOne vertex row = retainedStar data contracted u row := by
  classical
  have hMapU : sourceVertexMap data hc hab hOne u = vertex := by
    have hMem : u ∈ activeFibreVertices data hc hab hOne vertex := by
      rw [hFibre]
      exact Finset.mem_singleton_self u
    exact ((mem_activeFibreVertices data hc hab hOne vertex u).mp hMem).1
  ext e
  rw [mem_fibreStar, mem_retainedStar]
  constructor
  · rintro ⟨⟨hT, hRow⟩, hEnds⟩
    refine ⟨⟨?_, hT⟩, hRow⟩
    rcases hEnds with h | h
    · have hMem : (data.sourceEnds e.1).1 ∈ activeFibreVertices data hc hab hOne vertex :=
        (mem_activeFibreVertices data hc hab hOne vertex _).mpr
          ⟨h, nonDanglingValency_ne_zero_of_incident data e.2 (Or.inl rfl)⟩
      rw [hFibre, Finset.mem_singleton] at hMem
      exact Or.inl hMem
    · have hMem : (data.sourceEnds e.1).2 ∈ activeFibreVertices data hc hab hOne vertex :=
        (mem_activeFibreVertices data hc hab hOne vertex _).mpr
          ⟨h, nonDanglingValency_ne_zero_of_incident data e.2 (Or.inr rfl)⟩
      rw [hFibre, Finset.mem_singleton] at hMem
      exact Or.inr hMem
  · rintro ⟨⟨hInc, hT⟩, hRow⟩
    refine ⟨⟨hT, hRow⟩, ?_⟩
    rcases hInc with h | h
    · exact Or.inl (by rw [h]; exact hMapU)
    · exact Or.inr (by rw [h]; exact hMapU)

/-- A two-point fibre: the fibre star splits. -/
theorem fibreStar_pair (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (u p : data.SourceVertex)
    (hFibre : activeFibreVertices data hc hab hOne vertex = {u, p}) (row : StablePath data) :
    fibreStar data hc hab hOne vertex row =
      retainedStar data contracted u row ∪ retainedStar data contracted p row := by
  classical
  have hMapU : sourceVertexMap data hc hab hOne u = vertex := by
    have hMem : u ∈ activeFibreVertices data hc hab hOne vertex := by
      rw [hFibre]
      exact Finset.mem_insert_self _ _
    exact ((mem_activeFibreVertices data hc hab hOne vertex u).mp hMem).1
  have hMapP : sourceVertexMap data hc hab hOne p = vertex := by
    have hMem : p ∈ activeFibreVertices data hc hab hOne vertex := by
      rw [hFibre]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
    exact ((mem_activeFibreVertices data hc hab hOne vertex p).mp hMem).1
  ext e
  rw [Finset.mem_union, mem_fibreStar, mem_retainedStar, mem_retainedStar]
  constructor
  · rintro ⟨⟨hT, hRow⟩, hEnds⟩
    have hKey : ∀ w : data.SourceVertex, Incident data e.1 w →
        sourceVertexMap data hc hab hOne w = vertex → w = u ∨ w = p := by
      intro w hInc hMap
      have hMem : w ∈ activeFibreVertices data hc hab hOne vertex :=
        (mem_activeFibreVertices data hc hab hOne vertex w).mpr
          ⟨hMap, nonDanglingValency_ne_zero_of_incident data e.2 hInc⟩
      rw [hFibre] at hMem
      simpa using hMem
    rcases hEnds with h | h
    · rcases hKey _ (Or.inl rfl) h with hw | hw
      · exact Or.inl ⟨⟨Or.inl hw, hT⟩, hRow⟩
      · exact Or.inr ⟨⟨Or.inl hw, hT⟩, hRow⟩
    · rcases hKey _ (Or.inr rfl) h with hw | hw
      · exact Or.inl ⟨⟨Or.inr hw, hT⟩, hRow⟩
      · exact Or.inr ⟨⟨Or.inr hw, hT⟩, hRow⟩
  · rintro (⟨⟨hInc, hT⟩, hRow⟩ | ⟨⟨hInc, hT⟩, hRow⟩)
    · refine ⟨⟨hT, hRow⟩, ?_⟩
      rcases hInc with h | h
      · exact Or.inl (by rw [h]; exact hMapU)
      · exact Or.inr (by rw [h]; exact hMapU)
    · refine ⟨⟨hT, hRow⟩, ?_⟩
      rcases hInc with h | h
      · exact Or.inl (by rw [h]; exact hMapP)
      · exact Or.inr (by rw [h]; exact hMapP)

/-! ## 3.  The two shapes of an unramified fibre -/

theorem card_fibreStar_point (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (u : data.SourceVertex)
    (hFibre : activeFibreVertices data hc hab hOne vertex = {u})
    (hNone : ∀ e : NonDanglingEdge data, Incident data e.1 u → e.1.1.1 ≠ contracted)
    (q : StablePath data) :
    (fibreStar data hc hab hOne vertex q).card = incidenceCount data u q := by
  rw [fibreStar_point data hc hab hOne vertex u hFibre q,
    card_retainedStar_of_none data contracted u q hNone]

/-- **The pair case.**  The divalent constituent contributes exactly the bridge
occurrence the branch constituent loses, so the wall count is again the branch
vertex's own count. -/
theorem card_fibreStar_pair (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (u p : data.SourceVertex) (hNe : u ≠ p)
    (hFibre : activeFibreVertices data hc hab hOne vertex = {u, p})
    (bridge : NonDanglingEdge data)
    (hBridgeU : Incident data bridge.1 u) (hBridgeP : Incident data bridge.1 p)
    (hBridgeT : bridge.1.1.1 = contracted)
    (hUniqueU : ∀ e : NonDanglingEdge data, Incident data e.1 u →
      e.1.1.1 = contracted → e = bridge)
    (hUniqueP : ∀ e : NonDanglingEdge data, Incident data e.1 p →
      e.1.1.1 = contracted → e = bridge)
    (hTwoP : nonDanglingValency data p = 2) (q : StablePath data) :
    (fibreStar data hc hab hOne vertex q).card = incidenceCount data u q := by
  classical
  have hMapU : sourceVertexMap data hc hab hOne u = vertex := by
    have hMem : u ∈ activeFibreVertices data hc hab hOne vertex := by
      rw [hFibre]
      exact Finset.mem_insert_self _ _
    exact ((mem_activeFibreVertices data hc hab hOne vertex u).mp hMem).1
  have hMapP : sourceVertexMap data hc hab hOne p = vertex := by
    have hMem : p ∈ activeFibreVertices data hc hab hOne vertex := by
      rw [hFibre]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
    exact ((mem_activeFibreVertices data hc hab hOne vertex p).mp hMem).1
  rw [fibreStar_pair data hc hab hOne vertex u p hFibre q,
    Finset.card_union_of_disjoint
      (retainedStar_disjoint data hc hab hOne vertex u p hNe hMapU hMapP q)]
  have h1 := card_retainedStar_add_of_bridge data contracted u q bridge hBridgeU hBridgeT hUniqueU
  have h2 := card_retainedStar_add_of_bridge data contracted p q bridge hBridgeP hBridgeT hUniqueP
  have h3 := incidenceCount_divalent data p q bridge hBridgeP hTwoP
  by_cases hb : bridge.stablePath = q
  · rw [if_pos hb] at h1 h2
    rw [if_pos hb, mul_one] at h3
    omega
  · rw [if_neg hb] at h1 h2
    rw [if_neg hb, mul_zero] at h3
    omega

include hInj in
/-- The point case, read on the wall datum. -/
theorem incidenceCount_of_point (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (u : data.SourceVertex)
    (hFibre : activeFibreVertices data hc hab hOne vertex = {u})
    (hNone : ∀ e : NonDanglingEdge data, Incident data e.1 u → e.1.1.1 ≠ contracted)
    (row : StablePath (contractDatum data hc hab hOne)) :
    incidenceCount (contractDatum data hc hab hOne) vertex row =
      incidenceCount data u (incomingRow data fd hc hab hOne hCompat hForest row) := by
  rw [incidenceCount_eq_card_fibreStar data fd hc hab hOne hCompat hForest hInj vertex row,
    card_fibreStar_point data hc hab hOne vertex u hFibre hNone]

include hInj in
/-- The pair case, read on the wall datum. -/
theorem incidenceCount_of_internal (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (u p : data.SourceVertex) (hNe : u ≠ p)
    (hFibre : activeFibreVertices data hc hab hOne vertex = {u, p})
    (bridge : NonDanglingEdge data)
    (hBridgeU : Incident data bridge.1 u) (hBridgeP : Incident data bridge.1 p)
    (hBridgeT : bridge.1.1.1 = contracted)
    (hUniqueU : ∀ e : NonDanglingEdge data, Incident data e.1 u →
      e.1.1.1 = contracted → e = bridge)
    (hUniqueP : ∀ e : NonDanglingEdge data, Incident data e.1 p →
      e.1.1.1 = contracted → e = bridge)
    (hTwoP : nonDanglingValency data p = 2)
    (row : StablePath (contractDatum data hc hab hOne)) :
    incidenceCount (contractDatum data hc hab hOne) vertex row =
      incidenceCount data u (incomingRow data fd hc hab hOne hCompat hForest row) := by
  rw [incidenceCount_eq_card_fibreStar data fd hc hab hOne hCompat hForest hInj vertex row,
    card_fibreStar_pair data hc hab hOne vertex u p hNe hFibre bridge hBridgeU hBridgeP
      hBridgeT hUniqueU hUniqueP hTwoP]

include fd hInj in
/-- **The headline.**  At a wall source vertex whose pruned fibre carries at
most one internal occurrence -- the shape vanishing local ramification forces --
the row-filtered star of the wall datum is the row-filtered star of the unique
branch vertex in its fibre, read on the incoming row. -/
theorem incidenceCount_unramified (hConnected : data.Connected)
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (u : data.SourceVertex)
    (hMapU : sourceVertexMap data hc hab hOne u = vertex)
    (hThreeU : 3 ≤ nonDanglingValency data u)
    (hLeThree : nonDanglingValency (contractDatum data hc hab hOne) vertex ≤ 3)
    (hTri : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hSubsingleton : ∀ e ∈ internalEdges data hc hab hOne vertex,
      ∀ f ∈ internalEdges data hc hab hOne vertex, e = f)
    (row : StablePath (contractDatum data hc hab hOne)) :
    incidenceCount (contractDatum data hc hab hOne) vertex row =
      incidenceCount data u (incomingRow data fd hc hab hOne hCompat hForest row) := by
  classical
  have hUmem : u ∈ activeFibreVertices data hc hab hOne vertex :=
    (mem_activeFibreVertices data hc hab hOne vertex u).mpr ⟨hMapU, by omega⟩
  have hTree := WallSplitIncidence.internalEdges_card_add_one_eq_activeFibreVertices_card_general
    data hc hab hOne hForest vertex ⟨u, hUmem⟩
  by_cases hEmpty : internalEdges data hc hab hOne vertex = ∅
  · have hCard1 : (activeFibreVertices data hc hab hOne vertex).card = 1 := by
      rw [hEmpty, Finset.card_empty] at hTree
      omega
    have hFibre : activeFibreVertices data hc hab hOne vertex = {u} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hUmem,
        fun x hx ↦ Finset.card_le_one.mp (le_of_eq hCard1) x hx u hUmem⟩
    refine incidenceCount_of_point data fd hc hab hOne hCompat hForest hInj vertex u hFibre ?_ row
    intro e hInc hT
    have hMem : e.1 ∈ internalEdges data hc hab hOne vertex := by
      refine (mem_internalEdges data hc hab hOne vertex e.1).mpr ⟨e.2, hT, ?_⟩
      rcases hInc with h | h
      · rw [h]
        exact hMapU
      · rw [sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e.1 hT, h]
        exact hMapU
    rw [hEmpty] at hMem
    exact Finset.notMem_empty _ hMem
  · obtain ⟨bridgeVal, hBridgeMem⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hSingleton : internalEdges data hc hab hOne vertex = {bridgeVal} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hBridgeMem,
        fun x hx ↦ hSubsingleton x hx bridgeVal hBridgeMem⟩
    obtain ⟨hSurv, hT, hMapBridge⟩ :=
      (mem_internalEdges data hc hab hOne vertex bridgeVal).mp hBridgeMem
    have hEndsMem :=
      (sourceEnds_mem_activeFibre_iff data hc hab hOne vertex bridgeVal).mpr hBridgeMem
    have hCard2 : (activeFibreVertices data hc hab hOne vertex).card = 2 := by
      rw [hSingleton, Finset.card_singleton] at hTree
      omega
    have hEndsNe := data.sourceEnds_ne bridgeVal
    have hFibrePair : activeFibreVertices data hc hab hOne vertex =
        {(data.sourceEnds bridgeVal).1, (data.sourceEnds bridgeVal).2} := by
      symm
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hEndsMem.1
        · exact hEndsMem.2
      · rw [hCard2, Finset.card_pair hEndsNe]
    have hUin : u = (data.sourceEnds bridgeVal).1 ∨ u = (data.sourceEnds bridgeVal).2 := by
      rw [hFibrePair] at hUmem
      simpa using hUmem
    have hUnique : ∀ (w : data.SourceVertex) (e : NonDanglingEdge data),
        sourceVertexMap data hc hab hOne w = vertex →
        Incident data e.1 w → e.1.1.1 = contracted →
        e = (⟨bridgeVal, hSurv⟩ : NonDanglingEdge data) := by
      intro w e hMapW hInc hTe
      have hMem : e.1 ∈ internalEdges data hc hab hOne vertex := by
        refine (mem_internalEdges data hc hab hOne vertex e.1).mpr ⟨e.2, hTe, ?_⟩
        rcases hInc with h | h
        · rw [h]
          exact hMapW
        · rw [sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e.1 hTe, h]
          exact hMapW
      rw [hSingleton, Finset.mem_singleton] at hMem
      exact Subtype.ext hMem
    have hkey : ∀ p : data.SourceVertex, u ≠ p →
        Incident data bridgeVal u → Incident data bridgeVal p →
        activeFibreVertices data hc hab hOne vertex = {u, p} →
        incidenceCount (contractDatum data hc hab hOne) vertex row =
          incidenceCount data u (incomingRow data fd hc hab hOne hCompat hForest row) := by
      intro p hNe hIncU hIncP hFib
      have hMapP : sourceVertexMap data hc hab hOne p = vertex := by
        have hMem : p ∈ activeFibreVertices data hc hab hOne vertex := by
          rw [hFib]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p)
        exact ((mem_activeFibreVertices data hc hab hOne vertex p).mp hMem).1
      have hTwoP : nonDanglingValency data p = 2 := by
        have hSum := WallSplitIncidence.nonDanglingValency_eq_sum_activeFibre data hc hab hOne
          hCompat hForest vertex ⟨u, hUmem⟩
        rw [hFib, Finset.sum_pair hNe] at hSum
        have hPge : 2 ≤ nonDanglingValency data p :=
          WallSplitIncidence.two_le_nonDanglingValency_of_mem_activeFibre data hc hab hOne
            hConnected vertex p (by
              rw [hFib]
              exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p))
        have hPle := hTri p
        omega
      exact incidenceCount_of_internal data fd hc hab hOne hCompat hForest hInj vertex u p hNe
        hFib ⟨bridgeVal, hSurv⟩ hIncU hIncP hT (fun e ↦ hUnique u e hMapU)
        (fun e ↦ hUnique p e hMapP) hTwoP row
    rcases hUin with hU | hU
    · exact hkey (data.sourceEnds bridgeVal).2 (by rw [hU]; exact hEndsNe)
        (by rw [hU]; exact Or.inl rfl) (Or.inr rfl) (by rw [hFibrePair, hU])
    · exact hkey (data.sourceEnds bridgeVal).1 (by rw [hU]; exact Ne.symm hEndsNe)
        (by rw [hU]; exact Or.inr rfl) (Or.inl rfl)
        (by rw [hFibrePair, hU]; exact Finset.pair_comm _ _)

end Fibre

end DraismaVargas.LocalCases.WallSplitIncidenceOrdinary
