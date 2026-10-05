module

public import DraismaVargas.LocalCases.LeafFacetNoReturn
public import DraismaVargas.LocalCases.StableGraphIncidence

@[expose] public section

/-!
# The incidence dictionary across a facet wall contraction

Source: Vargas, Part II, arXiv:2609.09109, Section 5.1
(`subsec-setup-determinants`), labelling convention (1) (the contracting edge
`h_1` of the source and its two trivalent endpoints), and
`lm:change-comb-type` (the wall matrix is the common minor of the incoming
matrices), read on the *stable graph* rather than on the length matrix; and
Draisma–Vargas Part I, arXiv:1909.12924, the construction of the stable graph
`H(M)` from the branch vertices and the maximal stable paths (in the subsection
on the gluing datum), together with the definition of labellings compatible at
a contracted edge and `lemma-limit-matrix-change`.

Setting.  `data = M` is an incoming full-dimensional cover over a target tree
`T`, `contracted = t_1` is a target occurrence joining `a ≠ b`, and
`M_0 = contractDatum M hc hab hOne` is the wall datum over `T_0`.
`StablePathFacetContraction` transports the stable rows: `incomingRow` sends a
wall row to the incoming row of any of its retained occurrences, `descend` sends
a retained incoming occurrence to its wall occurrence, and
`nonDanglingEmbedding` is the inverse on occurrences.  Everything below is
stated for a *general* facet contraction, at any wall valency.

## The one hypothesis carried, and where it comes from

Every statement that mentions `incomingRow` carries

  `hInj : Function.Injective (incomingRow data fd hc hab hOne hCompat hForest)`

instead of a no-return predicate.  This is exactly the strength the chain
argument of `StablePathFacetContraction` produces, and both of its forms supply
it, so the file is neutral between them:

* `injective_incomingRow_of_noContractedReturn`, from
  `StablePathFacetContraction.NoContractedReturn` (`incomingRow_injective`);
* `injective_incomingRow_of_noContractedReturnOffRow`, from the weakening
  `LeafFacetNoReturn.NoContractedReturnOffRow` at a one-zero-row facet
  (`incomingRow_injective'`), which is the form that holds in the leaf
  sub-case, where `NoContractedReturn` fails.

## What is proved

For `StablePathCount.incidenceCount`, the single quantity the stable-graph dart
model is made of (`StableSourceDarts.card_incidence`):

* **(a)** `incidenceCount_sourceVertexMap`: away from the wall the star is
  unchanged,
  `incidenceCount M_0 (sourceVertexMap v) r = incidenceCount M v (incomingRow r)`
  for every source vertex `v` over a target vertex other than `a` and `b`.  The
  bijection is `descend`, with `WallDegeneration.incident_sourceEdgeMap_iff_of_ne`
  for the surjectivity and `descend_injective` for the injectivity.
* **(b)** `incidenceCount_anchor`: at a merged anchor `A` whose pruned fibre is
  a pair `{leftEnd, rightEnd}` carrying a single internal occurrence `bridge`,
  `incidenceCount M_0 A r = incidenceCount M leftEnd (incomingRow r)
  + incidenceCount M rightEnd (incomingRow r)` for every wall row `r`.  The two
  incoming stars are disjoint because a retained occurrence meeting both ends
  would become a loop of `M_0` (`PrunedFibreValency.sourceVertexMap_sourceEnds_ne`),
  and no occurrence over `t_1` intervenes because `hFacetOver` puts every
  surviving occurrence of the bridge's row over `t_1`, while
  `incomingRow_ne_of_over_contracted` keeps that row out of the image of
  `incomingRow`.
* **(b)** `incidenceCount_bridgeRow_leftEnd`, `incidenceCount_bridgeRow_rightEnd`:
  the bridge row meets each end of the anchor fibre exactly once, so the
  contracting stable edge really does run once between the two ends.
  `eq_bridge_of_over_contracted` is where the single-internal-occurrence
  hypothesis enters, and it is the anchor form of the no-return condition.
* **(c)** the branch-vertex dictionary.
  `internalEdges_card_add_one_eq_activeFibreVertices_card_general` extends the
  tree count of `PrunedFibreTree` from a merged vertex to every wall source
  vertex, and `nonDanglingValency_eq_sum_activeFibre` is Draisma–Vargas Part I,
  `lemma-ndval-of-GqA0`, there: `nd_{M_0}(W) = 2 + \sum_{V in fibre} (nd_M(V) - 2)`.
  Since connectedness excludes surviving valency one, every active fibre vertex
  has `nd_M ≥ 2`, and the three consequences are
  `three_le_nonDanglingValency_sourceVertexMap` (a branch vertex descends to a
  branch vertex), `exists_three_le_mem_activeFibre` (a branch vertex of the wall
  datum has a branch vertex in its fibre) and
  `eq_of_mem_activeFibre_of_three_le` (a *trivalent* wall vertex has only one).
  Together they give
  `branchVertexEquivAnchorComplement : {v : BranchVertex M // v ≠ leftEnd ∧ v ≠ rightEnd}
  ≃ {w : BranchVertex M_0 // w ≠ A}`, which is `sourceVertexMap` on the nose
  (`branchVertexEquivAnchorComplement_apply`).

## The hypotheses that stay explicit

1. `hInj`, as described above; and `hCompat : DanglingCompatible`,
   `hForest : ContractionForest`, `fd`, `hConnected : data.Connected`, which are
   the standing inputs of the wall contraction.
2. The anchor data `hFibre : activeFibreVertices A = {leftEnd, rightEnd}` and
   `hInternal : internalEdges A = {bridge.1}` are *hypotheses*, not conclusions:
   this file does not classify the anchor block.  At a Part II wall they are
   *not* uniformly available from the valency-specific anchor modules
   (`NonTrivalentAnchorValency`, `NonTrivalentValencyTwoAnchor`,
   `NonTrivalentValencyThreeAnchor`, `NonTrivalentValencyFourAnchor`): at
   valency three the census statements that would give `hFibre`/`hInternal`
   need `hChangeZero`, which fails at the valency-two endpoint (the anchor
   there is the *ramified* block, not the two-valent one), so `hFibre` is not
   available.  The exits therefore do not route through `hFibre`/`hInternal`
   at all: they use the branch-pair form
   `NonTrivalentValencyThreeTracks.branchEquivAnchorComplement` -- this
   module's dictionary with `hFibre` replaced by the two branch ends of the
   vanishing occurrence -- and its analogues at every valency.
3. `hFacetOver` (every surviving occurrence of the bridge's row lies over `t_1`)
   is discharged at a one-zero-row facet by `facetRow_over_contracted_of_facet`.
4. `hTrivalentAway` (the wall datum is trivalent away from the anchor) in
   part (c).  It is genuinely needed: a wall vertex of surviving valency four has
   a fibre that may contain two incoming branch vertices, so `sourceVertexMap` is
   not injective on branch vertices without it.  At a three-valent Part II wall it
   is `NonTrivalentValencyTwoExit.wallDatum_trivalent_away` off the merged target
   vertex together with
   `NonTrivalentAnchorValency.nonDanglingValency_wallBlock_le_three_of_threeStar`
   on the other wall blocks.

Nothing here constructs a `StableGraphIncidence.Equivalence`, a
`FullDimensionalSourcePresentation`, a dart isomorphism, or a labelling; and no
structure is introduced, so there is nothing to witness for non-vacuity beyond
the definitions of `StablePathFacetContraction`, each of which is applied.

## Consumers

The `iso` half of `InteriorGraphTracking.Tracks` at a type change, through
`MovedIncidenceIso.isoOfMovedIncidenceEquivalence`: part (a) and part (c) give
the vertex half of the star equality away from the wall, part (b) splits the
anchor star for the resolved candidate's two anchor vertices.  Hence
`OuterWalk.TypeChangeLink` at `NonTrivalentValencyTwoExit`,
`NonTrivalentValencyThreeExit` and `NonTrivalentValencyFourExit`.
-/

namespace DraismaVargas.LocalCases.WallSplitIncidence

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource WallDegeneration ClassInjectivity StablePathCount
open PrunedContractionFibre PrunedFibreValency PrunedFibreTree FullContractionFibre
open FullDimensionalSource StableGraphIncidence StablePathFacetContraction

variable {target : CFGraph} {degree : ℕ}

section Dictionary

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  (hInj : Function.Injective (incomingRow data fd hc hab hOne hCompat hForest))

include hInj in
/-- **The occurrence-level dictionary, from injectivity alone.**  A retained
occurrence lies on the wall row `row` exactly when it lies on the incoming row
of `row`.  Both `StablePathFacetContraction.incomingRow_injective` (under
`NoContractedReturn`) and `LeafFacetNoReturn.incomingRow_injective'` (under the
weaker `NoContractedReturnOffRow`) supply the hypothesis. -/
theorem stablePath_descend_eq_iff_of_injective (e : NonDanglingEdge data)
    (he : e.1.1.1 ≠ contracted) (row : StablePath (contractDatum data hc hab hOne)) :
    (descend data hc hab hOne hCompat e he).stablePath = row ↔
      e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row := by
  constructor
  · rintro rfl
    exact (incomingRow_descend data fd hc hab hOne hCompat hForest e he).symm
  · intro hRow
    refine hInj ?_
    rw [incomingRow_descend]
    exact hRow

/-- **A row all of whose occurrences lie over the contracted target occurrence
is not an incoming row.**  This is the abstract form of
`StablePathFacetContraction.incomingRow_ne_facet`. -/
theorem incomingRow_ne_of_over_contracted (facetRow : StablePath data)
    (hFacetOver : ∀ e : NonDanglingEdge data, e.stablePath = facetRow →
      e.1.1.1 = contracted)
    (row : StablePath (contractDatum data hc hab hOne)) :
    incomingRow data fd hc hab hOne hCompat hForest row ≠ facetRow := by
  obtain ⟨g, rfl⟩ := Quot.exists_rep row
  intro hBad
  exact sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1
    (hFacetOver (nonDanglingEmbedding data hCompat.1 g) hBad)

include hInj in
/-- **(a) Away from the wall the star of a row is unchanged.**  At a source
vertex over a target vertex other than the two ends of the contracted
occurrence, the wall datum's row-filtered star at the image vertex has exactly
as many surviving occurrences as the incoming star of the incoming row. -/
theorem incidenceCount_sourceVertexMap (v : data.SourceVertex)
    (hva : v.1.1 ≠ a) (hvb : v.1.1 ≠ b)
    (row : StablePath (contractDatum data hc hab hOne)) :
    incidenceCount (contractDatum data hc hab hOne)
        (sourceVertexMap data hc hab hOne v) row =
      incidenceCount data v (incomingRow data fd hc hab hOne hCompat hForest row) := by
  classical
  symm
  have hNe : ∀ e : NonDanglingEdge data, Incident data e.1 v → e.1.1.1 ≠ contracted := by
    intro e hIncident hEq
    exact not_incident_of_eq_contracted data hc hEq hva hvb hIncident
  refine Finset.card_bij (fun e he ↦ descend data hc hab hOne hCompat e
    (hNe e ((mem_incidentEdges data v e).mp (Finset.mem_filter.mp he).1))) ?_ ?_ ?_
  · intro e he
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact (mem_incidentEdges (contractDatum data hc hab hOne) _ _).mpr
        (incident_descend data hc hab hOne hCompat _ ((mem_incidentEdges data v e).mp hMem))
    · exact (stablePath_descend_eq_iff_of_injective data fd hc hab hOne hCompat hForest hInj
        e _ row).mpr hRow
  · intro e₁ he₁ e₂ he₂ hEq
    exact descend_injective data hc hab hOne hCompat hEq
  · intro g hg
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp hg
    have hIncidentDown := (mem_incidentEdges (contractDatum data hc hab hOne) _ g).mp hMem
    set e : NonDanglingEdge data := nonDanglingEmbedding data hCompat.1 g with hedef
    have heT : e.1.1.1 ≠ contracted := sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1
    have hDescend : descend data hc hab hOne hCompat e heT = g :=
      descend_nonDanglingEmbedding data hc hab hOne hCompat g heT
    have hIncidentUp : Incident data e.1 v := by
      refine (incident_sourceEdgeMap_iff_of_ne data hc hab hOne ⟨e.1, heT⟩ v hva hvb).mp ?_
      have hVal : sourceEdgeMap data hc hab hOne ⟨e.1, heT⟩ = g.1 :=
        congrArg (fun w : NonDanglingEdge (contractDatum data hc hab hOne) ↦ w.1) hDescend
      rw [hVal]
      exact hIncidentDown
    have hRowUp : e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row :=
      (stablePath_descend_eq_iff_of_injective data fd hc hab hOne hCompat hForest hInj
        e heT row).mp (by rw [hDescend]; exact hRow)
    refine ⟨e, Finset.mem_filter.mpr ⟨(mem_incidentEdges data v e).mpr hIncidentUp, hRowUp⟩, ?_⟩
    exact hDescend

/-! ### The anchor: the two incoming ends of the contracted occurrence -/

section Anchor

variable (anchor : (contractDatum data hc hab hOne).SourceVertex)
  (leftEnd rightEnd : data.SourceVertex) (bridge : NonDanglingEdge data)

/-- The first end of the anchor fibre is carried to the anchor. -/
theorem sourceVertexMap_leftEnd
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd}) :
    sourceVertexMap data hc hab hOne leftEnd = anchor := by
  have hMem : leftEnd ∈ activeFibreVertices data hc hab hOne anchor := by
    rw [hFibre]
    exact Finset.mem_insert_self _ _
  exact ((mem_activeFibreVertices data hc hab hOne anchor leftEnd).mp hMem).1

/-- The second end of the anchor fibre is carried to the anchor. -/
theorem sourceVertexMap_rightEnd
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd}) :
    sourceVertexMap data hc hab hOne rightEnd = anchor := by
  have hMem : rightEnd ∈ activeFibreVertices data hc hab hOne anchor := by
    rw [hFibre]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact ((mem_activeFibreVertices data hc hab hOne anchor rightEnd).mp hMem).1

/-- **The bridge runs between the two ends.**  The single internal occurrence of
the anchor fibre has the two fibre vertices as its endpoints. -/
theorem bridge_sourceEnds
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hInternal : internalEdges data hc hab hOne anchor = {bridge.1}) :
    data.sourceEnds bridge.1 = (leftEnd, rightEnd) ∨
      data.sourceEnds bridge.1 = (rightEnd, leftEnd) := by
  classical
  have hMem : bridge.1 ∈ internalEdges data hc hab hOne anchor := by
    rw [hInternal]
    exact Finset.mem_singleton_self _
  obtain ⟨hFst, hSnd⟩ :=
    (sourceEnds_mem_activeFibre_iff data hc hab hOne anchor bridge.1).mpr hMem
  rw [hFibre] at hFst hSnd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hFst hSnd
  have hNe := data.sourceEnds_ne bridge.1
  rcases hFst with h1 | h1 <;> rcases hSnd with h2 | h2
  · exact absurd (h1.trans h2.symm) hNe
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)
  · exact absurd (h1.trans h2.symm) hNe

/-- The two ends of the anchor fibre are distinct. -/
theorem leftEnd_ne_rightEnd
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hInternal : internalEdges data hc hab hOne anchor = {bridge.1}) :
    leftEnd ≠ rightEnd := by
  intro hBad
  refine data.sourceEnds_ne bridge.1 ?_
  rcases bridge_sourceEnds data hc hab hOne anchor leftEnd rightEnd bridge hFibre hInternal with
    h | h
  · rw [h, hBad]
  · rw [h, hBad]

/-- The bridge meets the first end. -/
theorem incident_bridge_leftEnd
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hInternal : internalEdges data hc hab hOne anchor = {bridge.1}) :
    Incident data bridge.1 leftEnd :=
  incident_of_sourceEnds data
    (bridge_sourceEnds data hc hab hOne anchor leftEnd rightEnd bridge hFibre hInternal)

/-- The bridge meets the second end. -/
theorem incident_bridge_rightEnd
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hInternal : internalEdges data hc hab hOne anchor = {bridge.1}) :
    Incident data bridge.1 rightEnd :=
  incident_of_sourceEnds data
    (bridge_sourceEnds data hc hab hOne anchor leftEnd rightEnd bridge hFibre hInternal).symm

/-- **The bridge is the only survivor over the contracted occurrence at the
anchor.**  Any surviving occurrence over the contracted target occurrence
meeting either end of the anchor fibre is the bridge itself. -/
theorem eq_bridge_of_over_contracted
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hInternal : internalEdges data hc hab hOne anchor = {bridge.1})
    (e : NonDanglingEdge data) (hT : e.1.1.1 = contracted)
    (hInc : Incident data e.1 leftEnd ∨ Incident data e.1 rightEnd) : e = bridge := by
  classical
  have hMapLeft := sourceVertexMap_leftEnd data hc hab hOne anchor leftEnd rightEnd hFibre
  have hMapRight := sourceVertexMap_rightEnd data hc hab hOne anchor leftEnd rightEnd hFibre
  have hSame := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e.1 hT
  have hMapFst : sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1 = anchor := by
    rcases hInc with h | h
    · rcases h with h | h
      · rw [h, hMapLeft]
      · rw [hSame, h, hMapLeft]
    · rcases h with h | h
      · rw [h, hMapRight]
      · rw [hSame, h, hMapRight]
  have hMemInternal : e.1 ∈ internalEdges data hc hab hOne anchor :=
    (mem_internalEdges data hc hab hOne anchor e.1).mpr ⟨e.2, hT, hMapFst⟩
  rw [hInternal, Finset.mem_singleton] at hMemInternal
  exact Subtype.ext hMemInternal

/-- **A retained occurrence at the anchor comes from an occurrence at one of
the two ends.** -/
theorem incident_nonDanglingEmbedding_of_incident_anchor
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (g : NonDanglingEdge (contractDatum data hc hab hOne))
    (hg : Incident (contractDatum data hc hab hOne) g.1 anchor) :
    Incident data (nonDanglingEmbedding data hCompat.1 g).1 leftEnd ∨
      Incident data (nonDanglingEmbedding data hCompat.1 g).1 rightEnd := by
  classical
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
  have hMem : ∀ u : data.SourceVertex,
      Incident data (nonDanglingEmbedding data hCompat.1 g).1 u →
        sourceVertexMap data hc hab hOne u = anchor → u = leftEnd ∨ u = rightEnd := by
    intro u hInc hMapU
    have hActive := nonDanglingValency_ne_zero_of_incident data
      (nonDanglingEmbedding data hCompat.1 g).2 hInc
    have hMemFibre : u ∈ activeFibreVertices data hc hab hOne anchor :=
      (mem_activeFibreVertices data hc hab hOne anchor u).mpr ⟨hMapU, hActive⟩
    rw [hFibre] at hMemFibre
    simpa using hMemFibre
  rcases hg with h | h
  · have h' : sourceVertexMap data hc hab hOne
        (data.sourceEnds (nonDanglingEmbedding data hCompat.1 g).1).1 = anchor := by
      rw [← h, hEnds]
    rcases hMem _ (incident_left data _) h' with hu | hu
    · exact Or.inl (Or.inl hu)
    · exact Or.inr (Or.inl hu)
  · have h' : sourceVertexMap data hc hab hOne
        (data.sourceEnds (nonDanglingEmbedding data hCompat.1 g).1).2 = anchor := by
      rw [← h, hEnds]
    rcases hMem _ (incident_right data _) h' with hu | hu
    · exact Or.inl (Or.inr hu)
    · exact Or.inr (Or.inr hu)

include hInj in
/-- **(b) At the anchor the star of a row splits.**  The wall datum's star of a
retained row at the merged anchor is the disjoint union of the incoming stars of
the incoming row at the two ends of the anchor fibre.  The bridge row itself is
excluded by `hFacetOver`: all its surviving occurrences lie over the contracted
target occurrence, and none of those survives the contraction. -/
theorem incidenceCount_anchor
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hInternal : internalEdges data hc hab hOne anchor = {bridge.1})
    (hFacetOver : ∀ e : NonDanglingEdge data, e.stablePath = bridge.stablePath →
      e.1.1.1 = contracted)
    (row : StablePath (contractDatum data hc hab hOne)) :
    incidenceCount (contractDatum data hc hab hOne) anchor row =
      incidenceCount data leftEnd (incomingRow data fd hc hab hOne hCompat hForest row) +
        incidenceCount data rightEnd
          (incomingRow data fd hc hab hOne hCompat hForest row) := by
  classical
  have hLR := leftEnd_ne_rightEnd data hc hab hOne anchor leftEnd rightEnd bridge hFibre hInternal
  have hMapLeft := sourceVertexMap_leftEnd data hc hab hOne anchor leftEnd rightEnd hFibre
  have hMapRight := sourceVertexMap_rightEnd data hc hab hOne anchor leftEnd rightEnd hFibre
  have hRowNe : incomingRow data fd hc hab hOne hCompat hForest row ≠ bridge.stablePath :=
    incomingRow_ne_of_over_contracted data fd hc hab hOne hCompat hForest bridge.stablePath
      hFacetOver row
  have hNotContracted : ∀ e : NonDanglingEdge data,
      (Incident data e.1 leftEnd ∨ Incident data e.1 rightEnd) →
      e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row →
      e.1.1.1 ≠ contracted := by
    intro e hInc hRow hT
    have hEq := eq_bridge_of_over_contracted data hc hab hOne anchor leftEnd rightEnd bridge
      hFibre hInternal e hT hInc
    rw [hEq] at hRow
    exact hRowNe hRow.symm
  have hDisjoint : Disjoint
      ((incidentEdges data leftEnd).filter fun e ↦
        e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row)
      ((incidentEdges data rightEnd).filter fun e ↦
        e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row) := by
    rw [Finset.disjoint_left]
    intro e heL heR
    obtain ⟨hMemL, hRow⟩ := Finset.mem_filter.mp heL
    obtain ⟨hMemR, -⟩ := Finset.mem_filter.mp heR
    have hIncL := (mem_incidentEdges data leftEnd e).mp hMemL
    have hIncR := (mem_incidentEdges data rightEnd e).mp hMemR
    have hT := hNotContracted e (Or.inl hIncL) hRow
    refine sourceVertexMap_sourceEnds_ne data hc hab hOne ⟨e.1, hT⟩ ?_
    rcases hIncL with h1 | h1 <;> rcases hIncR with h2 | h2
    · exact absurd (h1.symm.trans h2) hLR
    · rw [h1, h2, hMapLeft, hMapRight]
    · rw [h1, h2, hMapRight, hMapLeft]
    · exact absurd (h1.symm.trans h2) hLR
  unfold incidenceCount
  rw [← Finset.card_union_of_disjoint hDisjoint]
  have hUnion : ∀ e : NonDanglingEdge data,
      e ∈ ((incidentEdges data leftEnd).filter fun e ↦
            e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row) ∪
          ((incidentEdges data rightEnd).filter fun e ↦
            e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row) ↔
        ((Incident data e.1 leftEnd ∨ Incident data e.1 rightEnd) ∧
          e.stablePath = incomingRow data fd hc hab hOne hCompat hForest row) := by
    intro e
    simp only [Finset.mem_union, Finset.mem_filter, mem_incidentEdges]
    tauto
  symm
  refine Finset.card_bij (fun e he ↦ descend data hc hab hOne hCompat e
    (hNotContracted e ((hUnion e).mp he).1 ((hUnion e).mp he).2)) ?_ ?_ ?_
  · intro e he
    obtain ⟨hInc, hRow⟩ := (hUnion e).mp he
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine (mem_incidentEdges (contractDatum data hc hab hOne) _ _).mpr ?_
      rcases hInc with h | h
      · rw [← hMapLeft]
        exact incident_descend data hc hab hOne hCompat _ h
      · rw [← hMapRight]
        exact incident_descend data hc hab hOne hCompat _ h
    · exact (stablePath_descend_eq_iff_of_injective data fd hc hab hOne hCompat hForest hInj
        e _ row).mpr hRow
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
    have hIncUp := incident_nonDanglingEmbedding_of_incident_anchor data hc hab hOne hCompat
      anchor leftEnd rightEnd hFibre g hIncidentDown
    have hRowUp : (nonDanglingEmbedding data hCompat.1 g).stablePath =
        incomingRow data fd hc hab hOne hCompat hForest row :=
      (stablePath_descend_eq_iff_of_injective data fd hc hab hOne hCompat hForest hInj
        _ heT row).mp (by rw [hDescend]; exact hRow)
    exact ⟨nonDanglingEmbedding data hCompat.1 g, (hUnion _).mpr ⟨hIncUp, hRowUp⟩, hDescend⟩

/-- **(b) The bridge row meets the first end exactly once.** -/
theorem incidenceCount_bridgeRow_leftEnd
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hInternal : internalEdges data hc hab hOne anchor = {bridge.1})
    (hFacetOver : ∀ e : NonDanglingEdge data, e.stablePath = bridge.stablePath →
      e.1.1.1 = contracted) :
    incidenceCount data leftEnd bridge.stablePath = 1 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_one]
  refine ⟨bridge, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨(mem_incidentEdges data leftEnd bridge).mpr
      (incident_bridge_leftEnd data hc hab hOne anchor leftEnd rightEnd bridge hFibre hInternal),
      rfl⟩
  · intro e he
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp he
    exact eq_bridge_of_over_contracted data hc hab hOne anchor leftEnd rightEnd bridge
      hFibre hInternal e (hFacetOver e hRow)
      (Or.inl ((mem_incidentEdges data leftEnd e).mp hMem))

/-- **(b) The bridge row meets the second end exactly once.** -/
theorem incidenceCount_bridgeRow_rightEnd
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hInternal : internalEdges data hc hab hOne anchor = {bridge.1})
    (hFacetOver : ∀ e : NonDanglingEdge data, e.stablePath = bridge.stablePath →
      e.1.1.1 = contracted) :
    incidenceCount data rightEnd bridge.stablePath = 1 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_one]
  refine ⟨bridge, Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨(mem_incidentEdges data rightEnd bridge).mpr
      (incident_bridge_rightEnd data hc hab hOne anchor leftEnd rightEnd bridge hFibre hInternal),
      rfl⟩
  · intro e he
    obtain ⟨hMem, hRow⟩ := Finset.mem_filter.mp he
    exact eq_bridge_of_over_contracted data hc hab hOne anchor leftEnd rightEnd bridge
      hFibre hInternal e (hFacetOver e hRow)
      (Or.inr ((mem_incidentEdges data rightEnd e).mp hMem))

end Anchor

/-! ### The branch-vertex dictionary -/

section Branch

variable (hConnected : data.Connected)

include hForest in
/-- **The pruned fibre of every wall source vertex is a tree.**
`PrunedFibreTree.internalEdges_card_add_one_eq_activeFibreVertices_card` states
this at a merged vertex; away from the merged target vertex the fibre is a
single point with no internal occurrence. -/
theorem internalEdges_card_add_one_eq_activeFibreVertices_card_general
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    (internalEdges data hc hab hOne vertex).card + 1 =
      (activeFibreVertices data hc hab hOne vertex).card := by
  classical
  by_cases hTarget : vertex.1.1 = (⟨a, hab⟩ : GraphContraction.Vertex target b)
  · let block : (mergedPartition data a b).Blocks := ⟨vertex.1.2, by
      have hFixed := vertex.2
      change ((contractDatum data hc hab hOne).vertexPartition vertex.1.1).repr vertex.1.2 =
        vertex.1.2 at hFixed
      rw [hTarget, contractDatum_vertexPartition_merge] at hFixed
      exact hFixed⟩
    have hVertex : mergedVertex data hc hab hOne block = vertex :=
      Subtype.ext (Prod.ext hTarget.symm rfl)
    have hRes := internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne
      hForest block (by rw [hVertex]; exact hNonempty)
    rw [hVertex] at hRes
    exact hRes
  · obtain ⟨v, hv⟩ := sourceVertexMap_surjective data hc hab hOne vertex
    have hProj : GraphContraction.fold target hab v.1.1 = vertex.1.1 :=
      congrArg (fun z : (contractDatum data hc hab hOne).SourceVertex ↦ z.1.1) hv
    have hva : v.1.1 ≠ a := by
      intro hEq
      exact hTarget (by rw [← hProj, hEq, GraphContraction.fold_a])
    have hvb : v.1.1 ≠ b := by
      intro hEq
      exact hTarget (by rw [← hProj, hEq, GraphContraction.fold_self])
    have hEmpty : internalEdges data hc hab hOne vertex = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      obtain ⟨-, hT, hMap⟩ := (mem_internalEdges data hc hab hOne vertex e).mp he
      have h1 : (data.sourceEnds e).1.1.1 = a := by
        rw [sourceEnds_fst_fst data e, hT, hc]
      have h2 := congrArg (fun z : (contractDatum data hc hab hOne).SourceVertex ↦ z.1.1) hMap
      change GraphContraction.fold target hab (data.sourceEnds e).1.1.1 = vertex.1.1 at h2
      rw [h1, GraphContraction.fold_a] at h2
      exact hTarget h2.symm
    have hSingleton : activeFibreVertices data hc hab hOne vertex = {v} := by
      obtain ⟨u, hu⟩ := hNonempty
      obtain ⟨hMapU, hActiveU⟩ := (mem_activeFibreVertices data hc hab hOne vertex u).mp hu
      have hUV : u = v :=
        (sourceVertexMap_eq_iff_of_ne_right data hc hab hOne u v hva hvb).mp (hMapU.trans hv.symm)
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · rw [← hUV]
        exact hu
      · intro w hw
        obtain ⟨hMapW, -⟩ := (mem_activeFibreVertices data hc hab hOne vertex w).mp hw
        exact (sourceVertexMap_eq_iff_of_ne_right data hc hab hOne w v hva hvb).mp
          (hMapW.trans hv.symm)
    rw [hEmpty, hSingleton, Finset.card_empty, Finset.card_singleton]

include hCompat hForest in
/-- **Draisma–Vargas Part I, `lemma-ndval-of-GqA0`, at every wall source vertex.**  The
wall valency is two plus the sum of the incoming surviving-valency excesses over
the pruned fibre.  `PrunedFibreTree.nonDanglingValency_mergedVertex_eq_sum` is
the merged case; this is the statement at an arbitrary wall vertex with a
nonempty pruned fibre. -/
theorem nonDanglingValency_eq_sum_activeFibre
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (activeFibreVertices data hc hab hOne vertex).Nonempty) :
    (nonDanglingValency (contractDatum data hc hab hOne) vertex : ℤ) =
      (∑ u ∈ activeFibreVertices data hc hab hOne vertex,
        ((nonDanglingValency data u : ℤ) - 2)) + 2 := by
  classical
  have hAccounting :
      (∑ u ∈ activeFibreVertices data hc hab hOne vertex, (nonDanglingValency data u : ℤ)) =
        (nonDanglingValency (contractDatum data hc hab hOne) vertex : ℤ) +
          2 * ((internalEdges data hc hab hOne vertex).card : ℤ) := by
    exact_mod_cast sum_nonDanglingValency_activeFibre data hc hab hOne hCompat vertex
  have hTree : ((internalEdges data hc hab hOne vertex).card : ℤ) + 1 =
      ((activeFibreVertices data hc hab hOne vertex).card : ℤ) := by
    exact_mod_cast internalEdges_card_add_one_eq_activeFibreVertices_card_general data hc hab hOne
      hForest vertex hNonempty
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  omega

include hConnected in
/-- Every active incoming vertex has surviving valency at least two: valency one
is excluded by connectedness. -/
theorem two_le_nonDanglingValency_of_mem_activeFibre
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (u : data.SourceVertex)
    (hu : u ∈ activeFibreVertices data hc hab hOne vertex) :
    2 ≤ nonDanglingValency data u := by
  have hNeZero := ((mem_activeFibreVertices data hc hab hOne vertex u).mp hu).2
  have hNeOne := NonDanglingValency.nonDanglingValency_ne_one data hConnected u
  omega

include hCompat hForest hConnected in
/-- **(c) Branch vertices descend.**  A branch vertex of the incoming cover has
a branch vertex of the wall datum as its image. -/
theorem three_le_nonDanglingValency_sourceVertexMap
    (v : data.SourceVertex) (hv : 3 ≤ nonDanglingValency data v) :
    3 ≤ nonDanglingValency (contractDatum data hc hab hOne)
      (sourceVertexMap data hc hab hOne v) := by
  classical
  have hMemV : v ∈ activeFibreVertices data hc hab hOne (sourceVertexMap data hc hab hOne v) :=
    (mem_activeFibreVertices data hc hab hOne _ v).mpr ⟨rfl, by omega⟩
  have hFormula := nonDanglingValency_eq_sum_activeFibre data hc hab hOne hCompat hForest
    (sourceVertexMap data hc hab hOne v) ⟨v, hMemV⟩
  have hNonneg : ∀ u ∈ activeFibreVertices data hc hab hOne
      (sourceVertexMap data hc hab hOne v), 0 ≤ (nonDanglingValency data u : ℤ) - 2 := by
    intro u hu
    have := two_le_nonDanglingValency_of_mem_activeFibre data hc hab hOne hConnected _ u hu
    omega
  have hSingle := Finset.single_le_sum hNonneg hMemV
  omega

include hCompat hForest in
/-- **(c) Branch vertices of the wall datum come from branch vertices.**  A
branch vertex of the wall datum has a branch vertex of the incoming cover in its
pruned fibre. -/
theorem exists_three_le_mem_activeFibre
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hThree : 3 ≤ nonDanglingValency (contractDatum data hc hab hOne) vertex) :
    ∃ u ∈ activeFibreVertices data hc hab hOne vertex, 3 ≤ nonDanglingValency data u := by
  classical
  have hNonempty := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne
    hCompat vertex (by omega)
  have hFormula := nonDanglingValency_eq_sum_activeFibre data hc hab hOne hCompat hForest
    vertex hNonempty
  by_contra hNone
  push Not at hNone
  have hLe : (∑ u ∈ activeFibreVertices data hc hab hOne vertex,
      ((nonDanglingValency data u : ℤ) - 2)) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro u hu
    have := hNone u hu
    omega
  omega

include hCompat hForest hConnected in
/-- **(c) A trivalent wall vertex has only one branch vertex in its fibre.** -/
theorem eq_of_mem_activeFibre_of_three_le
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hLeThree : nonDanglingValency (contractDatum data hc hab hOne) vertex ≤ 3)
    (u u' : data.SourceVertex)
    (hu : u ∈ activeFibreVertices data hc hab hOne vertex)
    (hu' : u' ∈ activeFibreVertices data hc hab hOne vertex)
    (hThreeU : 3 ≤ nonDanglingValency data u) (hThreeU' : 3 ≤ nonDanglingValency data u') :
    u = u' := by
  classical
  by_contra hNe
  have hFormula := nonDanglingValency_eq_sum_activeFibre data hc hab hOne hCompat hForest
    vertex ⟨u, hu⟩
  have hNonneg : ∀ w ∈ activeFibreVertices data hc hab hOne vertex,
      0 ≤ (nonDanglingValency data w : ℤ) - 2 := by
    intro w hw
    have := two_le_nonDanglingValency_of_mem_activeFibre data hc hab hOne hConnected vertex w hw
    omega
  have hPair : ({u, u'} : Finset data.SourceVertex) ⊆
      activeFibreVertices data hc hab hOne vertex := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hu'
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg hPair
    (fun w hw _ ↦ hNonneg w hw)
  rw [Finset.sum_pair hNe] at hSum
  omega

include hCompat hForest hConnected in
/-- **(c) The branch-vertex dictionary across the wall.**  Away from the anchor
`sourceVertexMap` is a bijection from the branch vertices of the incoming cover
other than the two ends of the anchor fibre onto the branch vertices of the wall
datum other than the anchor.  The trivalence hypothesis off the anchor is what
makes the fibres carry at most one branch vertex; at a Part II wall it is the
wall datum's own trivalence away from its non-trivalent anchor. -/
noncomputable def branchVertexEquivAnchorComplement
    (anchor : (contractDatum data hc hab hOne).SourceVertex)
    (leftEnd rightEnd : data.SourceVertex)
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hTrivalentAway : ∀ w : (contractDatum data hc hab hOne).SourceVertex, w ≠ anchor →
      nonDanglingValency (contractDatum data hc hab hOne) w ≤ 3) :
    {v : BranchVertex data // v.1 ≠ leftEnd ∧ v.1 ≠ rightEnd} ≃
      {w : BranchVertex (contractDatum data hc hab hOne) // w.1 ≠ anchor} := by
  classical
  have hMapLeft := sourceVertexMap_leftEnd data hc hab hOne anchor leftEnd rightEnd hFibre
  have hMapRight := sourceVertexMap_rightEnd data hc hab hOne anchor leftEnd rightEnd hFibre
  have hNeAnchor : ∀ v : data.SourceVertex, 3 ≤ nonDanglingValency data v →
      v ≠ leftEnd → v ≠ rightEnd → sourceVertexMap data hc hab hOne v ≠ anchor := by
    intro v hv hvl hvr hBad
    have hMem : v ∈ activeFibreVertices data hc hab hOne anchor :=
      (mem_activeFibreVertices data hc hab hOne anchor v).mpr ⟨hBad, by omega⟩
    rw [hFibre] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with h | h
    · exact hvl h
    · exact hvr h
  refine Equiv.ofBijective
    (fun v ↦ ⟨⟨sourceVertexMap data hc hab hOne v.1.1,
      three_le_nonDanglingValency_sourceVertexMap data hc hab hOne hCompat hForest hConnected
        v.1.1 v.1.2⟩, hNeAnchor v.1.1 v.1.2 v.2.1 v.2.2⟩) ⟨?_, ?_⟩
  · intro v v' hEq
    have hMap : sourceVertexMap data hc hab hOne v.1.1 = sourceVertexMap data hc hab hOne v'.1.1 :=
      congrArg (fun w : {w : BranchVertex (contractDatum data hc hab hOne) // w.1 ≠ anchor} ↦ w.1.1)
        hEq
    have hLe := hTrivalentAway (sourceVertexMap data hc hab hOne v.1.1)
      (hNeAnchor v.1.1 v.1.2 v.2.1 v.2.2)
    have hMemV : v.1.1 ∈ activeFibreVertices data hc hab hOne
        (sourceVertexMap data hc hab hOne v.1.1) :=
      (mem_activeFibreVertices data hc hab hOne _ v.1.1).mpr ⟨rfl, by have := v.1.2; omega⟩
    have hMemV' : v'.1.1 ∈ activeFibreVertices data hc hab hOne
        (sourceVertexMap data hc hab hOne v.1.1) :=
      (mem_activeFibreVertices data hc hab hOne _ v'.1.1).mpr
        ⟨hMap.symm, by have := v'.1.2; omega⟩
    exact Subtype.ext (Subtype.ext (eq_of_mem_activeFibre_of_three_le data hc hab hOne hCompat
      hForest hConnected _ hLe v.1.1 v'.1.1 hMemV hMemV' v.1.2 v'.1.2))
  · intro w
    obtain ⟨u, hu, hThree⟩ := exists_three_le_mem_activeFibre data hc hab hOne hCompat hForest
      w.1.1 w.1.2
    obtain ⟨hMapU, -⟩ := (mem_activeFibreVertices data hc hab hOne w.1.1 u).mp hu
    have hul : u ≠ leftEnd := by
      intro hBad
      exact w.2 (by rw [← hMapU, hBad, hMapLeft])
    have hur : u ≠ rightEnd := by
      intro hBad
      exact w.2 (by rw [← hMapU, hBad, hMapRight])
    exact ⟨⟨⟨u, hThree⟩, hul, hur⟩, Subtype.ext (Subtype.ext hMapU)⟩

include hCompat hForest hConnected in
/-- The dictionary is `sourceVertexMap` on the nose. -/
theorem branchVertexEquivAnchorComplement_apply
    (anchor : (contractDatum data hc hab hOne).SourceVertex)
    (leftEnd rightEnd : data.SourceVertex)
    (hFibre : activeFibreVertices data hc hab hOne anchor = {leftEnd, rightEnd})
    (hTrivalentAway : ∀ w : (contractDatum data hc hab hOne).SourceVertex, w ≠ anchor →
      nonDanglingValency (contractDatum data hc hab hOne) w ≤ 3)
    (v : {v : BranchVertex data // v.1 ≠ leftEnd ∧ v.1 ≠ rightEnd}) :
    (branchVertexEquivAnchorComplement data hc hab hOne hCompat hForest hConnected anchor
      leftEnd rightEnd hFibre hTrivalentAway v).1.1 =
        sourceVertexMap data hc hab hOne v.1.1 := rfl

end Branch

end Dictionary

/-! ### Producers of the injectivity hypothesis -/

section Producers

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionForest data a b contracted)
  (coordinates : coordinate → ℚ) (facet : coordinate)
  (hZeroCoord : coordinates (fd.labelling.targetEdge.symm contracted) = 0)
  (hPosCoord : ∀ column, column ≠ fd.labelling.targetEdge.symm contracted →
    0 < coordinates column)
  (hFacetZero :
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
      coordinates facet = 0)

/-- The chain argument of `StablePathFacetContraction` supplies the injectivity
hypothesis under `StablePathFacetContraction.NoContractedReturn`. -/
theorem injective_incomingRow_of_noContractedReturn
    (hNoReturn : NoContractedReturn data contracted) :
    Function.Injective (incomingRow data fd hc hab hOne hCompat hForest) :=
  incomingRow_injective data fd hc hab hOne hCompat hForest hNoReturn

include hZeroCoord hPosCoord hFacetZero in
/-- The same chain argument, run in `LeafFacetNoReturn`, supplies the
injectivity hypothesis under the weaker `LeafFacetNoReturn.NoContractedReturnOffRow`. -/
theorem injective_incomingRow_of_noContractedReturnOffRow
    (hNoReturn : LeafFacetNoReturn.NoContractedReturnOffRow data contracted
      (fd.labelling.row.symm facet)) :
    Function.Injective (incomingRow data fd hc hab hOne hCompat hForest) :=
  LeafFacetNoReturn.incomingRow_injective' data fd hc hab hOne hCompat hForest coordinates facet
    hNoReturn hZeroCoord hPosCoord hFacetZero

include hZeroCoord hPosCoord hFacetZero in
/-- At a one-zero-row facet every surviving occurrence of the vanishing row lies
over the contracted target occurrence, which is the `hFacetOver` hypothesis of
the anchor statements above. -/
theorem facetRow_over_contracted_of_facet (bridge : NonDanglingEdge data)
    (hBridgeRow : bridge.stablePath = fd.labelling.row.symm facet)
    (e : NonDanglingEdge data) (hRow : e.stablePath = bridge.stablePath) :
    e.1.1.1 = contracted :=
  LeafFacetNoReturn.facetRow_over_contracted data fd coordinates facet hZeroCoord hPosCoord
    hFacetZero e (hRow.trans hBridgeRow)

end Producers

end DraismaVargas.LocalCases.WallSplitIncidence
