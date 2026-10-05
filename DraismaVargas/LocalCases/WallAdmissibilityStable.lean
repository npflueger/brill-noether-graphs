module

public import DraismaVargas.LocalCases.IncomingSourceCases
public import DraismaVargas.LocalCases.StablePathCount
public import DraismaVargas.LocalCases.PrunedFibreStablePath
public import DraismaVargas.LocalCases.WallAdmissibility

@[expose] public section

/-!
# `hTrivalent` and `hStable` are derivable at a wall event

`IncomingSourceCases.exists_classification` takes three admissibility receipts
as hypotheses.  `WallAdmissibility.danglingCompatible_of_fullDimensional` proves
the third: `DanglingCompatible` is a theorem at a wall event.  This module proves
the other two, so all three follow from the metric hypotheses of
`exists_classification` alone.

* **`trivalent_of_fullDimensional` — `hTrivalent` is a theorem.**  From a
  `FullDimensionalSourcePresentation` and the metric facts at the event
  (`hNonnegative`, `hRows`, `hZero`), every merged wall source vertex has
  surviving valency at most three.  Nothing is added to the hypothesis set
  `exists_classification` already takes.
* **`stablePath_equiv` — `hStable` is a theorem.**  The canonical map
  `PrunedFibreStablePath.stablePathLift` from limit stable classes to incoming
  stable classes is a bijection, so
  `Nonempty (StablePath (contractDatum …) ≃ StablePath data)` — exactly the
  receipt `exists_classification` takes — holds on the same hypothesis list.
  `card_stablePath_contractDatum` reads off the cardinality
  `#StablePath (contractDatum …) = |E(contract T)| + 1` that every consumer of
  `hStable` uses through `WallDegeneration.stablePath_card_contractDatum`.

## The one new input, and it is metric

`exists_stablePath_eq_target_ne`: **no stable class of the incoming datum lies
entirely over the contracted target edge.**  A row of the honest stable length
matrix lists exactly the surviving occurrences of one stable class
(`StableLengthMatrixLabelling.path`), and `matrix_mulVec` makes the row value
the sum of their lengths; `hRows` says that sum is nonzero, so some occurrence
of the class has a target edge of nonzero coordinate, and `hZero` excludes the
contracted one.  Nonnegativity of the coordinates is *not* used: the
contrapositive kills the whole sum termwise.  This is the same mechanism
`SourceFibreForest.isForest_of_nonzero_rows` runs for the forest receipt, read
on classes rather than on cycles.

## How `hTrivalent` follows

`PrunedFibreTree.nonDanglingValency_mergedVertex_eq_sum` (Draisma–Vargas Part I, arXiv:1909.12924,
`lemma-ndval-of-GqA0`)
gives `nd(merged) = 2 + Σ_{active constituents v} (nd(v) − 2)`, and
`fullDim.trivalent` with `nonDanglingValency_ne_one` make every summand `0` or
`1`.  So `hTrivalent` is exactly: **each wall fibre contains at most one
constituent with `nd = 3`** (`card_branch_le_one`).

That is proved by a spanning-forest count on a *local junction graph*
(`junctionGraph`): one vertex per surviving contracted occurrence inside the
fibre, one per divalent constituent, one edge occurrence per incidence.  Write
`I` for its contracted occurrences, `J` for its divalent constituents, `d(v)`
for the number of contracted survivors at `v`, `X` for the branch constituents
and `Z` for the divalent constituents with `d(v) = 0`.  Then

* `Trivalence.card_V_le_card_edges_add_componentCount` gives
  `|I| + |J| ≤ Σ_{v∈J} d(v) + c`, where `c` is the component count;
* `componentCount_junctionGraph_le` gives `c ≤ #{v ∈ J : d(v) ≤ 1}` — **this is
  where the metric enters**: a component with no such exit would be closed under
  `Consecutive` (`exists_reach_junction_of_inl`), hence a whole stable class
  lying over the contracted edge, which the metric forbids;
* `d(v) ≤ 2` at a divalent constituent, so
  `Σ_{v∈J} (d(v) + [d(v) ≤ 1] + [d(v) = 0]) ≤ 2|J|`.

Together `|I| + Z ≤ |J|` (`card_internalEdges_add_card_isolated_le`), and the
fibre tree count `|I| + 1 = |J| + X`
(`PrunedFibreTree.internalEdges_card_add_one_eq_activeFibreVertices_card`, which
is where `ContractionForest` is used) turns this into `X + Z ≤ 1`.  Hence
`nd(merged) = X + 2 ≤ 3`.

No path-finding in the fibre tree is needed anywhere: connectivity enters only
through the tree count, and the chain structure only through the component
count.

## How `hStable` follows

`hStable` is the equivalence `StablePath (contractDatum …) ≃ StablePath data`,
and `PrunedFibreStablePath.stablePathLift` realises it.

* **Surjective** (`stablePathLift_surjective`): the wall metric keeps, in every
  incoming class, an occurrence away from the contracted target edge, and
  `DanglingCompatible` keeps that occurrence surviving downstairs.
* **Injective** (`stablePathLift_injective`): no incoming stable class splits
  into two limit classes.  The left inverse is `stablePathDescend`, the
  `Quot.lift` of `exitClass`: a survivor away from the contracted target edge
  goes to its own limit class, and a survivor over it goes to the limit class
  of an exit of its chain of contracted survivors (`ChainExit`).

Three facts make `exitClass` well defined and constant along `Consecutive`.

* **Every chain has an exit** (`exists_chainExit`).  This is again the metric
  fact `exists_stablePath_eq_target_ne`, and it needs no graph machinery at
  all: the first non-contracted neighbour met along a chain already is an
  exit, so if there were none the whole stable class would lie over the
  contracted target edge.
* **Two exits of one chain give one limit class**
  (`stablePath_descend_eq_of_chainExit`).  Either they sit at the same
  junction, and a divalent junction carrying a contracted survivor has only one
  non-contracted survivor left; or they sit at two junctions of one component
  of the junction graph, the component count drops
  (`componentCount_junctionGraph_lt`), so `X = 0` and the merged vertex is
  divalent (`nonDanglingValency_mergedVertex_eq_two_of_two_exits`).
* **Two non-contracted survivors meeting at a divalent vertex meet a divalent
  limit vertex** (`nonDanglingValency_sourceVertexMap_eq_two`).  Away from the
  wall this is `WallDegeneration.nonDanglingValency_sourceVertexMap`; at the
  wall the vertex is a junction carrying no contracted survivor, so `Z ≥ 1`,
  again `X = 0` and the merged vertex is divalent
  (`nonDanglingValency_mergedVertex_eq_two_of_isolated_junction`).

In each case the two boundary occurrences stay incident to a divalent limit
vertex, hence stay consecutive downstairs, so the class does not split.  The
translation of a chain into the junction graph
(`reach_junctionGraph_of_reflTransGen`) is only needed for the second of the
three, and only in the easy direction.

## Hypotheses

The local theorems of the `Fibre` section below take
`DanglingCompatible data hc hab hOne` as a hypothesis, because they are stated
for an abstract contraction with no metric data attached.  The four theorems of
the closing `WallEvent` section -- `trivalent_of_fullDimensional`,
`card_edges_contract_add_one_le_card_stablePath`, `stablePath_equiv` and
`card_stablePath_contractDatum` -- do not: they discharge it internally through
`WallAdmissibility.danglingCompatible_of_fullDimensional`, whose hypothesis set
is a sub-list of theirs.  Their hypothesis lists are therefore exactly
`IncomingSourceCases.exists_classification`'s, with nothing added.
-/
namespace DraismaVargas.LocalCases.WallAdmissibilityStable

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionFibre
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallDegeneration
open DraismaVargas.LocalCases.PrunedFibreValency
open DraismaVargas.LocalCases.PrunedFibreTree
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.ClassInjectivity
open DraismaVargas.LocalCases.PrunedSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.FullContractionFibre

/-! ## The metric fact: no stable class sits entirely over one target edge -/

section Metric

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Every honest stable row keeps an occurrence of nonzero target
coordinate.**  A row of the stable length matrix lists exactly the surviving
occurrences of one stable class, and the matrix–vector product is the sum of
their lengths; a nonzero row value therefore exhibits one occurrence whose
target edge has a nonzero coordinate.  Nonnegativity of the coordinate vector
is *not* needed: the contrapositive kills the whole sum termwise. -/
theorem exists_mem_path_coordinate_ne_zero
    (labelling : StableLengthMatrixLabelling data coordinate)
    (coordinates : coordinate → ℚ)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).mulVec
        coordinates row ≠ 0)
    (row : coordinate) :
    ∃ edge ∈ labelling.path row,
      coordinates (labelling.targetEdge.symm edge.1.1) ≠ 0 := by
  by_contra hNone
  push Not at hNone
  apply hRows row
  rw [GluingDatum.LengthMatrixPresentation.matrix_mulVec]
  unfold GluingDatum.sourcePathLength
  apply List.sum_eq_zero
  intro term hTerm
  obtain ⟨edge, hEdge, rfl⟩ := List.mem_map.mp hTerm
  have hZero : coordinates (labelling.targetEdge.symm edge.1.1) = 0 :=
    hNone edge hEdge
  simp only [GluingDatum.sourceEdgeLength, StableLengthMatrixLabelling.presentation,
    hZero, zero_div]

/-- The same statement read on stable classes: every stable class of the
incoming datum contains a surviving occurrence whose target edge has a nonzero
coordinate. -/
theorem exists_stablePath_eq_coordinate_ne_zero
    (labelling : StableLengthMatrixLabelling data coordinate)
    (coordinates : coordinate → ℚ)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).mulVec
        coordinates row ≠ 0)
    (edge : NonDanglingEdge data) :
    ∃ other : NonDanglingEdge data, other.stablePath = edge.stablePath ∧
      coordinates (labelling.targetEdge.symm other.1.1.1) ≠ 0 := by
  obtain ⟨first, hMem, hNe⟩ := exists_mem_path_coordinate_ne_zero labelling coordinates
    hRows (labelling.row edge.stablePath)
  obtain ⟨hSurvives, hRow⟩ := (labelling.mem_path_iff _ first).mp hMem
  exact ⟨⟨first, hSurvives⟩, labelling.row.injective hRow, hNe⟩

/-- **No stable class of the incoming datum lies entirely over the contracted
target edge.**  This is the only place the wall metric enters the two
admissibility receipts below, and it is exactly the same mechanism that
`SourceFibreForest.isForest_of_nonzero_rows` runs for the forest receipt. -/
theorem exists_stablePath_eq_target_ne
    {contracted : target.edges}
    (labelling : StableLengthMatrixLabelling data coordinate)
    (coordinates : coordinate → ℚ)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hZero : coordinates (labelling.targetEdge.symm contracted) = 0)
    (edge : NonDanglingEdge data) :
    ∃ other : NonDanglingEdge data, other.stablePath = edge.stablePath ∧
      other.1.1.1 ≠ contracted := by
  obtain ⟨other, hPath, hNe⟩ :=
    exists_stablePath_eq_coordinate_ne_zero labelling coordinates hRows edge
  refine ⟨other, hPath, fun hBad ↦ hNe ?_⟩
  rw [hBad]
  exact hZero

/-- `Consecutive` is symmetric. -/
theorem consecutive_symm {first second : NonDanglingEdge data}
    (h : Consecutive data first second) : Consecutive data second first := by
  obtain ⟨hNe, v, hFirst, hSecond, hVal⟩ := h
  exact ⟨hNe.symm, v, hSecond, hFirst, hVal⟩

end Metric

/-! ## Chains of surviving contracted occurrences -/

section Chain

variable {target : CFGraph} {degree : ℕ}

/-- **One step of a chain of contracted survivors.**  Two surviving
occurrences over the contracted target occurrence meeting at a surviving
valency-two vertex.  Its chains are the walk components of `junctionGraph`
below, read on occurrences instead of on graph vertices. -/
def InternalStep (data : GluingDatum target degree) (contracted : target.edges)
    (first second : NonDanglingEdge data) : Prop :=
  first.1.1.1 = contracted ∧ second.1.1.1 = contracted ∧
    ∃ vertex : data.SourceVertex, Incident data first.1 vertex ∧
      Incident data second.1 vertex ∧ nonDanglingValency data vertex = 2

/-- **`exit` leaves the chain through `first`.**  Some contracted survivor
reachable from `first` inside the contracted target fibre meets `exit` at a
surviving valency-two vertex. -/
def ChainExit (data : GluingDatum target degree) (contracted : target.edges)
    (first exit : NonDanglingEdge data) : Prop :=
  ∃ last : NonDanglingEdge data,
    Relation.ReflTransGen (InternalStep data contracted) first last ∧
      ∃ vertex : data.SourceVertex, Incident data last.1 vertex ∧
        Incident data exit.1 vertex ∧ nonDanglingValency data vertex = 2

/-- Prefixing a chain step keeps the same exits. -/
theorem ChainExit.of_internalStep {data : GluingDatum target degree}
    {contracted : target.edges} {first second exit : NonDanglingEdge data}
    (hStep : InternalStep data contracted first second)
    (hExit : ChainExit data contracted second exit) :
    ChainExit data contracted first exit := by
  obtain ⟨last, hChain, rest⟩ := hExit
  exact ⟨last, Relation.ReflTransGen.head hStep hChain, rest⟩

/-- A neighbour of a contracted survivor at a surviving valency-two vertex is
an exit of its chain. -/
theorem chainExit_of_consecutive {data : GluingDatum target degree}
    {contracted : target.edges} {first exit : NonDanglingEdge data}
    (vertex : data.SourceVertex) (hFirst : Incident data first.1 vertex)
    (hExit : Incident data exit.1 vertex)
    (hValency : nonDanglingValency data vertex = 2) :
    ChainExit data contracted first exit :=
  ⟨first, Relation.ReflTransGen.refl, vertex, hFirst, hExit, hValency⟩

end Chain


/-! ## The local junction graph of one wall fibre -/

section Fibre

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)

/-- The divalent active constituents of one wall fibre. -/
noncomputable def fibreJunctions
    (vertex : (contractDatum data hc hab hOne).SourceVertex) : Finset data.SourceVertex :=
  (activeFibreVertices data hc hab hOne vertex).filter fun v ↦
    nonDanglingValency data v = 2

@[simp] theorem mem_fibreJunctions
    (vertex : (contractDatum data hc hab hOne).SourceVertex) (v : data.SourceVertex) :
    v ∈ fibreJunctions data hc hab hOne vertex ↔
      sourceVertexMap data hc hab hOne v = vertex ∧ nonDanglingValency data v = 2 := by
  classical
  rw [fibreJunctions, Finset.mem_filter, mem_activeFibreVertices]
  constructor
  · rintro ⟨⟨hMap, _⟩, hTwo⟩
    exact ⟨hMap, hTwo⟩
  · rintro ⟨hMap, hTwo⟩
    exact ⟨⟨hMap, by omega⟩, hTwo⟩

/-- The surviving contracted occurrences of the fibre that meet one
constituent. -/
noncomputable def internalAt
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (v : data.SourceVertex) : Finset data.SourceEdge := by
  classical
  exact (internalEdges data hc hab hOne vertex).filter fun e ↦ Incident data e v

@[simp] theorem mem_internalAt
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (v : data.SourceVertex) (e : data.SourceEdge) :
    e ∈ internalAt data hc hab hOne vertex v ↔
      e ∈ internalEdges data hc hab hOne vertex ∧ Incident data e v := by
  classical
  simp [internalAt]

/-- A constituent carries at most as many contracted survivors as it has
survivors. -/
theorem card_internalAt_le
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (v : data.SourceVertex) :
    (internalAt data hc hab hOne vertex v).card ≤ nonDanglingValency data v := by
  classical
  rw [← card_nonDanglingIncident data v]
  refine Finset.card_le_card ?_
  intro e he
  rw [mem_internalAt] at he
  rw [mem_nonDanglingIncident]
  exact ⟨((mem_internalEdges data hc hab hOne vertex e).mp he.1).1, he.2⟩

/-- At a divalent constituent carrying two contracted survivors, *every*
survivor is one of them. -/
theorem nonDanglingIncident_eq_internalAt
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    {v : data.SourceVertex} (hTwo : nonDanglingValency data v = 2)
    (hCard : (internalAt data hc hab hOne vertex v).card = 2) :
    nonDanglingIncident data v = internalAt data hc hab hOne vertex v := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro e he
    rw [mem_internalAt] at he
    rw [mem_nonDanglingIncident]
    exact ⟨((mem_internalEdges data hc hab hOne vertex e).mp he.1).1, he.2⟩
  · rw [hCard, card_nonDanglingIncident, hTwo]

/-- The incidences between the divalent constituents of the fibre and its
surviving contracted occurrences. -/
noncomputable def junctionIncidences
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    Finset ({e // e ∈ internalEdges data hc hab hOne vertex} ×
      {v // v ∈ fibreJunctions data hc hab hOne vertex}) := by
  classical
  exact Finset.univ.filter fun p ↦ Incident data p.1.1 p.2.1

@[simp] theorem mem_junctionIncidences
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (p : {e // e ∈ internalEdges data hc hab hOne vertex} ×
      {v // v ∈ fibreJunctions data hc hab hOne vertex}) :
    p ∈ junctionIncidences data hc hab hOne vertex ↔ Incident data p.1.1 p.2.1 := by
  classical
  simp [junctionIncidences]

/-- **The local junction graph of a wall fibre.**  One vertex per surviving
contracted occurrence inside the fibre, one per divalent constituent, and one
edge occurrence per incidence between them.  Its components are the maximal
chains of contracted survivors. -/
noncomputable def junctionGraph
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty) : CFGraph where
  V := {e // e ∈ internalEdges data hc hab hOne vertex} ⊕
    {v // v ∈ fibreJunctions data hc hab hOne vertex}
  instNonempty := ⟨Sum.inl ⟨hNonempty.choose, hNonempty.choose_spec⟩⟩
  edges := (junctionIncidences data hc hab hOne vertex).val.map
    fun p ↦ (Sum.inr p.2, Sum.inl p.1)
  loopless := by
    intro x hx
    obtain ⟨p, _, hp⟩ := Multiset.mem_map.mp hx
    have hFirst : (Sum.inr p.2 : {e // e ∈ internalEdges data hc hab hOne vertex} ⊕
        {v // v ∈ fibreJunctions data hc hab hOne vertex}) = x := congrArg Prod.fst hp
    have hSecond : (Sum.inl p.1 : {e // e ∈ internalEdges data hc hab hOne vertex} ⊕
        {v // v ∈ fibreJunctions data hc hab hOne vertex}) = x := congrArg Prod.snd hp
    have hBad := hFirst.trans hSecond.symm
    simp at hBad

theorem card_junctionGraph_V
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty) :
    Fintype.card (junctionGraph data hc hab hOne vertex hNonempty).V =
      (internalEdges data hc hab hOne vertex).card +
        (fibreJunctions data hc hab hOne vertex).card := by
  show Fintype.card ({e // e ∈ internalEdges data hc hab hOne vertex} ⊕
      {v // v ∈ fibreJunctions data hc hab hOne vertex}) = _
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]

theorem card_junctionGraph_edges
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty) :
    Multiset.card (junctionGraph data hc hab hOne vertex hNonempty).edges =
      (junctionIncidences data hc hab hOne vertex).card := by
  exact Multiset.card_map _ _

private theorem num_edges_pos_of_mem_edges {G : CFGraph} {x y : G.V}
    (h : (x, y) ∈ G.edges) : 0 < num_edges G x y := by
  refine Multiset.card_pos_iff_exists_mem.mpr ⟨(x, y), ?_⟩
  exact Multiset.mem_filter.mpr ⟨h, Or.inl rfl⟩

/-- A contracted survivor of the fibre is joined, in the junction graph, to
every divalent constituent it meets. -/
theorem reach_junctionGraph
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty)
    (e : {e // e ∈ internalEdges data hc hab hOne vertex})
    (v : {v // v ∈ fibreJunctions data hc hab hOne vertex})
    (hInc : Incident data e.1 v.1) :
    Reach (junctionGraph data hc hab hOne vertex hNonempty) (Sum.inl e) (Sum.inr v) := by
  refine reach_symm (reach_single (num_edges_pos_of_mem_edges ?_))
  show ((Sum.inr v, Sum.inl e) : _ × _) ∈ Multiset.map _ _
  exact Multiset.mem_map.mpr ⟨(e, v),
    (junctionIncidences data hc hab hOne vertex).mem_val.mpr
      ((mem_junctionIncidences data hc hab hOne vertex (e, v)).mpr hInc), rfl⟩

/-- **The core of the argument.**  Every surviving contracted occurrence of a
wall fibre reaches, inside the junction graph, a divalent constituent carrying
at most one contracted survivor -- that is, the chain through it leaves the
fibre.  If it did not, the whole stable class of that occurrence would consist
of occurrences over the contracted target edge, which the wall metric forbids
(`exists_stablePath_eq_target_ne`). -/
theorem exists_reach_junction_of_inl
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty)
    (e : {e // e ∈ internalEdges data hc hab hOne vertex}) :
    ∃ v : {v // v ∈ fibreJunctions data hc hab hOne vertex},
      (internalAt data hc hab hOne vertex v.1).card ≤ 1 ∧
        Reach (junctionGraph data hc hab hOne vertex hNonempty) (Sum.inl e)
          (Sum.inr v) := by
  classical
  by_contra hNo
  push Not at hNo
  set G := junctionGraph data hc hab hOne vertex hNonempty with hG
  let C : NonDanglingEdge data → Prop := fun f ↦
    ∃ h : f.1 ∈ internalEdges data hc hab hOne vertex,
      Reach G (Sum.inl e) (Sum.inl ⟨f.1, h⟩)
  have hStep : ∀ f g : NonDanglingEdge data, Consecutive data f g → C f → C g := by
    rintro f g ⟨-, w, hIncF, hIncG, hVal⟩ ⟨hfMem, hReach⟩
    obtain ⟨-, hfTarget, hfMap⟩ :=
      (mem_internalEdges data hc hab hOne vertex f.1).mp hfMem
    have hMaps := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne f.1 hfTarget
    have hwMap : sourceVertexMap data hc hab hOne w = vertex := by
      rcases hIncF with h | h
      · rw [← h]; exact hfMap
      · rw [← h, ← hMaps]; exact hfMap
    have hwJ : w ∈ fibreJunctions data hc hab hOne vertex :=
      (mem_fibreJunctions data hc hab hOne vertex w).mpr ⟨hwMap, hVal⟩
    have hReachW : Reach G (Sum.inl e) (Sum.inr ⟨w, hwJ⟩) :=
      reach_trans hReach (reach_junctionGraph data hc hab hOne vertex hNonempty
        ⟨f.1, hfMem⟩ ⟨w, hwJ⟩ hIncF)
    have hCardTwo : (internalAt data hc hab hOne vertex w).card = 2 := by
      have hLe := card_internalAt_le data hc hab hOne vertex w
      rw [hVal] at hLe
      have hNotOne : ¬ (internalAt data hc hab hOne vertex w).card ≤ 1 :=
        fun hBad ↦ hNo ⟨w, hwJ⟩ hBad hReachW
      omega
    have hEq := nonDanglingIncident_eq_internalAt data hc hab hOne vertex hVal hCardTwo
    have hgMem : g.1 ∈ internalEdges data hc hab hOne vertex := by
      have hgIn : g.1 ∈ nonDanglingIncident data w :=
        (mem_nonDanglingIncident data w g.1).mpr ⟨g.2, hIncG⟩
      rw [hEq, mem_internalAt] at hgIn
      exact hgIn.1
    exact ⟨hgMem, reach_trans hReachW (reach_symm
      (reach_junctionGraph data hc hab hOne vertex hNonempty ⟨g.1, hgMem⟩ ⟨w, hwJ⟩ hIncG))⟩
  have hIff : ∀ f g : NonDanglingEdge data,
      Relation.EqvGen (Consecutive data) f g → (C f ↔ C g) := by
    intro f g h
    induction h with
    | rel x y hxy => exact ⟨hStep x y hxy, hStep y x (consecutive_symm hxy)⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  have heSurv : ¬ IsDangling data e.1 :=
    ((mem_internalEdges data hc hab hOne vertex e.1).mp e.2).1
  have hCe : C ⟨e.1, heSurv⟩ := ⟨e.2, reach_refl _ _⟩
  obtain ⟨f, hfPath, hfNe⟩ := hMetric ⟨e.1, heSurv⟩
  obtain ⟨hfMem, -⟩ := (hIff f _ ((stablePath_eq_iff f _).mp hfPath)).mpr hCe
  exact hfNe ((mem_internalEdges data hc hab hOne vertex f.1).mp hfMem).2.1

/-- Every vertex of the junction graph reaches such an exit. -/
theorem exists_reach_junction
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty)
    (x : {e // e ∈ internalEdges data hc hab hOne vertex} ⊕
      {v // v ∈ fibreJunctions data hc hab hOne vertex}) :
    ∃ v : {v // v ∈ fibreJunctions data hc hab hOne vertex},
      (internalAt data hc hab hOne vertex v.1).card ≤ 1 ∧
        Reach (junctionGraph data hc hab hOne vertex hNonempty) x (Sum.inr v) := by
  classical
  rcases x with e | v
  · exact exists_reach_junction_of_inl data hc hab hOne hMetric vertex hNonempty e
  · by_cases hCard : (internalAt data hc hab hOne vertex v.1).card ≤ 1
    · exact ⟨v, hCard, reach_refl _ _⟩
    · have hPos : (internalAt data hc hab hOne vertex v.1).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨f, hf⟩ := hPos
      rw [mem_internalAt] at hf
      obtain ⟨w, hw, hReach⟩ :=
        exists_reach_junction_of_inl data hc hab hOne hMetric vertex hNonempty ⟨f, hf.1⟩
      exact ⟨w, hw, reach_trans (reach_symm (reach_junctionGraph data hc hab hOne vertex
        hNonempty ⟨f, hf.1⟩ v hf.2)) hReach⟩

/-- Hence the junction graph has at most as many components as the fibre has
exits. -/
theorem componentCount_junctionGraph_le
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty) :
    componentCount (junctionGraph data hc hab hOne vertex hNonempty) ≤
      ((fibreJunctions data hc hab hOne vertex).filter fun v ↦
        (internalAt data hc hab hOne vertex v).card ≤ 1).card := by
  classical
  rw [componentCount]
  have hsubset :
      Finset.image (component (junctionGraph data hc hab hOne vertex hNonempty))
          Finset.univ ⊆
        Finset.image (fun v : {v // v ∈ (fibreJunctions data hc hab hOne vertex).filter
            fun v ↦ (internalAt data hc hab hOne vertex v).card ≤ 1} ↦
          component (junctionGraph data hc hab hOne vertex hNonempty)
            (Sum.inr ⟨v.1, Finset.mem_of_mem_filter _ v.2⟩)) Finset.univ := by
    intro c hMem
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨v, hCard, hReach⟩ :=
      exists_reach_junction data hc hab hOne hMetric vertex hNonempty x
    exact Finset.mem_image.mpr ⟨⟨v.1, Finset.mem_filter.mpr ⟨v.2, hCard⟩⟩,
      Finset.mem_univ _, (component_eq_of_reach hReach).symm⟩
  refine le_trans (Finset.card_le_card hsubset) (le_trans Finset.card_image_le ?_)
  rw [Finset.card_univ, Fintype.card_coe]

/-- **Two distinct exits in one component cost one component.**  If two
distinct divalent constituents carrying at most one contracted survivor lie in
the same component of the junction graph, the component count is strictly below
the exit count. -/
theorem componentCount_junctionGraph_lt
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty)
    {v w : data.SourceVertex}
    (hv : v ∈ (fibreJunctions data hc hab hOne vertex).filter fun u ↦
      (internalAt data hc hab hOne vertex u).card ≤ 1)
    (hw : w ∈ (fibreJunctions data hc hab hOne vertex).filter fun u ↦
      (internalAt data hc hab hOne vertex u).card ≤ 1)
    (hne : v ≠ w)
    (hSame : component (junctionGraph data hc hab hOne vertex hNonempty)
        (Sum.inr ⟨v, Finset.mem_of_mem_filter _ hv⟩)
      = component (junctionGraph data hc hab hOne vertex hNonempty)
        (Sum.inr ⟨w, Finset.mem_of_mem_filter _ hw⟩)) :
    componentCount (junctionGraph data hc hab hOne vertex hNonempty) + 1 ≤
      ((fibreJunctions data hc hab hOne vertex).filter fun u ↦
        (internalAt data hc hab hOne vertex u).card ≤ 1).card := by
  classical
  rw [componentCount]
  have hsubset :
      Finset.image (component (junctionGraph data hc hab hOne vertex hNonempty))
          Finset.univ ⊆
        Finset.image (fun u : {u // u ∈ (fibreJunctions data hc hab hOne vertex).filter
            fun z ↦ (internalAt data hc hab hOne vertex z).card ≤ 1} ↦
          component (junctionGraph data hc hab hOne vertex hNonempty)
            (Sum.inr ⟨u.1, Finset.mem_of_mem_filter _ u.2⟩))
          (Finset.univ.erase ⟨w, hw⟩) := by
    intro c hMem
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨u, hCard, hReach⟩ :=
      exists_reach_junction data hc hab hOne hMetric vertex hNonempty x
    have huS : u.1 ∈ (fibreJunctions data hc hab hOne vertex).filter fun z ↦
        (internalAt data hc hab hOne vertex z).card ≤ 1 :=
      Finset.mem_filter.mpr ⟨u.2, hCard⟩
    by_cases hEqW : u.1 = w
    · refine Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_erase.mpr
        ⟨fun hBad ↦ hne (congrArg Subtype.val hBad), Finset.mem_univ _⟩, ?_⟩
      have hcw : component (junctionGraph data hc hab hOne vertex hNonempty)
            (Sum.inr (⟨w, Finset.mem_of_mem_filter _ hw⟩ :
              {z // z ∈ fibreJunctions data hc hab hOne vertex}))
          = component (junctionGraph data hc hab hOne vertex hNonempty) x := by
        have hu : (⟨w, Finset.mem_of_mem_filter _ hw⟩ :
            {z // z ∈ fibreJunctions data hc hab hOne vertex}) = u :=
          Subtype.ext hEqW.symm
        rw [hu]
        exact (component_eq_of_reach hReach).symm
      exact hSame.trans hcw
    · exact Finset.mem_image.mpr ⟨⟨u.1, huS⟩, Finset.mem_erase.mpr
        ⟨fun hBad ↦ hEqW (congrArg Subtype.val hBad), Finset.mem_univ _⟩,
        (component_eq_of_reach hReach).symm⟩
  have hCardLe := Finset.card_le_card hsubset
  have hImg := Finset.card_image_le (s := Finset.univ.erase
      (⟨w, hw⟩ : {u // u ∈ (fibreJunctions data hc hab hOne vertex).filter
        fun z ↦ (internalAt data hc hab hOne vertex z).card ≤ 1}))
    (f := fun u ↦ component (junctionGraph data hc hab hOne vertex hNonempty)
      (Sum.inr ⟨u.1, Finset.mem_of_mem_filter _ u.2⟩))
  have hErase : (Finset.univ.erase
      (⟨w, hw⟩ : {u // u ∈ (fibreJunctions data hc hab hOne vertex).filter
        fun z ↦ (internalAt data hc hab hOne vertex z).card ≤ 1})).card
      = ((fibreJunctions data hc hab hOne vertex).filter fun z ↦
          (internalAt data hc hab hOne vertex z).card ≤ 1).card - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_coe]
  have hPos : 1 ≤ ((fibreJunctions data hc hab hOne vertex).filter fun z ↦
      (internalAt data hc hab hOne vertex z).card ≤ 1).card :=
    Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-! ## The count: at most one branch constituent per wall fibre -/

theorem card_junctionIncidences
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    (junctionIncidences data hc hab hOne vertex).card =
      ∑ v ∈ fibreJunctions data hc hab hOne vertex,
        (internalAt data hc hab hOne vertex v).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p ↦ p.2.1)
    (t := fibreJunctions data hc hab hOne vertex) (fun p _ ↦ p.2.2)]
  refine Finset.sum_congr rfl ?_
  intro v hv
  refine Finset.card_bij (fun p _ ↦ p.1.1) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [mem_internalAt]
    exact ⟨p.1.2, hp.2 ▸ (mem_junctionIncidences data hc hab hOne vertex p).mp hp.1⟩
  · intro p hp q hq hEq
    rw [Finset.mem_filter] at hp hq
    exact Prod.ext (Subtype.ext hEq) (Subtype.ext (hp.2.trans hq.2.symm))
  · intro e he
    rw [mem_internalAt] at he
    exact ⟨(⟨e, he.1⟩, ⟨v, hv⟩), Finset.mem_filter.mpr
      ⟨(mem_junctionIncidences data hc hab hOne vertex _).mpr he.2, rfl⟩, rfl⟩

/-- **The spanning-forest bound for the junction graph of a wall fibre**, read
against the exit count supplied by the wall metric.  The parameter `k` records
any surplus in the exit count; `k = 1` is what a fibre whose junction graph has
a component with two exits supplies. -/
theorem card_internalEdges_add_le_aux
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty) (k : ℕ)
    (hComp : componentCount (junctionGraph data hc hab hOne vertex hNonempty) + k ≤
      ((fibreJunctions data hc hab hOne vertex).filter fun u ↦
        (internalAt data hc hab hOne vertex u).card ≤ 1).card) :
    (internalEdges data hc hab hOne vertex).card +
        ((fibreJunctions data hc hab hOne vertex).filter fun v ↦
          (internalAt data hc hab hOne vertex v).card = 0).card + k ≤
      (fibreJunctions data hc hab hOne vertex).card := by
  classical
  have hBound := Trivalence.card_V_le_card_edges_add_componentCount
    (junctionGraph data hc hab hOne vertex hNonempty)
  rw [card_junctionGraph_V, card_junctionGraph_edges] at hBound
  have hInc := card_junctionIncidences data hc hab hOne vertex
  have hFilter : ((fibreJunctions data hc hab hOne vertex).filter fun v ↦
      (internalAt data hc hab hOne vertex v).card ≤ 1).card =
      ∑ v ∈ fibreJunctions data hc hab hOne vertex,
        (if (internalAt data hc hab hOne vertex v).card ≤ 1 then 1 else 0) :=
    Finset.card_filter _ _
  have hFilterZero : ((fibreJunctions data hc hab hOne vertex).filter fun v ↦
      (internalAt data hc hab hOne vertex v).card = 0).card =
      ∑ v ∈ fibreJunctions data hc hab hOne vertex,
        (if (internalAt data hc hab hOne vertex v).card = 0 then 1 else 0) :=
    Finset.card_filter _ _
  have hSum : (∑ v ∈ fibreJunctions data hc hab hOne vertex,
        (internalAt data hc hab hOne vertex v).card) +
      (∑ v ∈ fibreJunctions data hc hab hOne vertex,
        (if (internalAt data hc hab hOne vertex v).card ≤ 1 then 1 else 0)) +
      (∑ v ∈ fibreJunctions data hc hab hOne vertex,
        (if (internalAt data hc hab hOne vertex v).card = 0 then 1 else 0))
      ≤ 2 * (fibreJunctions data hc hab hOne vertex).card := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc (∑ v ∈ fibreJunctions data hc hab hOne vertex,
            ((internalAt data hc hab hOne vertex v).card +
              (if (internalAt data hc hab hOne vertex v).card ≤ 1 then 1 else 0) +
              (if (internalAt data hc hab hOne vertex v).card = 0 then 1 else 0)))
        ≤ ∑ _v ∈ fibreJunctions data hc hab hOne vertex, 2 := by
          refine Finset.sum_le_sum ?_
          intro v hv
          have hTwo := ((mem_fibreJunctions data hc hab hOne vertex v).mp hv).2
          have hLe := card_internalAt_le data hc hab hOne vertex v
          rw [hTwo] at hLe
          split_ifs <;> omega
      _ = 2 * (fibreJunctions data hc hab hOne vertex).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

/-- The `k = 0` case, with the degenerate fibre folded in. -/
theorem card_internalEdges_add_card_isolated_le
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    (internalEdges data hc hab hOne vertex).card +
        ((fibreJunctions data hc hab hOne vertex).filter fun v ↦
          (internalAt data hc hab hOne vertex v).card = 0).card ≤
      (fibreJunctions data hc hab hOne vertex).card := by
  classical
  rcases (internalEdges data hc hab hOne vertex).eq_empty_or_nonempty with hEmpty | hNonempty
  · rw [hEmpty, Finset.card_empty, zero_add]
    exact Finset.card_filter_le _ _
  have h := card_internalEdges_add_le_aux data hc hab hOne vertex hNonempty 0
    (by simpa using componentCount_junctionGraph_le data hc hab hOne hMetric vertex hNonempty)
  omega

/-- **The fibre has at least as many divalent constituents as it has surviving
contracted occurrences.** -/
theorem card_internalEdges_le_card_fibreJunctions
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (vertex : (contractDatum data hc hab hOne).SourceVertex) :
    (internalEdges data hc hab hOne vertex).card ≤
      (fibreJunctions data hc hab hOne vertex).card := by
  have h := card_internalEdges_add_card_isolated_le data hc hab hOne hMetric vertex
  omega

/-- Every active constituent of a wall fibre is divalent or a branch. -/
theorem branchFilter_eq
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1) :
    (activeFibreVertices data hc hab hOne vertex).filter
        (fun v ↦ ¬ nonDanglingValency data v = 2)
      = (activeFibreVertices data hc hab hOne vertex).filter
        (fun v ↦ nonDanglingValency data v = 3) := by
  classical
  refine Finset.filter_congr ?_
  intro v hv
  have hNe0 := ((mem_activeFibreVertices data hc hab hOne vertex v).mp hv).2
  have hLe := hTrivalentUp v
  have hNe1 := hNeOne v
  omega

/-- **At most one branch constituent per wall fibre**, and none at all if some
divalent constituent of the fibre carries no contracted survivor. -/
theorem card_branch_add_card_isolated_le_one
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty) :
    ((activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).filter
        fun v ↦ nonDanglingValency data v = 3).card +
      ((fibreJunctions data hc hab hOne (mergedVertex data hc hab hOne block)).filter
        fun v ↦ (internalAt data hc hab hOne
          (mergedVertex data hc hab hOne block) v).card = 0).card ≤ 1 := by
  classical
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card
    data hc hab hOne hForest block hNonempty
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block))
    (p := fun v ↦ nonDanglingValency data v = 2)
  rw [branchFilter_eq data hc hab hOne _ hTrivalentUp hNeOne] at hSplit
  have hLe := card_internalEdges_add_card_isolated_le data hc hab hOne hMetric
    (mergedVertex data hc hab hOne block)
  rw [fibreJunctions] at hLe ⊢
  omega

/-- **At most one branch constituent per wall fibre.** -/
theorem card_branch_le_one
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty) :
    ((activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block)).filter
      fun v ↦ nonDanglingValency data v = 3).card ≤ 1 := by
  have h := card_branch_add_card_isolated_le_one data hc hab hOne hMetric hForest
    hTrivalentUp hNeOne block hNonempty
  omega

/-- **An active wall fibre is at least divalent in the limit.**  Its
constituents each carry at least two survivors, and its tree count leaves one
more constituent than contracted survivor, so at least two survivors are
boundary ones. -/
theorem two_le_nonDanglingValency_mergedVertex
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    (block : (mergedPartition data a b).Blocks)
    (hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty) :
    2 ≤ nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) := by
  classical
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card
    data hc hab hOne hForest block hNonempty
  have hCount := sum_nonDanglingValency_activeFibre data hc hab hOne hCompat
    (mergedVertex data hc hab hOne block)
  have hLower : 2 * (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).card ≤
      ∑ w ∈ activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block),
        nonDanglingValency data w := by
    calc 2 * (activeFibreVertices data hc hab hOne
          (mergedVertex data hc hab hOne block)).card
        = ∑ _w ∈ activeFibreVertices data hc hab hOne
            (mergedVertex data hc hab hOne block), 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ w ∈ activeFibreVertices data hc hab hOne
            (mergedVertex data hc hab hOne block), nonDanglingValency data w := by
          refine Finset.sum_le_sum ?_
          intro w hw
          have hNe0 := ((mem_activeFibreVertices data hc hab hOne _ w).mp hw).2
          have hNe1 := hNeOne w
          omega
  omega

/-- **The limit valency of a merged wall vertex is two plus its number of
branch constituents.**  This is `PrunedFibreTree.nonDanglingValency_mergedVertex_eq_sum`
with the excesses evaluated: an active constituent has surviving valency `2`
or `3`, so it contributes `0` or `1`. -/
theorem nonDanglingValency_mergedVertex_eq_card_branch_add_two
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    (block : (mergedPartition data a b).Blocks)
    (hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0) :
    nonDanglingValency (contractDatum data hc hab hOne)
        (mergedVertex data hc hab hOne block) =
      ((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
        fun v ↦ nonDanglingValency data v = 3).card + 2 := by
  classical
  have hFormula := nonDanglingValency_mergedVertex_eq_sum data hc hab hOne hCompat
    hForest block hNonzero
  have hSumSplit := Finset.sum_filter_add_sum_filter_not
    (activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block))
    (fun v ↦ nonDanglingValency data v = 2)
    (fun v ↦ ((nonDanglingValency data v : ℤ) - 2))
  rw [branchFilter_eq data hc hab hOne _ hTrivalentUp hNeOne] at hSumSplit
  have hZeroPart : (∑ x ∈ (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
        (fun v ↦ nonDanglingValency data v = 2),
      ((nonDanglingValency data x : ℤ) - 2)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
    norm_num
  have hOnePart : (∑ x ∈ (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
        (fun v ↦ nonDanglingValency data v = 3),
      ((nonDanglingValency data x : ℤ) - 2)) =
      (((activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
        (fun v ↦ nonDanglingValency data v = 3)).card : ℤ) := by
    have hTerm : ∀ x ∈ (activeFibreVertices data hc hab hOne
        (mergedVertex data hc hab hOne block)).filter
        (fun v ↦ nonDanglingValency data v = 3),
        ((nonDanglingValency data x : ℤ) - 2) = 1 := by
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
      norm_num
    rw [Finset.sum_congr rfl hTerm, Finset.sum_const, nsmul_eq_mul, mul_one]
  omega

/-- **The merged wall vertex is at most trivalent.** -/
theorem nonDanglingValency_mergedVertex_le_three
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    (block : (mergedPartition data a b).Blocks) :
    nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≤ 3 := by
  classical
  by_cases hZero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 0
  · omega
  have hNonempty := activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero
    data hc hab hOne hCompat _ hZero
  have hEq := nonDanglingValency_mergedVertex_eq_card_branch_add_two data hc hab hOne
    hCompat hForest hTrivalentUp hNeOne block hZero
  have hBranch := card_branch_le_one data hc hab hOne hMetric hForest hTrivalentUp
    hNeOne block hNonempty
  omega

/-- **A wall fibre with a divalent constituent carrying no contracted survivor
is divalent in the limit.**  This is the case in which an incoming stable class
merely touches the fibre at one constituent; the limit valency `2` is what makes
its two occurrences consecutive again downstairs. -/
theorem nonDanglingValency_mergedVertex_eq_two_of_isolated_junction
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    (block : (mergedPartition data a b).Blocks)
    {v : data.SourceVertex}
    (hv : v ∈ fibreJunctions data hc hab hOne (mergedVertex data hc hab hOne block))
    (hFree : (internalAt data hc hab hOne (mergedVertex data hc hab hOne block) v).card = 0) :
    nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 2 := by
  classical
  have hActive : v ∈ activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block) := by
    rw [fibreJunctions, Finset.mem_filter] at hv
    exact hv.1
  have hNonempty : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty := ⟨v, hActive⟩
  have hIsolated : 0 < ((fibreJunctions data hc hab hOne
      (mergedVertex data hc hab hOne block)).filter fun w ↦
      (internalAt data hc hab hOne (mergedVertex data hc hab hOne block) w).card = 0).card :=
    Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hFree⟩⟩
  have hBound := card_branch_add_card_isolated_le_one data hc hab hOne hMetric hForest
    hTrivalentUp hNeOne block hNonempty
  have hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0 := by
    have := two_le_nonDanglingValency_mergedVertex data hc hab hOne hCompat hForest
      hNeOne block hNonempty
    omega
  have hEq := nonDanglingValency_mergedVertex_eq_card_branch_add_two data hc hab hOne
    hCompat hForest hTrivalentUp hNeOne block hNonzero
  omega

/-- **A wall fibre whose junction graph has a component with two exits is
divalent in the limit.**  This is the configuration in which an incoming stable
class enters the fibre at one exit and leaves it at another; the limit valency
`2` is exactly what makes the two boundary occurrences consecutive again
downstairs, so the class is not split. -/
theorem nonDanglingValency_mergedVertex_eq_two_of_two_exits
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    (block : (mergedPartition data a b).Blocks)
    (hNonempty : (internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty)
    {v w : data.SourceVertex}
    (hv : v ∈ (fibreJunctions data hc hab hOne
      (mergedVertex data hc hab hOne block)).filter fun u ↦
        (internalAt data hc hab hOne (mergedVertex data hc hab hOne block) u).card ≤ 1)
    (hw : w ∈ (fibreJunctions data hc hab hOne
      (mergedVertex data hc hab hOne block)).filter fun u ↦
        (internalAt data hc hab hOne (mergedVertex data hc hab hOne block) u).card ≤ 1)
    (hne : v ≠ w)
    (hSame : component (junctionGraph data hc hab hOne
          (mergedVertex data hc hab hOne block) hNonempty)
        (Sum.inr ⟨v, Finset.mem_of_mem_filter _ hv⟩)
      = component (junctionGraph data hc hab hOne
          (mergedVertex data hc hab hOne block) hNonempty)
        (Sum.inr ⟨w, Finset.mem_of_mem_filter _ hw⟩)) :
    nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 2 := by
  classical
  have hLt := componentCount_junctionGraph_lt data hc hab hOne hMetric
    (mergedVertex data hc hab hOne block) hNonempty hv hw hne hSame
  have hCount := card_internalEdges_add_le_aux data hc hab hOne
    (mergedVertex data hc hab hOne block) hNonempty 1 hLt
  have hvJ : v ∈ fibreJunctions data hc hab hOne (mergedVertex data hc hab hOne block) :=
    Finset.mem_of_mem_filter _ hv
  have hActive : (activeFibreVertices data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty := by
    rw [fibreJunctions, Finset.mem_filter] at hvJ
    exact ⟨v, hvJ.1⟩
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card
    data hc hab hOne hForest block hActive
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := activeFibreVertices data hc hab hOne (mergedVertex data hc hab hOne block))
    (p := fun v ↦ nonDanglingValency data v = 2)
  rw [branchFilter_eq data hc hab hOne _ hTrivalentUp hNeOne] at hSplit
  rw [fibreJunctions] at hCount
  have hNonzero : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) ≠ 0 := by
    have := two_le_nonDanglingValency_mergedVertex data hc hab hOne hCompat hForest
      hNeOne block hActive
    omega
  have hEq := nonDanglingValency_mergedVertex_eq_card_branch_add_two data hc hab hOne
    hCompat hForest hTrivalentUp hNeOne block hNonzero
  omega

/-- **`hTrivalent`, in the exact form `IncomingSourceCases.exists_classification`
takes it**, from the fibre bound. -/
theorem trivalent_wallBlocks
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1) :
    ∀ sourceBlock : W4Assembly.WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ sourceBlock)
        ≤ 3 := by
  intro sourceBlock
  have hRepr : (mergedPartition data a b).repr sourceBlock.1 = sourceBlock.1 := by
    rw [← contractDatum_vertexPartition_merge data hc hab hOne]
    exact sourceBlock.2
  have hEq : WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ sourceBlock
      = mergedVertex data hc hab hOne ⟨sourceBlock.1, hRepr⟩ :=
    Subtype.ext (Prod.ext rfl sourceBlock.2)
  rw [hEq]
  exact nonDanglingValency_mergedVertex_le_three data hc hab hOne hMetric hCompat
    hForest hTrivalentUp hNeOne ⟨sourceBlock.1, hRepr⟩

/-! ## `hStable`, surjective half -/

/-- **No stable class of the incoming datum is swallowed by the wall.**  The
canonical lift `PrunedFibreStablePath.stablePathLift` from limit classes to
incoming classes is surjective: the wall metric keeps, in every incoming class,
an occurrence away from the contracted target edge, and that occurrence still
survives downstairs. -/
theorem stablePathLift_surjective
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hConnected : graph_connected data.sourceGraph)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted) :
    Function.Surjective
      (PrunedFibreStablePath.stablePathLift data hc hab hOne hConnected hCompat hForest) := by
  intro path
  obtain ⟨edge, hEdge⟩ := Quot.exists_rep path
  obtain ⟨first, hPath, hNe⟩ := hMetric edge
  have hSurvives : ¬ IsDangling (contractDatum data hc hab hOne)
      (sourceEdgeMap data hc hab hOne ⟨first.1, hNe⟩) :=
    fun hBad ↦ first.2 (hCompat.2 ⟨first.1, hNe⟩ hBad)
  refine ⟨NonDanglingEdge.stablePath
    ⟨sourceEdgeMap data hc hab hOne ⟨first.1, hNe⟩, hSurvives⟩, ?_⟩
  have hEmbed : nonDanglingEmbedding data hCompat.1
      ⟨sourceEdgeMap data hc hab hOne ⟨first.1, hNe⟩, hSurvives⟩ = first :=
    Subtype.ext (sourceEdgeEmbedding_sourceEdgeMap data hc hab hOne ⟨first.1, hNe⟩)
  have hFinal : (nonDanglingEmbedding data hCompat.1
      ⟨sourceEdgeMap data hc hab hOne ⟨first.1, hNe⟩, hSurvives⟩).stablePath = path := by
    rw [hEmbed]
    exact hPath.trans hEdge
  exact hFinal

/-! ## `hStable`, injective half -/

/-- A surviving occurrence away from the contracted target occurrence, read as
a surviving occurrence of the contracted datum.  This is the inverse of
`WallDegeneration.nonDanglingEmbedding` on its image; `DanglingReflected` is
exactly what makes it land among the survivors. -/
noncomputable def descend (hCompat : DanglingCompatible data hc hab hOne)
    (f : NonDanglingEdge data) (hf : f.1.1.1 ≠ contracted) :
    NonDanglingEdge (contractDatum data hc hab hOne) :=
  ⟨sourceEdgeMap data hc hab hOne ⟨f.1, hf⟩, fun hBad ↦ f.2 (hCompat.2 ⟨f.1, hf⟩ hBad)⟩

@[simp] theorem nonDanglingEmbedding_descend
    (hCompat : DanglingCompatible data hc hab hOne)
    (f : NonDanglingEdge data) (hf : f.1.1.1 ≠ contracted) :
    nonDanglingEmbedding data hCompat.1 (descend data hc hab hOne hCompat f hf) = f :=
  Subtype.ext (sourceEdgeEmbedding_sourceEdgeMap data hc hab hOne ⟨f.1, hf⟩)

/-- The embedded image of a limit survivor never lies over the contracted
target occurrence. -/
theorem nonDanglingEmbedding_ne_contracted
    (hPreserved : DanglingPreserved data hc hab hOne)
    (e : NonDanglingEdge (contractDatum data hc hab hOne)) :
    (nonDanglingEmbedding data hPreserved e).1.1.1 ≠ contracted :=
  sourceEdgeEmbedding_ne_contracted data hc hab hOne e.1

@[simp] theorem descend_nonDanglingEmbedding
    (hCompat : DanglingCompatible data hc hab hOne)
    (e : NonDanglingEdge (contractDatum data hc hab hOne))
    (he : (nonDanglingEmbedding data hCompat.1 e).1.1.1 ≠ contracted) :
    descend data hc hab hOne hCompat (nonDanglingEmbedding data hCompat.1 e) he = e := by
  refine nonDanglingEmbedding_injective data hCompat.1 ?_
  exact nonDanglingEmbedding_descend data hc hab hOne hCompat _ he

/-- Descending preserves incidence. -/
theorem incident_descend (hCompat : DanglingCompatible data hc hab hOne)
    {f : NonDanglingEdge data} (hf : f.1.1.1 ≠ contracted)
    {v : data.SourceVertex} (hInc : Incident data f.1 v) :
    Incident (contractDatum data hc hab hOne)
      (descend data hc hab hOne hCompat f hf).1
      (sourceVertexMap data hc hab hOne v) :=
  incident_sourceEdgeMap data hc hab hOne ⟨f.1, hf⟩ hInc

/-- **Two survivors meeting a divalent limit vertex descend into one limit
stable class.**  This is the single mechanism by which the two local
obstructions above are turned into non-splitting. -/
theorem stablePath_descend_eq_of_divalent
    (hCompat : DanglingCompatible data hc hab hOne)
    {f g : NonDanglingEdge data} (hf : f.1.1.1 ≠ contracted)
    (hg : g.1.1.1 ≠ contracted) {v w : data.SourceVertex}
    (hfv : Incident data f.1 v) (hgw : Incident data g.1 w)
    (hvw : sourceVertexMap data hc hab hOne v = sourceVertexMap data hc hab hOne w)
    (hTwo : nonDanglingValency (contractDatum data hc hab hOne)
      (sourceVertexMap data hc hab hOne v) = 2) :
    (descend data hc hab hOne hCompat f hf).stablePath =
      (descend data hc hab hOne hCompat g hg).stablePath := by
  refine PrunedFibreStablePath.stablePath_eq_of_incident_divalent
    (contractDatum data hc hab hOne) _ _ (sourceVertexMap data hc hab hOne v)
    (incident_descend data hc hab hOne hCompat hf hfv) ?_ hTwo
  rw [hvw]
  exact incident_descend data hc hab hOne hCompat hg hgw

/-- A source vertex over an end of the contracted target occurrence lies in
the fibre of a merged vertex. -/
theorem exists_mergedVertex_eq {v : data.SourceVertex} (hv : v.1.1 = a ∨ v.1.1 = b) :
    ∃ block : (mergedPartition data a b).Blocks,
      sourceVertexMap data hc hab hOne v = mergedVertex data hc hab hOne block := by
  refine ⟨(mergedPartition data a b).toBlock v.1.2, ?_⟩
  have hMem := (mem_fibreVertices_mergedVertex_iff data hc hab hOne
    ((mergedPartition data a b).toBlock v.1.2) v).mpr ⟨hv, rfl⟩
  rwa [mem_fibreVertices] at hMem

include hc in
/-- The first endpoint of an occurrence over the contracted target occurrence
lies over `a`. -/
theorem sourceEnds_fst_over_left (e : data.SourceEdge) (he : e.1.1 = contracted) :
    (data.sourceEnds e).1.1.1 = a := by
  show (e.1.1 : target.V × target.V).1 = a
  rw [he, hc]

/-- **A divalent source vertex carrying no contracted survivor stays divalent
in the limit.**  Away from the wall this is
`WallDegeneration.nonDanglingValency_sourceVertexMap`; at the wall it is the
isolated-junction obstruction. -/
theorem nonDanglingValency_sourceVertexMap_eq_two
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    {v : data.SourceVertex} (hTwo : nonDanglingValency data v = 2)
    (hFree : ∀ e ∈ nonDanglingIncident data v, e.1.1 ≠ contracted) :
    nonDanglingValency (contractDatum data hc hab hOne)
      (sourceVertexMap data hc hab hOne v) = 2 := by
  classical
  by_cases hv : v.1.1 = a ∨ v.1.1 = b
  · obtain ⟨block, hBlock⟩ := exists_mergedVertex_eq data hc hab hOne hv
    rw [hBlock]
    refine nonDanglingValency_mergedVertex_eq_two_of_isolated_junction data hc hab hOne
      hMetric hCompat hForest hTrivalentUp hNeOne block
      ((mem_fibreJunctions data hc hab hOne _ v).mpr ⟨hBlock, hTwo⟩) ?_
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [mem_internalAt] at he
    obtain ⟨heSurv, heTarget, -⟩ :=
      (mem_internalEdges data hc hab hOne _ e).mp he.1
    exact hFree e ((mem_nonDanglingIncident data v e).mpr ⟨heSurv, he.2⟩) heTarget
  · rw [not_or] at hv
    rw [nonDanglingValency_sourceVertexMap data hCompat v hv.1 hv.2]
    exact hTwo

/-- **Every chain of contracted survivors has an exit.**  If it did not, the
whole stable class of the chain would consist of occurrences over the
contracted target occurrence, which the wall metric forbids.  No graph
machinery is needed: the first non-contracted neighbour met along the chain is
already an exit. -/
theorem exists_chainExit
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (g : NonDanglingEdge data) (hg : g.1.1.1 = contracted) :
    ∃ f : NonDanglingEdge data, f.1.1.1 ≠ contracted ∧
      ChainExit data contracted g f := by
  by_contra hNo
  push Not at hNo
  let C : NonDanglingEdge data → Prop := fun f ↦
    f.1.1.1 = contracted ∧ Relation.ReflTransGen (InternalStep data contracted) g f
  have hStep : ∀ p q : NonDanglingEdge data, Consecutive data p q → C p → C q := by
    rintro p q ⟨-, w, hpw, hqw, hwTwo⟩ ⟨hpC, hpChain⟩
    have hqC : q.1.1.1 = contracted := by
      by_contra hqNe
      exact hNo q hqNe ⟨p, hpChain, w, hpw, hqw, hwTwo⟩
    exact ⟨hqC, hpChain.tail ⟨hpC, hqC, w, hpw, hqw, hwTwo⟩⟩
  have hIff : ∀ p q : NonDanglingEdge data,
      Relation.EqvGen (Consecutive data) p q → (C p ↔ C q) := by
    intro p q h
    induction h with
    | rel x y hxy => exact ⟨hStep x y hxy, hStep y x (consecutive_symm hxy)⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  have hCg : C g := ⟨hg, Relation.ReflTransGen.refl⟩
  obtain ⟨f, hfPath, hfNe⟩ := hMetric g
  exact hfNe ((hIff f g ((stablePath_eq_iff f g).mp hfPath)).mpr hCg).1

/-- A chain of contracted survivors stays inside one fibre, and is a walk of
that fibre's junction graph. -/
theorem reach_junctionGraph_of_reflTransGen
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty)
    {first last : NonDanglingEdge data}
    (hFirst : first.1 ∈ internalEdges data hc hab hOne vertex)
    (hChain : Relation.ReflTransGen (InternalStep data contracted) first last) :
    ∃ h : last.1 ∈ internalEdges data hc hab hOne vertex,
      Reach (junctionGraph data hc hab hOne vertex hNonempty)
        (Sum.inl ⟨first.1, hFirst⟩) (Sum.inl ⟨last.1, h⟩) := by
  classical
  induction hChain with
  | refl => exact ⟨hFirst, reach_refl _ _⟩
  | @tail p q hChainPrev hStep ih =>
      obtain ⟨hp, hReach⟩ := ih
      obtain ⟨-, hqC, w, hpw, hqw, hwTwo⟩ := hStep
      obtain ⟨-, hpTarget, hpMap⟩ :=
        (mem_internalEdges data hc hab hOne vertex p.1).mp hp
      have hMapsP :=
        sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne p.1 hpTarget
      have hwMap : sourceVertexMap data hc hab hOne w = vertex := by
        rcases hpw with h | h
        · rw [← h]; exact hpMap
        · rw [← h, ← hMapsP]; exact hpMap
      have hwJ : w ∈ fibreJunctions data hc hab hOne vertex :=
        (mem_fibreJunctions data hc hab hOne vertex w).mpr ⟨hwMap, hwTwo⟩
      have hqMem : q.1 ∈ internalEdges data hc hab hOne vertex := by
        rw [mem_internalEdges]
        refine ⟨q.2, hqC, ?_⟩
        have hMapsQ :=
          sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne q.1 hqC
        rcases hqw with h | h
        · rw [h]; exact hwMap
        · rw [hMapsQ, h]; exact hwMap
      refine ⟨hqMem, reach_trans (reach_trans hReach
        (reach_junctionGraph data hc hab hOne vertex hNonempty ⟨p.1, hp⟩ ⟨w, hwJ⟩ hpw))
        (reach_symm (reach_junctionGraph data hc hab hOne vertex hNonempty
          ⟨q.1, hqMem⟩ ⟨w, hwJ⟩ hqw))⟩

/-- **An exit of a chain is an exit of the junction graph**, reachable in it
from the chain's start, and it carries a contracted survivor. -/
theorem exists_exit_of_chainExit
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hNonempty : (internalEdges data hc hab hOne vertex).Nonempty)
    {g f : NonDanglingEdge data}
    (hg : g.1 ∈ internalEdges data hc hab hOne vertex)
    (hf : f.1.1.1 ≠ contracted) (hChain : ChainExit data contracted g f) :
    ∃ v : data.SourceVertex, Incident data f.1 v ∧
      nonDanglingValency data v = 2 ∧
      (internalAt data hc hab hOne vertex v).Nonempty ∧
      ∃ hv : v ∈ (fibreJunctions data hc hab hOne vertex).filter fun u ↦
          (internalAt data hc hab hOne vertex u).card ≤ 1,
        Reach (junctionGraph data hc hab hOne vertex hNonempty)
          (Sum.inl ⟨g.1, hg⟩)
          (Sum.inr ⟨v, Finset.mem_of_mem_filter _ hv⟩) := by
  classical
  obtain ⟨last, hChainRel, v, hlastInc, hfInc, hvTwo⟩ := hChain
  obtain ⟨hlast, hReach⟩ := reach_junctionGraph_of_reflTransGen data hc hab hOne
    vertex hNonempty hg hChainRel
  obtain ⟨-, hlastTarget, hlastMap⟩ :=
    (mem_internalEdges data hc hab hOne vertex last.1).mp hlast
  have hMaps :=
    sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne last.1 hlastTarget
  have hvMap : sourceVertexMap data hc hab hOne v = vertex := by
    rcases hlastInc with h | h
    · rw [← h]; exact hlastMap
    · rw [← h, ← hMaps]; exact hlastMap
  have hvJ : v ∈ fibreJunctions data hc hab hOne vertex :=
    (mem_fibreJunctions data hc hab hOne vertex v).mpr ⟨hvMap, hvTwo⟩
  have hlastAt : last.1 ∈ internalAt data hc hab hOne vertex v :=
    (mem_internalAt data hc hab hOne vertex v last.1).mpr ⟨hlast, hlastInc⟩
  have hfMem : f.1 ∈ nonDanglingIncident data v :=
    (mem_nonDanglingIncident data v f.1).mpr ⟨f.2, hfInc⟩
  have hCard : (internalAt data hc hab hOne vertex v).card ≤ 1 := by
    have hSub : internalAt data hc hab hOne vertex v ⊆
        (nonDanglingIncident data v).erase f.1 := by
      intro e he
      rw [mem_internalAt] at he
      obtain ⟨heSurv, heTarget, -⟩ :=
        (mem_internalEdges data hc hab hOne vertex e).mp he.1
      refine Finset.mem_erase.mpr ⟨fun hBad ↦ hf (hBad ▸ heTarget), ?_⟩
      exact (mem_nonDanglingIncident data v e).mpr ⟨heSurv, he.2⟩
    have hLe := Finset.card_le_card hSub
    rw [Finset.card_erase_of_mem hfMem, card_nonDanglingIncident, hvTwo] at hLe
    omega
  refine ⟨v, hfInc, hvTwo, ⟨last.1, hlastAt⟩,
    Finset.mem_filter.mpr ⟨hvJ, hCard⟩, ?_⟩
  exact reach_trans hReach (reach_junctionGraph data hc hab hOne vertex hNonempty
    ⟨last.1, hlast⟩ ⟨v, hvJ⟩ hlastInc)

/-- **The chain of a contracted survivor determines one limit stable class.**
Two exits of the same chain descend into the same limit class: either they sit
at the same junction, where a divalent junction with a contracted survivor has
only one non-contracted survivor left, or they sit at two junctions of one
component of the junction graph, and then the merged vertex is divalent
(`nonDanglingValency_mergedVertex_eq_two_of_two_exits`). -/
theorem stablePath_descend_eq_of_chainExit
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    {g f f' : NonDanglingEdge data} (hg : g.1.1.1 = contracted)
    (hf : f.1.1.1 ≠ contracted) (hf' : f'.1.1.1 ≠ contracted)
    (hChain : ChainExit data contracted g f)
    (hChain' : ChainExit data contracted g f') :
    (descend data hc hab hOne hCompat f hf).stablePath =
      (descend data hc hab hOne hCompat f' hf').stablePath := by
  classical
  obtain ⟨block, hBlock⟩ := exists_mergedVertex_eq data hc hab hOne
    (Or.inl (sourceEnds_fst_over_left data hc g.1 hg))
  have hgMem : g.1 ∈ internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block) :=
    (mem_internalEdges data hc hab hOne _ g.1).mpr ⟨g.2, hg, hBlock⟩
  have hNonempty : (internalEdges data hc hab hOne
      (mergedVertex data hc hab hOne block)).Nonempty := ⟨g.1, hgMem⟩
  obtain ⟨v, hfInc, hvTwo, hvInternal, hv, hReach⟩ :=
    exists_exit_of_chainExit data hc hab hOne _ hNonempty hgMem hf hChain
  obtain ⟨v', hf'Inc, hv'Two, hv'Internal, hv', hReach'⟩ :=
    exists_exit_of_chainExit data hc hab hOne _ hNonempty hgMem hf' hChain'
  by_cases hvv : v = v'
  · subst hvv
    obtain ⟨e, heAt⟩ := hvInternal
    rw [mem_internalAt] at heAt
    obtain ⟨heSurv, heTarget, -⟩ :=
      (mem_internalEdges data hc hab hOne _ e).mp heAt.1
    have hfMem : f.1 ∈ nonDanglingIncident data v :=
      (mem_nonDanglingIncident data v f.1).mpr ⟨f.2, hfInc⟩
    have hf'Mem : f'.1 ∈ nonDanglingIncident data v :=
      (mem_nonDanglingIncident data v f'.1).mpr ⟨f'.2, hf'Inc⟩
    have heMem : e ∈ nonDanglingIncident data v :=
      (mem_nonDanglingIncident data v e).mpr ⟨heSurv, heAt.2⟩
    have hef : e ≠ f.1 := fun hBad ↦ hf (hBad ▸ heTarget)
    have hef' : e ≠ f'.1 := fun hBad ↦ hf' (hBad ▸ heTarget)
    have hff' : f.1 = f'.1 := by
      by_contra hNe
      have hSub : ({f.1, f'.1, e} : Finset data.SourceEdge) ⊆
          nonDanglingIncident data v := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfMem
        · exact hf'Mem
        · exact heMem
      have hCard : ({f.1, f'.1, e} : Finset data.SourceEdge).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact fun hx ↦ hx.elim hNe fun hy ↦ hef hy.symm),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]
            exact fun hx ↦ hef' hx.symm), Finset.card_singleton]
      have hLe := Finset.card_le_card hSub
      rw [hCard, card_nonDanglingIncident, hvTwo] at hLe
      omega
    have hfEq : f = f' := Subtype.ext hff'
    subst hfEq
    rfl
  · have hSame : component (junctionGraph data hc hab hOne
          (mergedVertex data hc hab hOne block) hNonempty)
        (Sum.inr ⟨v, Finset.mem_of_mem_filter _ hv⟩)
      = component (junctionGraph data hc hab hOne
          (mergedVertex data hc hab hOne block) hNonempty)
        (Sum.inr ⟨v', Finset.mem_of_mem_filter _ hv'⟩) :=
      (component_eq_of_reach hReach).symm.trans (component_eq_of_reach hReach')
    have hTwo := nonDanglingValency_mergedVertex_eq_two_of_two_exits data hc hab hOne
      hMetric hCompat hForest hTrivalentUp hNeOne block hNonempty hv hv' hvv hSame
    have hvMap : sourceVertexMap data hc hab hOne v =
        mergedVertex data hc hab hOne block :=
      ((mem_fibreJunctions data hc hab hOne _ v).mp
        (Finset.mem_of_mem_filter _ hv)).1
    have hv'Map : sourceVertexMap data hc hab hOne v' =
        mergedVertex data hc hab hOne block :=
      ((mem_fibreJunctions data hc hab hOne _ v').mp
        (Finset.mem_of_mem_filter _ hv')).1
    refine stablePath_descend_eq_of_divalent data hc hab hOne hCompat hf hf'
      hfInc hf'Inc (hvMap.trans hv'Map.symm) ?_
    rw [hvMap]
    exact hTwo

/-- **The limit stable class attached to an incoming survivor.**  Away from the
contracted target occurrence it is the class of the occurrence itself; over it,
the class of any exit of the occurrence's chain, which
`stablePath_descend_eq_of_chainExit` shows does not depend on the exit. -/
noncomputable def exitClass
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne) (g : NonDanglingEdge data) :
    StablePath (contractDatum data hc hab hOne) :=
  if hg : g.1.1.1 = contracted then
    (descend data hc hab hOne hCompat
      (exists_chainExit data hMetric g hg).choose
      (exists_chainExit data hMetric g hg).choose_spec.1).stablePath
  else (descend data hc hab hOne hCompat g hg).stablePath

theorem exitClass_of_ne_contracted
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne) (g : NonDanglingEdge data)
    (hg : g.1.1.1 ≠ contracted) :
    exitClass data hc hab hOne hMetric hCompat g =
      (descend data hc hab hOne hCompat g hg).stablePath := by
  rw [exitClass, dite_eq_right hg]

theorem exitClass_eq_of_chainExit
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    {g f : NonDanglingEdge data} (hg : g.1.1.1 = contracted)
    (hf : f.1.1.1 ≠ contracted) (hChain : ChainExit data contracted g f) :
    exitClass data hc hab hOne hMetric hCompat g =
      (descend data hc hab hOne hCompat f hf).stablePath := by
  rw [exitClass, dite_eq_left hg]
  exact stablePath_descend_eq_of_chainExit data hc hab hOne hMetric hCompat hForest
    hTrivalentUp hNeOne hg _ hf
    (exists_chainExit data hMetric g hg).choose_spec.2 hChain

/-- **The attached limit class is constant along incoming stable classes.**
Both of the two ways in which an incoming class can cross a wall fibre are
covered: a class passing straight through a junction stays on one chain, and a
class touching a fibre only at a divalent constituent with no contracted
survivor meets a divalent limit vertex. -/
theorem exitClass_eq_of_consecutive
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1)
    {p q : NonDanglingEdge data} (h : Consecutive data p q) :
    exitClass data hc hab hOne hMetric hCompat p =
      exitClass data hc hab hOne hMetric hCompat q := by
  classical
  obtain ⟨hne, w, hpw, hqw, hwTwo⟩ := h
  by_cases hp : p.1.1.1 = contracted
  · by_cases hq : q.1.1.1 = contracted
    · obtain ⟨f, hf, hChainQ⟩ := exists_chainExit data hMetric q hq
      rw [exitClass_eq_of_chainExit data hc hab hOne hMetric hCompat hForest
          hTrivalentUp hNeOne hq hf hChainQ,
        exitClass_eq_of_chainExit data hc hab hOne hMetric hCompat hForest
          hTrivalentUp hNeOne hp hf
          (hChainQ.of_internalStep ⟨hp, hq, w, hpw, hqw, hwTwo⟩)]
    · rw [exitClass_eq_of_chainExit data hc hab hOne hMetric hCompat hForest
          hTrivalentUp hNeOne hp hq (chainExit_of_consecutive w hpw hqw hwTwo),
        exitClass_of_ne_contracted data hc hab hOne hMetric hCompat q hq]
  · by_cases hq : q.1.1.1 = contracted
    · rw [exitClass_eq_of_chainExit data hc hab hOne hMetric hCompat hForest
          hTrivalentUp hNeOne hq hp (chainExit_of_consecutive w hqw hpw hwTwo),
        exitClass_of_ne_contracted data hc hab hOne hMetric hCompat p hp]
    · rw [exitClass_of_ne_contracted data hc hab hOne hMetric hCompat p hp,
        exitClass_of_ne_contracted data hc hab hOne hMetric hCompat q hq]
      have hPair : nonDanglingIncident data w = {p.1, q.1} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact (mem_nonDanglingIncident data w p.1).mpr ⟨p.2, hpw⟩
          · exact (mem_nonDanglingIncident data w q.1).mpr ⟨q.2, hqw⟩
        · rw [card_nonDanglingIncident, hwTwo,
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]
              exact fun hBad ↦ hne (Subtype.ext hBad)), Finset.card_singleton]
      refine stablePath_descend_eq_of_divalent data hc hab hOne hCompat hp hq
        hpw hqw rfl ?_
      refine nonDanglingValency_sourceVertexMap_eq_two data hc hab hOne hMetric
        hCompat hForest hTrivalentUp hNeOne hwTwo ?_
      intro e he
      rw [hPair] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hp
      · exact hq

/-- **The left inverse of `PrunedFibreStablePath.stablePathLift`.** -/
noncomputable def stablePathDescend
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1) :
    StablePath data → StablePath (contractDatum data hc hab hOne) :=
  Quot.lift (exitClass data hc hab hOne hMetric hCompat)
    fun _ _ hStep ↦ exitClass_eq_of_consecutive data hc hab hOne hMetric hCompat
      hForest hTrivalentUp hNeOne hStep

/-- **No incoming stable class splits at the wall.**  The canonical lift
`PrunedFibreStablePath.stablePathLift` is injective: `stablePathDescend` is a
left inverse of it. -/
theorem stablePathLift_injective
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hConnected : graph_connected data.sourceGraph)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1) :
    Function.Injective
      (PrunedFibreStablePath.stablePathLift data hc hab hOne hConnected hCompat hForest) := by
  intro first second hEq
  obtain ⟨e, rfl⟩ := Quot.exists_rep first
  obtain ⟨e', rfl⟩ := Quot.exists_rep second
  rw [show (Quot.mk (Consecutive (contractDatum data hc hab hOne)) e) =
      e.stablePath from rfl,
    show (Quot.mk (Consecutive (contractDatum data hc hab hOne)) e') =
      e'.stablePath from rfl,
    PrunedFibreStablePath.stablePathLift_mk,
    PrunedFibreStablePath.stablePathLift_mk] at hEq
  have hClass := congrArg (stablePathDescend data hc hab hOne hMetric hCompat hForest
    hTrivalentUp hNeOne) hEq
  have hExit : exitClass data hc hab hOne hMetric hCompat
        (nonDanglingEmbedding data hCompat.1 e)
      = exitClass data hc hab hOne hMetric hCompat
        (nonDanglingEmbedding data hCompat.1 e') := hClass
  rw [exitClass_of_ne_contracted data hc hab hOne hMetric hCompat _
      (nonDanglingEmbedding_ne_contracted data hc hab hOne hCompat.1 e),
    exitClass_of_ne_contracted data hc hab hOne hMetric hCompat _
      (nonDanglingEmbedding_ne_contracted data hc hab hOne hCompat.1 e'),
    descend_nonDanglingEmbedding, descend_nonDanglingEmbedding] at hExit
  exact hExit

/-- **`hStable`, in full.**  The canonical lift is a bijection, so the limit
stable classes and the incoming stable classes correspond. -/
theorem stablePathLift_bijective
    (hMetric : ∀ e : NonDanglingEdge data, ∃ f : NonDanglingEdge data,
      f.stablePath = e.stablePath ∧ f.1.1.1 ≠ contracted)
    (hConnected : graph_connected data.sourceGraph)
    (hCompat : DanglingCompatible data hc hab hOne)
    (hForest : ContractionForest data a b contracted)
    (hTrivalentUp : ∀ v : data.SourceVertex, nonDanglingValency data v ≤ 3)
    (hNeOne : ∀ v : data.SourceVertex, nonDanglingValency data v ≠ 1) :
    Function.Bijective
      (PrunedFibreStablePath.stablePathLift data hc hab hOne hConnected hCompat hForest) :=
  ⟨stablePathLift_injective data hc hab hOne hMetric hConnected hCompat hForest
      hTrivalentUp hNeOne,
    stablePathLift_surjective data hc hab hOne hMetric hConnected hCompat hForest⟩

end Fibre

/-! ## The decision, at an actual wall event -/

section WallEvent

variable {target : CFGraph.{0}} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- **`hTrivalent` is derivable.**  From a full-dimensional source presentation,
and the metric facts that hold at a wall event -- the dangling-compatibility
receipt being itself a theorem at a wall event, by
`WallAdmissibility.danglingCompatible_of_fullDimensional` -- every merged wall
source vertex has surviving valency at most three.  Nothing is added to the
hypothesis set of `IncomingSourceCases.exists_classification`. -/
theorem trivalent_of_fullDimensional {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ)
    (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec coordinates row ≠ 0)
    (hZero : coordinates (fullDim.labelling.targetEdge.symm contracted) = 0) :
    ∀ sourceBlock : W4Assembly.WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      nonDanglingValency (contractDatum data hc hab hOne)
        (WallBlock.sourceVertex (contractDatum data hc hab hOne) ⟨a, hab⟩ sourceBlock)
        ≤ 3 :=
  trivalent_wallBlocks data hc hab hOne
    (exists_stablePath_eq_target_ne fullDim.labelling coordinates hRows hZero)
    (WallAdmissibility.danglingCompatible_of_fullDimensional data hc hab hOne
      fullDim coordinates hNonnegative hRows hZero)
    (SourceFibreForest.contractionForest_of_fullDimensional
      (data := data) (coordinate := coordinate) fullDim coordinates
      hNonnegative hRows hc hZero)
    fullDim.trivalent
    (nonDanglingValency_ne_one data fullDim.connected)

/-- **`hStable`'s cardinality statement: the inequality surjectivity gives.**
The consumers of `hStable` use it only through
`WallDegeneration.stablePath_card_contractDatum`, i.e. only to know

```
Fintype.card (StablePath (contractDatum data hc hab hOne))
  = (contract target hab hOne).edges.card + 1.
```

Surjectivity of the canonical lift gives the `≥` half outright, from the
full-dimensional stable-path count `Fintype.card (StablePath data) = |E(T)|`
and `WallDegeneration.edge_card_contract`. -/
theorem card_edges_contract_add_one_le_card_stablePath {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ)
    (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec coordinates row ≠ 0)
    (hZero : coordinates (fullDim.labelling.targetEdge.symm contracted) = 0) :
    (GraphContraction.contract target hab hOne).edges.card + 1 ≤
      Fintype.card (StablePath (contractDatum data hc hab hOne)) := by
  have hSurjective := stablePathLift_surjective data hc hab hOne
    (exists_stablePath_eq_target_ne fullDim.labelling coordinates hRows hZero)
    fullDim.connected
    (WallAdmissibility.danglingCompatible_of_fullDimensional data hc hab hOne
      fullDim coordinates hNonnegative hRows hZero)
    (SourceFibreForest.contractionForest_of_fullDimensional
      (data := data) (coordinate := coordinate) fullDim coordinates
      hNonnegative hRows hc hZero)
  have hCard := Fintype.card_le_of_surjective _ hSurjective
  have hUp := fullDim.stablePath_card
  have hEdges := edge_card_contract (target := target) (a := a) (b := b) hab hOne
  omega

/-- **`hStable` is derivable, as the equivalence the march payload carries.**
From a full-dimensional source presentation and the metric facts that hold at a
wall event, the canonical lift
`PrunedFibreStablePath.stablePathLift` is a bijection from the limit stable
classes to the incoming ones.  Nothing is added to the hypothesis set of
`IncomingSourceCases.exists_classification`: the dangling-compatibility receipt
is discharged internally by
`WallAdmissibility.danglingCompatible_of_fullDimensional`. -/
theorem stablePath_equiv {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ)
    (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec coordinates row ≠ 0)
    (hZero : coordinates (fullDim.labelling.targetEdge.symm contracted) = 0) :
    Nonempty (StablePath (contractDatum data hc hab hOne) ≃ StablePath data) :=
  ⟨Equiv.ofBijective _
    (stablePathLift_bijective data hc hab hOne
      (exists_stablePath_eq_target_ne fullDim.labelling coordinates hRows hZero)
      fullDim.connected
      (WallAdmissibility.danglingCompatible_of_fullDimensional data hc hab hOne
        fullDim coordinates hNonnegative hRows hZero)
      (SourceFibreForest.contractionForest_of_fullDimensional
        (data := data) (coordinate := coordinate) fullDim coordinates
        hNonnegative hRows hc hZero)
      fullDim.trivalent
      (nonDanglingValency_ne_one data fullDim.connected))⟩

/-- **The cardinality every consumer of `hStable` actually uses.**  This is
`WallDegeneration.stablePath_card_contractDatum` with its stable-path receipt
discharged. -/
theorem card_stablePath_contractDatum {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    (coordinates : coordinate → ℚ)
    (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ row,
      (GluingDatum.LengthMatrixPresentation.matrix
        fullDim.labelling.presentation).mulVec coordinates row ≠ 0)
    (hZero : coordinates (fullDim.labelling.targetEdge.symm contracted) = 0) :
    Fintype.card (StablePath (contractDatum data hc hab hOne))
      = (GraphContraction.contract target hab hOne).edges.card + 1 :=
  stablePath_card_contractDatum data hc hab hOne fullDim
    (stablePath_equiv data hc hab hOne fullDim coordinates hNonnegative hRows hZero)

end WallEvent



end DraismaVargas.LocalCases.WallAdmissibilityStable
