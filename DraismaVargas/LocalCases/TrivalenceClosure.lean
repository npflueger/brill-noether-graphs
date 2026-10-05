module

public import DraismaVargas.LocalCases.StablePathCount
public import DraismaVargas.LocalCases.DanglingBetti
public import DraismaVargas.LocalCases.FullDimensionalSource

@[expose] public section

/-!
# Trivalence is exactly the Brill--Noether equality

`DraismaVargas/LocalCases/Trivalence.lean` reduces trivalence of the stable
graph to a numerical saturation inequality and two identifications.
`DraismaVargas/LocalCases/StablePathCount.lean` supplies the first
(`∑_{V₃} nd = 2 · #StablePath`) and
`DraismaVargas/LocalCases/DanglingBetti.lean` the second
(`cyclomatic Γ = genus data.sourceGraph`).  This module chains them together
with the `saturated` and `stablePath_card` data of
`FullDimensionalSource.FullDimensionalSourcePresentation` and computes what is
left.

## The chain

Write, over a connected quotient source with `HasPathEnds`,

* `m = #StablePath data`, `E = |E(target)|`,
* `g = genus data.sourceGraph`, `b₁ = cyclomatic (prunedSource data)`,
* `c = componentCount (prunedSource data)`, `z = |V₀|`, `s = |V₃|`,
* `c(H) = c - z` (`stableComponentCount`), the component count of the stable
  graph: every isolated vertex is a component of `Γ` on its own.

The four inputs are

```
m = E                              (stablePath_card)
E = 2 g + 2 degree - 5             (saturated)
b₁ = g                             (DanglingBetti)
m + c = b₁ + z + s                 (StablePathCount, needs HasPathEnds)
```

They determine the vertex count of the stable graph outright,

```
s = g + 2 degree - 5 + c(H)        (card_stableVertices_eq)
```

and the *unconditional* Euler bound `3 s ≤ 2 m` of `Trivalence` then reads

```
2 degree - 5 + 3 c(H) ≤ g          (two_mul_degree_le_genus_sourceGraph)
```

with **no** trivalence input.  Trivalence is the reverse inequality, hence
exactly the equality: `trivalent_iff_genus_eq`.

## The verdict

`2 · #StablePath ≤ 3 · |V₃|` does **not** follow.  It is equivalent, given
everything else the presentation carries, to

```
genus data.sourceGraph = 2 * degree - 5 + 3 * stableComponentCount data,
```

i.e. to `ρ = 0` when the stable graph is connected — the Brill--Noether number
`ρ = g - 2(g - degree + 1) = 2 degree - 2 - g` vanishing.  The counting
identities give only `ρ ≤ 0` (`two_mul_degree_sub_two_le_genus_sourceGraph`),
the usual "a full-dimensional family of degree-`degree` maps forces
`g ≥ 2 degree - 2`".

Nothing among `valid`, `targetConnected`, `targetGenus`, `saturated`,
`labelling`, `det_ne_zero`, `pathEnds` bounds `g` from above in terms of
`degree`: `saturated` *defines* `E` from `g` and `degree`, and the target is
free to be any tree with `E` edges.  The quantity that is unconstrained is
therefore the source genus `g` itself relative to `degree`; what would
constrain it is a genuine geometric input (the Brill--Noether inequality
`ρ ≥ 0`, or an independent identification of `|E(target)|` with `3g - 3`),
not a further count on `Γ`.

The remaining field is `valid`, whose second half is
`GluingDatum.RiemannHurwitz`, and it pushes the same way as everything else.
Read at a source vertex `u` over a target vertex `v`, with `k` the block size
of `u` and `SheetPartition.blockCountWithin` summed over the incident target
occurrences giving the source valency, that field says
`val(u) - 2 ≥ k · (val(v) - 2)`.  Summing over all source vertices, the local
degrees over a fixed target vertex add up to `degree`
(`GluingDatum.sum_sourceVertex_localDegree_over`) and the target is a tree, so
the sum telescopes to `2|E(source)| ≥ 2|V(source)| - 2 degree`, i.e.
`g ≥ 1 - degree`.  Riemann--Hurwitz bounds the source genus from **below**.
The only upper bounds available are the crude `|E(source)| ≤ degree · E` and
`|V(source)| ≥ |V(target)| = E + 1`, giving `g ≤ (degree - 1) E`, which with
`E = 2 g + 2 degree - 5` is again a lower bound on `g` for every
`degree ≥ 2`.  So no field of the structure, alone or combined, bounds `g`
above.

A rescue via isolated vertices and components does not help either:
`noDanglingTargetFibres` — which a full-dimensional presentation does
have — gives exactly `1 ≤ c(H)` (`one_le_stableComponentCount`), and that is
the *wrong direction*: it strengthens the already-provable
`2 degree - 5 + 3 c(H) ≤ g` to `2 degree - 2 ≤ g`, i.e. it makes `ρ ≤ 0`
sharper rather than supplying `ρ ≥ 0`.

What the module does deliver about the structure is a necessary condition:
every `FullDimensionalSourcePresentation` satisfies
`g = 2 degree - 5 + 3 c(H)` exactly (`genus_sourceGraph_eq_of_presentation`),
so with a connected stable graph `g = 2 degree - 2`, `ρ = 0`.  The `trivalent`
field is therefore not redundant; it is equivalent to that equality, and any
construction of an instance of the structure (such as the caterpillar seed,
`CaterpillarRows.fullDim`) must produce it.
-/

namespace DraismaVargas.LocalCases.TrivalenceClosure

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonDanglingValency
open DraismaVargas.LocalCases.PrunedSource
open DraismaVargas.LocalCases.Trivalence
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.LocalCases.DanglingBetti
open DraismaVargas.LocalCases.FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

/-! ## The component count of the stable graph -/

/-- **The number of components of the stable graph `H(M)`.**  Its vertices are
`Trivalence.stableVertices data` and its edges are the stable paths; its
components are the components of the pruned source `Γ` other than the isolated
vertices, each of which is a component of `Γ` on its own
(`Trivalence.component_prunedSource_eq_singleton`). -/
noncomputable def stableComponentCount (data : GluingDatum target degree) : ℤ :=
  (componentCount (prunedSource data) : ℤ) - ((isolatedVertices data).card : ℤ)

/-- The stable graph has a nonnegative number of components. -/
theorem stableComponentCount_nonneg (data : GluingDatum target degree) :
    0 ≤ stableComponentCount data := by
  have h : ((isolatedVertices data).card : ℤ)
      ≤ (componentCount (prunedSource data) : ℤ) := by
    exact_mod_cast card_isolatedVertices_le_componentCount data
  unfold stableComponentCount
  linarith

/-- Over a connected quotient source the pruned source has one component per
deleted dangling occurrence, plus one, so the stable graph has
`1 + #dangling - |V₀|` components. -/
theorem stableComponentCount_eq_card_danglingEdges
    (data : GluingDatum target degree) (hConnected : data.Connected) :
    stableComponentCount data
      = 1 + ((danglingEdges data).card : ℤ)
          - ((isolatedVertices data).card : ℤ) := by
  unfold stableComponentCount
  rw [componentCount_prunedSource data hConnected]
  push_cast
  ring

/-! ### A surviving occurrence makes the stable graph nonempty -/

/-- A source vertex carrying a surviving occurrence is not isolated in the
pruned source. -/
theorem notMem_isolatedVertices_of_mem_nonDanglingEdges
    (data : GluingDatum target degree) {edge : data.SourceEdge}
    (hEdge : edge ∈ nonDanglingEdges data) :
    (data.sourceEnds edge).1 ∉ isolatedVertices data := by
  classical
  rw [mem_isolatedVertices]
  intro hZero
  have hPos : 0 < nonDanglingValency data (data.sourceEnds edge).1 := by
    rw [nonDanglingValency_eq_card_filter]
    refine Finset.card_pos.2 ⟨edge, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(mem_nonDanglingEdges data edge).1 hEdge, incident_left data edge⟩
  omega

/-- **The isolated vertices miss a component.**  If the pruned source has a
surviving occurrence at all, the component carrying it is not one of the
singleton components contributed by the isolated vertices, so there are
strictly more components than isolated vertices. -/
theorem card_isolatedVertices_lt_componentCount
    (data : GluingDatum target degree)
    (hNonempty : (nonDanglingEdges data).Nonempty) :
    (isolatedVertices data).card < componentCount (prunedSource data) := by
  classical
  obtain ⟨edge, hEdge⟩ := hNonempty
  have hNotIso :=
    notMem_isolatedVertices_of_mem_nonDanglingEdges data hEdge
  have hInj : Set.InjOn (component (prunedSource data))
      ((isolatedVertices data) : Set data.SourceVertex) := by
    intro v hv w hw hEq
    rw [component_prunedSource_eq_singleton data
        ((mem_isolatedVertices data v).1 (Finset.mem_coe.1 hv)),
      component_prunedSource_eq_singleton data
        ((mem_isolatedVertices data w).1 (Finset.mem_coe.1 hw))] at hEq
    exact Finset.singleton_injective hEq
  have hSub : (isolatedVertices data).image (component (prunedSource data))
      ⊆ (Finset.univ.image (component (prunedSource data))).erase
          (component (prunedSource data) (data.sourceEnds edge).1) := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨v, hv, hvs⟩ := hs
    refine Finset.mem_erase.2 ⟨?_, ?_⟩
    · intro hEq
      have hMem : (data.sourceEnds edge).1 ∈ component (prunedSource data) v := by
        rw [hvs, hEq]
        exact self_mem_component _
      rw [component_prunedSource_eq_singleton data
        ((mem_isolatedVertices data v).1 hv), Finset.mem_singleton] at hMem
      rw [hMem] at hNotIso
      exact hNotIso hv
    · rw [← hvs]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hCardImage : ((isolatedVertices data).image
      (component (prunedSource data))).card = (isolatedVertices data).card :=
    Finset.card_image_of_injOn hInj
  have hCardErase : ((Finset.univ.image (component (prunedSource data))).erase
      (component (prunedSource data) (data.sourceEnds edge).1)).card
        = componentCount (prunedSource data) - 1 := by
    unfold componentCount
    exact Finset.card_erase_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hLe := Finset.card_le_card hSub
  rw [hCardImage, hCardErase] at hLe
  have hPos := componentCount_pos (prunedSource data)
  omega

/-- The stable graph has at least one component as soon as one occurrence
survives the pruning. -/
theorem one_le_stableComponentCount (data : GluingDatum target degree)
    (hNonempty : (nonDanglingEdges data).Nonempty) :
    1 ≤ stableComponentCount data := by
  have h := card_isolatedVertices_lt_componentCount data hNonempty
  unfold stableComponentCount
  have hCast : ((isolatedVertices data).card : ℤ)
      < (componentCount (prunedSource data) : ℤ) := by exact_mod_cast h
  linarith

/-! ## The chain of identities

Every statement in this section carries exactly the hypotheses it uses, and
**none of them is trivalence**: they are the fields of
`FullDimensionalSource.FullDimensionalSourcePresentation` other than
`trivalent`, spelled out. -/

/-- The stable-path count read through `saturated`. -/
theorem card_stablePath_eq (data : GluingDatum target degree)
    (hStablePathCard : Fintype.card (StablePath data) = target.edges.card)
    (hSaturated : (target.edges.card : ℤ)
      = 2 * genus data.sourceGraph + 2 * degree - 5) :
    (Fintype.card (StablePath data) : ℤ)
      = 2 * genus data.sourceGraph + 2 * degree - 5 := by
  rw [hStablePathCard]
  exact hSaturated

/-- **The vertex count of the stable graph is determined.**  The Euler relation
of the stable graph, the identification of its first Betti number with the
source genus and the two numerical inputs leave no freedom in `|V₃|`. -/
theorem card_stableVertices_eq (data : GluingDatum target degree)
    (hConnected : data.Connected) (hPathEnds : HasPathEnds data)
    (hStablePathCard : Fintype.card (StablePath data) = target.edges.card)
    (hSaturated : (target.edges.card : ℤ)
      = 2 * genus data.sourceGraph + 2 * degree - 5) :
    ((stableVertices data).card : ℤ)
      = genus data.sourceGraph + 2 * (degree : ℤ) - 5
          + stableComponentCount data := by
  have hEuler := card_stablePath_add_componentCount_eq data hConnected hPathEnds
  have hBetti := cyclomatic_prunedSource_eq_genus_sourceGraph data hConnected
  have hCard := card_stablePath_eq data hStablePathCard hSaturated
  unfold stableComponentCount
  linarith

/-- **The Euler bound, with no trivalence input: `ρ ≤ 0` modulo components.**
`Trivalence.card_stableVertices_add_two_mul_componentCount_le` is
unconditional; through the determined vertex count it says exactly that the
source genus is at least `2 degree - 5 + 3 c(H)`.  With a connected stable
graph this is `g ≥ 2 degree - 2`, the statement that a full-dimensional family
of degree-`degree` maps has nonpositive Brill--Noether number. -/
theorem two_mul_degree_le_genus_sourceGraph (data : GluingDatum target degree)
    (hConnected : data.Connected) (hPathEnds : HasPathEnds data)
    (hStablePathCard : Fintype.card (StablePath data) = target.edges.card)
    (hSaturated : (target.edges.card : ℤ)
      = 2 * genus data.sourceGraph + 2 * degree - 5) :
    2 * (degree : ℤ) - 5 + 3 * stableComponentCount data
      ≤ genus data.sourceGraph := by
  have hBound := card_stableVertices_add_two_mul_componentCount_le data hConnected
  have hBetti := cyclomatic_prunedSource_eq_genus_sourceGraph data hConnected
  have hCards := card_stableVertices_eq data hConnected hPathEnds hStablePathCard
    hSaturated
  unfold stableComponentCount at hCards ⊢
  linarith

/-- **Trivalence is the reverse of the Euler bound.**  Nothing more, nothing
less: the whole Draisma--Vargas count, run in both directions, reduces
`nd(v) ≤ 3` to a single inequality between the source genus and the degree. -/
theorem trivalent_iff_genus_le (data : GluingDatum target degree)
    (hConnected : data.Connected) (hPathEnds : HasPathEnds data)
    (hStablePathCard : Fintype.card (StablePath data) = target.edges.card)
    (hSaturated : (target.edges.card : ℤ)
      = 2 * genus data.sourceGraph + 2 * degree - 5) :
    (∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≤ 3)
      ↔ genus data.sourceGraph
          ≤ 2 * (degree : ℤ) - 5 + 3 * stableComponentCount data := by
  have hCards := card_stableVertices_eq data hConnected hPathEnds hStablePathCard
    hSaturated
  have hCard := card_stablePath_eq data hStablePathCard hSaturated
  have hTwo := sum_stableValency_eq_two_mul_card_stablePath_int data hConnected
    hPathEnds
  constructor
  · intro hTrivalent
    have hEq : ∀ vertex ∈ stableVertices data,
        (nonDanglingValency data vertex : ℤ) = 3 := by
      intro vertex hVertex
      have hThree := (mem_stableVertices data vertex).1 hVertex
      have hLe := hTrivalent vertex
      omega
    have hSum : (∑ vertex ∈ stableVertices data,
        (nonDanglingValency data vertex : ℤ))
          = 3 * ((stableVertices data).card : ℤ) := by
      rw [Finset.sum_congr rfl hEq, Finset.sum_const, nsmul_eq_mul]
      ring
    unfold stableComponentCount at hCards ⊢
    linarith
  · intro hLe
    refine nonDanglingValency_le_three_of_two_mul_card_stablePath_le data
      hConnected hPathEnds ?_
    have hInt : (2 * Fintype.card (StablePath data) : ℤ)
        ≤ (3 * (stableVertices data).card : ℤ) := by
      unfold stableComponentCount at hCards hLe
      linarith
    exact_mod_cast hInt

/-- **The closing statement.**  Trivalence of the stable graph is *equivalent*
to the source genus taking one exact value, which for a connected stable graph
is `g = 2 degree - 2`, i.e. Brill--Noether number `ρ = 0`.  It is therefore not
a consequence of the remaining data: those give the inequality
`two_mul_degree_le_genus_sourceGraph` and nothing bounds `g` from above. -/
theorem trivalent_iff_genus_eq (data : GluingDatum target degree)
    (hConnected : data.Connected) (hPathEnds : HasPathEnds data)
    (hStablePathCard : Fintype.card (StablePath data) = target.edges.card)
    (hSaturated : (target.edges.card : ℤ)
      = 2 * genus data.sourceGraph + 2 * degree - 5) :
    (∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≤ 3)
      ↔ genus data.sourceGraph
          = 2 * (degree : ℤ) - 5 + 3 * stableComponentCount data := by
  have hGe := two_mul_degree_le_genus_sourceGraph data hConnected hPathEnds
    hStablePathCard hSaturated
  rw [trivalent_iff_genus_le data hConnected hPathEnds hStablePathCard hSaturated]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **`ρ ≤ 0` needs no trivalence.**  The half of the equality that the
counting identities really do supply, sharpened by `NoDanglingTargetFibres`
from `2 degree - 5 + 3 c(H)` to `2 degree - 2`.  Note the direction: this is
the *opposite* of what closing `trivalent` would need. -/
theorem two_mul_degree_sub_two_le_genus_sourceGraph
    (data : GluingDatum target degree) (hConnected : data.Connected)
    (hPathEnds : HasPathEnds data)
    (hStablePathCard : Fintype.card (StablePath data) = target.edges.card)
    (hSaturated : (target.edges.card : ℤ)
      = 2 * genus data.sourceGraph + 2 * degree - 5)
    (hNonempty : (nonDanglingEdges data).Nonempty) :
    2 * (degree : ℤ) - 2 ≤ genus data.sourceGraph := by
  have hBound := two_mul_degree_le_genus_sourceGraph data hConnected hPathEnds
    hStablePathCard hSaturated
  have hOne := one_le_stableComponentCount data hNonempty
  linarith

/-- **The `3g - 3` of the Draisma--Vargas sketch, as an equivalence.**  The
identity `|E(target)| = 3 g - 3` is not the `saturated` field; it is exactly
trivalence, once the stable graph is connected.  In general the two are
equivalent up to the component count of the stable graph. -/
theorem trivalent_iff_card_target_edges_eq (data : GluingDatum target degree)
    (hConnected : data.Connected) (hPathEnds : HasPathEnds data)
    (hStablePathCard : Fintype.card (StablePath data) = target.edges.card)
    (hSaturated : (target.edges.card : ℤ)
      = 2 * genus data.sourceGraph + 2 * degree - 5) :
    (∀ vertex : data.SourceVertex, nonDanglingValency data vertex ≤ 3)
      ↔ (target.edges.card : ℤ)
          = 3 * genus data.sourceGraph - 3 * stableComponentCount data := by
  rw [trivalent_iff_genus_eq data hConnected hPathEnds hStablePathCard hSaturated]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-! ## Read off a full-dimensional presentation -/

section Presentation

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {data : GluingDatum target degree}

/-- A full-dimensional target has at least one edge occurrence: it is a graph
of genus zero on at least two vertices. -/
theorem card_target_edges_pos
    (fd : FullDimensionalSourcePresentation data coordinate) :
    0 < Multiset.card target.edges := by
  have := fd.nontrivial_target
  have hCard : 1 < Fintype.card target.V := Fintype.one_lt_card
  have hGenus := fd.targetGenus
  unfold genus at hGenus
  omega

/-- **The stable graph is nonempty.**  Nonsingularity gives
`NoDanglingTargetFibres`, so some occurrence above each target edge survives
the pruning. -/
theorem nonDanglingEdges_nonempty
    (fd : FullDimensionalSourcePresentation data coordinate) :
    (nonDanglingEdges data).Nonempty := by
  have hCard : 0 < Fintype.card (target.edges : Type _) := by
    rw [Multiset.card_coe]
    exact card_target_edges_pos fd
  obtain ⟨targetEdge⟩ := Fintype.card_pos_iff.1 hCard
  obtain ⟨sourceEdge, -, hNotDangling⟩ := fd.noDanglingTargetFibres targetEdge
  exact ⟨sourceEdge, (mem_nonDanglingEdges data sourceEdge).2 hNotDangling⟩

/-- The stable graph of a full-dimensional presentation has at least one
component. -/
theorem one_le_stableComponentCount_of_presentation
    (fd : FullDimensionalSourcePresentation data coordinate) :
    1 ≤ stableComponentCount data :=
  one_le_stableComponentCount data (nonDanglingEdges_nonempty fd)

/-- **Every full-dimensional presentation forces the Brill--Noether equality.**
A necessary condition on the structure: its `trivalent` field is equivalent,
given the others, to this exact value of the source genus. -/
theorem genus_sourceGraph_eq_of_presentation
    (fd : FullDimensionalSourcePresentation data coordinate) :
    genus data.sourceGraph
      = 2 * (degree : ℤ) - 5 + 3 * stableComponentCount data :=
  (trivalent_iff_genus_eq data fd.connected fd.pathEnds fd.stablePath_card
    fd.saturated).1 fd.trivalent

/-- **`|E(target)| = 3 g - 3 c(H)` for every full-dimensional presentation**,
so `3 g - 3` when the stable graph is connected: this count is a consequence
of the `trivalent` field, not of `saturated`. -/
theorem card_target_edges_eq_of_presentation
    (fd : FullDimensionalSourcePresentation data coordinate) :
    (target.edges.card : ℤ)
      = 3 * genus data.sourceGraph - 3 * stableComponentCount data :=
  (trivalent_iff_card_target_edges_eq data fd.connected fd.pathEnds
    fd.stablePath_card fd.saturated).1 fd.trivalent

/-- With a connected stable graph the value is `2 degree - 2`, i.e. `ρ = 0`. -/
theorem genus_sourceGraph_eq_of_connected_stable_graph
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hOne : stableComponentCount data = 1) :
    genus data.sourceGraph = 2 * (degree : ℤ) - 2 := by
  have h := genus_sourceGraph_eq_of_presentation fd
  rw [hOne] at h
  linarith

end Presentation

/-! ## Summary of the verdict

`2 * #StablePath ≤ 3 * |V₃|` is **not** derivable from the fields of
`FullDimensionalSource.FullDimensionalSourcePresentation` other than
`trivalent`.  `trivalent_iff_genus_eq` is the exact residue: given
connectedness, `pathEnds`, `stablePath_card` and `saturated`, trivalence holds
if and only if

```
genus data.sourceGraph = 2 * degree - 5 + 3 * stableComponentCount data.
```

The counting identities prove `≥` (`two_mul_degree_le_genus_sourceGraph`), and
`noDanglingTargetFibres` sharpens that to `2 * degree - 2 ≤ genus` — the same
direction, not the missing one.  The unconstrained quantity is the source genus
relative to the degree: `saturated` merely *defines* `|E(target)|` as
`2 g + 2 degree - 5`, and a genus-zero connected target with that many edges
exists for every `g`, so no upper bound on `g` is available from the datum.
Supplying one is a geometric input (`ρ ≥ 0`), not a further Euler count, and in
particular it cannot come from the isolated vertices or from the component
count, both of which push the inequality the other way.
-/

end DraismaVargas.LocalCases.TrivalenceClosure
