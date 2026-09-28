import DraismaVargasCount.LollipopLeafRow

/-!
# The valency census of the target tree

**Source.**  Vargas, Part II (arXiv:2609.09109), the proof of
`lm:combinatorial-structure-caterpillar-of-loops`: change-minimality gives
`ch(u_i) = 1` and `ch(v_i) = 2` at the lollipop vertices, these account for the total
change `3g` by the Riemann--Hurwitz formula, so every other vertex of `T` has change `0`;
and since `T` has `3g - 3` edges, the image of the spine path has at most
`(3g-3) - 2g = g-3` edges.

## What this module is, and what it is not

At a change-minimal full-dimensional datum the change is *determined* by the valency --
`ch(v) = 3 - val(v)` -- so that Part II's change bookkeeping is a valency census of `T`,
and its content is a counting argument.  That census is what this module proves, and it
proves it **from the member alone** plus one named hypothesis:

* every target vertex has valency between one and three, which is
  change-minimality (`GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt`,
  `StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt`) and is
  *derived* here, not assumed;
* `|E(T)| = p` and `|V(T)| = p + 1`, both read off the fields a `FibreMember`
  already carries (`labelling.targetEdge` and `targetGenus`), so the
  `2L + D = |E| + 3` identity needs no Riemann--Hurwitz input;
* **(divalent images)**: the `g` lollipop branch vertices have pairwise distinct divalent
  images, as the named hypothesis `hDivalent`, in the shape
  `g ≤ divalentCount member.target`.  The adapter `card_le_divalentCount_of_injective`
  turns "an injection from the `g` loop slots to divalent target vertices" into that
  inequality.  It is proved with no hypothesis in `LollipopDivalent`
  (`LollipopDivalent.genus_le_divalentCount_catCore`, `divalentCount_eq_catCore`), so
  `hDivalent` here is a convenience binder, and discharging it at a use site is a citation
  rather than a proof.

The leaf bound `g ≤ leafCount` is **not** assumed: it is
`LollipopLeafRow.genus_le_leafCount_catCore`, unconditional over every member.

## What is proved

* §1 `valency`, `valencySet`, `divalentCount`, `trivalentCount`,
  `valencySet_one_eq_leafVertices`, `sum_split`,
  `card_valencySet_sum` (`L + D + Tr = |V|`) and `sum_valency_split`
  (`L + 2D + 3Tr = ∑ val`) — the three-way partition of a target all of whose
  valencies lie in `[1,3]`.
* §2 `sum_valency` — the handshake `∑_v val(v) = 2|E|`, from
  `GluingDatum.sum_incidentEdges`; and `census_identity`: `2L + D = |E| + 3`, for
  any target with `|V| = |E| + 1` and valencies in `[1,3]`.  No genus, no
  degree, no Riemann--Hurwitz.
* §3 at an arbitrary `FibreMember`: `valency_pos`, `valency_le_three`,
  `member_edge_card` (`|E| = p`), `member_vertex_card` (`|V| = p + 1`) and
  `member_census_identity` (`2L + D = p + 3`).
* §4 at the caterpillar of loops: `catCore_census` — under `hDivalent`,
  `leafCount = 2m+2`, `divalentCount = 2m+2`, `trivalentCount = 2m`, i.e.
  `L = D = g` and `Tr = g - 2` for `g = 2m + 2`; `catCore_census_of_divalentMap`,
  the same from an injection of the core's loop slots into the divalent target
  vertices; and `catCore_spine_edge_budget`, the arithmetic of the spine edge budget: a
  set of target edges disjoint from `2g` lollipop edges has at most `g - 3` elements.

## What is not proved here

* **(divalent images) is a hypothesis wherever it is used in this file**; see above for
  where it is proved.
* **The spine path `P` is not constructed**, in the source or in the target.
  No statement here mentions a path, a walk, or `Neigh`.  The spine argument asks for
  three things — `P` itself, the bound `|E(φ(P))| ≤ g-3`, and disjointness of
  `φ(P)` from the lollipop images — and only the *arithmetic* of the second is
  here (`catCore_spine_edge_budget`), as a statement about an abstract
  `2g`-element set of edges that nothing here produces.
* **Disjointness does not follow from (divalent images).**  Part II gets it from
  the *fibre* statement of `lm:bridge-and-loop` — that `e_b, A, e_1, e_2, C`
  are the only non-dangling elements above the lollipop's two target edges
  (`Count/LollipopBridgeFibre.lean`).  An alternative route: once `A_φ` is known to be a
  monomial matrix (`Count/SpineOffDiagonal.lean`) the row → edge map is injective, and
  disjointness of the spine rows' images from the loop and bridge rows' images is
  immediate.
* Nothing here says the target is `T^CL_g`, that its trivalent vertices form a
  path, or that the member is a ballot member.  The census constrains the
  *numbers* of vertices of each valency and says nothing about how they are
  joined.
* No statement here is conditional on `Open`, on `HasOddMult`, on the request
  being positive or generic, or on integrality.
-/

namespace DraismaVargas.Count.SpinePath

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.FullDimensionalSource
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  The three valency classes of a target -/

section Classes

variable (target : CFGraph)

/-- The valency of a target vertex: the number of edge occurrences meeting it.
This is the `val(v)` of the change formula `ch(v) + val(v) = 3`. -/
def valency (vertex : target.V) : ℕ := (GluingDatum.incidentEdges vertex).card

/-- The target vertices of a given valency. -/
def valencySet (k : ℕ) : Finset target.V :=
  Finset.univ.filter fun vertex ↦ valency target vertex = k

/-- `D`, the number of divalent vertices of the target. -/
def divalentCount : ℕ := (valencySet target 2).card

/-- `Tr`, the number of trivalent vertices of the target. -/
def trivalentCount : ℕ := (valencySet target 3).card

theorem mem_valencySet {k : ℕ} {vertex : target.V} :
    vertex ∈ valencySet target k ↔ valency target vertex = k := by
  simp [valencySet]

/-- The valency-one class is `leafVertices`. -/
theorem valencySet_one_eq_leafVertices : valencySet target 1 = leafVertices target :=
  Finset.filter_congr fun _ _ ↦ Iff.rfl

/-- `L`, the number of leaves, is the cardinality of the valency-one class. -/
theorem card_valencySet_one : (valencySet target 1).card = leafCount target := by
  rw [valencySet_one_eq_leafVertices]; rfl

variable {target}

/-- A target all of whose valencies lie in `[1,3]` splits into its three
valency classes. -/
theorem sum_split (g : target.V → ℤ)
    (hLow : ∀ vertex, 1 ≤ valency target vertex)
    (hHigh : ∀ vertex, valency target vertex ≤ 3) :
    ∑ vertex : target.V, g vertex =
      (∑ vertex ∈ valencySet target 1, g vertex) +
        (∑ vertex ∈ valencySet target 2, g vertex) +
        (∑ vertex ∈ valencySet target 3, g vertex) := by
  have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset target.V)
    (fun v ↦ valency target v = 1) g
  have h2 := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun v ↦ ¬ valency target v = 1)) (fun v ↦ valency target v = 2) g
  have e2 : (Finset.univ.filter (fun v ↦ ¬ valency target v = 1)).filter
      (fun v ↦ valency target v = 2) =
      Finset.univ.filter (fun v ↦ valency target v = 2) := by
    ext vertex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have e3 : (Finset.univ.filter (fun v ↦ ¬ valency target v = 1)).filter
      (fun v ↦ ¬ valency target v = 2) =
      Finset.univ.filter (fun v ↦ valency target v = 3) := by
    ext vertex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hl := hLow vertex
    have hh := hHigh vertex
    omega
  rw [e2, e3] at h2
  simp only [valencySet]
  rw [← h1, ← h2]
  ring

/-- `L + D + Tr = |V(T)|`. -/
theorem card_valencySet_sum
    (hLow : ∀ vertex, 1 ≤ valency target vertex)
    (hHigh : ∀ vertex, valency target vertex ≤ 3) :
    leafCount target + divalentCount target + trivalentCount target =
      Fintype.card target.V := by
  have h := sum_split (fun _ ↦ (1 : ℤ)) hLow hHigh
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
    card_valencySet_one] at h
  have h' : (Fintype.card target.V : ℤ) =
      (leafCount target : ℤ) + (divalentCount target : ℤ) + (trivalentCount target : ℤ) := h
  exact_mod_cast h'.symm

/-- On its own valency class the valency is constant. -/
theorem sum_valency_on_valencySet (k : ℕ) :
    (∑ vertex ∈ valencySet target k, (valency target vertex : ℤ)) =
      (k : ℤ) * (valencySet target k).card := by
  rw [Finset.sum_congr rfl (fun vertex hvertex ↦ by
    rw [(mem_valencySet target).mp hvertex])]
  simp [mul_comm]

/-- `L + 2D + 3Tr = ∑_v val(v)`. -/
theorem sum_valency_split
    (hLow : ∀ vertex, 1 ≤ valency target vertex)
    (hHigh : ∀ vertex, valency target vertex ≤ 3) :
    (∑ vertex : target.V, (valency target vertex : ℤ)) =
      (leafCount target : ℤ) + 2 * (divalentCount target : ℤ) +
        3 * (trivalentCount target : ℤ) := by
  rw [sum_split (fun vertex ↦ (valency target vertex : ℤ)) hLow hHigh,
    sum_valency_on_valencySet 1, sum_valency_on_valencySet 2, sum_valency_on_valencySet 3,
    card_valencySet_one]
  simp [divalentCount, trivalentCount]

end Classes

/-! ## 2.  The handshake and the census identity -/

section Census

variable {target : CFGraph}

/-- **The handshake.**  Every target edge occurrence has two distinct endpoints
(`CFGraph.loopless`), so the valencies sum to twice the edge count.  This is
`GluingDatum.sum_incidentEdges` at the constant weight one. -/
theorem sum_valency (target : CFGraph) :
    (∑ vertex : target.V, (valency target vertex : ℤ)) =
      2 * (Fintype.card target.edges : ℤ) := by
  have h := GluingDatum.sum_incidentEdges target (fun _ ↦ (1 : ℤ))
  simpa [valency] using h

/-- **The census identity `2L + D = |E| + 3`.**

This is the whole of Part II's change bookkeeping, and it needs no
Riemann--Hurwitz input: at a change-minimal
datum `ch(v) = 3 - val(v)`, so `∑_v ch(v) = 3|V| - 2|E|`, which for a tree is
`|E| + 3` identically.  What has content is the valency bound `1 ≤ val ≤ 3`,
which is where change-minimality actually enters. -/
theorem census_identity {edgeCard : ℕ}
    (hLow : ∀ vertex, 1 ≤ valency target vertex)
    (hHigh : ∀ vertex, valency target vertex ≤ 3)
    (hE : Fintype.card target.edges = edgeCard)
    (hV : Fintype.card target.V = edgeCard + 1) :
    2 * leafCount target + divalentCount target = edgeCard + 3 := by
  have hA := card_valencySet_sum hLow hHigh
  have hB := (sum_valency_split hLow hHigh).symm.trans (sum_valency target)
  rw [hE] at hB
  rw [hV] at hA
  omega

/-- **The adapter for (divalent images).**  Whatever indexing supplies the divalent
images — one per self-loop slot of the core, pairwise distinct — this converts
it into the cardinality bound the census consumes. -/
theorem card_le_divalentCount_of_injective {ι : Type*} [Fintype ι]
    (f : ι → target.V) (hf : Function.Injective f)
    (hdiv : ∀ i, valency target (f i) = 2) :
    Fintype.card ι ≤ divalentCount target := by
  classical
  have hinj : Function.Injective (fun i : ι ↦ (⟨f i, hdiv i⟩ :
      {vertex : target.V // valency target vertex = 2})) := by
    intro a b hab
    exact hf (congrArg Subtype.val hab)
  have hle := Fintype.card_le_of_injective _ hinj
  have hcard : Fintype.card {vertex : target.V // valency target vertex = 2} =
      divalentCount target := by
    simp [divalentCount, valencySet, Fintype.card_subtype]
  omega

end Census

/-! ## 3.  The census inputs at an arbitrary member of the fibre -/

section Member

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
  (member : FibreMember core y degree)

/-- Every target vertex of a member has positive valency: change-minimality is
derived from full dimensionality, and a change-minimal vertex carries at least
one incident occurrence. -/
theorem valency_pos (vertex : member.target.V) : 1 ≤ valency member.target vertex :=
  DraismaVargas.LocalCases.StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt
    member.data vertex (member.fullDim.changeMinimal vertex)

/-- Every target vertex of a member has valency at most three. -/
theorem valency_le_three (vertex : member.target.V) : valency member.target vertex ≤ 3 :=
  GluingDatum.incidentEdges_card_le_three_of_changeMinimalAt member.data
    member.fullDim.valid vertex (member.fullDim.changeMinimal vertex)

/-- `|E(T)| = p`: the labelling numbers the target's edge occurrences by the
request's slot type. -/
theorem member_edge_card : Fintype.card member.target.edges = p := by
  have hc := Fintype.card_congr member.fullDim.labelling.targetEdge
  rw [Fintype.card_fin] at hc
  exact hc.symm

/-- `|V(T)| = p + 1`: the target is a tree. -/
theorem member_vertex_card : Fintype.card member.target.V = p + 1 := by
  have hc := Fintype.card_congr member.fullDim.labelling.targetEdge
  rw [Fintype.card_fin, Multiset.card_coe] at hc
  have hg : (Multiset.card member.target.edges : ℤ) -
      (Fintype.card member.target.V : ℤ) + 1 = 0 := member.fullDim.targetGenus
  omega

/-- **The census identity at an arbitrary member**: `2L + D = p + 3`, with no
hypothesis at all beyond membership of the fibre. -/
theorem member_census_identity :
    2 * leafCount member.target + divalentCount member.target = p + 3 :=
  census_identity (valency_pos member) (valency_le_three member)
    (member_edge_card member) (member_vertex_card member)

end Member

/-! ## 4.  The census at the caterpillar of loops -/

section CaterpillarOfLoops

open DraismaVargas.Count.FibreCaterpillar

/-- **The valency census of `T`, under (divalent images).**  For `g = 2m + 2`:
`L = D = g` and `Tr = g - 2`.  The leaf bound is the unconditional
`LollipopLeafRow.genus_le_leafCount_catCore`; the divalent bound `hDivalent` is
(divalent images) and is the only hypothesis. -/
theorem catCore_census (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (hDivalent : 2 * m + 2 ≤ divalentCount member.target) :
    leafCount member.target = 2 * m + 2 ∧
      divalentCount member.target = 2 * m + 2 ∧
      trivalentCount member.target = 2 * m := by
  have hLeaf : 2 * m + 2 ≤ leafCount member.target :=
    LollipopLeafRow.genus_le_leafCount_catCore m member
  have hCensus : 2 * leafCount member.target + divalentCount member.target = 6 * m + 3 + 3 :=
    member_census_identity member
  have hSum : leafCount member.target + divalentCount member.target +
      trivalentCount member.target = Fintype.card member.target.V :=
    card_valencySet_sum (valency_pos member) (valency_le_three member)
  have hV : Fintype.card member.target.V = 6 * m + 3 + 1 := member_vertex_card member
  rw [hV] at hSum
  refine ⟨by omega, by omega, by omega⟩

/-- **The census from an injection of the core's self-loop slots into divalent target
vertices**, mirroring `LollipopLeafRow.loopLeafMap` on the leaf side.  If (divalent
images) is supplied in another form, `catCore_census` takes the cardinality bound
directly. -/
theorem catCore_census_of_divalentMap (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (divalentMap : {slot : Fin (6 * m + 3) //
        (catCore m).tail slot = (catCore m).head slot} → member.target.V)
    (hInjective : Function.Injective divalentMap)
    (hDivalent : ∀ slot, valency member.target (divalentMap slot) = 2) :
    leafCount member.target = 2 * m + 2 ∧
      divalentCount member.target = 2 * m + 2 ∧
      trivalentCount member.target = 2 * m := by
  have hle := card_le_divalentCount_of_injective divalentMap hInjective hDivalent
  rw [LollipopLeafRow.card_catCore_loopSlots m] at hle
  exact catCore_census m member hle

/-- **The arithmetic of the spine edge budget.**  Part II's `(3g-3) - 2g = g-3`: a
set of target edges disjoint from the `2g` lollipop edges has at most `g - 3`
elements.  Nothing here produces either set; `lollipopEdges` is a hypothesis. -/
theorem catCore_spine_edge_budget (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (member : FibreMember (catCore m) request (m + 2))
    (lollipopEdges spineEdges : Finset member.target.edges)
    (hCard : lollipopEdges.card = 2 * (2 * m + 2))
    (hDisj : Disjoint lollipopEdges spineEdges) :
    spineEdges.card + 3 ≤ 2 * m + 2 := by
  classical
  have hE : Fintype.card member.target.edges = 6 * m + 3 := member_edge_card member
  have hUnion : (lollipopEdges ∪ spineEdges).card =
      lollipopEdges.card + spineEdges.card := Finset.card_union_of_disjoint hDisj
  have hLe : (lollipopEdges ∪ spineEdges).card ≤ Fintype.card member.target.edges := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  omega

end CaterpillarOfLoops

end DraismaVargas.Count.SpinePath
