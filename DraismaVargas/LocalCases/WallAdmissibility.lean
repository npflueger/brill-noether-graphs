module

public import DraismaVargas.LocalCases.SourceFibreForest
public import DraismaVargas.LocalCases.WallDegeneration

@[expose] public section

/-!
# `DanglingCompatible` is derivable at a wall event

`WallDegeneration.DanglingCompatible data hc hab hOne` appears as a hypothesis
in many places -- including `IncomingSourceCases.exists_classification`.  This
module shows that **it is not an extra hypothesis.**

`danglingCompatible_of_fullDimensional` derives it from exactly the hypothesis
set `exists_classification` already takes, with nothing added: a
`FullDimensionalSourcePresentation` together with the metric facts at the
event (a nonnegative coordinate vector, every honest stable row nonzero, the
contracted column zero).  Both halves hold, and both are instances of one
biconditional, `isDangling_sourceEdgeMap_iff`: on the occurrences that survive
the contraction, danglingness upstairs and downstairs agree.

## What the proof actually uses

The whole derivation factors through `ContractionForest data a b contracted`,
which `SourceFibreForest.contractionForest_of_fullDimensional` already extracts
from the metric facts.  `danglingCompatible_of_contractionForest` is the
mathematical statement; the metric hypotheses enter only through it.  This
matches Draisma--Vargas `lemma-dangling-limit` ("dangling in the limit"), whose
hypothesis is that the contraction destroys no cycle.

`WallDegeneration`'s header reads the two halves asymmetrically -- preserved
true, reflected "false in general".  That reading is correct *without* the
forest hypothesis, and the forest hypothesis is exactly what makes the two
halves symmetric; the header says so itself, and names `ContractionForest` as
the fix.  What is needed beyond that idea is bookkeeping, and the bookkeeping
is finite:

* `graph_connected` is the **cut form**, `∀ S, (∃ v ∈ S, ∃ w ∉ S) → ∃ crossing
  edge`.  So connectivity of an induced subgraph is an ambient statement about
  `num_edges`, recorded here as `ConnectedOn` with `connectedOn_iff`, and it
  transfers in both directions (`connectedOn_image`, `connectedOn_preimage`)
  with no path machinery: the only new input downstairs-to-upstairs is that a
  fibre straddling the proposed cut is itself crossed by a contracted
  occurrence.
* `genus` is `|E| - |V| + 1`, and `Utilities.inducedSubgraph` already exposes
  both counts (`inducedSubgraph_edge_card_eq_filter`,
  `inducedSubgraph_vertex_card`).  So `genus_side_eq` is arithmetic once one
  knows `card_side_eq`: a saturated side loses exactly one vertex per
  contracted occurrence it contains.  That is `card_fibre_eq`, and at the
  merged vertex `card_fibre_eq` *is* `ContractionForest`, read through
  `SheetPartition.blocksWithin` -- the fibre above a merged block has one more
  vertex than it has contracted occurrences.
* The cut itself transfers by counting occurrences
  (`num_edges_sourceGraph`, `num_edges_contract_sourceGraph`):
  `cross_num_edges_image` descends it, and `cross_num_edges_preimage` lifts it,
  the latter using that the unique crossing occurrence downstairs is the image
  of the distinguished occurrence upstairs.

Everything is glued in `nonempty_danglingSide_map_iff`, which sends a
`W4StableSource.DanglingSide` in either direction along
`GluingContraction.sourceVertexMap`.

## Scope

This settles `DanglingCompatible` only.  The other two carried admissibility
receipts, `hStable` and `hTrivalent`, are untouched here; nothing below bears
on them.
-/

namespace DraismaVargas.LocalCases.WallAdmissibility

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionFibre
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.WallDegeneration

section General

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- Occurrence form of `num_edges` on a quotient source graph: the edge
multiplicity between two source vertices counts the source occurrences whose
ordered ends are that pair in either order. -/
theorem num_edges_sourceGraph (data : GluingDatum target degree)
    (u v : data.SourceVertex) :
    num_edges data.sourceGraph u v =
      ((Finset.univ : Finset data.SourceEdge).filter fun e =>
        data.sourceEnds e = (u, v) ∨ data.sourceEnds e = (v, u)).card := by
  have h := Multiset.filter_map
    (p := fun e : data.SourceVertex × data.SourceVertex => e = (u, v) ∨ e = (v, u))
    data.sourceEnds (Finset.univ : Finset data.SourceEdge).val
  calc num_edges data.sourceGraph u v
      = Multiset.card (Multiset.filter
          (fun e : data.SourceVertex × data.SourceVertex => e = (u, v) ∨ e = (v, u))
          ((Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds)) := rfl
    _ = _ := by rw [h, Multiset.card_map]; rfl

/-- An occurrence between two source vertices makes their multiplicity
positive. -/
theorem num_edges_sourceGraph_pos (data : GluingDatum target degree)
    {u v : data.SourceVertex} (e : data.SourceEdge)
    (he : data.sourceEnds e = (u, v) ∨ data.sourceEnds e = (v, u)) :
    0 < num_edges data.sourceGraph u v := by
  rw [num_edges_sourceGraph]
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩⟩

/-- Conversely, a positive multiplicity is witnessed by an occurrence. -/
theorem exists_sourceEnds_of_num_edges_pos (data : GluingDatum target degree)
    {u v : data.SourceVertex} (h : 0 < num_edges data.sourceGraph u v) :
    ∃ e : data.SourceEdge,
      data.sourceEnds e = (u, v) ∨ data.sourceEnds e = (v, u) := by
  rw [num_edges_sourceGraph] at h
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  exact ⟨e, (Finset.mem_filter.mp he).2⟩

/-- The occurrence count downstairs, read through the surviving-occurrence
equivalence `ContractionFibre.sourceEdgeEquiv`. -/
theorem num_edges_contract_sourceGraph (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (p q : (contractDatum data hc hab hOne).SourceVertex) :
    num_edges (contractDatum data hc hab hOne).sourceGraph p q =
      ((Finset.univ : Finset {e : data.SourceEdge // e.1.1 ≠ contracted}).filter
        fun e =>
          (sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1 = p ∧
            sourceVertexMap data hc hab hOne (data.sourceEnds e.1).2 = q) ∨
          (sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1 = q ∧
            sourceVertexMap data hc hab hOne (data.sourceEnds e.1).2 = p)).card := by
  classical
  rw [num_edges_sourceGraph]
  refine (Finset.card_equiv (sourceEdgeEquiv data hc hab hOne) ?_).symm
  intro e
  have hends := sourceEnds_sourceEdgeMap data hc hab hOne e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    sourceEdgeEquiv_apply, hends, Prod.mk.injEq]

/-! ## The fibres of the contraction -/

/-- A surviving occurrence has its two endpoints in two *different* fibres of
`sourceVertexMap`: the only target occurrence joining `a` to `b` is the
contracted one. -/
theorem sourceVertexMap_sourceEnds_ne (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {e : data.SourceEdge} (hne : e.1.1 ≠ contracted) :
    sourceVertexMap data hc hab hOne (data.sourceEnds e).1
      ≠ sourceVertexMap data hc hab hOne (data.sourceEnds e).2 := by
  intro h
  obtain ⟨hfold, -⟩ := (sourceVertexMap_eq_iff_parts data hc hab hOne _ _).mp h
  rw [sourceEnds_fst_fst, sourceEnds_snd_fst] at hfold
  rcases (GraphContraction.fold_eq_fold_iff target hab _ _).mp hfold with
    heq | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · refine target.loopless (e.1.1 : target.V × target.V).1 ?_
    have hPair : (e.1.1 : target.V × target.V)
        = ((e.1.1 : target.V × target.V).1, (e.1.1 : target.V × target.V).1) :=
      Prod.ext rfl heq.symm
    rw [← hPair]
    exact Multiset.coe_mem
  · exact hne (eq_contracted_of_coe_eq_pair hc hOne (Prod.ext hA hB))
  · refine notMem_swapped hc hab hOne ?_
    have hPair : (e.1.1 : target.V × target.V) = ((b, a) : target.V × target.V) :=
      Prod.ext hA hB
    rw [← hPair]
    exact Multiset.coe_mem

/-! ## Transferring a cut across the contraction

Throughout, `S` and `T` are the two sides of one cut, tied together by
`hmem : ∀ u, u ∈ S ↔ sourceVertexMap … u ∈ T`.  That single hypothesis says
both that `S` is a union of fibres and that `T` is its image, and it is what
`WallDegeneration.separatingEdgeCut_mem_iff_of_sourceVertexMap_eq` supplies
upstairs and what the preimage supplies downstairs. -/

/-- **The crossing condition descends.** -/
theorem cross_num_edges_image (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {S : Finset data.SourceVertex}
    {T : Finset (contractDatum data hc hab hOne).SourceVertex}
    (hmem : ∀ u : data.SourceVertex,
      u ∈ S ↔ sourceVertexMap data hc hab hOne u ∈ T)
    {x y : data.SourceVertex} (hx : x ∈ S) (hy : y ∉ S)
    (hcross : ∀ u ∈ S, ∀ v ∉ S, num_edges data.sourceGraph u v
      = if u = x ∧ v = y then 1 else 0)
    (p q : (contractDatum data hc hab hOne).SourceVertex)
    (hp : p ∈ T) (hq : q ∉ T) :
    num_edges (contractDatum data hc hab hOne).sourceGraph p q
      = if p = sourceVertexMap data hc hab hOne x ∧
          q = sourceVertexMap data hc hab hOne y then 1 else 0 := by
  classical
  have key : ∀ e : {e : data.SourceEdge // e.1.1 ≠ contracted},
      ((sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1 = p ∧
          sourceVertexMap data hc hab hOne (data.sourceEnds e.1).2 = q) ∨
        (sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1 = q ∧
          sourceVertexMap data hc hab hOne (data.sourceEnds e.1).2 = p)) →
      (p = sourceVertexMap data hc hab hOne x ∧
          q = sourceVertexMap data hc hab hOne y) ∧
        (data.sourceEnds e.1 = (x, y) ∨ data.sourceEnds e.1 = (y, x)) := by
    rintro e (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hu : (data.sourceEnds e.1).1 ∈ S := (hmem _).mpr (by rw [h1]; exact hp)
      have hv : (data.sourceEnds e.1).2 ∉ S := fun hIn => hq (by
        rw [← h2]; exact (hmem _).mp hIn)
      have hPos := num_edges_sourceGraph_pos
        (u := (data.sourceEnds e.1).1) (v := (data.sourceEnds e.1).2)
        data e.1 (Or.inl rfl)
      rw [hcross _ hu _ hv] at hPos
      by_cases hCase : (data.sourceEnds e.1).1 = x ∧ (data.sourceEnds e.1).2 = y
      · exact ⟨⟨by rw [← h1, hCase.1], by rw [← h2, hCase.2]⟩,
          Or.inl (Prod.ext hCase.1 hCase.2)⟩
      · rw [ite_eq_right hCase] at hPos
        exact absurd hPos (lt_irrefl 0)
    · have hu : (data.sourceEnds e.1).2 ∈ S := (hmem _).mpr (by rw [h2]; exact hp)
      have hv : (data.sourceEnds e.1).1 ∉ S := fun hIn => hq (by
        rw [← h1]; exact (hmem _).mp hIn)
      have hPos := num_edges_sourceGraph_pos
        (u := (data.sourceEnds e.1).2) (v := (data.sourceEnds e.1).1)
        data e.1 (Or.inr rfl)
      rw [hcross _ hu _ hv] at hPos
      by_cases hCase : (data.sourceEnds e.1).2 = x ∧ (data.sourceEnds e.1).1 = y
      · exact ⟨⟨by rw [← h2, hCase.1], by rw [← h1, hCase.2]⟩,
          Or.inr (Prod.ext hCase.2 hCase.1)⟩
      · rw [ite_eq_right hCase] at hPos
        exact absurd hPos (lt_irrefl 0)
  rw [num_edges_contract_sourceGraph]
  by_cases hpq : p = sourceVertexMap data hc hab hOne x ∧
      q = sourceVertexMap data hc hab hOne y
  · rw [ite_eq_left hpq]
    have hxy : sourceVertexMap data hc hab hOne x ≠ sourceVertexMap data hc hab hOne y := by
      intro hEq
      exact hq (by rw [hpq.2, ← hEq, ← hpq.1]; exact hp)
    have hOneUp : num_edges data.sourceGraph x y = 1 := by
      rw [hcross x hx y hy, ite_eq_left ⟨rfl, rfl⟩]
    rw [← hOneUp, num_edges_sourceGraph]
    refine Finset.card_bij' (fun e _ => e.1) (fun e he => ⟨e, ?_⟩) ?_ ?_ ?_ ?_
    · intro hCon
      have hSame := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e hCon
      rcases (Finset.mem_filter.mp he).2 with hEnds | hEnds
      · rw [hEnds] at hSame; exact hxy hSame
      · rw [hEnds] at hSame; exact hxy hSame.symm
    · intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (key e (Finset.mem_filter.mp he).2).2⟩
    · intro e he
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases (Finset.mem_filter.mp he).2 with hEnds | hEnds
      · exact Or.inl ⟨by rw [hEnds, ← hpq.1], by rw [hEnds, ← hpq.2]⟩
      · exact Or.inr ⟨by rw [hEnds, ← hpq.2], by rw [hEnds, ← hpq.1]⟩
    · intro e _
      rfl
    · intro e _
      rfl
  · rw [ite_eq_right hpq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e _
    exact fun hBad => hpq (key e hBad).1

/-- An occurrence between two source vertices with distinct images survives the
contraction. -/
theorem ne_contracted_of_sourceVertexMap_ne (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {u v : data.SourceVertex}
    (huv : sourceVertexMap data hc hab hOne u ≠ sourceVertexMap data hc hab hOne v)
    {e : data.SourceEdge}
    (he : data.sourceEnds e = (u, v) ∨ data.sourceEnds e = (v, u)) :
    e.1.1 ≠ contracted := by
  intro hCon
  have hSame := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e hCon
  rcases he with h | h
  · rw [h] at hSame; exact huv hSame
  · rw [h] at hSame; exact huv hSame.symm

/-- When every occurrence between `u` and `v` survives, the surviving
occurrences between them are counted by the ambient multiplicity. -/
theorem card_filter_surviving (data : GluingDatum target degree)
    {u v : data.SourceVertex}
    (hne : ∀ e : data.SourceEdge,
      (data.sourceEnds e = (u, v) ∨ data.sourceEnds e = (v, u)) → e.1.1 ≠ contracted) :
    ((Finset.univ : Finset {e : data.SourceEdge // e.1.1 ≠ contracted}).filter
        fun e => data.sourceEnds e.1 = (u, v) ∨ data.sourceEnds e.1 = (v, u)).card
      = num_edges data.sourceGraph u v := by
  classical
  rw [num_edges_sourceGraph]
  refine Finset.card_bij' (fun e _ => e.1)
    (fun e he => ⟨e, hne e (Finset.mem_filter.mp he).2⟩) ?_ ?_ ?_ ?_
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩
  · intro e _
    rfl
  · intro e _
    rfl

/-- Multiplicities can only drop under the contraction. -/
theorem num_edges_le_contract (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {u v : data.SourceVertex}
    (huv : sourceVertexMap data hc hab hOne u ≠ sourceVertexMap data hc hab hOne v) :
    num_edges data.sourceGraph u v
      ≤ num_edges (contractDatum data hc hab hOne).sourceGraph
          (sourceVertexMap data hc hab hOne u) (sourceVertexMap data hc hab hOne v) := by
  classical
  rw [← card_filter_surviving (contracted := contracted) data
      (fun e he => ne_contracted_of_sourceVertexMap_ne data hc hab hOne huv he),
    num_edges_contract_sourceGraph]
  refine Finset.card_le_card ?_
  intro e he
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rcases (Finset.mem_filter.mp he).2 with h | h
  · exact Or.inl ⟨by rw [h], by rw [h]⟩
  · exact Or.inr ⟨by rw [h], by rw [h]⟩

/-- **The crossing condition lifts.**  The distinguished occurrence `e` is
carried explicitly: downstairs the unique crossing occurrence is its image, so
its preimage pins the upstairs crossing pair. -/
theorem cross_num_edges_preimage (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {S : Finset data.SourceVertex}
    {T : Finset (contractDatum data hc hab hOne).SourceVertex}
    (hmem : ∀ u : data.SourceVertex,
      u ∈ S ↔ sourceVertexMap data hc hab hOne u ∈ T)
    {x y : data.SourceVertex} {e : data.SourceEdge} (hne : e.1.1 ≠ contracted)
    (hEnds : data.sourceEnds e = (x, y) ∨ data.sourceEnds e = (y, x))
    (hx : x ∈ S) (hy : y ∉ S)
    (hcross : ∀ p ∈ T, ∀ q ∉ T,
      num_edges (contractDatum data hc hab hOne).sourceGraph p q
        = if p = sourceVertexMap data hc hab hOne x ∧
            q = sourceVertexMap data hc hab hOne y then 1 else 0) :
    ∀ u ∈ S, ∀ v ∉ S, num_edges data.sourceGraph u v
      = if u = x ∧ v = y then 1 else 0 := by
  classical
  have hxT : sourceVertexMap data hc hab hOne x ∈ T := (hmem x).mp hx
  have hyT : sourceVertexMap data hc hab hOne y ∉ T := fun hIn => hy ((hmem y).mpr hIn)
  have hOneDown : num_edges (contractDatum data hc hab hOne).sourceGraph
      (sourceVertexMap data hc hab hOne x) (sourceVertexMap data hc hab hOne y) = 1 := by
    rw [hcross _ hxT _ hyT, ite_eq_left ⟨rfl, rfl⟩]
  intro u hu v hv
  have huT : sourceVertexMap data hc hab hOne u ∈ T := (hmem u).mp hu
  have hvT : sourceVertexMap data hc hab hOne v ∉ T := fun hIn => hv ((hmem v).mpr hIn)
  have huv : sourceVertexMap data hc hab hOne u ≠ sourceVertexMap data hc hab hOne v :=
    fun hEq => hvT (hEq ▸ huT)
  by_cases hCase : u = x ∧ v = y
  · obtain ⟨rfl, rfl⟩ := hCase
    rw [ite_eq_left ⟨rfl, rfl⟩]
    have hLe := num_edges_le_contract data hc hab hOne huv
    rw [hOneDown] at hLe
    have hPos := num_edges_sourceGraph_pos data e hEnds
    omega
  · rw [ite_eq_right hCase]
    by_contra hPos
    obtain ⟨e', hEnds'⟩ := exists_sourceEnds_of_num_edges_pos data
      (Nat.pos_of_ne_zero hPos)
    have hne' : e'.1.1 ≠ contracted :=
      ne_contracted_of_sourceVertexMap_ne data hc hab hOne huv hEnds'
    have hDownPos : 0 < num_edges (contractDatum data hc hab hOne).sourceGraph
        (sourceVertexMap data hc hab hOne u) (sourceVertexMap data hc hab hOne v) := by
      refine num_edges_sourceGraph_pos (contractDatum data hc hab hOne)
        (sourceEdgeMap data hc hab hOne ⟨e', hne'⟩) ?_
      rw [sourceEnds_sourceEdgeMap data hc hab hOne ⟨e', hne'⟩]
      rcases hEnds' with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    rw [hcross _ huT _ hvT] at hDownPos
    by_cases hImage : sourceVertexMap data hc hab hOne u = sourceVertexMap data hc hab hOne x ∧
        sourceVertexMap data hc hab hOne v = sourceVertexMap data hc hab hOne y
    · have hEq : sourceEdgeMap data hc hab hOne ⟨e, hne⟩
          = sourceEdgeMap data hc hab hOne ⟨e', hne'⟩ := by
        refine sourceEdge_unique_of_num_edges_eq_one (contractDatum data hc hab hOne)
          hOneDown ?_ ?_
        · rw [sourceEnds_sourceEdgeMap data hc hab hOne ⟨e, hne⟩]
          rcases hEnds with h | h
          · exact Or.inl (by rw [h])
          · exact Or.inr (by rw [h])
        · rw [sourceEnds_sourceEdgeMap data hc hab hOne ⟨e', hne'⟩]
          rcases hEnds' with h | h
          · exact Or.inl (by rw [h, hImage.1, hImage.2])
          · exact Or.inr (by rw [h, hImage.1, hImage.2])
      have hSame : e = e' :=
        congrArg Subtype.val (sourceEdgeMap_injective data hc hab hOne hEq)
      subst hSame
      rcases hEnds with h | h <;> rcases hEnds' with h' | h'
      · rw [h] at h'
        have hux : u = x := (congrArg Prod.fst h').symm
        have hvy : v = y := (congrArg Prod.snd h').symm
        exact hCase ⟨hux, hvy⟩
      · rw [h] at h'
        have hyu : y = u := congrArg Prod.snd h'
        exact hy (by rw [hyu]; exact hu)
      · rw [h] at h'
        have hyu : y = u := congrArg Prod.fst h'
        exact hy (by rw [hyu]; exact hu)
      · rw [h] at h'
        have hux : u = x := (congrArg Prod.snd h').symm
        have hvy : v = y := (congrArg Prod.fst h').symm
        exact hCase ⟨hux, hvy⟩
    · rw [ite_eq_right hImage] at hDownPos
      exact absurd hDownPos (lt_irrefl 0)

/-! ## Connectivity of a saturated side

`graph_connected` is the cut form, so connectivity of an induced subgraph is
an ambient statement about `num_edges`.  Phrasing it ambiently once, for an
abstract graph, keeps every transfer below free of subtype bookkeeping. -/

/-- Cut-form connectivity of the subgraph induced on `S`, phrased ambiently. -/
def ConnectedOn (G : CFGraph) (S : Finset G.V) : Prop :=
  ∀ A : Finset G.V, A ⊆ S → (∃ u ∈ A, ∃ v ∈ S, v ∉ A) →
    ∃ u ∈ A, ∃ v ∈ S, v ∉ A ∧ 0 < num_edges G u v

/-- Membership witnessed by an occurrence makes the multiplicity positive. -/
theorem num_edges_pos_of_mem_edges {G : CFGraph} {p q : G.V} (h : (p, q) ∈ G.edges) :
    0 < num_edges G p q :=
  Multiset.card_pos_iff_exists_mem.mpr
    ⟨(p, q), Multiset.mem_filter.mpr ⟨h, Or.inl rfl⟩⟩

/-- `ConnectedOn` is exactly connectivity of the induced subgraph. -/
theorem connectedOn_iff (G : CFGraph) (S : Finset G.V) (hS : S.Nonempty) :
    ConnectedOn G S ↔ graph_connected (Utilities.inducedSubgraph G S hS) := by
  classical
  constructor
  · intro h
    show ∀ U : Finset {v : G.V // v ∈ S},
        (∃ x y : {v : G.V // v ∈ S}, x ∈ U ∧ y ∉ U) →
        ∃ x ∈ U, ∃ y ∉ U,
          num_edges (Utilities.inducedSubgraph G S hS) x y > 0
    intro U hU
    obtain ⟨uStart, uEnd, hStart, hEnd⟩ := hU
    have hmemImage : ∀ x : G.V, ∀ hx : x ∈ S,
        x ∈ U.image Subtype.val ↔ (⟨x, hx⟩ : {v : G.V // v ∈ S}) ∈ U := by
      intro x hx
      constructor
      · intro hIn
        obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hIn
        rwa [show (⟨x, hx⟩ : {v : G.V // v ∈ S}) = z from (Subtype.ext hzx).symm]
      · intro hIn
        exact Finset.mem_image.mpr ⟨⟨x, hx⟩, hIn, rfl⟩
    obtain ⟨u, huA, v, hvS, hvA, hPos⟩ := h (U.image Subtype.val)
      (fun x hx => by
        obtain ⟨z, -, hzx⟩ := Finset.mem_image.mp hx
        exact hzx ▸ z.2)
      ⟨uStart.1, (hmemImage uStart.1 uStart.2).mpr hStart,
        uEnd.1, uEnd.2, fun hBad => hEnd ((hmemImage uEnd.1 uEnd.2).mp hBad)⟩
    have huS : u ∈ S := by
      obtain ⟨z, -, hzu⟩ := Finset.mem_image.mp huA
      exact hzu ▸ z.2
    refine ⟨⟨u, huS⟩, (hmemImage u huS).mp huA, ⟨v, hvS⟩,
      fun hBad => hvA ((hmemImage v hvS).mpr hBad), ?_⟩
    have hEq := Utilities.num_edges_inducedSubgraph G S hS ⟨u, huS⟩ ⟨v, hvS⟩
    rw [hEq]
    exact hPos
  · intro h A hA hwit
    obtain ⟨u₀, hu₀, v₀, hv₀S, hv₀A⟩ := hwit
    have h' : ∀ U : Finset {v : G.V // v ∈ S},
        (∃ x y : {v : G.V // v ∈ S}, x ∈ U ∧ y ∉ U) →
        ∃ x ∈ U, ∃ y ∉ U,
          num_edges (Utilities.inducedSubgraph G S hS) x y > 0 := h
    obtain ⟨u, huU, v, hvU, hPos⟩ := h'
      (Finset.univ.filter fun x : {v : G.V // v ∈ S} => x.1 ∈ A)
      ⟨⟨u₀, hA hu₀⟩, ⟨v₀, hv₀S⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₀⟩,
        fun hBad => hv₀A (Finset.mem_filter.mp hBad).2⟩
    have hEq := Utilities.num_edges_inducedSubgraph G S hS u v
    rw [hEq] at hPos
    exact ⟨u.1, (Finset.mem_filter.mp huU).2, v.1, v.2,
      fun hBad => hvU (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBad⟩), hPos⟩

/-- A property constant along contracted occurrences is constant on the fibres
of `sourceVertexMap`. -/
theorem reach_iff_of_contractedStep (data : GluingDatum target degree)
    (P : data.SourceVertex → Prop)
    (hStep : ∀ p q : data.SourceVertex,
      ContractedStep data contracted p q → (P p ↔ P q))
    {u v : data.SourceVertex} (h : ReachThroughContracted data contracted u v) :
    P u ↔ P v := by
  induction h with
  | rel p q hpq => exact hStep p q hpq
  | refl p => exact Iff.rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- A saturated side contains both endpoints of a contracted occurrence or
neither. -/
theorem mem_iff_of_contractedStep (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {S : Finset data.SourceVertex}
    {T : Finset (contractDatum data hc hab hOne).SourceVertex}
    (hmem : ∀ u : data.SourceVertex,
      u ∈ S ↔ sourceVertexMap data hc hab hOne u ∈ T)
    {p q : data.SourceVertex} (h : ContractedStep data contracted p q) :
    p ∈ S ↔ q ∈ S := by
  obtain ⟨e, he, hp, hq⟩ := h
  have hEq := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e he
  rw [hp, hq] at hEq
  rw [hmem p, hmem q, hEq]

/-- A downstairs occurrence lifts to a surviving upstairs occurrence between
the two fibres. -/
theorem exists_surviving_of_num_edges_contract_pos (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {p q : (contractDatum data hc hab hOne).SourceVertex}
    (h : 0 < num_edges (contractDatum data hc hab hOne).sourceGraph p q) :
    ∃ e : data.SourceEdge, e.1.1 ≠ contracted ∧
      ((sourceVertexMap data hc hab hOne (data.sourceEnds e).1 = p ∧
          sourceVertexMap data hc hab hOne (data.sourceEnds e).2 = q) ∨
        (sourceVertexMap data hc hab hOne (data.sourceEnds e).1 = q ∧
          sourceVertexMap data hc hab hOne (data.sourceEnds e).2 = p)) := by
  classical
  rw [num_edges_contract_sourceGraph] at h
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  exact ⟨e.1, e.2, (Finset.mem_filter.mp he).2⟩

/-- **Connectivity of a saturated side descends.** -/
theorem connectedOn_image (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {S : Finset data.SourceVertex}
    {T : Finset (contractDatum data hc hab hOne).SourceVertex}
    (hmem : ∀ u : data.SourceVertex,
      u ∈ S ↔ sourceVertexMap data hc hab hOne u ∈ T)
    (hConn : ConnectedOn data.sourceGraph S) :
    ConnectedOn (contractDatum data hc hab hOne).sourceGraph T := by
  classical
  intro B hB hwit
  obtain ⟨p₀, hp₀, q₀, hq₀T, hq₀B⟩ := hwit
  set A : Finset data.SourceVertex :=
    Finset.univ.filter (fun u => sourceVertexMap data hc hab hOne u ∈ B) with hAdef
  have hmemA : ∀ u, u ∈ A ↔ sourceVertexMap data hc hab hOne u ∈ B := by
    intro u
    rw [hAdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ u, h⟩⟩
  have hAS : A ⊆ S := fun u hu => (hmem u).mpr (hB ((hmemA u).mp hu))
  obtain ⟨uStart, hStart⟩ := sourceVertexMap_surjective data hc hab hOne p₀
  obtain ⟨uEnd, hEnd⟩ := sourceVertexMap_surjective data hc hab hOne q₀
  obtain ⟨u, huA, v, hvS, hvA, hPos⟩ := hConn A hAS
    ⟨uStart, (hmemA uStart).mpr (by rw [hStart]; exact hp₀),
      uEnd, (hmem uEnd).mpr (by rw [hEnd]; exact hq₀T),
      fun hBad => hq₀B (by rw [← hEnd]; exact (hmemA uEnd).mp hBad)⟩
  have hImage : sourceVertexMap data hc hab hOne u ≠ sourceVertexMap data hc hab hOne v :=
    fun hEq => hvA ((hmemA v).mpr (hEq ▸ (hmemA u).mp huA))
  exact ⟨sourceVertexMap data hc hab hOne u, (hmemA u).mp huA,
    sourceVertexMap data hc hab hOne v, (hmem v).mp hvS,
    fun hBad => hvA ((hmemA v).mpr hBad),
    lt_of_lt_of_le hPos (num_edges_le_contract data hc hab hOne hImage)⟩

/-- **Connectivity of a saturated side lifts.**  Either a fibre straddles the
proposed cut, in which case a contracted occurrence crosses it, or the cut
descends and the downstairs connectivity supplies a surviving crossing
occurrence. -/
theorem connectedOn_preimage (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {S : Finset data.SourceVertex}
    {T : Finset (contractDatum data hc hab hOne).SourceVertex}
    (hmem : ∀ u : data.SourceVertex,
      u ∈ S ↔ sourceVertexMap data hc hab hOne u ∈ T)
    (hConn : ConnectedOn (contractDatum data hc hab hOne).sourceGraph T) :
    ConnectedOn data.sourceGraph S := by
  classical
  intro A hAS hwit
  obtain ⟨uStart, hStart, uEnd, hEndS, hEndA⟩ := hwit
  by_cases hStep : ∀ p q : data.SourceVertex,
      ContractedStep data contracted p q → (p ∈ A ↔ q ∈ A)
  · set B : Finset (contractDatum data hc hab hOne).SourceVertex :=
      Finset.univ.filter (fun p => ∃ u : data.SourceVertex,
        sourceVertexMap data hc hab hOne u = p ∧ u ∈ A) with hBdef
    have hmemB : ∀ u : data.SourceVertex,
        sourceVertexMap data hc hab hOne u ∈ B ↔ u ∈ A := by
      intro u
      rw [hBdef, Finset.mem_filter]
      constructor
      · rintro ⟨-, v, hv, hvA⟩
        exact (reach_iff_of_contractedStep data (fun z => z ∈ A) hStep
          ((sourceVertexMap_eq_iff data hc hab hOne v u).mp hv)).mp hvA
      · intro hu
        exact ⟨Finset.mem_univ _, u, rfl, hu⟩
    have hBT : B ⊆ T := by
      intro p hp
      obtain ⟨-, u, hu, huA⟩ := Finset.mem_filter.mp hp
      exact hu ▸ (hmem u).mp (hAS huA)
    obtain ⟨p, hpB, q, hqT, hqB, hPos⟩ := hConn B hBT
      ⟨sourceVertexMap data hc hab hOne uStart, (hmemB uStart).mpr hStart,
        sourceVertexMap data hc hab hOne uEnd, (hmem uEnd).mp hEndS,
        fun hBad => hEndA ((hmemB uEnd).mp hBad)⟩
    obtain ⟨e, hne, hEnds⟩ :=
      exists_surviving_of_num_edges_contract_pos data hc hab hOne hPos
    rcases hEnds with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(data.sourceEnds e).1, (hmemB _).mp (by rw [h1]; exact hpB),
        (data.sourceEnds e).2, (hmem _).mpr (by rw [h2]; exact hqT),
        fun hBad => hqB (by rw [← h2]; exact (hmemB _).mpr hBad), ?_⟩
      exact num_edges_sourceGraph_pos
        (u := (data.sourceEnds e).1) (v := (data.sourceEnds e).2) data e (Or.inl rfl)
    · refine ⟨(data.sourceEnds e).2, (hmemB _).mp (by rw [h2]; exact hpB),
        (data.sourceEnds e).1, (hmem _).mpr (by rw [h1]; exact hqT),
        fun hBad => hqB (by rw [← h1]; exact (hmemB _).mpr hBad), ?_⟩
      exact num_edges_sourceGraph_pos
        (u := (data.sourceEnds e).2) (v := (data.sourceEnds e).1) data e (Or.inr rfl)
  · push Not at hStep
    obtain ⟨p, q, hpq, hIff⟩ := hStep
    have hpS : p ∈ S ↔ q ∈ S := mem_iff_of_contractedStep data hc hab hOne hmem hpq
    have hEdge : (p, q) ∈ data.sourceGraph.edges :=
      contractedStep_mem_sourceGraph_edges data hpq
    rcases hIff with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨p, hp, q, hpS.mp (hAS hp), hq, num_edges_pos_of_mem_edges hEdge⟩
    · refine ⟨q, hq, p, hpS.mpr (hAS hq), hp, ?_⟩
      have hSymm : num_edges data.sourceGraph q p = num_edges data.sourceGraph p q :=
        num_edges_symmetric data.sourceGraph q p
      rw [hSymm]
      exact num_edges_pos_of_mem_edges hEdge

/-! ## The fibre count, from `ContractionForest`

The vertices lost to the contraction inside a saturated side are counted by
the contracted occurrences inside it.  That is exactly the forest hypothesis,
blockwise, and it is the only place below where `ContractionForest` is used. -/

/-- The two components of `sourceVertexMap`. -/
theorem sourceVertexMap_eq_iff_components (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (u : data.SourceVertex)
    (p : (contractDatum data hc hab hOne).SourceVertex) :
    sourceVertexMap data hc hab hOne u = p ↔
      (GraphContraction.fold target hab u.1.1 = p.1.1 ∧
        (contractVertexPartition data a b
          (GraphContraction.fold target hab u.1.1)).repr u.1.2 = p.1.2) := by
  constructor
  · intro h
    exact ⟨congrArg
        (fun z : (contractDatum data hc hab hOne).SourceVertex => z.1.1) h,
      congrArg (fun z : (contractDatum data hc hab hOne).SourceVertex => z.1.2) h⟩
  · rintro ⟨h1, h2⟩
    exact Subtype.ext (Prod.ext h1 h2)

/-- The fibre of `sourceVertexMap` above a source vertex of the contracted
datum. -/
noncomputable def fibre (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (p : (contractDatum data hc hab hOne).SourceVertex) :
    Finset data.SourceVertex := by
  classical
  exact Finset.univ.filter fun u => sourceVertexMap data hc hab hOne u = p

@[simp] theorem mem_fibre (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (p : (contractDatum data hc hab hOne).SourceVertex) (u : data.SourceVertex) :
    u ∈ fibre data hc hab hOne p ↔ sourceVertexMap data hc hab hOne u = p := by
  classical
  rw [fibre, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ u, h⟩⟩

/-- The occurrences above the contracted target occurrence sitting in one
fibre. -/
noncomputable def contractedOver (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (p : (contractDatum data hc hab hOne).SourceVertex) :
    Finset data.SourceEdge := by
  classical
  exact Finset.univ.filter fun e => e.1.1 = contracted ∧
    sourceVertexMap data hc hab hOne (data.sourceEnds e).1 = p

@[simp] theorem mem_contractedOver (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (p : (contractDatum data hc hab hOne).SourceVertex) (e : data.SourceEdge) :
    e ∈ contractedOver data hc hab hOne p ↔ e.1.1 = contracted ∧
      sourceVertexMap data hc hab hOne (data.sourceEnds e).1 = p := by
  classical
  rw [contractedOver, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩

/-- Above the merged vertex the fibre condition is a condition on the merged
block of the sheet. -/
theorem mem_fibre_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {p : (contractDatum data hc hab hOne).SourceVertex}
    (hp : p.1.1 = (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V))
    (u : data.SourceVertex) :
    u ∈ fibre data hc hab hOne p ↔
      ((u.1.1 = a ∨ u.1.1 = b) ∧
        (mergedPartition data a b).repr u.1.2 = p.1.2) := by
  rw [mem_fibre, sourceVertexMap_eq_iff_components]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hp] at h1
    have hu : u.1.1 = a ∨ u.1.1 = b := by
      by_cases hb : u.1.1 = b
      · exact Or.inr hb
      · rw [GraphContraction.fold_of_ne target hab hb] at h1
        exact Or.inl (congrArg Subtype.val h1)
    refine ⟨hu, ?_⟩
    rw [h1, contractVertexPartition_merge data a b hab] at h2
    exact h2
  · rintro ⟨hu, h2⟩
    have h1 : GraphContraction.fold target hab u.1.1 = p.1.1 := by
      rw [hp]
      rcases hu with h | h <;> rw [h]
      · exact GraphContraction.fold_a target hab
      · exact GraphContraction.fold_self target hab
    refine ⟨h1, ?_⟩
    rw [h1, hp, contractVertexPartition_merge data a b hab]
    exact h2

/-- Above the merged vertex the contracted occurrences in a fibre are the
occurrences whose sheet lies in the merged block. -/
theorem mem_contractedOver_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {p : (contractDatum data hc hab hOne).SourceVertex}
    (hp : p.1.1 = (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V))
    (e : data.SourceEdge) :
    e ∈ contractedOver data hc hab hOne p ↔
      (e.1.1 = contracted ∧
        (mergedPartition data a b).repr e.1.2 = p.1.2) := by
  rw [mem_contractedOver]
  constructor
  · rintro ⟨he, hmap⟩
    refine ⟨he, ?_⟩
    have hEnd : (data.sourceEnds e).1 = data.sourceEndpoint a e.1.2 := by
      have hA : (e.1.1 : target.V × target.V).1 = a := by rw [he, hc]
      show data.sourceEndpoint (e.1.1 : target.V × target.V).1 e.1.2
        = data.sourceEndpoint a e.1.2
      rw [hA]
    rw [hEnd] at hmap
    obtain ⟨-, h2⟩ := (sourceVertexMap_eq_iff_components data hc hab hOne _ p).mp hmap
    have hFst : (data.sourceEndpoint a e.1.2).1.1 = a := rfl
    rw [hFst, GraphContraction.fold_a, contractVertexPartition_merge data a b hab] at h2
    have hRefine : (mergedPartition data a b).repr
        ((data.vertexPartition a).repr e.1.2)
        = (mergedPartition data a b).repr e.1.2 :=
      (vertexPartition_refines_mergedPartition data a b).rel
        ((data.vertexPartition a).rel_repr_left e.1.2)
    exact (hRefine.symm.trans h2)
  · rintro ⟨he, hrepr⟩
    refine ⟨he, ?_⟩
    have hEnd : (data.sourceEnds e).1 = data.sourceEndpoint a e.1.2 := by
      have hA : (e.1.1 : target.V × target.V).1 = a := by rw [he, hc]
      show data.sourceEndpoint (e.1.1 : target.V × target.V).1 e.1.2
        = data.sourceEndpoint a e.1.2
      rw [hA]
    rw [hEnd]
    refine (sourceVertexMap_eq_iff_components data hc hab hOne _ p).mpr ⟨?_, ?_⟩
    · show GraphContraction.fold target hab a = p.1.1
      rw [hp, GraphContraction.fold_a]
    · have hFst : (data.sourceEndpoint a e.1.2).1.1 = a := rfl
      rw [hFst, GraphContraction.fold_a, contractVertexPartition_merge data a b hab]
      have hRefine : (mergedPartition data a b).repr
          ((data.vertexPartition a).repr e.1.2)
          = (mergedPartition data a b).repr e.1.2 :=
        (vertexPartition_refines_mergedPartition data a b).rel
          ((data.vertexPartition a).rel_repr_left e.1.2)
      exact hRefine.trans hrepr

/-- Above the merged vertex the stored sheet of a source vertex is its own
merged-block representative. -/
theorem mergedPartition_repr_snd (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {p : (contractDatum data hc hab hOne).SourceVertex}
    (hp : p.1.1 = (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V)) :
    (mergedPartition data a b).repr p.1.2 = p.1.2 := by
  have h := p.2
  rw [hp] at h
  have hEq : mergedPartition data a b = contractVertexPartition data a b ⟨a, hab⟩ :=
    (contractVertexPartition_merge data a b hab).symm
  rw [hEq]
  exact h

/-- The part of a fibre above one of the two merged target vertices is counted
by the blocks of that vertex's partition inside the merged block. -/
theorem card_fibre_filter_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {p : (contractDatum data hc hab hOne).SourceVertex}
    (hp : p.1.1 = (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V))
    (v : target.V) (hv : v = a ∨ v = b) :
    ((fibre data hc hab hOne p).filter (fun u => u.1.1 = v)).card
      = (SheetPartition.blocksWithin (data.vertexPartition v)
          (mergedPartition data a b)
          ⟨p.1.2, mergedPartition_repr_snd data hc hab hOne hp⟩).card := by
  classical
  refine Finset.card_bij' (fun u hu => ⟨u.1.2, ?_⟩)
    (fun blk _ => (⟨(v, blk.1), blk.2⟩ : data.SourceVertex)) ?_ ?_ ?_ ?_
  · rw [← (Finset.mem_filter.mp hu).2]
    exact u.2
  · intro u hu
    refine (SheetPartition.mem_blocksWithin _ _ _ _).mpr (Subtype.ext ?_)
    exact ((mem_fibre_merge data hc hab hOne hp u).mp (Finset.mem_filter.mp hu).1).2
  · intro blk hblk
    refine Finset.mem_filter.mpr ⟨(mem_fibre_merge data hc hab hOne hp _).mpr ⟨hv, ?_⟩, rfl⟩
    exact congrArg Subtype.val
      ((SheetPartition.mem_blocksWithin _ _ _ _).mp hblk)
  · intro u hu
    exact Subtype.ext (Prod.ext (Finset.mem_filter.mp hu).2.symm rfl)
  · intro blk _
    exact Subtype.ext rfl

/-- The contracted occurrences in a fibre above the merged vertex are counted
by the blocks of the contracted occurrence's partition inside the merged
block. -/
theorem card_contractedOver_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {p : (contractDatum data hc hab hOne).SourceVertex}
    (hp : p.1.1 = (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V)) :
    (contractedOver data hc hab hOne p).card
      = (SheetPartition.blocksWithin (data.edgePartition contracted)
          (mergedPartition data a b)
          ⟨p.1.2, mergedPartition_repr_snd data hc hab hOne hp⟩).card := by
  classical
  refine Finset.card_bij' (fun e he => ⟨e.1.2, ?_⟩)
    (fun blk _ => (⟨(contracted, blk.1), blk.2⟩ : data.SourceEdge)) ?_ ?_ ?_ ?_
  · rw [← (mem_contractedOver data hc hab hOne p e).mp he |>.1]
    exact e.2
  · intro e he
    refine (SheetPartition.mem_blocksWithin _ _ _ _).mpr (Subtype.ext ?_)
    exact ((mem_contractedOver_merge data hc hab hOne hp e).mp he).2
  · intro blk hblk
    refine (mem_contractedOver_merge data hc hab hOne hp _).mpr ⟨rfl, ?_⟩
    exact congrArg Subtype.val
      ((SheetPartition.mem_blocksWithin _ _ _ _).mp hblk)
  · intro e he
    exact Subtype.ext (Prod.ext ((mem_contractedOver data hc hab hOne p e).mp he).1.symm rfl)
  · intro blk _
    exact Subtype.ext rfl

/-- **The fibre count at the merged vertex is the forest hypothesis.** -/
theorem card_fibre_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    {p : (contractDatum data hc hab hOne).SourceVertex}
    (hp : p.1.1 = (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V)) :
    (fibre data hc hab hOne p).card = (contractedOver data hc hab hOne p).card + 1 := by
  classical
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := fibre data hc hab hOne p) (fun u => u.1.1 = a)
  have hNeg : ((fibre data hc hab hOne p).filter fun u => ¬ u.1.1 = a)
      = (fibre data hc hab hOne p).filter fun u => u.1.1 = b := by
    refine Finset.filter_congr ?_
    intro u hu
    have hCases := ((mem_fibre_merge data hc hab hOne hp u).mp hu).1
    constructor
    · intro hNe
      exact hCases.resolve_left hNe
    · intro hEqB hEqA
      exact hab (hEqA.symm.trans hEqB)
  rw [hNeg, card_fibre_filter_merge data hc hab hOne hp a (Or.inl rfl),
    card_fibre_filter_merge data hc hab hOne hp b (Or.inr rfl)] at hSplit
  rw [card_contractedOver_merge data hc hab hOne hp, ← hSplit]
  exact (hForest ⟨p.1.2, mergedPartition_repr_snd data hc hab hOne hp⟩).symm

/-- Away from the merged vertex the fibre is a single source vertex and carries
no contracted occurrence. -/
theorem card_fibre_of_ne_merge (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {p : (contractDatum data hc hab hOne).SourceVertex}
    (hp : p.1.1 ≠ (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V)) :
    (fibre data hc hab hOne p).card = (contractedOver data hc hab hOne p).card + 1 := by
  classical
  have hca : p.1.1.1 ≠ a := fun hEq => hp (Subtype.ext hEq)
  have hcb : p.1.1.1 ≠ b := p.1.1.2
  have hPart : contractVertexPartition data a b p.1.1
      = data.vertexPartition p.1.1.1 :=
    contractVertexPartition_of_ne data a b hca
  have hReprP : (data.vertexPartition p.1.1.1).repr p.1.2 = p.1.2 := by
    have h := p.2
    rw [← hPart]
    exact h
  have hEmpty : contractedOver data hc hab hOne p = ∅ := by
    refine Finset.eq_empty_of_forall_notMem ?_
    intro e he
    obtain ⟨heq, hmap⟩ := (mem_contractedOver data hc hab hOne p e).mp he
    obtain ⟨h1, -⟩ := (sourceVertexMap_eq_iff_components data hc hab hOne _ p).mp hmap
    have hA : (data.sourceEnds e).1.1.1 = a := by
      rw [sourceEnds_fst_fst, heq, hc]
    rw [hA, GraphContraction.fold_a] at h1
    exact hp h1.symm
  have hSingleton : fibre data hc hab hOne p
      = {(⟨(p.1.1.1, p.1.2), hReprP⟩ : data.SourceVertex)} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · refine (mem_fibre data hc hab hOne p _).mpr
        ((sourceVertexMap_eq_iff_components data hc hab hOne _ p).mpr ⟨?_, ?_⟩)
      · show GraphContraction.fold target hab p.1.1.1 = p.1.1
        exact GraphContraction.fold_of_ne target hab hcb
      · show (contractVertexPartition data a b
          (GraphContraction.fold target hab p.1.1.1)).repr p.1.2 = p.1.2
        rw [GraphContraction.fold_of_ne target hab hcb]
        rw [show (⟨p.1.1.1, hcb⟩ : GraphContraction.Vertex target b) = p.1.1 from rfl,
          hPart]
        exact hReprP
    · intro u hu
      obtain ⟨h1, h2⟩ := (sourceVertexMap_eq_iff_components data hc hab hOne u p).mp
        ((mem_fibre data hc hab hOne p u).mp hu)
      have hub : u.1.1 ≠ b := by
        intro hEq
        rw [hEq, GraphContraction.fold_self] at h1
        exact hp h1.symm
      rw [GraphContraction.fold_of_ne target hab hub] at h1 h2
      have hvc : u.1.1 = p.1.1.1 := congrArg Subtype.val h1
      rw [show (⟨u.1.1, hub⟩ : GraphContraction.Vertex target b) = p.1.1 from h1,
        hPart] at h2
      have hu2 : u.1.2 = p.1.2 := by
        rw [← h2, ← hvc]
        exact u.2.symm
      exact Subtype.ext (Prod.ext hvc hu2)
  rw [hSingleton, hEmpty, Finset.card_empty]
  exact Finset.card_singleton _

/-- **The fibre count.**  Every fibre of `sourceVertexMap` has one more vertex
than it carries contracted occurrences: away from the wall both sides are
trivial, and at the merged vertex this is exactly `ContractionForest`. -/
theorem card_fibre_eq (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (p : (contractDatum data hc hab hOne).SourceVertex) :
    (fibre data hc hab hOne p).card = (contractedOver data hc hab hOne p).card + 1 := by
  by_cases hp : p.1.1 = (⟨a, hab⟩ : (GraphContraction.contract target hab hOne).V)
  · exact card_fibre_merge data hc hab hOne hForest hp
  · exact card_fibre_of_ne_merge data hc hab hOne hp

/-! ## The genus of a saturated side -/

/-- The genus of an induced subgraph, ambiently. -/
theorem genus_inducedSubgraph (G : CFGraph) (S : Finset G.V) (hS : S.Nonempty) :
    genus (Utilities.inducedSubgraph G S hS)
      = ((G.edges.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card : ℤ) - S.card + 1 := by
  classical
  unfold genus
  rw [Utilities.inducedSubgraph_edge_card_eq_filter,
    Utilities.inducedSubgraph_vertex_card]

/-- The edges of the subgraph a source graph induces on a side, counted as
source occurrences. -/
theorem card_inducedEdges_sourceGraph (data : GluingDatum target degree)
    (S : Finset data.SourceVertex) :
    (data.sourceGraph.edges.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card
      = ((Finset.univ : Finset data.SourceEdge).filter
          fun e => (data.sourceEnds e).1 ∈ S ∧ (data.sourceEnds e).2 ∈ S).card := by
  have h := Multiset.filter_map
    (p := fun e : data.SourceVertex × data.SourceVertex => e.1 ∈ S ∧ e.2 ∈ S)
    data.sourceEnds (Finset.univ : Finset data.SourceEdge).val
  calc (data.sourceGraph.edges.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card
      = Multiset.card (Multiset.filter
          (fun e : data.SourceVertex × data.SourceVertex => e.1 ∈ S ∧ e.2 ∈ S)
          ((Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds)) := rfl
    _ = _ := by rw [h, Multiset.card_map]; rfl

/-- The source occurrences above the contracted target occurrence lying inside
a side. -/
noncomputable def contractedInside (data : GluingDatum target degree)
    (S : Finset data.SourceVertex) : Finset data.SourceEdge := by
  classical
  exact Finset.univ.filter fun e => e.1.1 = contracted ∧ (data.sourceEnds e).1 ∈ S

@[simp] theorem mem_contractedInside (data : GluingDatum target degree)
    (S : Finset data.SourceVertex) (e : data.SourceEdge) :
    e ∈ contractedInside (contracted := contracted) data S ↔
      e.1.1 = contracted ∧ (data.sourceEnds e).1 ∈ S := by
  classical
  rw [contractedInside, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ e, h⟩⟩

/-- **The vertex count.**  A saturated side loses exactly one vertex for each
contracted occurrence it contains. -/
theorem card_side_eq (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    {S : Finset data.SourceVertex}
    {T : Finset (contractDatum data hc hab hOne).SourceVertex}
    (hmem : ∀ u : data.SourceVertex,
      u ∈ S ↔ sourceVertexMap data hc hab hOne u ∈ T) :
    S.card = T.card + (contractedInside (contracted := contracted) data S).card := by
  classical
  have hVertices : S.card
      = ∑ p ∈ T, (fibre data hc hab hOne p).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun u => sourceVertexMap data hc hab hOne u) (t := T)
      (fun u hu => (hmem u).mp hu)]
    refine Finset.sum_congr rfl fun p hp => ?_
    congr 1
    ext u
    rw [Finset.mem_filter, mem_fibre]
    exact ⟨fun h => h.2, fun h => ⟨(hmem u).mpr (h ▸ hp), h⟩⟩
  have hEdges : (contractedInside (contracted := contracted) data S).card
      = ∑ p ∈ T, (contractedOver data hc hab hOne p).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun e => sourceVertexMap data hc hab hOne (data.sourceEnds e).1) (t := T)
      (fun e he => (hmem _).mp ((mem_contractedInside data S e).mp he).2)]
    refine Finset.sum_congr rfl fun p hp => ?_
    congr 1
    ext e
    rw [Finset.mem_filter, mem_contractedInside, mem_contractedOver]
    constructor
    · rintro ⟨⟨he, -⟩, hmap⟩
      exact ⟨he, hmap⟩
    · rintro ⟨he, hmap⟩
      exact ⟨⟨he, (hmem _).mpr (hmap ▸ hp)⟩, hmap⟩
  rw [hVertices, hEdges, Finset.card_eq_sum_ones T, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [card_fibre_eq data hc hab hOne hForest p]
  omega

/-- **The edge count.**  The occurrences inside a saturated side are the
occurrences inside its image together with the contracted occurrences it
contains. -/
theorem card_inducedEdges_eq (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    {S : Finset data.SourceVertex}
    {T : Finset (contractDatum data hc hab hOne).SourceVertex}
    (hmem : ∀ u : data.SourceVertex,
      u ∈ S ↔ sourceVertexMap data hc hab hOne u ∈ T) :
    ((Finset.univ : Finset data.SourceEdge).filter
        fun e => (data.sourceEnds e).1 ∈ S ∧ (data.sourceEnds e).2 ∈ S).card
      = ((Finset.univ : Finset (contractDatum data hc hab hOne).SourceEdge).filter
          fun e => ((contractDatum data hc hab hOne).sourceEnds e).1 ∈ T ∧
            ((contractDatum data hc hab hOne).sourceEnds e).2 ∈ T).card
        + (contractedInside (contracted := contracted) data S).card := by
  classical
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset data.SourceEdge).filter
      fun e => (data.sourceEnds e).1 ∈ S ∧ (data.sourceEnds e).2 ∈ S)
    (fun e => e.1.1 = contracted)
  have hContracted : (((Finset.univ : Finset data.SourceEdge).filter
        fun e => (data.sourceEnds e).1 ∈ S ∧ (data.sourceEnds e).2 ∈ S).filter
      fun e => e.1.1 = contracted)
      = contractedInside (contracted := contracted) data S := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter, mem_contractedInside]
    constructor
    · rintro ⟨⟨-, hIn, -⟩, he⟩
      exact ⟨he, hIn⟩
    · rintro ⟨he, hIn⟩
      have hSame := sourceVertexMap_sourceEnds_eq_of_contracted data hc hab hOne e he
      exact ⟨⟨Finset.mem_univ e, hIn, (hmem _).mpr (hSame ▸ (hmem _).mp hIn)⟩, he⟩
  have hSurviving : (((Finset.univ : Finset data.SourceEdge).filter
        fun e => (data.sourceEnds e).1 ∈ S ∧ (data.sourceEnds e).2 ∈ S).filter
      fun e => ¬ e.1.1 = contracted).card
      = ((Finset.univ : Finset (contractDatum data hc hab hOne).SourceEdge).filter
          fun e => ((contractDatum data hc hab hOne).sourceEnds e).1 ∈ T ∧
            ((contractDatum data hc hab hOne).sourceEnds e).2 ∈ T).card := by
    refine Finset.card_bij'
      (fun e he => sourceEdgeMap data hc hab hOne ⟨e, (Finset.mem_filter.mp he).2⟩)
      (fun e _ => ((sourceEdgeEquiv data hc hab hOne).symm e).1) ?_ ?_ ?_ ?_
    · intro e he
      obtain ⟨hIn, hne⟩ := Finset.mem_filter.mp he
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hIn
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [congrArg Prod.fst (sourceEnds_sourceEdgeMap data hc hab hOne ⟨e, hne⟩)]
        exact (hmem _).mp h1
      · rw [congrArg Prod.snd (sourceEnds_sourceEdgeMap data hc hab hOne ⟨e, hne⟩)]
        exact (hmem _).mp h2
    · intro f hf
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hf
      have hMap : sourceEdgeMap data hc hab hOne
          ((sourceEdgeEquiv data hc hab hOne).symm f) = f :=
        (sourceEdgeEquiv data hc hab hOne).apply_symm_apply f
      have hEnds := sourceEnds_sourceEdgeMap data hc hab hOne
        ((sourceEdgeEquiv data hc hab hOne).symm f)
      rw [hMap] at hEnds
      have hFst : ((contractDatum data hc hab hOne).sourceEnds f).1
          = sourceVertexMap data hc hab hOne
            (data.sourceEnds ((sourceEdgeEquiv data hc hab hOne).symm f).1).1 :=
        congrArg Prod.fst hEnds
      have hSnd : ((contractDatum data hc hab hOne).sourceEnds f).2
          = sourceVertexMap data hc hab hOne
            (data.sourceEnds ((sourceEdgeEquiv data hc hab hOne).symm f).1).2 :=
        congrArg Prod.snd hEnds
      rw [hFst] at h1
      rw [hSnd] at h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hmem _).mpr h1, (hmem _).mpr h2⟩,
        ((sourceEdgeEquiv data hc hab hOne).symm f).2⟩
    · intro e he
      exact congrArg Subtype.val
        ((sourceEdgeEquiv data hc hab hOne).symm_apply_apply
          ⟨e, (Finset.mem_filter.mp he).2⟩)
    · intro f _
      exact (sourceEdgeEquiv data hc hab hOne).apply_symm_apply f
  rw [hContracted] at hSplit
  rw [hSurviving] at hSplit
  omega

/-- **The genus of a saturated side is unchanged.**  One vertex and one edge
disappear together for every contracted occurrence inside the side; that is
the forest hypothesis and nothing else. -/
theorem genus_side_eq (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    {S : Finset data.SourceVertex}
    {T : Finset (contractDatum data hc hab hOne).SourceVertex}
    (hmem : ∀ u : data.SourceVertex,
      u ∈ S ↔ sourceVertexMap data hc hab hOne u ∈ T)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    genus (Utilities.inducedSubgraph data.sourceGraph S hS)
      = genus (Utilities.inducedSubgraph
          (contractDatum data hc hab hOne).sourceGraph T hT) := by
  classical
  have hUp : genus (Utilities.inducedSubgraph data.sourceGraph S hS)
      = ((data.sourceGraph.edges.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card : ℤ)
        - S.card + 1 :=
    genus_inducedSubgraph data.sourceGraph S hS
  have hDown : genus (Utilities.inducedSubgraph
        (contractDatum data hc hab hOne).sourceGraph T hT)
      = (((contractDatum data hc hab hOne).sourceGraph.edges.filter
          (fun e => e.1 ∈ T ∧ e.2 ∈ T)).card : ℤ) - T.card + 1 :=
    genus_inducedSubgraph (contractDatum data hc hab hOne).sourceGraph T hT
  have hE1 := card_inducedEdges_sourceGraph data S
  have hE2 := card_inducedEdges_sourceGraph (contractDatum data hc hab hOne) T
  have hE := card_inducedEdges_eq data hc hab hOne hmem
  have hV := card_side_eq data hc hab hOne hForest hmem
  have harith : ((data.sourceGraph.edges.filter
        (fun e => e.1 ∈ S ∧ e.2 ∈ S)).card : ℤ) - S.card + 1
      = (((contractDatum data hc hab hOne).sourceGraph.edges.filter
          (fun e => e.1 ∈ T ∧ e.2 ∈ T)).card : ℤ) - T.card + 1 := by
    omega
  exact hUp.trans (harith.trans hDown.symm)

/-! ## The answer: danglingness is compatible with the contraction -/

/-- **A dangling cut descends and lifts.**  Both directions hold, and the only
hypothesis beyond the setup is `ContractionForest`, which is what makes the
genus of the side survive the contraction. -/
theorem nonempty_danglingSide_map_iff (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    {x y : data.SourceVertex}
    {p q : (contractDatum data hc hab hOne).SourceVertex}
    (hp : p = sourceVertexMap data hc hab hOne x)
    (hq : q = sourceVertexMap data hc hab hOne y)
    {e : data.SourceEdge} (hne : e.1.1 ≠ contracted)
    (hEnds : data.sourceEnds e = (x, y) ∨ data.sourceEnds e = (y, x)) :
    Nonempty (DanglingSide data.sourceGraph x y) ↔
      Nonempty (DanglingSide (contractDatum data hc hab hOne).sourceGraph p q) := by
  classical
  subst hp
  subst hq
  constructor
  · rintro ⟨cut⟩
    have hmem : ∀ u : data.SourceVertex,
        u ∈ cut.side ↔ sourceVertexMap data hc hab hOne u
          ∈ cut.side.image (sourceVertexMap data hc hab hOne) := by
      intro u
      constructor
      · intro hu
        exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
      · intro hu
        obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hu
        exact (separatingEdgeCut_mem_iff_of_sourceVertexMap_eq data hc hab hOne
          cut.toSeparatingEdgeCut hEnds hne hvu).mp hv
    have hmemC : ∀ u : data.SourceVertex,
        u ∈ (Finset.univ \ cut.side) ↔ sourceVertexMap data hc hab hOne u
          ∈ (Finset.univ \ cut.side.image (sourceVertexMap data hc hab hOne)) := by
      intro u
      have h1 : u ∈ (Finset.univ \ cut.side) ↔ (u ∈ Finset.univ ∧ u ∉ cut.side) :=
        Finset.mem_sdiff
      have h2 : sourceVertexMap data hc hab hOne u
            ∈ (Finset.univ \ cut.side.image (sourceVertexMap data hc hab hOne))
          ↔ (sourceVertexMap data hc hab hOne u ∈ Finset.univ ∧
              sourceVertexMap data hc hab hOne u
                ∉ cut.side.image (sourceVertexMap data hc hab hOne)) :=
        Finset.mem_sdiff
      refine h1.trans (Iff.trans ?_ h2.symm)
      exact ⟨fun h => ⟨Finset.mem_univ _, fun hBad => h.2 ((hmem u).mpr hBad)⟩,
        fun h => ⟨Finset.mem_univ _, fun hBad => h.2 ((hmem u).mp hBad)⟩⟩
    have hx : x ∈ cut.side := cut.left_mem
    have hy : y ∉ cut.side := cut.right_not_mem
    refine ⟨{ side := cut.side.image (sourceVertexMap data hc hab hOne)
              left_mem := (hmem x).mp hx
              right_not_mem := fun hBad => hy ((hmem y).mpr hBad)
              cross_num_edges := ?_
              side_connected := ?_
              complement_connected := ?_
              side_genus_zero := ?_ }⟩
    · exact fun u v hu hv => cross_num_edges_image data hc hab hOne hmem hx hy
        (fun s hs t ht => cut.cross_num_edges s t hs ht) u v hu hv
    · exact (connectedOn_iff _ _ _).mp (connectedOn_image data hc hab hOne hmem
        ((connectedOn_iff _ cut.side ⟨x, hx⟩).mpr cut.side_connected))
    · exact (connectedOn_iff _ _ _).mp (connectedOn_image data hc hab hOne hmemC
        ((connectedOn_iff _ (Finset.univ \ cut.side)
          ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩).mpr
            cut.complement_connected))
    · exact (genus_side_eq data hc hab hOne hForest hmem ⟨x, hx⟩
        ⟨_, (hmem x).mp hx⟩).symm.trans cut.side_genus_zero
  · rintro ⟨cut⟩
    have hmem : ∀ u : data.SourceVertex,
        u ∈ (Finset.univ.filter
            fun u => sourceVertexMap data hc hab hOne u ∈ cut.side) ↔
          sourceVertexMap data hc hab hOne u ∈ cut.side := by
      intro u
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ u, h⟩⟩
    have hmemC : ∀ u : data.SourceVertex,
        u ∈ (Finset.univ \ Finset.univ.filter
            fun u => sourceVertexMap data hc hab hOne u ∈ cut.side) ↔
          sourceVertexMap data hc hab hOne u ∈ (Finset.univ \ cut.side) := by
      intro u
      have h1 : u ∈ (Finset.univ \ Finset.univ.filter
            fun u => sourceVertexMap data hc hab hOne u ∈ cut.side)
          ↔ (u ∈ Finset.univ ∧ u ∉ Finset.univ.filter
              fun u => sourceVertexMap data hc hab hOne u ∈ cut.side) :=
        Finset.mem_sdiff
      have h2 : sourceVertexMap data hc hab hOne u ∈ (Finset.univ \ cut.side)
          ↔ (sourceVertexMap data hc hab hOne u ∈ Finset.univ ∧
              sourceVertexMap data hc hab hOne u ∉ cut.side) :=
        Finset.mem_sdiff
      refine h1.trans (Iff.trans ?_ h2.symm)
      exact ⟨fun h => ⟨Finset.mem_univ _, fun hBad => h.2 ((hmem u).mpr hBad)⟩,
        fun h => ⟨Finset.mem_univ _, fun hBad => h.2 ((hmem u).mp hBad)⟩⟩
    have hx : x ∈ (Finset.univ.filter
        fun u => sourceVertexMap data hc hab hOne u ∈ cut.side) :=
      (hmem x).mpr cut.left_mem
    have hy : y ∉ (Finset.univ.filter
        fun u => sourceVertexMap data hc hab hOne u ∈ cut.side) :=
      fun hBad => cut.right_not_mem ((hmem y).mp hBad)
    refine ⟨{ side := Finset.univ.filter
                fun u => sourceVertexMap data hc hab hOne u ∈ cut.side
              left_mem := hx
              right_not_mem := hy
              cross_num_edges := ?_
              side_connected := ?_
              complement_connected := ?_
              side_genus_zero := ?_ }⟩
    · exact fun u v hu hv => cross_num_edges_preimage data hc hab hOne hmem hne hEnds
        hx hy (fun s hs t ht => cut.cross_num_edges s t hs ht) u hu v hv
    · exact (connectedOn_iff _ _ _).mp (connectedOn_preimage data hc hab hOne hmem
        ((connectedOn_iff _ cut.side ⟨_, cut.left_mem⟩).mpr cut.side_connected))
    · exact (connectedOn_iff _ _ _).mp (connectedOn_preimage data hc hab hOne hmemC
        ((connectedOn_iff _ (Finset.univ \ cut.side)
          ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, cut.right_not_mem⟩⟩).mpr
            cut.complement_connected))
    · exact (genus_side_eq data hc hab hOne hForest hmem ⟨x, hx⟩
        ⟨_, cut.left_mem⟩).trans cut.side_genus_zero

/-- **Danglingness is unchanged on the surviving occurrences.** -/
theorem isDangling_sourceEdgeMap_iff (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) :
    IsDangling (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne e)
      ↔ IsDangling data e.1 := by
  have hEnds := sourceEnds_sourceEdgeMap data hc hab hOne e
  have hFst : ((contractDatum data hc hab hOne).sourceEnds
        (sourceEdgeMap data hc hab hOne e)).1
      = sourceVertexMap data hc hab hOne (data.sourceEnds e.1).1 :=
    congrArg Prod.fst hEnds
  have hSnd : ((contractDatum data hc hab hOne).sourceEnds
        (sourceEdgeMap data hc hab hOne e)).2
      = sourceVertexMap data hc hab hOne (data.sourceEnds e.1).2 :=
    congrArg Prod.snd hEnds
  constructor
  · rintro (h | h)
    · exact Or.inl ((nonempty_danglingSide_map_iff data hc hab hOne hForest
        hFst hSnd e.2 (Or.inl rfl)).mpr h)
    · exact Or.inr ((nonempty_danglingSide_map_iff data hc hab hOne hForest
        hSnd hFst e.2 (Or.inr rfl)).mpr h)
  · rintro (h | h)
    · exact Or.inl ((nonempty_danglingSide_map_iff data hc hab hOne hForest
        hFst hSnd e.2 (Or.inl rfl)).mp h)
    · exact Or.inr ((nonempty_danglingSide_map_iff data hc hab hOne hForest
        hSnd hFst e.2 (Or.inr rfl)).mp h)

/-- `DanglingPreserved` is a theorem. -/
theorem danglingPreserved_of_contractionForest (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) :
    DanglingPreserved data hc hab hOne :=
  fun e h => (isDangling_sourceEdgeMap_iff data hc hab hOne hForest e).mpr h

/-- `DanglingReflected` is a theorem, under the same hypothesis. -/
theorem danglingReflected_of_contractionForest (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) :
    DanglingReflected data hc hab hOne :=
  fun e h => (isDangling_sourceEdgeMap_iff data hc hab hOne hForest e).mp h

/-- `DanglingCompatible` follows from the forest hypothesis alone. -/
theorem danglingCompatible_of_contractionForest (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) :
    DanglingCompatible data hc hab hOne :=
  ⟨danglingPreserved_of_contractionForest data hc hab hOne hForest,
    danglingReflected_of_contractionForest data hc hab hOne hForest⟩

end General

/-! ## The wall event

`IncomingSourceCases.exists_classification` works over `CFGraph.{0}`, and so
does `SourceFibreForest.contractionForest_of_fullDimensional`, which is what
turns the metric facts at the event into the forest hypothesis. -/

section WallEvent

variable {target : CFGraph.{0}} {degree : ℕ} {a b : target.V}
  {contracted : target.edges}

/-- **The decision.**  `WallDegeneration.DanglingCompatible` is *not* an extra
hypothesis: it is a consequence of a full-dimensional source presentation
together with the metric facts that hold at a wall event -- exactly the
hypothesis set of `IncomingSourceCases.exists_classification`, with no
addition. -/
theorem danglingCompatible_of_fullDimensional {coordinate : Type*} [Fintype coordinate]
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
    DanglingCompatible data hc hab hOne :=
  danglingCompatible_of_contractionForest data hc hab hOne
    (SourceFibreForest.contractionForest_of_fullDimensional
      (data := data) (coordinate := coordinate) fullDim coordinates
      hNonnegative hRows hc hZero)

end WallEvent

end DraismaVargas.LocalCases.WallAdmissibility
