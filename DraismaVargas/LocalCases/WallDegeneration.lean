module

public import DraismaVargas.Infrastructure.ContractionFibre
public import DraismaVargas.LocalCases.FullDimensionalSource

@[expose] public section

/-!
# The codimension-one bridge: what a contraction supplies, and what it does not

`FullDimensionalSource` establishes that
`W4StableSource.AuxR0SourceInput data star` and a square honest stable
presentation of the **same** `data` are contradictory, so the four-valent (W4)
interface can only be fed by relating **two** data.  It states the relation as
`FullDimensionalSource.WallDegeneration`, with two fields, `edge_card` and
`stablePath`.  Transferring the `dangling_no_glue` and `nonDangling_valency`
fields along that relation would need an equivalence
`wallDatum.SourceEdge ≃ data.SourceEdge` compatible with `IsDangling` and
`Incident`.

This module takes the candidate the library supplies for the wall datum —
`GluingContraction.contractDatum`, Draisma–Vargas Part I, Definition 15 (the
limit gluing datum, `def-limit-gluing`), arXiv:1909.12924 — and determines what
it does and does not give.

## What is proved here

* `edge_card_contract` — the `edge_card` field of `WallDegeneration`, outright,
  so half the bridge is a theorem.
* `not_nonempty_sourceEdge_equiv` — the equivalence
  `wallDatum.SourceEdge ≃ data.SourceEdge` **does not exist**, and not for a
  subtle reason.  The contracted datum deletes the whole source fibre above the
  contracted target occurrence, and that fibre is never empty
  (`exists_sourceEdge_over`), so the two types have different cardinalities
  (`card_sourceEdge_contractDatum_lt`).  The correct shape is an embedding
  `sourceEdgeEmbedding : wallDatum.SourceEdge ↪ data.SourceEdge`, whose image
  is the complement of that fibre.
* `sourceEdgeIndex_sourceEdgeEmbedding` — the embedding preserves the
  ramification index (`ContractionFibre`, restated).
* `incident_sourceEdgeMap`, `incident_sourceEdgeMap_iff`,
  `incident_sourceEdgeMap_iff_of_ne` — incidence transfers forwards
  unconditionally, is reflected exactly up to `ReachThroughContracted`, and is
  therefore reflected *verbatim* at every source vertex lying over a target
  vertex other than the two ends of the contracted occurrence.  So `Incident`
  compatibility is **not** the obstruction: it fails only at the merged vertex,
  and it fails there by design.
* `contractedStep_side_iff`, `reachThroughContracted_side_iff`,
  `danglingSide_mem_iff_of_sourceVertexMap_eq` — no fibre of
  `GluingContraction.sourceVertexMap` straddles the cut of a surviving dangling
  occurrence.  The cut is crossed by exactly one occurrence, and a contracted
  occurrence is not it.
* `danglingEdgeNoGlue_contractDatum`, `nonDanglingValency_sourceVertexMap` —
  the two W4 fields, transferred, each from the *minimal* danglingness
  hypothesis it actually needs.
* `card_nonDanglingEdge_contractDatum_lt` — the wall datum's stable model has
  strictly fewer edges.
* `wallDegeneration_contractDatum`, `stablePath_card_contractDatum` — the
  bridge and the `stablePath_card` field it buys, with `edge_card` discharged
  and `stablePath` passed through.
* `not_nonempty_labelling_of_wallDegeneration` — a datum carrying a
  `WallDegeneration` from a full-dimensional one admits no square honest stable
  labelling of its own.  The inconsistency `FullDimensionalSource` found is
  therefore not a defect of the bridge: it is the statement that the bridge
  relates two genuinely different data.

## Danglingness compatibility

Danglingness is where the contraction alone does not suffice, and **its two
directions are not symmetric**.  `IsDangling data e` says that deleting `e`
separates `data.sourceGraph` into two connected pieces, one of genus zero.

*Upstairs implies downstairs (`DanglingPreserved`) holds.*  The one
combinatorial step is proved here: `reachThroughContracted_side_iff` shows the
side of the cut is a union of fibres of `sourceVertexMap`, so it pushes forward
to a well-defined set of wall-datum source vertices; the mapped occurrence is
still its only crossing occurrence, both sides stay connected because they are
continuous images of connected sets, and contracting edges inside a genus-zero
side keeps it a tree.  Completing the proof needs only bookkeeping for
connectivity and genus of `Utilities.inducedSubgraph` under contraction, not a
new mathematical idea; this module carries the statement as a hypothesis.

*Downstairs implies upstairs (`DanglingReflected`) fails in general.*  The
same lemma pulls a downstairs cut back to a cut crossed by exactly one
occurrence, and the fibres are connected, so the pullback is again a separating
edge cut with connected sides.  But genus is **not** preserved backwards: the
genus of the pulled-back side is the genus of the downstairs side plus the
number of independent cycles carried by the contracted occurrences inside it.
A side of genus zero downstairs can therefore have positive genus upstairs, so
the contraction genuinely **creates** dangling occurrences whenever the source
fibre over the contracted target occurrence carries a cycle on one side of the
cut.  Nothing in the definition of the contraction rules that out; the same
phenomenon appears from the other side in the fact that ramification is
additive under contraction only when the contracted source fibre is a forest
(`ContractionRamification`).

*Why that matters for W4.*  The two fields `FullDimensionalSource` says do
not transfer both need the reverse direction, the one that fails in general:
`dangling_no_glue` for the wall datum quantifies over occurrences downstairs,
so `danglingEdgeNoGlue_contractDatum` consumes `DanglingReflected`; and
`nonDanglingValency_sourceVertexMap` consumes both directions, and even then
only away from the wall.  So those fields are not consequences of the same
fields upstairs.  Either they are genuine extra hypotheses on the wall datum,
or the contraction must be restricted to one whose contracted source fibre is a
forest (`ContractionRamification.ContractionForest`); Part I obtains forest-ness
from genus preservation, the hypothesis of `lemma-dangling-limit`.
`W4Bridge.auxR0SourceInput_of_contraction` carries
`DanglingReflected` alongside that forest hypothesis.  At an actual wall event
both directions are theorems:
`WallAdmissibility.danglingCompatible_of_fullDimensional` derives them from a
full-dimensional presentation and the wall metric.

## `WallDegeneration.stablePath`

It is a hypothesis here, and it is *not* induced by the occurrence
correspondence.  Even granting full danglingness compatibility, the contraction
strictly loses surviving occurrences: a full-dimensional datum has no entirely
dangling target fibre (`FullDimensionalSourcePresentation.noDanglingTargetFibres`),
so at least one surviving occurrence sits above the contracted target
occurrence and is deleted (`card_nonDanglingEdge_contractDatum_lt`).  Any
equivalence `StablePath wallDatum ≃ StablePath data` must therefore merge
stable classes upstairs to compensate — which is precisely the paper's claim
that the stable model `H(M)` survives the degeneration.  This module does not
prove it for an abstract contraction; at an actual wall event it is
`WallAdmissibilityStable.stablePath_equiv`.  The hypothesis is consistent: the
counts it forces (`#StablePath wallDatum = |E(wallTarget)| + 1`) are exactly
the W4 field, and they refute only the wall datum's *own* squareness, which is
`not_nonempty_labelling_of_wallDegeneration` rather than a contradiction.
-/

namespace DraismaVargas.LocalCases.WallDegeneration

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionFibre
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-! ## The candidate wall datum, and the `edge_card` field

Throughout, the wall datum is `GluingContraction.contractDatum data hc hab hOne`
over the target `GraphContraction.contract target hab hOne`: Draisma–Vargas
Part I, Definition 15, the contraction of one target edge occurrence.  Its `edge_card`
obligation is immediate. -/

/-- Contracting one target occurrence removes exactly one target edge. -/
theorem edge_card_contract (hab : a ≠ b) (hOne : num_edges target a b = 1) :
    target.edges.card = (GraphContraction.contract target hab hOne).edges.card + 1 := by
  have hle : 1 ≤ Multiset.card target.edges :=
    GraphContraction.one_le_card_edges target hOne
  have hcard : Multiset.card (GraphContraction.contract target hab hOne).edges
      = Multiset.card target.edges - 1 :=
    GraphContraction.card_edges_contract target hab hOne
  omega

/-! ## The occurrences above the contracted target edge have nowhere to go -/

/-- Every target occurrence carries at least one source occurrence: the block
of the sheet `0`, which exists because the degree is positive. -/
theorem exists_sourceEdge_over (data : GluingDatum target degree)
    (edge : target.edges) : ∃ e : data.SourceEdge, e.1.1 = edge :=
  ⟨data.sourceEdge edge ⟨0, data.degree_pos⟩, rfl⟩

/-- The contracted datum has strictly fewer source occurrences than the datum
it comes from: exactly the occurrences above the contracted target occurrence
are lost, and there is at least one of those. -/
theorem card_sourceEdge_contractDatum_lt (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    Fintype.card (contractDatum data hc hab hOne).SourceEdge
      < Fintype.card data.SourceEdge := by
  classical
  obtain ⟨x, hx⟩ := exists_sourceEdge_over data contracted
  calc Fintype.card (contractDatum data hc hab hOne).SourceEdge
      = Fintype.card {e : data.SourceEdge // e.1.1 ≠ contracted} :=
        (Fintype.card_congr (sourceEdgeEquiv data hc hab hOne)).symm
    _ < Fintype.card data.SourceEdge :=
        Fintype.card_subtype_lt (p := fun e : data.SourceEdge => e.1.1 ≠ contracted)
          (x := x) (not_not_intro hx)

/-- **The equivalence of source occurrences does not exist.**

`FullDimensionalSource` records that transferring the `dangling_no_glue` and
`nonDangling_valency` fields would need an equivalence
`wallDatum.SourceEdge ≃ data.SourceEdge`.  For the contraction — the
candidate wall datum the library supplies — no such equivalence exists, and the
reason has nothing to do with `IsDangling` or `Incident`: the two types have
different cardinalities. -/
theorem not_nonempty_sourceEdge_equiv (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    ¬ Nonempty ((contractDatum data hc hab hOne).SourceEdge ≃ data.SourceEdge) := by
  rintro ⟨equiv⟩
  exact absurd (Fintype.card_congr equiv)
    (Nat.ne_of_lt (card_sourceEdge_contractDatum_lt data hc hab hOne))

/-! ## The honest shape: an embedding, not an equivalence -/

/-- The source occurrences of the contracted datum, read as source occurrences
of the incoming datum.  This — an `Embedding`, not an `Equiv` — is the shape
the correspondence actually has. -/
noncomputable def sourceEdgeEmbedding (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) :
    (contractDatum data hc hab hOne).SourceEdge ↪ data.SourceEdge where
  toFun f := ((sourceEdgeEquiv data hc hab hOne).symm f).1
  inj' _ _ h :=
    (sourceEdgeEquiv data hc hab hOne).symm.injective (Subtype.ext h)

@[simp] theorem sourceEdgeEmbedding_apply (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (f : (contractDatum data hc hab hOne).SourceEdge) :
    sourceEdgeEmbedding data hc hab hOne f =
      ((sourceEdgeEquiv data hc hab hOne).symm f).1 := rfl

/-- Nothing in the image lies over the contracted target occurrence. -/
theorem sourceEdgeEmbedding_ne_contracted (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (f : (contractDatum data hc hab hOne).SourceEdge) :
    (sourceEdgeEmbedding data hc hab hOne f).1.1 ≠ contracted :=
  ((sourceEdgeEquiv data hc hab hOne).symm f).2

/-- The embedding undoes `sourceEdgeMap`. -/
@[simp] theorem sourceEdgeEmbedding_sourceEdgeMap (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) :
    sourceEdgeEmbedding data hc hab hOne (sourceEdgeMap data hc hab hOne e) = e.1 := by
  show ((sourceEdgeEquiv data hc hab hOne).symm
    (sourceEdgeEquiv data hc hab hOne e)).1 = e.1
  rw [Equiv.symm_apply_apply]

/-- Every occurrence away from the contracted target occurrence is in the
image; with `sourceEdgeEmbedding_ne_contracted` this pins the image down
exactly. -/
theorem exists_sourceEdgeEmbedding_eq (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {e : data.SourceEdge} (he : e.1.1 ≠ contracted) :
    ∃ f : (contractDatum data hc hab hOne).SourceEdge,
      sourceEdgeEmbedding data hc hab hOne f = e :=
  ⟨sourceEdgeMap data hc hab hOne ⟨e, he⟩,
    sourceEdgeEmbedding_sourceEdgeMap data hc hab hOne ⟨e, he⟩⟩

/-- **What does transfer:** the embedding preserves the ramification index.
This is `ContractionFibre.sourceEdgeIndex_symm_sourceEdgeEquiv` in embedding
form, and it is the only ingredient of `DanglingEdgeNoGlue` that is free. -/
theorem sourceEdgeIndex_sourceEdgeEmbedding (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (f : (contractDatum data hc hab hOne).SourceEdge) :
    data.sourceEdgeIndex (sourceEdgeEmbedding data hc hab hOne f)
      = (contractDatum data hc hab hOne).sourceEdgeIndex f :=
  sourceEdgeIndex_symm_sourceEdgeEquiv data hc hab hOne f

/-! ## Incidence: transferred forwards, and reflected only away from the wall -/

/-- The target vertex under the left source endpoint of an occurrence. -/
theorem sourceEnds_fst_fst (data : GluingDatum target degree) (e : data.SourceEdge) :
    (data.sourceEnds e).1.1.1 = (e.1.1 : target.V × target.V).1 := rfl

/-- The target vertex under the right source endpoint of an occurrence. -/
theorem sourceEnds_snd_fst (data : GluingDatum target degree) (e : data.SourceEdge) :
    (data.sourceEnds e).2.1.1 = (e.1.1 : target.V × target.V).2 := rfl

/-- An occurrence above the contracted target occurrence meets only source
vertices above its two endpoints. -/
theorem not_incident_of_eq_contracted (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b))
    {e : data.SourceEdge} (he : e.1.1 = contracted)
    {v : data.SourceVertex} (hva : v.1.1 ≠ a) (hvb : v.1.1 ≠ b) :
    ¬ Incident data e v := by
  have hPair : (e.1.1 : target.V × target.V) = (a, b) := by rw [he]; exact hc
  rintro (h | h)
  · exact hva (by
      rw [← congrArg (fun w : data.SourceVertex => w.1.1) h, sourceEnds_fst_fst,
        hPair])
  · exact hvb (by
      rw [← congrArg (fun w : data.SourceVertex => w.1.1) h, sourceEnds_snd_fst,
        hPair])

/-- **What does transfer:** incidence is carried forwards by the contraction. -/
theorem incident_sourceEdgeMap (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) {v : data.SourceVertex}
    (h : Incident data e.1 v) :
    Incident (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne e)
      (sourceVertexMap data hc hab hOne v) := by
  have hEnds := sourceEnds_sourceEdgeMap data hc hab hOne e
  rcases h with h | h
  · exact Or.inl (by rw [congrArg Prod.fst hEnds, h])
  · exact Or.inr (by rw [congrArg Prod.snd hEnds, h])

/-- **Exactly how far incidence fails to be reflected.**  Downstairs an
occurrence is incident to a source vertex as soon as one of its endpoints is
joined to that vertex by a walk of occurrences above the contracted target
occurrence.  This is the precise obstruction: incidence downstairs is
incidence upstairs *up to* `ReachThroughContracted`. -/
theorem incident_sourceEdgeMap_iff (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) (v : data.SourceVertex) :
    Incident (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne e)
        (sourceVertexMap data hc hab hOne v) ↔
      ReachThroughContracted data contracted (data.sourceEnds e.1).1 v ∨
        ReachThroughContracted data contracted (data.sourceEnds e.1).2 v := by
  have hEnds := sourceEnds_sourceEdgeMap data hc hab hOne e
  show ((contractDatum data hc hab hOne).sourceEnds
        (sourceEdgeMap data hc hab hOne e)).1 = _ ∨
      ((contractDatum data hc hab hOne).sourceEnds
        (sourceEdgeMap data hc hab hOne e)).2 = _ ↔ _
  rw [congrArg Prod.fst hEnds, congrArg Prod.snd hEnds,
    sourceVertexMap_eq_iff data hc hab hOne, sourceVertexMap_eq_iff data hc hab hOne]

/-- Away from the merged vertex, `sourceVertexMap` is injective in its second
argument as well. -/
theorem sourceVertexMap_eq_iff_of_ne_right (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (x v : data.SourceVertex)
    (hva : v.1.1 ≠ a) (hvb : v.1.1 ≠ b) :
    sourceVertexMap data hc hab hOne x = sourceVertexMap data hc hab hOne v ↔
      x = v := by
  rw [eq_comm, sourceVertexMap_eq_iff_of_ne data hc hab hOne v x hva hvb, eq_comm]

/-- **Incidence is reflected away from the wall.**  At a source vertex over a
target vertex other than the two ends of the contracted occurrence, the
contraction changes nothing: the occurrences incident to the image are exactly
the images of the occurrences incident to the vertex. -/
theorem incident_sourceEdgeMap_iff_of_ne (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (e : {e : data.SourceEdge // e.1.1 ≠ contracted}) (v : data.SourceVertex)
    (hva : v.1.1 ≠ a) (hvb : v.1.1 ≠ b) :
    Incident (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne e)
        (sourceVertexMap data hc hab hOne v) ↔ Incident data e.1 v := by
  have hEnds := sourceEnds_sourceEdgeMap data hc hab hOne e
  show ((contractDatum data hc hab hOne).sourceEnds
        (sourceEdgeMap data hc hab hOne e)).1 = _ ∨
      ((contractDatum data hc hab hOne).sourceEnds
        (sourceEdgeMap data hc hab hOne e)).2 = _ ↔ _
  rw [congrArg Prod.fst hEnds, congrArg Prod.snd hEnds,
    sourceVertexMap_eq_iff_of_ne_right data hc hab hOne _ v hva hvb,
    sourceVertexMap_eq_iff_of_ne_right data hc hab hOne _ v hva hvb]
  rfl

/-! ## Danglingness: the cut survives, the genus need not -/

/-- A pair of source vertices joined by exactly one occurrence is joined by
exactly one *source edge occurrence*: multiplicity one in `sourceGraph` pins
the occurrence, not merely the adjacency. -/
theorem sourceEdge_unique_of_num_edges_eq_one (data : GluingDatum target degree)
    {x y : data.SourceVertex} (hOne : num_edges data.sourceGraph x y = 1)
    {e₁ e₂ : data.SourceEdge}
    (h₁ : data.sourceEnds e₁ = (x, y) ∨ data.sourceEnds e₁ = (y, x))
    (h₂ : data.sourceEnds e₂ = (x, y) ∨ data.sourceEnds e₂ = (y, x)) :
    e₁ = e₂ := by
  by_contra hne
  rw [GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum] at hOne
  have hLe : (∑ f ∈ ({e₁, e₂} : Finset data.SourceEdge),
        if data.sourceEnds f = (x, y) ∨ data.sourceEnds f = (y, x) then 1 else 0)
      ≤ ∑ f : data.SourceEdge,
        if data.sourceEnds f = (x, y) ∨ data.sourceEnds f = (y, x) then 1 else 0 :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hne, ite_eq_left h₁, ite_eq_left h₂] at hLe
  omega

/-- A step through the contracted target occurrence cannot cross the cut of a
surviving dangling occurrence: the cut is crossed by exactly one occurrence,
and that occurrence is not one of the contracted ones. -/
theorem contractedStep_side_iff (data : GluingDatum target degree)
    {x y : data.SourceVertex} (cut : Utilities.SeparatingEdgeCut data.sourceGraph x y)
    {e : data.SourceEdge}
    (hEnds : data.sourceEnds e = (x, y) ∨ data.sourceEnds e = (y, x))
    (hNe : e.1.1 ≠ contracted) {u v : data.SourceVertex}
    (hStep : ContractedStep data contracted u v) :
    u ∈ cut.side ↔ v ∈ cut.side := by
  obtain ⟨w, hwOver, hwFirst, hwSecond⟩ := hStep
  have hwEnds : data.sourceEnds w = (u, v) := by rw [← hwFirst, ← hwSecond]
  have hMem : (u, v) ∈ data.sourceGraph.edges :=
    contractedStep_mem_sourceGraph_edges data ⟨w, hwOver, hwFirst, hwSecond⟩
  constructor
  · intro hu
    by_contra hv
    have hCross := cut.cross_num_edges u v hu hv
    have hPos : 0 < num_edges data.sourceGraph u v :=
      GraphContraction.num_edges_pos_of_mem_edges data.sourceGraph u v hMem
    have hxy : u = x ∧ v = y := by
      split_ifs at hCross with hIf
      · exact hIf
      · omega
    have hw : data.sourceEnds w = (x, y) := by rw [hwEnds, hxy.1, hxy.2]
    have hEq : w = e := sourceEdge_unique_of_num_edges_eq_one data
      cut.num_edges_endpoints (Or.inl hw) hEnds
    exact hNe (hEq ▸ hwOver)
  · intro hv
    by_contra hu
    have hCross := cut.cross_num_edges v u hv hu
    have hPos : 0 < num_edges data.sourceGraph v u :=
      GraphContraction.num_edges_pos_of_mem_edges' data.sourceGraph v u hMem
    have hxy : v = x ∧ u = y := by
      split_ifs at hCross with hIf
      · exact hIf
      · omega
    have hw : data.sourceEnds w = (y, x) := by rw [hwEnds, hxy.1, hxy.2]
    have hEq : w = e := sourceEdge_unique_of_num_edges_eq_one data
      cut.num_edges_endpoints (Or.inr hw) hEnds
    exact hNe (hEq ▸ hwOver)

/-- Hence no whole fibre of the contraction straddles such a cut. -/
theorem reachThroughContracted_side_iff (data : GluingDatum target degree)
    {x y : data.SourceVertex} (cut : Utilities.SeparatingEdgeCut data.sourceGraph x y)
    {e : data.SourceEdge}
    (hEnds : data.sourceEnds e = (x, y) ∨ data.sourceEnds e = (y, x))
    (hNe : e.1.1 ≠ contracted) {u v : data.SourceVertex}
    (h : ReachThroughContracted data contracted u v) :
    u ∈ cut.side ↔ v ∈ cut.side := by
  induction h with
  | rel p q hpq => exact contractedStep_side_iff data cut hEnds hNe hpq
  | refl p => exact Iff.rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **The cut of a surviving dangling occurrence descends to the wall datum.**
Its side is a union of fibres of `GluingContraction.sourceVertexMap`, so it
pushes forward to a well-defined set of wall-datum source vertices.  This is
the combinatorial step behind `DanglingPreserved`; the rest is induced-subgraph
bookkeeping, not a new idea. -/
theorem separatingEdgeCut_mem_iff_of_sourceVertexMap_eq
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {x y : data.SourceVertex}
    (cut : Utilities.SeparatingEdgeCut data.sourceGraph x y) {e : data.SourceEdge}
    (hEnds : data.sourceEnds e = (x, y) ∨ data.sourceEnds e = (y, x))
    (hNe : e.1.1 ≠ contracted) {u v : data.SourceVertex}
    (h : sourceVertexMap data hc hab hOne u = sourceVertexMap data hc hab hOne v) :
    u ∈ cut.side ↔ v ∈ cut.side :=
  reachThroughContracted_side_iff data cut hEnds hNe
    ((sourceVertexMap_eq_iff data hc hab hOne u v).mp h)

/-- The first orientation of a dangling cut. -/
theorem danglingSide_mem_iff_of_sourceVertexMap_eq (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {e : data.SourceEdge} (hNe : e.1.1 ≠ contracted)
    (side : DanglingSide data.sourceGraph
      (data.sourceEnds e).1 (data.sourceEnds e).2)
    {u v : data.SourceVertex}
    (h : sourceVertexMap data hc hab hOne u = sourceVertexMap data hc hab hOne v) :
    u ∈ side.side ↔ v ∈ side.side :=
  separatingEdgeCut_mem_iff_of_sourceVertexMap_eq data hc hab hOne
    side.toSeparatingEdgeCut (Or.inl rfl) hNe h

/-- The other orientation of a dangling cut. -/
theorem danglingSide_mem_iff_of_sourceVertexMap_eq' (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {e : data.SourceEdge} (hNe : e.1.1 ≠ contracted)
    (side : DanglingSide data.sourceGraph
      (data.sourceEnds e).2 (data.sourceEnds e).1)
    {u v : data.SourceVertex}
    (h : sourceVertexMap data hc hab hOne u = sourceVertexMap data hc hab hOne v) :
    u ∈ side.side ↔ v ∈ side.side :=
  separatingEdgeCut_mem_iff_of_sourceVertexMap_eq data hc hab hOne
    side.toSeparatingEdgeCut (Or.inr rfl) hNe h

/-! ## Danglingness: the one input the contraction does not supply -/

/-- **The forward direction.**  A surviving occurrence that is dangling upstairs
is dangling in the contracted datum.

`reachThroughContracted_side_iff` above is its one combinatorial step: the side
of the cut is a union of fibres of `GluingContraction.sourceVertexMap`, so it
pushes forward to a well-defined set downstairs, the mapped occurrence is still
its only crossing occurrence, both sides stay connected because they are images
of connected sets, and contracting edges inside a genus-zero side leaves a
genus-zero side.  Completing the proof needs only connectivity and genus
bookkeeping for `Utilities.inducedSubgraph` under contraction, which is not
developed here, so it is carried as a hypothesis.  At an actual wall event it
is a theorem (`WallAdmissibility.danglingCompatible_of_fullDimensional`). -/
def DanglingPreserved (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) : Prop :=
  ∀ e : {e : data.SourceEdge // e.1.1 ≠ contracted},
    IsDangling data e.1 →
      IsDangling (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne e)

/-- **The reverse direction.**  An occurrence dangling in the contracted datum
need *not* have been dangling upstairs.  Pulling the cut back along
`sourceVertexMap` is fine — same lemma — and the fibres are connected, so the
pullback is again a separating edge cut with connected sides.  Genus is what
breaks: the genus of the pulled-back side is the genus of the side downstairs
**plus** the number of independent cycles carried by the contracted occurrences
inside it.  So a genus-zero side downstairs can sit under a positive-genus side
upstairs, and the contraction genuinely creates dangling occurrences whenever
the contracted source fibre carries a cycle on one side of the cut.

This is stated only because the W4 fields below need it, and it is exactly what
a forest hypothesis on the contracted source fibre would buy.

**Draisma–Vargas Part I states this biconditional under the hypothesis that
makes it hold.**  Its `lemma-dangling-limit` ("dangling in the limit", in the
subsection on inherited properties, `section-inherited-properties`) says: if
`g(H(M)) = g(H(M_0))`, then a vertex `A_0` above `w_0` is dangling **if and
only if** all the vertices `A_1, …, A_r` that contract to `A_0` are dangling.
Its proof is the same observation made here, from the other side: since
`g(H(M)) = g(H(M_0))`, no cycle of `G` is contracted, so a vertex lies on a
cycle downstairs exactly when one of its preimages did.  The failure described
above is precisely what that hypothesis excludes.  The paper carries it through
the limit lemmas that follow, including `lemma-limit-dangling-no-glue`, which is
dangling-no-glue in the limit under the same hypothesis.

The same hypothesis is in this development: it is `ContractionForest`, and
`prop-rphi-under-contraction` -- whose Lean form is
`ContractionRamification.valid_contractDatum` -- carries it too, the paper's
proof deriving forest-ness of the contracted fibre from genus preservation.
So the consumer to build on is the *hypothesised* version; the unconditional
statement below records why the hypothesis cannot be dropped. -/
def DanglingReflected (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) : Prop :=
  ∀ e : {e : data.SourceEdge // e.1.1 ≠ contracted},
    IsDangling (contractDatum data hc hab hOne) (sourceEdgeMap data hc hab hOne e) →
      IsDangling data e.1

/-- Both directions at once: danglingness is unchanged on the occurrences that
survive the contraction. -/
def DanglingCompatible (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) : Prop :=
  DanglingPreserved data hc hab hOne ∧ DanglingReflected data hc hab hOne

/-- The forward direction, read on an arbitrary occurrence of the wall datum. -/
theorem DanglingPreserved.embedding {data : GluingDatum target degree}
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1}
    (hPreserved : DanglingPreserved data hc hab hOne)
    (f : (contractDatum data hc hab hOne).SourceEdge)
    (hDangling : IsDangling data (sourceEdgeEmbedding data hc hab hOne f)) :
    IsDangling (contractDatum data hc hab hOne) f := by
  have hmap : sourceEdgeMap data hc hab hOne
      ((sourceEdgeEquiv data hc hab hOne).symm f) = f :=
    (sourceEdgeEquiv data hc hab hOne).apply_symm_apply f
  have h := hPreserved ((sourceEdgeEquiv data hc hab hOne).symm f) hDangling
  rwa [hmap] at h

/-- The reverse direction, read on an arbitrary occurrence of the wall datum. -/
theorem DanglingReflected.embedding {data : GluingDatum target degree}
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1}
    (hReflected : DanglingReflected data hc hab hOne)
    (f : (contractDatum data hc hab hOne).SourceEdge)
    (hDangling : IsDangling (contractDatum data hc hab hOne) f) :
    IsDangling data (sourceEdgeEmbedding data hc hab hOne f) := by
  have hmap : sourceEdgeMap data hc hab hOne
      ((sourceEdgeEquiv data hc hab hOne).symm f) = f :=
    (sourceEdgeEquiv data hc hab hOne).apply_symm_apply f
  exact hReflected ((sourceEdgeEquiv data hc hab hOne).symm f)
    (by rw [hmap]; exact hDangling)

/-- **`dangling_no_glue` transfers only along the reverse direction.**  The index
half is free (`sourceEdgeIndex_sourceEdgeEmbedding`); the danglingness half is
`DanglingReflected`, because the field quantifies over the occurrences of the
*wall* datum and so has to pull their danglingness back upstairs.  This is the
precise sense in which `dangling_no_glue` does not transfer along a
contraction. -/
theorem danglingEdgeNoGlue_contractDatum (data : GluingDatum target degree)
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1}
    (hReflected : DanglingReflected data hc hab hOne)
    (hNoGlue : DanglingEdgeNoGlue data) :
    DanglingEdgeNoGlue (contractDatum data hc hab hOne) := by
  intro f hDangling
  rw [← sourceEdgeIndex_sourceEdgeEmbedding data hc hab hOne f]
  exact hNoGlue _ (hReflected.embedding f hDangling)

/-- **`nonDangling_valency` transfers away from the wall, and needs both
directions.**  At a source vertex over a target vertex other than the two ends
of the contracted occurrence, the surviving valency is literally unchanged.
The merged vertex is the only place where the contraction can move it; there
the bound is the `hTrivalent` hypothesis of
`W4Bridge.auxR0SourceInput_of_contraction`, which
`WallAdmissibilityStable.trivalent_of_fullDimensional` derives at an actual wall
event. -/
theorem nonDanglingValency_sourceVertexMap (data : GluingDatum target degree)
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1}
    (hCompat : DanglingCompatible data hc hab hOne)
    (v : data.SourceVertex) (hva : v.1.1 ≠ a) (hvb : v.1.1 ≠ b) :
    nonDanglingValency (contractDatum data hc hab hOne)
        (sourceVertexMap data hc hab hOne v) = nonDanglingValency data v := by
  classical
  have hne : ∀ e : data.SourceEdge, Incident data e v → e.1.1 ≠ contracted := by
    intro e hIncident hEq
    exact not_incident_of_eq_contracted data hc hEq hva hvb hIncident
  have key : ((Finset.univ : Finset data.SourceEdge).filter fun e ↦
        ¬ IsDangling data e ∧ Incident data e v).card
      = ((Finset.univ : Finset (contractDatum data hc hab hOne).SourceEdge).filter
        fun f ↦ ¬ IsDangling (contractDatum data hc hab hOne) f ∧
          Incident (contractDatum data hc hab hOne) f
            (sourceVertexMap data hc hab hOne v)).card := by
    refine Finset.card_bij
      (fun e he ↦ sourceEdgeMap data hc hab hOne
        ⟨e, hne e (Finset.mem_filter.mp he).2.2⟩) ?_ ?_ ?_
    · intro e he
      obtain ⟨hDangling, hIncident⟩ := (Finset.mem_filter.mp he).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact fun hBad ↦ hDangling (hCompat.2 ⟨e, hne e hIncident⟩ hBad)
      · exact incident_sourceEdgeMap data hc hab hOne ⟨e, hne e hIncident⟩ hIncident
    · intro e₁ he₁ e₂ he₂ hEq
      exact congrArg Subtype.val
        (sourceEdgeMap_injective data hc hab hOne hEq)
    · intro f hf
      obtain ⟨hDangling, hIncident⟩ := (Finset.mem_filter.mp hf).2
      set e : {e : data.SourceEdge // e.1.1 ≠ contracted} :=
        (sourceEdgeEquiv data hc hab hOne).symm f with hedef
      have hmap : sourceEdgeMap data hc hab hOne e = f :=
        (sourceEdgeEquiv data hc hab hOne).apply_symm_apply f
      have hIncidentUp : Incident data e.1 v := by
        refine (incident_sourceEdgeMap_iff_of_ne data hc hab hOne e v hva hvb).mp ?_
        rw [hmap]
        exact hIncident
      have hDanglingUp : ¬ IsDangling data e.1 := by
        intro hBad
        exact hDangling (hmap ▸ hCompat.1 e hBad)
      refine ⟨e.1, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hDanglingUp, hIncidentUp⟩, ?_⟩
      rw [show (⟨e.1, hne e.1 hIncidentUp⟩ :
          {e : data.SourceEdge // e.1.1 ≠ contracted}) = e from Subtype.ext rfl]
      exact hmap
  exact key.symm

/-! ## The stable model does shrink -/

/-- The surviving occurrences of the contracted datum, as surviving
occurrences upstairs.  Well defined exactly because `DanglingPreserved`
holds: an occurrence that survives downstairs cannot have been dangling
upstairs. -/
noncomputable def nonDanglingEmbedding (data : GluingDatum target degree)
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1}
    (hPreserved : DanglingPreserved data hc hab hOne) :
    NonDanglingEdge (contractDatum data hc hab hOne) → NonDanglingEdge data :=
  fun g ↦ ⟨sourceEdgeEmbedding data hc hab hOne g.1,
    fun hBad ↦ g.2 (hPreserved.embedding g.1 hBad)⟩

@[simp] theorem nonDanglingEmbedding_val (data : GluingDatum target degree)
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1}
    (hPreserved : DanglingPreserved data hc hab hOne)
    (g : NonDanglingEdge (contractDatum data hc hab hOne)) :
    (nonDanglingEmbedding data hPreserved g).1 =
      sourceEdgeEmbedding data hc hab hOne g.1 := rfl

theorem nonDanglingEmbedding_injective (data : GluingDatum target degree)
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1}
    (hPreserved : DanglingPreserved data hc hab hOne) :
    Function.Injective (nonDanglingEmbedding data hPreserved) := by
  intro g g' h
  have hVal : sourceEdgeEmbedding data hc hab hOne g.1 =
      sourceEdgeEmbedding data hc hab hOne g'.1 :=
    congrArg (fun x : NonDanglingEdge data ↦ x.1) h
  exact Subtype.ext ((sourceEdgeEmbedding data hc hab hOne).injective hVal)

/-- **The stable model of the wall datum has strictly fewer edges.**  A
full-dimensional datum has no entirely dangling target fibre
(`FullDimensionalSourcePresentation.noDanglingTargetFibres`), so at least one
surviving occurrence sits above the contracted target occurrence and is lost.

Consequently `WallDegeneration.stablePath` cannot be induced by the occurrence
correspondence: any equivalence `StablePath wallDatum ≃ StablePath data` has to
merge stable classes upstairs to compensate for the occurrences it drops. -/
theorem card_nonDanglingEdge_contractDatum_lt (data : GluingDatum target degree)
    {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
    {hOne : num_edges target a b = 1}
    (hPreserved : DanglingPreserved data hc hab hOne)
    (hFibres : NoDanglingTargetFibres data) :
    Fintype.card (NonDanglingEdge (contractDatum data hc hab hOne))
      < Fintype.card (NonDanglingEdge data) := by
  obtain ⟨e, hOver, hSurvives⟩ := hFibres contracted
  refine Fintype.card_lt_of_injective_of_notMem
    (nonDanglingEmbedding data hPreserved)
    (nonDanglingEmbedding_injective data hPreserved)
    (b := ⟨e, hSurvives⟩) ?_
  rintro ⟨g, hg⟩
  refine sourceEdgeEmbedding_ne_contracted data hc hab hOne g.1 ?_
  have hVal : sourceEdgeEmbedding data hc hab hOne g.1 = e :=
    congrArg (fun x : NonDanglingEdge data ↦ x.1) hg
  rw [hVal]
  exact hOver

/-! ## The bridge -/

/-- **Half the bridge is a theorem.**  `WallDegeneration.edge_card` holds for
the contraction outright; `WallDegeneration.stablePath` is passed through,
because it is the paper's claim that the stable model survives the
degeneration, which does not follow from the contraction alone (at an actual
wall event it is `WallAdmissibilityStable.stablePath_equiv`). -/
theorem wallDegeneration_contractDatum (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hStable : Nonempty
      (StablePath (contractDatum data hc hab hOne) ≃ StablePath data)) :
    WallDegeneration data (contractDatum data hc hab hOne) :=
  ⟨edge_card_contract hab hOne, hStable⟩

/-- The `stablePath_card` field of `W4StableSource.AuxR0SourceInput`, for the
contracted wall datum, from a full-dimensional presentation of the incoming
datum. -/
theorem stablePath_card_contractDatum {coordinate : Type*} [Fintype coordinate]
    [DecidableEq coordinate] (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fd : FullDimensionalSourcePresentation data coordinate)
    (hStable : Nonempty
      (StablePath (contractDatum data hc hab hOne) ≃ StablePath data)) :
    Fintype.card (StablePath (contractDatum data hc hab hOne))
      = (GraphContraction.contract target hab hOne).edges.card + 1 :=
  stablePath_card_of_wallDegeneration fd
    (wallDegeneration_contractDatum data hc hab hOne hStable)

/-- **The two data really are different data.**  A wall datum related to a
full-dimensional one by `WallDegeneration` admits no square honest stable
length-matrix labelling of its own, for any coordinate type.  This is the
positive form of `FullDimensionalSource.false_of_labelling_auxR0SourceInput`:
the inconsistency found there is not a defect of the bridge, it is the
statement that the bridge relates two genuinely different data. -/
theorem not_nonempty_labelling_of_wallDegeneration {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate] {wallCoordinate : Type*}
    [Fintype wallCoordinate] {data : GluingDatum target degree}
    {wallTarget : CFGraph} {wallDatum : GluingDatum wallTarget degree}
    (fd : FullDimensionalSourcePresentation data coordinate)
    (bridge : WallDegeneration data wallDatum) :
    ¬ Nonempty (StableLengthMatrixLabelling wallDatum wallCoordinate) := by
  rintro ⟨labelling⟩
  have hSquare := stablePath_card_of_labelling labelling
  have hWall := stablePath_card_of_wallDegeneration fd bridge
  omega

/-!
## What this module takes as hypotheses

1. **`DanglingPreserved` and `DanglingReflected`.**  The first holds, and its
   combinatorial step is proved here (`reachThroughContracted_side_iff`);
   completing it is induced-subgraph connectivity and genus bookkeeping under
   contraction.  The second **fails in general**, and the two W4 fields that
   `FullDimensionalSource` flags need exactly it.  A contraction whose
   contracted source fibre is a forest (`ContractionRamification.ContractionForest`)
   supplies it; this is the same hypothesis under which
   `ContractionRamification` proves the local Riemann–Hurwitz inequality at the
   merged vertex.  At an actual wall event both directions are theorems
   (`WallAdmissibility.danglingCompatible_of_fullDimensional`).

2. **`WallDegeneration.stablePath`.**  It is the paper's claim that the stable
   model survives the degeneration.  It is not induced by the occurrence
   correspondence, which strictly loses surviving occurrences
   (`card_nonDanglingEdge_contractDatum_lt`), so it cannot be built from the
   contraction alone; at an actual wall event it is
   `WallAdmissibilityStable.stablePath_equiv`.

What this module rules out: an equivalence `wallDatum.SourceEdge ≃
data.SourceEdge`.  No contraction can provide one
(`not_nonempty_sourceEdge_equiv`); the object the transfers actually run
through is the embedding `sourceEdgeEmbedding`, together with the two
danglingness directions above.

Nothing here weakens `WallDegeneration`: both of its fields are stated exactly
as `FullDimensionalSource` states them, `edge_card` is discharged, and
`stablePath` is passed through unchanged.
-/

end DraismaVargas.LocalCases.WallDegeneration
