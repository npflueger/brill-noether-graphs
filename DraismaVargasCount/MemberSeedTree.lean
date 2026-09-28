import DraismaVargasCount.MemberCertifiedPencil
import DraismaVargas.Infrastructure.IteratedContraction
import DraismaVargas.LocalCases.ZeroForestBridge

/-!
# Reducing the member-seed receipt to its one real clause

`MemberCertifiedPencil` produces a certified pencil from a fibre member that carries
a `MemberSeed` receipt.  This file settles three of the `MemberSeed`'s four clauses
outright and isolates the fourth; `MemberSeedExists` then proves the fourth.

## What a `MemberSeed` actually asks for

`Count.MemberCertifiedPencil.MemberSeed member` is a seven-field structure, but
four of its fields are bookkeeping (`first`, `second`, `contracted`,
`endpoints`) and two of the remaining three are **free over a target tree**:

* `distinct` -- the contracted occurrence is not a loop.  Free for *any*
  occurrence of *any* `CFGraph`: `CFGraph.loopless` is a field, and
  `GluingContraction.fst_ne_snd` reads it off.  The target's being a tree is not
  even needed.
* `numEdges` -- the contracted occurrence is the only one joining its ends.
  Free for any occurrence of a *connected genus-zero* target, which is exactly
  what `FullDimensionalSourcePresentation.targetConnected` and `.targetGenus`
  say about a member's target:
  `IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected`.
* `forest` -- `ContractionRamification.ContractionForest`, the source-topology
  receipt.  **This one is not free**, and it is the entire residue.

So `memberSeedOfForest` below turns a single `ContractionForestAt member.data c`
into a full `MemberSeed member`, and `nonempty_memberSeed_iff` says the two are
equivalent: a member admits a seed **iff** some occurrence of its target has a
forest source fibre.  Nothing is lost by the reduction.

## What is proved

* `numEdges_of_member`, `distinct_of_member` -- the two free clauses.
* `memberSeedOfForest`, `nonempty_memberSeed_iff` -- the reduction, and that it
  is exact.
* `carriesCertifiedPencil_of_forest` -- the producer of `MemberCertifiedPencil`
  restated with `MemberSeed member` replaced by the single hypothesis
  `ContractionForestAt member.data c` at one named target occurrence `c`.
* `contractionForestAt_iff_global_count` -- the residue in its numerical form,
  `E + C = p + q`, specialized to a member (`ZeroForestBridge` proves the
  equivalence for an arbitrary gluing datum).
* `contractionForest_of_edgePartition_eq_left` / `_right` -- a *sufficient*
  criterion that is a single equality of sheet partitions: if the fibre over the
  occurrence is unramified at one of its two ends (its edge partition is that
  endpoint's vertex partition) then the fibre is a forest.  This is the
  criterion the genus-six caterpillar witness satisfies, and unlike the
  seven-field structure it can be checked at a concrete member by `rfl`.
* `memberSeedOfEdgePartitionEqLeft` -- the two combined.
* `blocksEquivOfSameBlocks`, `card_blocks_of_sameBlocks`,
  `sameBlocks_join_of_refines` -- the block arithmetic the criterion runs on:
  two representative maps presenting the same partition have equinumerous block
  types, and joining a refinement with what it refines changes nothing.

## What is NOT proved (every hypothesis, explicitly)

* **Existence of a forest occurrence is not proved *here*.**  No theorem in this
  file says that a `FibreMember`, closed or not, has *some* target occurrence
  with a forest source fibre.  `nonempty_memberSeed_iff` shows that this is
  exactly what the receipt asks for, and it is proved, at degree at least
  three, in `MemberSeedExists` (`nonempty_memberSeed_of_member`).  This file is
  the statement of the reduction, and is what to read to see that the reduction
  loses nothing.
* `spec.core.Cubic`, `spec.core.Connected`, `2 ≤ degree` and a strictly positive
  `start` are explicit hypotheses of the producer, inherited verbatim from
  `MemberCertifiedPencil`; nothing here discharges any of them.
* The sufficient criterion is only sufficient.  A member all of whose
  occurrences are ramified at both ends is not excluded by anything here.
* `Odd member.oddMult` is used nowhere, exactly as in `MemberCertifiedPencil`:
  the producer is count-independent.
* **There is no open/closed asymmetry.**
  `FibreMember.Closed.of_open` makes every open member closed, and
  `MemberSeed` mentions `member.coords` not at all, so the receipt is available for
  the open members of odd multiplicity that the count delivers.  `Closed`
  is terminality of the synthetic march state of `MemberCertifiedPencil`, and it
  is the weaker of the two hypotheses.

## Why the existence statement is true

Write `E_c` for the set of source occurrences above a target occurrence `c`.
`ZeroForestBridge.contractionForest_iff_global_count` says the fibre over `c` is
a forest exactly when `E_c` is acyclic for the census on
`UnitSubdivisionPresentation.core data.sourceGraph`.  The sets `E_c` partition
the source occurrences.  Let `F` be a spanning tree of the (connected) source
graph, so `|univ \ F| = genus data.sourceGraph`.  A target occurrence with
`E_c ⊆ F` has an acyclic fibre, by `ZeroForestBridge.isForest_of_subset`.  At
most `genus data.sourceGraph` target occurrences can fail `E_c ⊆ F`, because the
`E_c` are disjoint and each failure consumes an element of `univ \ F`.  The
member's own `saturated` field says the target has
`2 * genus data.sourceGraph + 2 * degree - 5` occurrences, which exceeds
`genus data.sourceGraph` exactly when `5 < genus + 2 * degree` -- so for every
`3 ≤ degree`, the source genus being nonnegative.  The count therefore leaves
`genus + 2 * degree - 5` of the target occurrences with forest fibres, nine of
the fifteen at `g = 6`, `degree = 4`; only the existence statement is proved
downstream, since nothing consumes the quantitative form.

The argument needs two generic inputs:

1. `Utilities.Subdivision.CensusSpanningForest` -- a spanning forest for the
   census, `∃ F, IsForest core F` realizing full reachability, whence
   `F.card + 1 = n` when the core is connected;
2. `CensusConnected` -- the bridge from `graph_connected G` to that census
   hypothesis.

`MemberSeedExists` runs the count itself.
-/

namespace DraismaVargas.Count.MemberSeedTree

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.Count.MemberCertifiedPencil
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  The two free clauses -/

/-- **Free clause 1.**  A contracted target occurrence is never a loop: a
`CFGraph` carries looplessness as a field.  No hypothesis on the member is
used. -/
theorem distinct_of_member (member : FibreMember core y degree)
    (c : member.target.edges) :
    (c : member.target.V × member.target.V).1 ≠
      (c : member.target.V × member.target.V).2 :=
  GluingContraction.fst_ne_snd c

/-- **Free clause 2.**  A contracted target occurrence is the only one joining
its two ends: a member's target is connected of genus zero, hence a tree, hence
has no parallel occurrences. -/
theorem numEdges_of_member (member : FibreMember core y degree)
    (c : member.target.edges) :
    num_edges member.target (c : member.target.V × member.target.V).1
      (c : member.target.V × member.target.V).2 = 1 :=
  IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected member.target
    member.fullDim.targetConnected member.fullDim.targetGenus c

/-! ## 2.  The reduction -/

/-- **The reduction.**  One forest receipt at one named target occurrence is a
whole `MemberSeed`. -/
def memberSeedOfForest (member : FibreMember core y degree)
    (c : member.target.edges)
    (hForest : ContractionForestAt member.data c) : MemberSeed member where
  first := (c : member.target.V × member.target.V).1
  second := (c : member.target.V × member.target.V).2
  contracted := c
  endpoints := rfl
  distinct := distinct_of_member member c
  numEdges := numEdges_of_member member c
  forest := hForest

/-- The converse: a `MemberSeed` is a forest receipt at its own occurrence. -/
theorem contractionForestAt_of_memberSeed {member : FibreMember core y degree}
    (ms : MemberSeed member) : ContractionForestAt member.data ms.contracted := by
  have h := ms.forest
  unfold ContractionForestAt
  rw [ms.endpoints]
  exact h

/-- **The reduction is exact.**  A member admits the `MemberSeed` receipt if and
only if some occurrence of its target has a forest source fibre. -/
theorem nonempty_memberSeed_iff (member : FibreMember core y degree) :
    Nonempty (MemberSeed member) ↔
      ∃ c : member.target.edges, ContractionForestAt member.data c :=
  ⟨fun ⟨ms⟩ ↦ ⟨ms.contracted, contractionForestAt_of_memberSeed ms⟩,
    fun ⟨c, hForest⟩ ↦ ⟨memberSeedOfForest member c hForest⟩⟩

/-! ## 3.  The producer under the single hypothesis -/

section Spec

variable {spec : Spec n p}
  {member : FibreMember spec.core (fun slot ↦ ((spec.length slot : ℕ) : ℚ)) degree}

/-- **The producer under one hypothesis.** -/
theorem carriesCertifiedPencil_of_forest (c : member.target.edges)
    (hForest : ContractionForestAt member.data c)
    (hCubic : spec.core.Cubic) (hCoreConnected : spec.core.Connected)
    (hDegree : 2 ≤ degree) (start : Fin p → ℚ) (hStart : ∀ i, 0 < start i) :
    LocalCases.CertifiedPencil.CarriesCertifiedPencil spec degree member.matrix
      start member.coords :=
  carriesCertifiedPencil_of_member (memberSeedOfForest member c hForest) hCubic
    hCoreConnected hDegree start hStart

end Spec

/-! ## 4.  The residue in numerical form, and one sufficient criterion -/

/-- The residue, numerically: the fibre over `c` is a forest exactly when the
four block counts balance.  `ZeroForestBridge.contractionForest_iff_global_count`
proves this for an arbitrary gluing datum; this is its reading at the
occurrence's own endpoints. -/
theorem contractionForestAt_iff_global_count {target : CFGraph} {deg : ℕ}
    (data : GluingDatum target deg) (c : target.edges) :
    ContractionForestAt data c ↔
      Fintype.card (data.edgePartition c).Blocks
          + Fintype.card (mergedPartition data
              (c : target.V × target.V).1 (c : target.V × target.V).2).Blocks
        = Fintype.card (data.vertexPartition
              (c : target.V × target.V).1).Blocks
          + Fintype.card (data.vertexPartition
              (c : target.V × target.V).2).Blocks :=
  LocalCases.ZeroForestBridge.contractionForest_iff_global_count data rfl



section Unramified

variable {d : ℕ}

/-- Two representative maps presenting the same partition have equinumerous
block types: send a `first`-representative to its `second`-representative. -/
def blocksEquivOfSameBlocks {first second : SheetPartition d}
    (h : first.SameBlocks second) : first.Blocks ≃ second.Blocks where
  toFun block := ⟨second.repr block.1, second.repr_idem block.1⟩
  invFun block := ⟨first.repr block.1, first.repr_idem block.1⟩
  left_inv := by
    rintro ⟨i, hi⟩
    refine Subtype.ext ?_
    show first.repr (second.repr i) = i
    have hrel : first.Rel (second.repr i) i := (h _ _).mpr (second.rel_repr_left i)
    rw [SheetPartition.rel_iff] at hrel
    rw [hrel, hi]
  right_inv := by
    rintro ⟨i, hi⟩
    refine Subtype.ext ?_
    show second.repr (first.repr i) = i
    have hrel : second.Rel (first.repr i) i := (h _ _).mp (first.rel_repr_left i)
    rw [SheetPartition.rel_iff] at hrel
    rw [hrel, hi]

theorem card_blocks_of_sameBlocks {first second : SheetPartition d}
    (h : first.SameBlocks second) :
    Fintype.card first.Blocks = Fintype.card second.Blocks :=
  Fintype.card_congr (blocksEquivOfSameBlocks h)

/-- The join of a refinement with the partition it refines presents that
partition. -/
theorem sameBlocks_join_of_refines {left right : SheetPartition d}
    (h : left.Refines right) :
    (SheetPartition.join left right).SameBlocks right := by
  intro i j
  constructor
  · intro hij
    exact SheetPartition.rel_of_joinRel h (SheetPartition.Refines.refl right)
      ((SheetPartition.isJoin_join left right) i j |>.mp hij)
  · intro hij
    exact SheetPartition.right_refines_join left right i j hij

/-- **A sufficient criterion for the forest receipt, in one equality of sheet
partitions.**  If the source fibre over the contracted occurrence is unramified
at its first end -- that is, its edge partition *is* that endpoint's vertex
partition -- then the fibre graph has every first-end vertex of degree one, so
it is a disjoint union of trees.  Numerically: the join collapses onto the
second endpoint's partition, and the global count `E + C = p + q` reads
`p + q = p + q`. -/
theorem contractionForest_of_edgePartition_eq_left {target : CFGraph} {deg : ℕ}
    {a b : target.V} {c : target.edges} (data : GluingDatum target deg)
    (hc : (c : target.V × target.V) = (a, b))
    (h : data.edgePartition c = data.vertexPartition a) :
    ContractionForest data a b c := by
  have hRefines : (data.vertexPartition a).Refines (data.vertexPartition b) := by
    have hr := data.refines_right c
    rw [hc] at hr
    rwa [h] at hr
  rw [LocalCases.ZeroForestBridge.contractionForest_iff_global_count data hc, h,
    mergedPartition, card_blocks_of_sameBlocks (sameBlocks_join_of_refines hRefines)]

/-- The same criterion at the second end. -/
theorem contractionForest_of_edgePartition_eq_right {target : CFGraph} {deg : ℕ}
    {a b : target.V} {c : target.edges} (data : GluingDatum target deg)
    (hc : (c : target.V × target.V) = (a, b))
    (h : data.edgePartition c = data.vertexPartition b) :
    ContractionForest data a b c := by
  have hRefines : (data.vertexPartition b).Refines (data.vertexPartition a) := by
    have hr := data.refines_left c
    rw [hc] at hr
    rwa [h] at hr
  have hJoin : Fintype.card (mergedPartition data a b).Blocks
      = Fintype.card (data.vertexPartition a).Blocks := by
    refine card_blocks_of_sameBlocks ?_
    intro i j
    constructor
    · intro hij
      exact SheetPartition.rel_of_joinRel (SheetPartition.Refines.refl _) hRefines
        ((SheetPartition.isJoin_join (data.vertexPartition a)
          (data.vertexPartition b)) i j |>.mp hij)
    · intro hij
      exact SheetPartition.left_refines_join (data.vertexPartition a)
        (data.vertexPartition b) i j hij
  rw [LocalCases.ZeroForestBridge.contractionForest_iff_global_count data hc, h, hJoin]
  omega

/-- The criterion, delivered as a whole `MemberSeed`. -/
def memberSeedOfEdgePartitionEqLeft (member : FibreMember core y degree)
    (c : member.target.edges)
    (h : member.data.edgePartition c =
      member.data.vertexPartition (c : member.target.V × member.target.V).1) :
    MemberSeed member :=
  memberSeedOfForest member c (contractionForest_of_edgePartition_eq_left member.data rfl h)

end Unramified

end DraismaVargas.Count.MemberSeedTree
