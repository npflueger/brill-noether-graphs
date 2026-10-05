module

public import DraismaVargasCount.MemberSeedTree
public import DraismaVargasCount.CensusConnected

@[expose] public section

/-!
# Every full-dimensional member has a forest occurrence

`MemberSeedTree` reduces the `MemberSeed` receipt of `MemberCertifiedPencil`
to a single clause: some occurrence of the member's target must have a forest
source fibre.  This file proves that clause, so the producer of
`MemberCertifiedPencil` needs no receipt at all.

## The argument

Write `E_c` for the canonical source slots above a target occurrence `c`.  The
`E_c` partition the source occurrences, and
`ZeroForestBridge.contractionForest_iff_global_count` says the fibre over `c` is
a forest exactly when `E_c` is acyclic for the union-find census on
`UnitSubdivisionPresentation.core data.sourceGraph`.

Choose a census spanning tree `F` of the source graph, which exists because the
source is connected (`CensusConnected.exists_spanning_tree_of_graph_connected`).
Then `|univ \ F| = genus data.sourceGraph`, since a spanning tree has
`|V| - 1` slots.  If `E_c ⊆ F` then `E_c` is acyclic
(`ZeroForestBridge.isForest_of_subset`) and `c` is a forest occurrence.  So
every *non*-forest occurrence consumes at least one slot of `univ \ F`, and the
`E_c` are disjoint, whence

```
#(non-forest occurrences)  ≤  |univ \ F|  =  genus data.sourceGraph.
```

A full-dimensional member's `saturated` field says its target has
`2 * genus data.sourceGraph + 2 * degree - 5` occurrences.  Since the genus is
nonnegative -- the spanning tree proves that too -- this exceeds the genus as
soon as `3 ≤ degree`.  Hence some occurrence is a forest occurrence.

The same count gives more than existence: at least
`genus data.sourceGraph + 2 * degree - 5` of the target occurrences must have
forest fibres, nine of the fifteen at the endgame's `g = 6`, `degree = 4`.
**Only the existence statement is proved below**; the quantitative form would
need the forest occurrences collected into a `Finset`, and nothing downstream
asks for it.

## What is proved

* `zeroRealization` -- the all-zero nonnegative integral realization, which
  exists over every gluing datum.  It is used only to name the canonical
  slot/occurrence dictionary that `ZeroForestBridge.fibreSlots` is stated
  through; that dictionary does not depend on the realization
  (`NonnegativeIntegralRealization.sourceSlotEquiv` ignores its argument).
* `contractionForest_of_isForest_fibreSlots` -- the census bridge with the
  hypothesis reduced to the fibre's own acyclicity, which is all
  `ZeroForestBridge.contractionForest_of_isForest` actually uses.
* `sum_card_sdiff_fibreSlots`, `exists_contractionForestAt_of_genus_lt` -- the
  count.
* `exists_contractionForestAt_of_member_of_five_lt` -- the sharp form,
  `5 < genus + 2 * degree`; `genus_sourceGraph_nonneg`;
  `exists_contractionForestAt_of_member`, `nonempty_memberSeed_of_member` -- the
  conclusion at a `Count.FibreMember`.
* `caterpillar_nonempty_memberSeed`, `caterpillar_two_nonempty_memberSeed` --
  non-vacuity: the hypotheses hold at the caterpillar-of-loops member of every
  genus `2m + 2` with `m ≥ 1`, and in particular at genus six.
* `carriesCertifiedPencil_of_spec_member` -- **the producer with no receipt**.

## What is NOT proved (every hypothesis, explicitly)

* `3 ≤ degree` replaces the `2 ≤ degree` of `MemberCertifiedPencil`.  At `degree = 2` the saturation
  formula gives `target.edges.card = 2 * genus - 1`, which is `≤ genus` when
  `genus ≤ 1`, and the count above then proves nothing.  The endgame runs at
  `degree = 4`, so this is not a restriction there, but it is a real hypothesis
  and it is not removable by this argument.  What *is* removable is the shape:
  `exists_contractionForestAt_of_member_of_five_lt` asks only for
  `5 < genus + 2 * degree`, so a degree-two member of source genus at least two
  is covered as well.
* `spec.core.Cubic`, `spec.core.Connected` and a strictly positive `start`
  remain explicit, inherited from `MemberCertifiedPencil`.
* The *producer* needs neither `member.Closed` nor oddness; `Closed` is
  terminality of the synthetic march state of `MemberCertifiedPencil`.
* **No inhabitant of the `Spec`-indexed conclusion is exhibited.**  As
  `MemberCertifiedPencil` records, the caterpillar member is over the caterpillar
  *of loops*, whose core is not a `Spec.core`; this file does not change that.
* Nothing here counts anything, and nothing here produces a closed member of odd
  multiplicity.
-/

namespace DraismaVargas.Count.MemberSeedExists

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ContractionForestCensusGeneral
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.ZeroForestBridge
open DraismaVargas.Count.MemberCertifiedPencil
open DraismaVargas.Count.MemberSeedTree
open Utilities.Certificate.ExplicitPotential (Core)

variable {target : CFGraph} {degree : ℕ}

/-! ## 1.  A realization always exists, and the slot dictionary is canonical -/

/-- The all-zero nonnegative integral realization.  Every gluing datum has one;
it is used only to name the canonical dictionary between the census slots of the
source graph and the source edge occurrences. -/
def zeroRealization (data : GluingDatum target degree) :
    data.NonnegativeIntegralRealization where
  targetLength _ := 0
  sourceLength _ := 0
  dilation_length := by intro edge; simp

/-- The canonical census slots above one target occurrence. -/
noncomputable def fibreSlots (data : GluingDatum target degree) (c : target.edges) :
    Finset (Fin data.sourceGraph.edges.card) :=
  DraismaVargas.LocalCases.ZeroForestBridge.fibreSlots data (zeroRealization data) c

theorem mem_fibreSlots (data : GluingDatum target degree) (c : target.edges)
    (slot : Fin data.sourceGraph.edges.card) :
    slot ∈ fibreSlots data c ↔
      ((zeroRealization data).sourceEdgeAt slot).1.1 = c :=
  DraismaVargas.LocalCases.ZeroForestBridge.mem_fibreSlots data (zeroRealization data) c slot

/-! ## 2.  The census bridge, with only the fibre's own acyclicity -/

/-- **The bridge, sharpened.**  `ZeroForestBridge.contractionForest_of_isForest`
passes through the whole zero set; all it uses is that the slots above the
contracted occurrence are acyclic.  This is that statement. -/
theorem contractionForest_of_isForest_fibreSlots (data : GluingDatum target degree)
    {a b : target.V} {c : target.edges} (hc : (c : target.V × target.V) = (a, b))
    (hFibreForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      (fibreSlots data c)) :
    ContractionForest data a b c := by
  have hab : a ≠ b := by
    have hMember : (c : target.V × target.V) ∈ target.edges := Multiset.coe_mem
    rw [hc] at hMember
    intro hEq
    rw [hEq] at hMember
    exact target.loopless b hMember
  have hAdd := forest_image_add_card_eq
    (UnitSubdivisionPresentation.core data.sourceGraph) hFibreForest
  rw [fibreSlots, card_fibreSlots data (zeroRealization data) c] at hAdd
  have hLe := card_image_mergeLabel_le data (zeroRealization data) hc
  have hLabel := card_image_mergeLabel data hab
  have hVertices : Fintype.card data.sourceGraph.V
      = Fintype.card data.SourceVertex := rfl
  rw [← hVertices] at hLabel
  have hGe := global_count_ge data hc
  rw [contractionForest_iff_global_count data hc]
  rw [fibreSlots] at hFibreForest
  omega

/-- A forest occurrence, read at the occurrence's own endpoints. -/
theorem contractionForestAt_of_isForest_fibreSlots (data : GluingDatum target degree)
    (c : target.edges)
    (hFibreForest : IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      (fibreSlots data c)) :
    ContractionForestAt data c :=
  contractionForest_of_isForest_fibreSlots data rfl hFibreForest

/-! ## 3.  The count -/

/-- Every source slot lies above exactly one target occurrence, so the
complements of a slot set split fibrewise. -/
theorem sum_card_sdiff_fibreSlots (data : GluingDatum target degree)
    (F : Finset (Fin data.sourceGraph.edges.card)) :
    ∑ c : target.edges, ((fibreSlots data c) \ F).card
      = ((Finset.univ : Finset (Fin data.sourceGraph.edges.card)) \ F).card := by
  classical
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := fun slot : Fin data.sourceGraph.edges.card ↦
      ((zeroRealization data).sourceEdgeAt slot).1.1)
    (s := (Finset.univ : Finset (Fin data.sourceGraph.edges.card)) \ F)
    (t := (Finset.univ : Finset target.edges)) (fun x _ ↦ Finset.mem_univ _)
  rw [hfiber]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  congr 1
  ext slot
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_fibreSlots]
  tauto

/-- **The count.**  A source-connected gluing datum whose source genus is
smaller than the number of target occurrences has a forest occurrence. -/
theorem exists_contractionForestAt_of_genus_lt (data : GluingDatum target degree)
    (hConnected : graph_connected data.sourceGraph)
    (hlt : genus data.sourceGraph < (Fintype.card target.edges : ℤ)) :
    ∃ c : target.edges, ContractionForestAt data c := by
  classical
  obtain ⟨F, hF, hFcard⟩ :=
    CensusConnected.exists_spanning_tree_of_graph_connected data.sourceGraph hConnected
  by_contra hcon
  have hnot : ∀ c : target.edges, ¬ (fibreSlots data c ⊆ F) := by
    intro c hsub
    exact hcon ⟨c, contractionForestAt_of_isForest_fibreSlots data c
      (isForest_of_subset (UnitSubdivisionPresentation.core data.sourceGraph) hsub hF)⟩
  have hone : ∀ c : target.edges, 1 ≤ ((fibreSlots data c) \ F).card := by
    intro c
    refine Finset.card_pos.mpr ?_
    obtain ⟨slot, hslot, hnotF⟩ := Finset.not_subset.mp (hnot c)
    exact ⟨slot, Finset.mem_sdiff.mpr ⟨hslot, hnotF⟩⟩
  have hsum : (Fintype.card target.edges)
      ≤ ((Finset.univ : Finset (Fin data.sourceGraph.edges.card)) \ F).card := by
    rw [← sum_card_sdiff_fibreSlots data F]
    calc (Fintype.card target.edges)
        = ∑ _c : target.edges, 1 := by simp
      _ ≤ ∑ c : target.edges, ((fibreSlots data c) \ F).card :=
          Finset.sum_le_sum fun c _ ↦ hone c
  have hsubF : F ⊆ (Finset.univ : Finset (Fin data.sourceGraph.edges.card)) :=
    Finset.subset_univ F
  have hsdiff : ((Finset.univ : Finset (Fin data.sourceGraph.edges.card)) \ F).card
      + F.card = data.sourceGraph.edges.card := by
    have h := Finset.card_sdiff_add_card_eq_card hsubF
    simpa using h
  have hgenus : genus data.sourceGraph
      = ((((Finset.univ : Finset (Fin data.sourceGraph.edges.card)) \ F).card : ℤ)) := by
    unfold genus
    omega
  omega

/-! ## 4.  At a labelled fibre member -/

section Member

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The sharp form.**  A full-dimensional member has a forest occurrence
exactly when its saturation formula makes the target occurrence count exceed the
source genus, which is the inequality `5 < genus + 2 * degree`. -/
theorem exists_contractionForestAt_of_member_of_five_lt
    (member : FibreMember core y degree)
    (h : 5 < genus member.data.sourceGraph + 2 * (degree : ℤ)) :
    ∃ c : member.target.edges, ContractionForestAt member.data c := by
  refine exists_contractionForestAt_of_genus_lt member.data member.fullDim.connected ?_
  have hcard : (Fintype.card member.target.edges : ℤ)
      = (member.target.edges.card : ℤ) := by simp
  rw [hcard, member.fullDim.saturated]
  omega

/-- The source genus of a full-dimensional member is nonnegative: its source is
connected, so its census spanning tree has one fewer slot than it has
vertices. -/
theorem genus_sourceGraph_nonneg (member : FibreMember core y degree) :
    0 ≤ genus member.data.sourceGraph := by
  classical
  obtain ⟨F, hF, hFcard⟩ := CensusConnected.exists_spanning_tree_of_graph_connected
    member.data.sourceGraph member.fullDim.connected
  have hcardle : F.card ≤ member.data.sourceGraph.edges.card := by
    have := Finset.card_le_card
      (Finset.subset_univ (α := Fin member.data.sourceGraph.edges.card) F)
    simpa using this
  unfold genus
  omega

/-- **Every full-dimensional member has a forest occurrence**, at degree at
least three. -/
theorem exists_contractionForestAt_of_member (member : FibreMember core y degree)
    (hDegree : 3 ≤ degree) :
    ∃ c : member.target.edges, ContractionForestAt member.data c := by
  refine exists_contractionForestAt_of_member_of_five_lt member ?_
  have hgenus := genus_sourceGraph_nonneg member
  have hd : (3 : ℤ) ≤ (degree : ℤ) := by exact_mod_cast hDegree
  omega

/-- **The `MemberSeed` receipt is unconditional at degree at least three.** -/
theorem nonempty_memberSeed_of_member (member : FibreMember core y degree)
    (hDegree : 3 ≤ degree) : Nonempty (MemberSeed member) :=
  (nonempty_memberSeed_iff member).mpr (exists_contractionForestAt_of_member member hDegree)

/-- **Non-vacuity.**  The hypotheses are satisfied at a member that actually
exists: the caterpillar-of-loops member of genus `2m + 2` has degree `m + 2`, so
every `m ≥ 1` -- genus four and up, the endgame's genus six among them -- is
covered.  `MemberCertifiedPencil.caterpillarMemberSeed`, built by hand, is the
same receipt at the same member; this one is not built, it is deduced. -/
theorem caterpillar_nonempty_memberSeed (m : ℕ) (hm : 1 ≤ m)
    (request : Fin (6 * m + 3) → ℚ) :
    Nonempty (MemberSeed (FibreCaterpillar.caterpillarMember m request)) :=
  nonempty_memberSeed_of_member _ (by omega)

/-- Genus six, degree four: the case the endgame runs at. -/
theorem caterpillar_two_nonempty_memberSeed (request : Fin (6 * 2 + 3) → ℚ) :
    Nonempty (MemberSeed (FibreCaterpillar.caterpillarMember 2 request)) :=
  caterpillar_nonempty_memberSeed 2 (by omega) request

end Member

/-! ## 5.  The producer with no receipt -/

section Spec

variable {n p : ℕ} {spec : Spec n p}
  {member : FibreMember spec.core (fun slot ↦ ((spec.length slot : ℕ) : ℚ)) degree}

/-- **The producer, with no receipt.**  Neither `member.Closed` nor any
multiplicity is used. -/
theorem carriesCertifiedPencil_of_spec_member
    (hCubic : spec.core.Cubic) (hCoreConnected : spec.core.Connected)
    (hDegree : 3 ≤ degree) (start : Fin p → ℚ) (hStart : ∀ i, 0 < start i) :
    LocalCases.CertifiedPencil.CarriesCertifiedPencil spec degree member.matrix
      start member.coords := by
  obtain ⟨ms⟩ := nonempty_memberSeed_of_member member hDegree
  exact carriesCertifiedPencil_of_member ms hCubic hCoreConnected
    (by omega) start hStart

end Spec

end DraismaVargas.Count.MemberSeedExists
