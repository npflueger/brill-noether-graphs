import DraismaVargas.Infrastructure.BlockSplitCount
import DraismaVargas.LocalCases.StatementFromLink

/-!
# The retained relabeling at a nonempty expansion forest: the shape it needs

**Source.**  Draisma--Vargas Part I, the proof of the main theorem (§5.4): a
non-trivalent requested type is presented as a point of the closed cone of a
trivalent one; and Vargas, Part II, §4.4 (proofs of the main theorems).  At a
terminal face the model's target is the pruned contracted spec, and at a
nonempty expansion forest the collapsed edges are the zero rows of the
trivalent model.  The marker cut of §2--§3 below, and the arithmetic of it in
the companion module `DraismaVargas.Infrastructure.BlockSplitCount`, is in
neither paper: neither spells out the transport at an integral scale, and a
fortiori neither writes down the ordered block split
(`DraismaVargas.Infrastructure.OrderedBlockSplit`).

## What is proved

`StatementFromLink` reduces the whole Part II route to two receipts, the
type-change link `link` (`OuterWalk.TypeChangeLink`) and
`StatementFromLink.RetainedRelabeling`, and offers
`StatementFromLink.laplacianEquiv_of_coreModel` as a reduction of the second:
produce a `RefinementCore.CoreModel` of the retained segment data on the face's
pruned contracted spec.  This file shows that this shape is **too strong**, and
gives the right one.

* §1 re-proves at a **general forest** the part of `OrientedTraversal` §3 that
  is forest-independent: the positive sublist of a row, the refined slots it
  carries, and the bijection `keptSlotEquiv` of those with the face's kept
  slots.  A forest row contributes nothing
  (`positiveRow_eq_nil_of_mem_forest`), so the kept slots are counted by the
  retained rows alone (`card_keptSlots`).

* §2 transports the marker-cut arithmetic of the companion module
  `DraismaVargas.Infrastructure.BlockSplitCount` -- where `countPos` counts the
  refined slots a list of cleared occurrence lengths prescribes, `Aligned l a`
  says the cut at total `a` lands on an occurrence boundary, and
  `sum_countPos_blocks` is the exact count
  `((blocks l ws).map countPos).sum = countPos l + cutCount l ws` -- to the
  terminal face: the retained refinement has
  `(keptSlots topology).card + ∑ cutCount` slots
  (`sum_segments_eq_card_keptSlots_add`), hence at least as many as the pruned
  contracted source has, with equality exactly when no marker straddles.

* §3 is the **mismatch**.  A `RefinementCore.CoreModel` carries a bijection
  `slotModel` of the refined slots with the target's slots, so it forces the
  two counts to agree (`sum_segments_of_coreModel`).  At a straddled marker
  they do not, so there is **no** such core model
  (`isEmpty_coreModel_of_straddle`), and none for the expansion model of the
  stable-model reduction either (`isEmpty_coreModel_of_straddle_of_double`,
  stated at a `CoreExpansion.SlotKind.double` slot; `exists_kind_double`
  records that such slots occur, at the wedge witness
  `StableModelReduction.wedge_expansion`).  So
  `StatementFromLink.laplacianEquiv_of_coreModel` is not a reduction of
  `RetainedRelabeling`: it is a sufficient condition that is unavailable
  exactly where the general forest is needed.

* §4 gives the right shape, and it costs nothing.  `Spec.graph` is the *unit*
  subdivision, so a canonical bivalent split of the target does not change the
  graph (`IteratedSplitRefinement.CanonicalSplitChain.laplacianEquiv`).
  `CutRelabeling` therefore asks, at each terminal face, for a split chain out
  of the pruned contracted spec and a core model of the retained segment data
  on its end; `retainedRelabeling_of_cutRelabeling` turns that into
  `StatementFromLink.RetainedRelabeling`.

* §5 feeds it to `StatementFromLink`: `nonempty_evenSubdivisionPencil_of_link'`
  has the Statement's four binders, the type-change link, and `CutRelabeling`
  at every expansion datum -- the same theorem as
  `StatementFromLink.nonempty_evenSubdivisionPencil_of_link` with a hypothesis
  that can hold at a straddled marker.

## What is not proved here -- the explicit hypotheses

1. **`link`**, unchanged: the type-change link `OuterWalk.TypeChangeLink`.
2. **`CutRelabeling`**: at every terminal face of every candidate carrying the
   cubic model with a faithful spanning core dictionary, a canonical split
   chain out of the pruned contracted spec together with a core model of the
   retained segment data on its end.  What §1--§3 supply towards it is the slot
   half in the two directions that are forest-independent (`keptSlotEquiv`) and
   the exact slot count (`sum_segments_eq_card_keptSlots_add`), which is what
   the chain's length must be.  The rest is built downstream: `RetainedCut`
   constructs the chain (`RetainedCut.cutChain`) and proves
   `cutRelabeling_of_cutCoreModel`, which reduces `CutRelabeling` to one
   `RefinementCore.CoreModel` of the retained segment data on
   `RetainedCut.cutSpec`, both of whose cardinalities it computes (`cutSpec_p`,
   and `card_refinedVertex_eq_cutSpec_n` on the general-forest count
   `RetainedExhausts`); `RetainedTraversal` and `RetainedFibre` re-index the
   traversal; `RetainedExhausts` proves the general-forest count,
   `RetainedVertexModel` the vertex map and its endpoint equations, and
   `RetainedClassInjectivity` the general-forest injectivity, so `CutRelabeling`
   holds unconditionally for the expansion model of the stable-model reduction
   (`RetainedClassInjectivity.cutRelabeling_of_expansion`).

Nothing else is assumed: no genericity, no interior tracked progress, no
terminal identification.  All of those are discharged inside
`StatementFromLink`.

## Consumers

`StatementFromLink`'s route to `DraismaVargas.Statement`, and `RetainedCut`,
`RetainedTraversal` and `RetainedFibre`, which build the chain and reduce the
core model to `RetainedCut.cutSpec`, whose target shape is fixed here.  The
final assembly (`RetainedClassInjectivity.nonempty_evenSubdivisionPencil`) goes
through `RetainedClassInjectivity` rather than through this file's
`link`/`CutRelabeling` binders.
-/

namespace DraismaVargas.LocalCases.RetainedRelabeling

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.BlockSplitCount
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.OrderedBlockSplit
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.SlotRefinement
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TerminalExhausts
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.ZeroForestPreservation

/-! ## 0.  Packing, and a Laplacian equivalence through a split chain -/

/-- A subdivision specification, packed.  Reducible, so that a chain out of it
unifies with the specification it packs. -/
abbrev packed {N P : ℕ} (base : SubdivisionGraph.Spec N P) : PackedSpec := ⟨N, P, base⟩

/-- **A core model on the far end of a split chain is a relabeling onto the
near end.**  `CanonicalSplitChain.laplacianEquiv` says a canonical bivalent
split does not change the graph -- `Spec.graph` is the unit subdivision, so an
extra core vertex at an interior integer point of a slot is already a vertex of
the graph -- so a model of the refinement on the split target relabels it onto
the unsplit source. -/
def laplacianEquivOfChainOfCoreModel {source : PackedSpec} {data : SegmentData source}
    {N P : ℕ} {base : SubdivisionGraph.Spec N P} {mid : PackedSpec}
    (chain : CanonicalSplitChain (packed base) mid)
    (cm : RefinementCore.CoreModel data mid.spec) :
    LaplacianEquiv (refineAllSlots data).graph base.graph :=
  cm.laplacianEquiv.trans chain.laplacianEquiv.symm

/-! ## 1.  Rows, positive rows and kept slots at a general forest -/

section Slots

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}

/-- The row displaying stable slot `i`, at a general forest. -/
abbrev row (iface : InputInterface spec strong.toPresentation coordinates F)
    (i : Fin p) : List candidate.datum.SourceEdge :=
  strong.toPresentation.path (iface.slot i)

/-- The positive sublist of that row: the occurrences the face does not
contract, in traversal order. -/
def positiveRow (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates) (i : Fin p) :
    List candidate.datum.SourceEdge :=
  (row iface i).filter fun edge ↦ decide (0 < face.realization.sourceLength edge)

variable {iface : InputInterface spec strong.toPresentation coordinates F}

theorem mem_positiveRow {i : Fin p} {edge : candidate.datum.SourceEdge} :
    edge ∈ positiveRow iface face i ↔
      edge ∈ row iface i ∧ 0 < face.realization.sourceLength edge := by
  simp [positiveRow, List.mem_filter]

theorem positiveRow_nodup (i : Fin p) : (positiveRow iface face i).Nodup :=
  (strong.decomposes.nodup _).filter _

theorem length_positiveRow (i : Fin p) :
    (positiveRow iface face i).length =
      (row iface i).countP fun edge ↦ decide (0 < face.realization.sourceLength edge) :=
  List.countP_eq_length_filter.symm

/-- **A forest row contributes no refined slot.**  Its occurrences are all
contracted (`InputRefinementData.sourceLength_eq_zero_of_mem_forest`). -/
theorem positiveRow_eq_nil_of_mem_forest {i : Fin p} (hi : i ∈ F) :
    positiveRow iface face i = [] := by
  refine List.eq_nil_of_length_eq_zero ?_
  rw [length_positiveRow, List.countP_eq_zero]
  intro edge hedge
  have h := sourceLength_eq_zero_of_mem_forest iface face hi edge hedge
  simp [h]

/-- The refined slots carried by the retained rows: a stable slot together
with the position of a surviving occurrence in the row displaying it. -/
abbrev SlotIndex (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates) : Type :=
  Σ i : Fin p, Fin (positiveRow iface face i).length

/-- The positive source occurrence a refined slot names. -/
def occurrence (x : SlotIndex iface face) : candidate.datum.SourceEdge :=
  (positiveRow iface face x.1)[(x.2 : ℕ)]

theorem occurrence_mem_positiveRow (x : SlotIndex iface face) :
    occurrence x ∈ positiveRow iface face x.1 :=
  List.getElem_mem _

theorem occurrence_mem (x : SlotIndex iface face) : occurrence x ∈ row iface x.1 :=
  (mem_positiveRow.mp (occurrence_mem_positiveRow x)).1

theorem sourceLength_occurrence_pos (x : SlotIndex iface face) :
    0 < face.realization.sourceLength (occurrence x) :=
  (mem_positiveRow.mp (occurrence_mem_positiveRow x)).2

theorem not_isDangling_occurrence (x : SlotIndex iface face) :
    ¬ IsDangling candidate.datum (occurrence x) :=
  strong.decomposes.not_isDangling_of_mem (occurrence_mem x)

theorem occurrence_injective :
    Function.Injective (occurrence (iface := iface) (face := face)) := by
  rintro ⟨i, m⟩ ⟨i', m'⟩ hEq
  have hMem : occurrence (⟨i, m⟩ : SlotIndex iface face) ∈ row iface i :=
    occurrence_mem ⟨i, m⟩
  have hMem' : occurrence (⟨i, m⟩ : SlotIndex iface face) ∈ row iface i' := by
    rw [hEq]; exact occurrence_mem ⟨i', m'⟩
  have hRow : i = i' := by
    by_contra hNe
    exact strong.decomposes.disjoint (iface.slot i) (iface.slot i')
      (fun hSlot ↦ hNe (iface.slot.injective hSlot)) _ hMem hMem'
  subst hRow
  have hIdx : (m : ℕ) = (m' : ℕ) :=
    (positiveRow_nodup (iface := iface) (face := face) i).getElem_inj_iff.mp hEq
  exact congrArg (Sigma.mk i) (Fin.ext hIdx)

theorem occurrence_surjective {edge : candidate.datum.SourceEdge}
    (hPos : 0 < face.realization.sourceLength edge)
    (hSurvives : ¬ IsDangling candidate.datum edge) :
    ∃ x : SlotIndex iface face, occurrence x = edge := by
  obtain ⟨r, hr⟩ := strong.decomposes.surviving_mem edge hSurvives
  have hMem : edge ∈ positiveRow iface face (iface.slot.symm r) := by
    refine mem_positiveRow.mpr ⟨?_, hPos⟩
    show edge ∈ strong.toPresentation.path (iface.slot (iface.slot.symm r))
    rw [Equiv.apply_symm_apply]; exact hr
  obtain ⟨m, hm, hmEq⟩ := List.mem_iff_getElem.mp hMem
  exact ⟨⟨iface.slot.symm r, ⟨m, hm⟩⟩, hmEq⟩

/-- **The kept slots are the positive occurrences of the retained rows.**
The general-forest form of `OrientedTraversal.RowDictionary.slotEquiv`: only
`PresentationDecomposition.Decomposes` is used, no dictionary and no
positivity of the row totals, so it holds verbatim at a nonempty forest. -/
def keptSlotEquiv
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (topology : ClearedFace.SourceContractionTopology face) :
    SlotIndex iface face ≃
      {e : topology.degSpec.PositiveSlot // topology.KeptSlot e} :=
  Equiv.ofBijective
    (fun x ↦ ⟨⟨slotOf candidate.datum face.realization (occurrence x), by
        show 0 < face.realization.sourceLength
          (face.realization.sourceEdgeAt
            (slotOf candidate.datum face.realization (occurrence x)))
        rw [sourceEdgeAt_slotOf]
        exact sourceLength_occurrence_pos x⟩, by
        show ¬ IsDangling candidate.datum
          (face.realization.sourceEdgeAt
            (slotOf candidate.datum face.realization (occurrence x)))
        rw [sourceEdgeAt_slotOf]
        exact not_isDangling_occurrence x⟩)
    ⟨fun x y hxy ↦ occurrence_injective (by
        have h := congrArg (fun s ↦ face.realization.sourceEdgeAt s.val.val) hxy
        simpa using h),
      fun s ↦ by
        obtain ⟨x, hx⟩ := occurrence_surjective
          (show 0 < face.realization.sourceLength
            (face.realization.sourceEdgeAt s.val.val) from s.val.property) s.property
        refine ⟨x, Subtype.ext (Subtype.ext ?_)⟩
        show slotOf candidate.datum face.realization (occurrence x) = s.val.val
        rw [hx, slotOf_sourceEdgeAt]⟩

/-- **The kept slot count, read on the rows.** -/
theorem card_keptSlots (iface : InputInterface spec strong.toPresentation coordinates F)
    (topology : ClearedFace.SourceContractionTopology face) :
    (ClearedFace.SourceContractionTopology.keptSlots topology).card =
      ∑ i : Fin p, (positiveRow iface face i).length := by
  have h := Fintype.card_congr
    ((keptSlotEquiv iface topology).trans (RefinementCore.keptSlotIndex topology))
  simp only [Fintype.card_sigma, Fintype.card_fin] at h
  exact h.symm

end Slots


/-! ## 2.  The retained refined slot count against the kept slot count -/

section Counting

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p} {F : Finset (Fin p)}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}
  {n' p' : ℕ} {small : SubdivisionGraph.Spec n' p'}

/-- `pos` really reads off the position in the carrier list. -/
theorem pos_getElem (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F})
    {k : ℕ} (hk : k < (idx.carried e).length) :
    idx.pos ((idx.carried e)[k]) = k := by
  have hmem : (idx.carried e)[k] ∈ idx.carried e := List.getElem_mem hk
  have he : idx.owner ((idx.carried e)[k]) = e := idx.owner_eq_of_mem e _ hmem
  have hget := idx.carried_getElem ((idx.carried e)[k])
  have hlt : idx.pos ((idx.carried e)[k]) < (idx.carried e).length := by
    have h := idx.pos_lt ((idx.carried e)[k])
    rwa [he] at h
  rw [he, List.getElem?_eq_getElem hlt, Option.some_inj] at hget
  exact (idx.nodup e).getElem_inj_iff.mp hget

/-- **The carrier lists partition the requested slots.**  Summing a quantity
over the slots of `small` is summing it along the carrier list of each
retained slot. -/
theorem sum_over_carried (idx : RetainedIndex spec F small) (g : Fin p' → ℕ) :
    ∑ j : Fin p', g j =
      ∑ e : {i : Fin p // i ∉ F}, ((idx.carried e).map g).sum := by
  classical
  have hfib : ∀ e : {i : Fin p // i ∉ F},
      ((Finset.univ : Finset (Fin p')).filter fun j ↦ idx.owner j = e) =
        (idx.carried e).toFinset := by
    intro e
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    exact ⟨fun h ↦ h ▸ idx.mem_carried_owner j, fun h ↦ idx.owner_eq_of_mem e j h⟩
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun j : Fin p' ↦ idx.owner j) (fun j _ ↦ Finset.mem_univ (idx.owner j)) g]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [hfib e, List.sum_toFinset _ (idx.nodup e)]

/-- The positive occurrences of a row, counted on its measured form. -/
theorem countPos_rowSegments
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (face : ClearedFace candidate strong.toPresentation coordinates) (i : Fin p) :
    countPos (rowSegments iface face i) = (positiveRow iface face i).length := by
  rw [countPos, rowSegments, length_positiveSegments_map, length_positiveRow]

/-- The refined slot counts prescribed along one retained row are the positive
counts of the blocks its occurrence list is cut into. -/
theorem map_carried_segments_length
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) :
    (idx.carried e).map
        (fun j ↦ ((Retained.segmentData iface face idx).segments j).length) =
      (blocks (rowSegments iface face ↑e) (Retained.blockTotals face idx e)).map
        countPos := by
  have hlen : (idx.carried e).length =
      (blocks (rowSegments iface face ↑e) (Retained.blockTotals face idx e)).length := by
    rw [length_blocks, Retained.length_blockTotals]
  refine List.ext_getElem (by rw [List.length_map, List.length_map, hlen]) ?_
  intro k h1 h2
  simp only [List.getElem_map]
  have hk : k < (idx.carried e).length := by rwa [List.length_map] at h1
  have hmem : (idx.carried e)[k] ∈ idx.carried e := List.getElem_mem hk
  have he : idx.owner ((idx.carried e)[k]) = e := idx.owner_eq_of_mem e _ hmem
  have hp : idx.pos ((idx.carried e)[k]) = k := pos_getElem idx e hk
  rw [Retained.segmentData_segments]
  show countPos (Retained.blockSegments iface face idx ((idx.carried e)[k])) = _
  rw [Retained.blockSegments, he, hp,
    List.getD_eq_getElem _ _ (by simpa using h2)]

/-- **The retained refined slots, counted row by row.** -/
theorem sum_segments_length
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (idx : RetainedIndex spec F small) :
    ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length =
      ∑ e : {i : Fin p // i ∉ F},
        ((blocks (rowSegments iface face ↑e)
          (Retained.blockTotals face idx e)).map countPos).sum := by
  rw [sum_over_carried idx
    (fun j ↦ ((Retained.segmentData iface face idx).segments j).length)]
  exact Finset.sum_congr rfl fun e _ ↦ by rw [map_carried_segments_length]

theorem sum_positiveRow_eq
    (iface : InputInterface spec strong.toPresentation coordinates F) :
    ∑ i : Fin p, (positiveRow iface face i).length =
      ∑ e : {i : Fin p // i ∉ F}, (positiveRow iface face ↑e).length := by
  classical
  have h1 : ∑ i ∈ Fᶜ, (positiveRow iface face i).length =
      ∑ i : Fin p, (positiveRow iface face i).length := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i _ hi
    rw [Finset.mem_compl, not_not] at hi
    rw [positiveRow_eq_nil_of_mem_forest hi, List.length_nil]
  have h2 : ∑ i ∈ Fᶜ, (positiveRow iface face i).length =
      ∑ e : {i : Fin p // i ∉ F}, (positiveRow iface face ↑e).length :=
    Finset.sum_subtype _ (fun x ↦ Finset.mem_compl) _
  rw [← h1, h2]

theorem blockTotals_ne_nil
    (face : ClearedFace candidate strong.toPresentation coordinates)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) :
    Retained.blockTotals face idx e ≠ [] := by
  simp only [Retained.blockTotals, ne_eq, List.map_eq_nil_iff]
  exact idx.carried_ne_nil e

theorem sum_blockTotals_eq_sum_rowSegments
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (idx : RetainedIndex spec F small) (e : {i : Fin p // i ∉ F}) :
    (Retained.blockTotals face idx e).sum = (rowSegments iface face ↑e).sum := by
  rw [Retained.sum_blockTotals face idx e, rowSegments_sum_of_not_mem iface face e.2]

/-- **The retained refinement, counted exactly.**  It has one slot per kept
slot of the face, plus one for every occurrence a marker cut straddles. -/
theorem sum_segments_eq_card_keptSlots_add
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face) :
    ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length =
      (ClearedFace.SourceContractionTopology.keptSlots topology).card +
        ∑ e : {i : Fin p // i ∉ F},
          cutCount (rowSegments iface face ↑e) (Retained.blockTotals face idx e) := by
  rw [card_keptSlots iface topology, sum_segments_length iface idx,
    sum_positiveRow_eq iface, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [sum_countPos_blocks _ _ (sum_blockTotals_eq_sum_rowSegments iface idx e),
    countPos_rowSegments iface face ↑e]

/-- **The kept slots never outnumber the retained refined slots.** -/
theorem card_keptSlots_le_sum_segments
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face) :
    (ClearedFace.SourceContractionTopology.keptSlots topology).card ≤
      ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length := by
  rw [sum_segments_eq_card_keptSlots_add iface idx topology]
  exact Nat.le_add_right _ _

/-- **and at a straddled marker they are strictly fewer.**  If some retained
slot carries two requested slots (a `CoreExpansion.SlotKind.double`) and the
marker's metric position is not a partial sum of the cleared occurrence
lengths along the row displaying it, then the retained refinement has strictly
more slots than the face's pruned contracted source. -/
theorem card_keptSlots_lt_sum_segments
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (idx : RetainedIndex spec F small)
    (topology : ClearedFace.SourceContractionTopology face)
    {e₀ : {i : Fin p // i ∉ F}} {j₁ j₂ : Fin p'}
    (hcar : idx.carried e₀ = [j₁, j₂])
    (hAl : ¬ Aligned (rowSegments iface face ↑e₀) (face.scale * small.length j₁)) :
    (ClearedFace.SourceContractionTopology.keptSlots topology).card <
      ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length := by
  classical
  rw [sum_segments_eq_card_keptSlots_add iface idx topology]
  refine Nat.lt_add_of_pos_right (Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _)
    ⟨e₀, Finset.mem_univ _, ?_⟩)
  have htot : Retained.blockTotals face idx e₀ =
      [face.scale * small.length j₁, face.scale * small.length j₂] := by
    rw [Retained.blockTotals, hcar]; rfl
  rw [htot, cutCount_cons_cons,
    if_neg (by simpa only [alignedB_iff] using hAl), cutCount_singleton]
  omega

/-! ## 3.  The `CoreModel` shape fails at a straddled marker -/

/-- A core model of the retained segment data on the pruned contracted source
would equate the two counts. -/
theorem sum_segments_of_coreModel
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (idx : RetainedIndex spec F small)
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (cm : RefinementCore.CoreModel (Retained.segmentData iface face idx)
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)) :
    ∑ j : Fin p', ((Retained.segmentData iface face idx).segments j).length =
      (ClearedFace.SourceContractionTopology.keptSlots topology).card := by
  have h := Fintype.card_congr cm.slotModel
  simp only [Fintype.card_sigma, Fintype.card_fin] at h
  exact h

/-- **The mismatch.**  At a straddled marker there is no
`RefinementCore.CoreModel` of the retained segment data on the pruned
contracted source: `slotModel` would be a bijection between two sets of
different size.  So `StatementFromLink.laplacianEquiv_of_coreModel` is not a
reduction of the general-forest relabeling -- §4 replaces it by splitting the
straddled kept slots on the target side, which does not change the graph. -/
theorem isEmpty_coreModel_of_straddle
    (iface : InputInterface spec strong.toPresentation coordinates F)
    (idx : RetainedIndex spec F small)
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    {e₀ : {i : Fin p // i ∉ F}} {j₁ j₂ : Fin p'}
    (hcar : idx.carried e₀ = [j₁, j₂])
    (hAl : ¬ Aligned (rowSegments iface face ↑e₀) (face.scale * small.length j₁)) :
    IsEmpty (RefinementCore.CoreModel (Retained.segmentData iface face idx)
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)) :=
  ⟨fun cm ↦ absurd (sum_segments_of_coreModel iface idx hKept cm)
    (Nat.ne_of_gt (card_keptSlots_lt_sum_segments iface idx topology hcar hAl))⟩

end Counting

/-! ### The same, for the expansion model of the stable-model reduction -/

section Producer

variable {n₀ p₀ N Q : ℕ} {D : ExpansionData n₀ p₀ N Q} {spec₀ : Spec n₀ p₀}

/-- A `CoreExpansion.SlotKind.double` slot of the expansion datum carries
its two requested slots in series: its carrier list has length two. -/
theorem carried_eq_of_kind_double (hCond : D.Conditions spec₀.core) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    {e : Fin Q} (he : e ∉ expansionForest D) {j₁ j₂ : Fin p₀}
    (hk : D.kind e = SlotKind.double j₁ j₂) :
    (RetainedIndexProducer.retainedIndex hCond hN hL).carried ⟨e, he⟩ = [j₁, j₂] := by
  show RetainedIndexProducer.kindCarried (D.kind e) = _
  rw [hk]
  rfl

/-- **The mismatch, for the expansion model.**  At a `double` slot whose marker
does not land on an occurrence boundary of the row displaying it, the retained
segment data of the retained indexing of the stable-model reduction has no
core model on the face's pruned contracted source. -/
theorem isEmpty_coreModel_of_straddle_of_double {target : CFGraph} {degree : ℕ}
    {gluing : GluingDatum target degree} {wall : target.V}
    {candidate : Candidate target degree gluing wall}
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    {coordinates : coordinate → ℚ}
    {strong : StrongPresentation candidate.datum coordinate}
    {face : ClearedFace candidate strong.toPresentation coordinates}
    (hCond : D.Conditions spec₀.core) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
      (expansionForest D))
    {topology : ClearedFace.SourceContractionTopology face}
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    {e : Fin Q} (he : e ∉ expansionForest D) {j₁ j₂ : Fin p₀}
    (hk : D.kind e = SlotKind.double j₁ j₂)
    (hAl : ¬ Aligned (rowSegments iface face e) (face.scale * spec₀.length j₁)) :
    IsEmpty (RefinementCore.CoreModel
      (Retained.segmentData iface face (RetainedIndexProducer.retainedIndex hCond hN hL))
      (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)) :=
  isEmpty_coreModel_of_straddle iface _ hKept
    (carried_eq_of_kind_double hCond hN hL he hk) hAl

/-- **`double` slots occur.**  `StableModelReduction.wedge_expansion` is the
marker-aware expansion, by the stable-model reduction, of the wedge of two loops
-- four requested slots over a three-slot cubic model -- so some retained cubic
slot really does carry two requested slots in series, and
`Retained.blockSegments` really does have to cut a row. -/
theorem exists_kind_double :
    ∃ (D : ExpansionData 3 4 2 3), D.Conditions StableModelReduction.wedgeCore ∧
      ∃ (e : Fin 3) (j₁ j₂ : Fin 4), D.kind e = SlotKind.double j₁ j₂ := by
  obtain ⟨D, hCond, hMF⟩ := RetainedIndexProducer.exists_conditions_not_markerFree
  refine ⟨D, hCond, ?_⟩
  by_contra h
  refine hMF ?_
  intro e j₁ j₂ hk
  exact h ⟨e, j₁, j₂, hk⟩

end Producer

/-! ## 4.  The right shape: a canonical split of the pruned side -/

section Repair

open DraismaVargas.LocalCases.OrientedTraversal

/-- **The retained relabeling, in the shape the retained data can supply.**

`StatementFromLink.RetainedRelabeling` verbatim, except that the core model is
asked for on the far end of a canonical split chain out of the pruned contracted
spec instead of on the pruned contracted spec itself.  §3 shows that difference
is not cosmetic: at a straddled marker the second is empty and the first is
not, and by `CanonicalSplitChain.laplacianEquiv` it costs nothing, because
`Spec.graph` is the unit subdivision.

Every hypothesis of `StatementFromLink.RetainedRelabeling` is kept inside the
binder, so this is the honest general-forest analogue of
`OrientedTraversal.RowDictionary.sourceModel` and not a statement about
arbitrary candidates. -/
def CutRelabeling {N Q n p : ℕ} (model : Spec N Q) (F : Finset (Fin Q))
    (small : Spec n p) (idx : RetainedIndex model F small) : Prop :=
  ∀ (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
    (tgt : CFGraph.{0}) (gdata : GluingDatum tgt degree) (wall : tgt.V)
    (candidate : Candidate tgt degree gdata wall)
    (strong : StrongPresentation candidate.datum coordinate)
    (coordinates : coordinate → ℚ)
    (iface : InputInterface model strong.toPresentation coordinates F)
    (dict : CoreDictionary model strong iface),
    Faithful dict → Spanning dict → candidate.datum.Connected →
    SourceGenusMatches model candidate.datum →
    ∀ (face : ClearedFace candidate strong.toPresentation coordinates)
      (topology : ClearedFace.SourceContractionTopology face)
      (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty),
      ∃ (mid : PackedSpec) (_ : CanonicalSplitChain
          (packed (ClearedFace.SourceContractionTopology.prunedSpec topology hKept)) mid),
        Nonempty (RefinementCore.CoreModel (Retained.segmentData iface face idx) mid.spec)

/-- **The reduction.**  A cut plus a core model at every terminal face is
`StatementFromLink.RetainedRelabeling`. -/
theorem retainedRelabeling_of_cutRelabeling {N Q n p : ℕ} {model : Spec N Q}
    {F : Finset (Fin Q)} {small : Spec n p} {idx : RetainedIndex model F small}
    (H : CutRelabeling model F small idx) :
    StatementFromLink.RetainedRelabeling model F small idx := by
  intro degree coordinate _ _ tgt gdata wall candidate strong coordinates iface dict
    hFaithful hSpanning hConnected hSource face topology hKept
  obtain ⟨mid, chain, ⟨cm⟩⟩ := H degree coordinate tgt gdata wall candidate strong
    coordinates iface dict hFaithful hSpanning hConnected hSource face topology hKept
  exact ⟨laplacianEquivOfChainOfCoreModel chain cm⟩

end Repair

/-! ## 5.  The Statement's conclusion, on `CutRelabeling` -/

/-- **The Statement's conclusion for an arbitrary connected request, on the
type-change link and `CutRelabeling`.**

The binders `spec`, `hconn`, `hGenus`, `hEven` and the conclusion are
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one`'s
verbatim, and `link` is
`StatementFromLink.nonempty_evenSubdivisionPencil_of_link`'s verbatim.  Only
the reduction-side receipt changes: `CutRelabeling` in place of
`StatementFromLink.RetainedRelabeling`, which by §3 is the difference between a
hypothesis that fails at a straddled marker and one that need not. -/
theorem nonempty_evenSubdivisionPencil_of_link' {n p : ℕ} (spec : Spec n p)
    (hconn : graph_connected spec.graph) (hGenus : 6 ≤ p + 1 - n)
    (hEven : Even (p + 1 - n))
    (link : ∀ m : ℕ, p + 1 - n = 2 * m + 2 →
      ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (cut : ∀ {n₀ p₀ : ℕ} (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e)
      (hCond : D.Conditions spec₀.core),
      CutRelabeling (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀
        (RetainedIndexProducer.retainedIndex hCond hN hL)) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  StatementFromLink.nonempty_evenSubdivisionPencil_of_link spec hconn hGenus hEven link
    (fun spec₀ D hN hL hCond ↦
      retainedRelabeling_of_cutRelabeling (cut spec₀ D hN hL hCond))

/-- **The same theorem with the two receipts pulled out** in front of the
Statement's own four binders, exactly as
`StatementFromLink.nonempty_evenSubdivisionPencil_of_receipts` does.  (The
final assembly goes through `RetainedClassInjectivity` instead.) -/
theorem nonempty_evenSubdivisionPencil_of_receipts'
    (link : ∀ m : ℕ,
      ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (cut : ∀ {n₀ p₀ : ℕ} (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e)
      (hCond : D.Conditions spec₀.core),
      CutRelabeling (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀
        (RetainedIndexProducer.retainedIndex hCond hN hL))
    {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph)
    (hGenus : 6 ≤ p + 1 - n) (hEven : Even (p + 1 - n)) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  nonempty_evenSubdivisionPencil_of_link' spec hconn hGenus hEven (fun m _ ↦ link m) cut

/-! ## 6.  A straddled cut, concretely -/

/-- The cut prescribed by a marker at metric position `1` along a row whose
single cleared occurrence has length `3`. -/
example : blocks [3] [1, 2] = [[1], [2]] := rfl

theorem not_aligned_three_one : ¬ Aligned [3] 1 := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk
  | succ k => simp at hk

/-- **The straddle hypothesis of §3 is arithmetic, and satisfiable**: one
occurrence, two prescribed blocks, two refined slots where the face has one
kept slot. -/
theorem countPos_lt_cut_three_one_two :
    countPos [3] < ((blocks [3] [1, 2]).map countPos).sum := by
  rw [sum_countPos_blocks [3] [1, 2] (by norm_num),
    cutCount_cons_cons, if_neg (by simpa only [alignedB_iff] using not_aligned_three_one),
    cutCount_singleton]
  omega

/-- and the count of §2 reads it off: exactly one occurrence is straddled. -/
theorem cutCount_three_one_two : cutCount [3] [1, 2] = 1 := by
  rw [cutCount_cons_cons, if_neg (by simpa only [alignedB_iff] using not_aligned_three_one),
    cutCount_singleton]

end

end DraismaVargas.LocalCases.RetainedRelabeling
