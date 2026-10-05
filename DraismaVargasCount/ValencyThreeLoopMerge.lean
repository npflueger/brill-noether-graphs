module

public import DraismaVargasCount.ValencyThreeCensus
public import DraismaVargasCount.PassOnceLollipopWitness

@[expose] public section

set_option autoImplicit false

/-!
# The loop merge: the valency-three census at a parallel slot

`ValencyThreeCensus.metricCensus_clause_of_v3` proves the `FacetCensus.MetricCensus` clause at
every valency-three metric limit of a step at which **neither** core has a slot parallel to the
contracted slot `e₀` (`NoParallel`).  This file removes that hypothesis wherever the step has a
loop core on the other side, and reduces the rest (digon--digon steps) to a named input,
`LoopPresented`, which `ValencyThreeDigon` discharges.  It is part of the type-change step,
step 3 of `Assembly`; the stages are those of `ValencyThreeSplit`.

## The mathematics

Where `NoParallel` fails on a cubic core, the parallel slot `s` is unique
(`parallel_unique`) and the contraction `c/e₀` has a loop at the merged vertex.  Suppose the
same metric limit is also presented over a core `cL` with a loop `f` at an end of `e₀` (a *loop
presenter*).  At the loop presenter, the lollipop lemmas of Draisma--Vargas Part I
(`loop_labels`) put the two survivors `e₂`, `e₅` (labels `0`, `3`, which lie over one target
edge) on the loop row, over the leaf edge adjacent to the loop branch; so they share a stable
path and sheets there, and the sheet swap (`ValencyThreeSplit.swapIso`) is a limit
automorphism fixing every target edge and exchanging exactly `e₂` and `e₅` (`exists_loopSwap`,
`loop_lpaths`).  Both facts transport to every presentation along any geometric limit
isomorphism (`loopData_of_limitIso`).  Back on the digon core, the slots of `e₃` and `e₄` are
then *not* parallel (`nonPar_of_lpaths`: otherwise the shared slot of `e₂`, `e₅` would be a
second parallel slot, or a slot met twice beside a parallel one, on a cubic core), so Type III
(`e₃ ~ e₄`, `paired12_iff`) is read off the core on both sides, while Types I and II are
exchanged by the swap (`type_swap03`).  Hence either the given metric isomorphism `ψ` or
`ψ ≫ σ'` matches the types, and stages 4--5 conclude (`frameClass_eq_of_loopPresenter`).  In
words: Types I and II over the digon core are one class, identified by the label-moving
automorphism `σ'`.

**The census does not fail at a parallel slot**: no counterexample exists in the form
analysed.  Computer experiments (not part of this library) found every parallel case in the
genus-four catalogue (2550 cases) and in a genus-six sample (817 cases) shaped as the lollipop
lemmas predict: two surviving occurrences of index one over one target edge.

## What is proved

* §1 `loopBranch_mem`, `leafEdge_ne_contracted`, `loop_labels`, **`exists_loopSwap`**, `lpath`,
  **`loop_lpaths`**.
* §2 `lpath_transport`, **`loopData_of_limitIso`**.
* §3 `Parallel`, **`parallel_unique`**, `incidence_lt_two_of_parallel` (cubic cores).
* §4 `homed_unique`, `paired_compl`, **`paired12_iff`**, `paired_relabel`, **`type_swap03`**.
* §5 `NonPar`, `slotOf`, `paired_iff_coreShare_of` (the reading of `ValencyThreeCoreSlots`, one
  slot at a time), `two_le_incidence`.
* §6 **`nonPar_of_lpaths`**, **`frameClass_eq_of_loopPresenter`** (the loop merge).
* §7 `LoopAtEnd`, `LoopMerge` (decidable), `near_nonloop`, `LoopPresented`,
  `loopPresented_of_move`, `loopPresented_far`, `frameClass_eq_of_side`,
  **`metricCensus_clause_of_presented`** (general form), **`metricCensus_clause_of_v3'`**
  (`LoopMerge` both ways in place of `NoParallel` both ways), `metricCensus_of_forall_v3'`.
* §8 `loopMerge_cat` (`LoopMerge` holds both ways at `cat_step`, where the far core fails
  `NoParallel`), **`metricCensus_clause_cat`** (the clause at every valency-three metric limit
  of `cat_step`, for every class), `cat_obligation_of_forall_v3`, `digonMove` and
  `not_loopMerge_digon` (a genus-six digon--digon step, where `LoopMerge` fails on both sides).

## Hypotheses

* **Digon--digon steps.**  `LoopMerge c c' e₀ := NoParallel c e₀ ∨ LoopAtEnd c' e₀` fails when
  both cores have a slot parallel to `e₀` (`not_loopMerge_digon`).  There the loop presenter must
  come from the *third* resolution `c''` of the merged vertex: `loopPresented_of_move` supplies
  `LoopPresented` from a move `c → c''` and a `FacetDatum c c'' … e₀ y₀ ε` **at the same `y₀`**
  with Lemma G.  Such a datum is not constructed here, so `metricCensus_clause_of_presented`
  carries `LoopPresented` as a hypothesis.  `ValencyThreeDigon.exists_facetDatum_v3Clause_of_step`
  chooses `y₀` generic for all four cores at once and proves the clause at every valency-three
  limit of every step.
* **`V3Limit m`** (the dispatch hypothesis), `3 ≤ degree`, `3 ≤ n`, `FacetGeneric`: as in
  `ValencyThreeCensus`.  The dispatch is `CensusAssembly.valency_trichotomy` (every metric facet
  limit is exactly one of `V2Limit`, `V3Limit`, `V4Limit`).
* Uniqueness on the far side of `cat_step` at **coarse** facet limits, for odd classes, is not
  proved here; only its metric refinement in census form (`metricCensus_clause_cat`) is, and no
  coarse-from-metric upgrade is attempted.  The consumer
  `FacetCensus.cat_obligation_of_metricCensus` takes the metric form, and
  `cat_obligation_of_forall_v3` feeds it (under `V3Limit` at every metric limit).
* Valency-two and valency-four limits are not treated here.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.

## Non-vacuity

`LoopMerge` holds at `cat_step` on both sides although the far core fails `NoParallel`
(`loopMerge_cat`); it fails on both sides at `digonMove` (`not_loopMerge_digon`), so it is
neither vacuous nor automatic.  `LoopPresented` is inhabited at `cat_step` through
`loopPresented_of_move`/`loopPresented_far` (used by `metricCensus_clause_cat`).
-/

namespace DraismaVargas.Count.ValencyThreeLoopMerge

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification W4StableSource
open FullDimensionalSource
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyThreeSplit
open ValencyThreeCoreSlots
open DraismaVargas.Count.RowWalk (OnRow)

/-! ## 1.  The loop side: the two survivors of a core loop at an end of `e₀` -/

section LoopSide

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
variable {w : Regrowth core y degree}
  {block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks}

/-- The branch vertex of a core loop at an end of `e₀` is one of the anchor frame's two
branch constituents. -/
theorem loopBranch_mem (Fr : RegrowthFrame w block) {e₀ : Fin p} (hy : y e₀ = 0)
    {f : Fin p}
    (hend : core.tail f = core.tail e₀ ∨ core.tail f = core.head e₀) :
    (w.frame.ident.vertex.symm (core.tail f)).1 = Fr.R ∨
      (w.frame.ident.vertex.symm (core.tail f)).1 = Fr.Y := by
  have hR := vertexOf_end Fr w.frame.ident (row_e₁ Fr hy) Fr.R (Or.inl rfl) Fr.R_nd
  have hY := vertexOf_end Fr w.frame.ident (row_e₁ Fr hy) Fr.Y (Or.inr rfl) Fr.Y_nd
  have hRY : vertexOf w.frame.ident Fr.R Fr.R_nd ≠ vertexOf w.frame.ident Fr.Y Fr.Y_nd := by
    intro h
    exact Fr.R_ne_Y (congrArg Subtype.val (w.frame.ident.vertex.injective h))
  have key : core.tail f = vertexOf w.frame.ident Fr.R Fr.R_nd ∨
      core.tail f = vertexOf w.frame.ident Fr.Y Fr.Y_nd := by
    rcases hend with h | h <;> rcases hR with hR | hR <;> rcases hY with hY | hY
    all_goals first
      | exact Or.inl (h.trans hR.symm)
      | exact Or.inr (h.trans hY.symm)
      | exact absurd (hR.trans hY.symm) hRY
  rcases key with h | h
  · left
    rw [h]
    exact congrArg Subtype.val (Equiv.symm_apply_apply w.frame.ident.vertex _)
  · right
    rw [h]
    exact congrArg Subtype.val (Equiv.symm_apply_apply w.frame.ident.vertex _)

/-- The leaf of a core loop's row, read at a regrowth's member. -/
abbrev loopLeafOf (w : Regrowth core y degree) {f : Fin p} (hLoop : core.tail f = core.head f) :
    IsLeafVertex w.frame.target (LollipopLeafRow.loopLeaf (w.frame.member y) hLoop) :=
  LollipopLeafRow.loopLeaf_isLeafVertex (w.frame.member y) hLoop

/-- The contracted occurrence is not a leaf edge: its ends have valency two and three. -/
theorem leafEdge_ne_contracted (H : RegrowthAnchor w block) {v : w.frame.target.V}
    (hLeaf : IsLeafVertex w.frame.target v) : leafEdge hLeaf ≠ w.frame.edgeOf w.column := by
  intro h
  obtain ⟨huv, hu2, hv3, -, -⟩ := H.sides w.frame.fullDim
  have hmem := leafEdge_mem hLeaf
  rw [h] at hmem
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  have hcard : (GluingDatum.incidentEdges v).card = 1 := hLeaf
  have ha : (GluingDatum.incidentEdges (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1).card ≠ 1 := by
    rcases huv with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [← h1]; omega
    · rw [← h2]; omega
  have hb : (GluingDatum.incidentEdges (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).2).card ≠ 1 := by
    rcases huv with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [← h2]; omega
    · rw [← h1]; omega
  rcases hmem with hm | hm
  · exact ha (hm ▸ hcard)
  · exact hb (hm ▸ hcard)

/-- **The loop survivors are the labels `0` and `3`**: at a regrowth over a core with a loop
slot `f` at an end of the vanishing slot, the two occurrences of `f`'s row at its branch vertex
are the lifts of the survivors `e₂`, `e₅`, and both lie over the leaf edge of the leaf the loop
row passes above (Part II `lm:bridge-and-loop`, through `PassOnceLollipopWitness`). -/
theorem loop_labels (H : RegrowthAnchor w block) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    {f : Fin p} (hLoop : core.tail f = core.head f)
    (hend : core.tail f = core.tail e₀ ∨ core.tail f = core.head e₀)
    (L : AnchorLabelling w.limit (anchorOf w block)) :
    (w.frame.ident.vertex.symm (core.tail f)).1 ∈ fib w.frame.data rfl
        (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) block ∧
      ∀ i, i = 0 ∨ i = 3 →
        OnRow w.frame.data (w.frame.ident.row.symm f) (lift L i) ∧
        (lift L i).1.1 = leafEdge (loopLeafOf w hLoop) ∧
        Incident w.frame.data (lift L i) (w.frame.ident.vertex.symm (core.tail f)).1 := by
  classical
  obtain ⟨Fr⟩ := nonempty_anchorFrame w.frame.fullDim H
  set B := (w.frame.ident.vertex.symm (core.tail f)).1 with hBdef
  have hBfib : B ∈ fib w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) block := by
    rcases loopBranch_mem Fr hpt.1 hend with h | h
    · exact hBdef ▸ h ▸ Fr.R_mem
    · exact hBdef ▸ h ▸ Fr.Y_mem
  refine ⟨hBfib, ?_⟩
  have hcount := LollipopLeafRow.incidenceCount_eq_two_of_core_loop (w.frame.member y) hLoop
  change ((StablePathCount.incidentEdges w.frame.data B).filter
    fun edge ↦ edge.stablePath = w.frame.ident.row.symm f).card = 2 at hcount
  obtain ⟨x, x', hxx', hEq⟩ := Finset.card_eq_two.mp hcount
  have hx : x ∈ (StablePathCount.incidentEdges w.frame.data B).filter
      fun edge ↦ edge.stablePath = w.frame.ident.row.symm f := by rw [hEq]; simp
  have hx' : x' ∈ (StablePathCount.incidentEdges w.frame.data B).filter
      fun edge ↦ edge.stablePath = w.frame.ident.row.symm f := by rw [hEq]; simp
  rw [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hx hx'
  have hT : ∀ z : NonDanglingEdge w.frame.data, Incident w.frame.data z.1 B →
      z.stablePath = w.frame.ident.row.symm f → z.1.1.1 = leafEdge (loopLeafOf w hLoop) :=
    fun z hInc hRow ↦ PassOnceLollipopWitness.loopRowLengthTwo (w.frame.member y) hLoop z.1
      ⟨z.2, hRow⟩ hInc
  have hLift : ∀ z : NonDanglingEdge w.frame.data, Incident w.frame.data z.1 B →
      z.stablePath = w.frame.ident.row.symm f → ∃ i, lift L i = z.1 := by
    intro z hInc hRow
    refine exists_lift_eq L H.compat H.nd4 hBfib ((mem_bdAt _ _ _).mpr ⟨?_, ?_⟩)
    · exact (mem_ndAt _ _ _).mpr ⟨z.2, hInc⟩
    · rw [hT z hInc hRow]
      exact leafEdge_ne_contracted H (loopLeafOf w hLoop)
  obtain ⟨i, hi⟩ := hLift x hx.1 hx.2
  obtain ⟨i', hi'⟩ := hLift x' hx'.1 hx'.2
  have hii' : i ≠ i' := by
    intro h
    subst h
    exact hxx' (Subtype.ext (hi.symm.trans hi'))
  have htarget : (L.e i).1.1 = (L.e i').1.1 := by
    refine (lift_target_eq_iff L i i').mp ?_
    rw [hi, hi', hT x hx.1 hx.2, hT x' hx'.1 hx'.2]
  have hpair := label_pair_of_target_eq L hii' htarget
  have key : ∀ j, (j = i ∨ j = i') → OnRow w.frame.data (w.frame.ident.row.symm f) (lift L j) ∧
      (lift L j).1.1 = leafEdge (loopLeafOf w hLoop) ∧ Incident w.frame.data (lift L j) B := by
    rintro j (rfl | rfl)
    · rw [hi]; exact ⟨⟨x.2, hx.2⟩, hT x hx.1 hx.2, hx.1⟩
    · rw [hi']; exact ⟨⟨x'.2, hx'.2⟩, hT x' hx'.1 hx'.2, hx'.1⟩
  intro j hj
  apply key
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hj with rfl | rfl <;> simp

/-- A sheet whose block has one element is its own representative. -/
theorem repr_eq_of_blockCard {d : ℕ} (P : SheetPartition d) (k : Fin d)
    (h : P.blockCard (P.repr k) = 1) : P.repr k = k := by
  have hb : P.blockCard k = 1 := by
    rw [SheetPartition.blockCard, P.block_eq_of_rel (P.rel_repr_right k)]; exact h
  have hk := P.block_eq_singleton_of_blockCard_eq_one k hb
  have hmem : P.repr k ∈ P.block k := (P.mem_block_iff k _).mpr (P.rel_repr_right k)
  rw [hk] at hmem
  exact Finset.mem_singleton.mp hmem

/-- **The label-moving automorphism on the loop side** (`ValencyThreeSplit.swapIso` over the leaf edge):
at a regrowth over a core with a loop slot at an end of the vanishing slot, the sheet swap of the
two loop survivors over the leaf edge is a geometric automorphism of the limit fixing every
target occurrence, exchanging `e₂` and `e₅` and fixing `e₃`, `e₄`. -/
theorem exists_loopSwap (H : RegrowthAnchor w block) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) {f : Fin p} (hLoop : core.tail f = core.head f)
    (hend : core.tail f = core.tail e₀ ∨ core.tail f = core.head e₀)
    (L : AnchorLabelling w.limit (anchorOf w block)) :
    ∃ σ : GeometricDatumIso w.limit w.limit, (∀ e, σ.targetEdge e = e) ∧
      σ.sourceEdgeEquiv (L.e 0) = L.e 3 ∧ σ.sourceEdgeEquiv (L.e 3) = L.e 0 ∧
      σ.sourceEdgeEquiv (L.e 1) = L.e 1 ∧ σ.sourceEdgeEquiv (L.e 2) = L.e 2 := by
  classical
  obtain ⟨hBfib, hlab⟩ := loop_labels H hpt hLoop hend L
  obtain ⟨hRow0, hT0, hI0⟩ := hlab 0 (Or.inl rfl)
  obtain ⟨hRow3, hT3, hI3⟩ := hlab 3 (Or.inr rfl)
  set hLeaf := loopLeafOf w hLoop
  set t₂ := (L.e 0).1.1 with ht₂
  have h30 : (L.e 3).1.1 = t₂ := L.dir25.symm
  -- the leaf edge is discrete in the incoming datum
  have hdiscIn : ∀ k, (w.frame.data.edgePartition (leafEdge hLeaf)).repr k = k := by
    intro k
    apply repr_eq_of_blockCard
    have := LeafFibre.sourceEdgeIndex_eq_one_above_leaf w.frame.fullDim hLeaf
      (edge := ⟨(leafEdge hLeaf, (w.frame.data.edgePartition (leafEdge hLeaf)).repr k),
        (w.frame.data.edgePartition (leafEdge hLeaf)).repr_idem k⟩) rfl
    exact this
  have hdisc : ∀ k, (w.limit.edgePartition t₂).repr k = k := by
    intro k
    have h := ValencyThreeResolutionMatch.label_edgePartition L 0
    change w.limit.edgePartition t₂ = _ at h
    rw [h, hT0]
    exact hdiscIn k
  -- the two sheets are related at both ends of the leaf edge
  set s₀ := (L.e 0).1.2
  set s₃ := (L.e 3).1.2
  have hs₀ : s₀ = (lift L 0).1.2 := ValencyThreeResolutionMatch.label_sheet L 0
  have hs₃ : s₃ = (lift L 3).1.2 := ValencyThreeResolutionMatch.label_sheet L 3
  obtain ⟨hTB, hRB0⟩ := (incident_iff_target_mem_and_rel w.frame.data _ _).mp hI0
  obtain ⟨-, hRB3⟩ := (incident_iff_target_mem_and_rel w.frame.data _ _).mp hI3
  have hC0 := (incident_iff_target_mem_and_rel w.frame.data _ _).mp
    (LeafFibre.incident_coreVertex_of_mem_leafSurvivors w.frame.fullDim hLeaf
      ((LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hRow0.survives, hT0⟩))
  have hC3 := (incident_iff_target_mem_and_rel w.frame.data _ _).mp
    (LeafFibre.incident_coreVertex_of_mem_leafSurvivors w.frame.fullDim hLeaf
      ((LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨hRow3.survives, hT3⟩))
  rw [hT0] at hTB
  have hBne : (w.frame.ident.vertex.symm (core.tail f)).1.1.1 ≠
      LollipopLeafRow.loopLeaf (w.frame.member y) hLoop := by
    intro h
    obtain ⟨huv, hu2, hv3, -, -⟩ := H.sides w.frame.fullDim
    have hcard : (GluingDatum.incidentEdges (w.frame.ident.vertex.symm (core.tail f)).1.1.1).card
        = 1 := by rw [h]; exact hLeaf
    rcases ((mem_fib_iff _ _ _ _ _ _).mp hBfib).1 with ha | ha <;> rw [ha] at hcard <;>
      rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    all_goals first
      | (rw [← h1] at hcard; omega)
      | (rw [← h2] at hcard; omega)
  have hInRel : ∀ x, ((leafEdge hLeaf : w.frame.target.V × w.frame.target.V).1 = x ∨
      (leafEdge hLeaf : w.frame.target.V × w.frame.target.V).2 = x) →
      (w.frame.data.vertexPartition x).Rel s₀ s₃ := by
    intro x hx
    have hℓ := leafEdge_mem hLeaf
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ hTB
    have hne := fst_ne_snd (leafEdge hLeaf)
    have hxcase : x = LollipopLeafRow.loopLeaf (w.frame.member y) hLoop ∨
        x = (w.frame.ident.vertex.symm (core.tail f)).1.1.1 := by
      rcases hx with hx | hx <;> rcases hℓ with hℓ | hℓ <;> rcases hTB with hb | hb
      all_goals first
        | exact Or.inl (hx.symm.trans hℓ)
        | exact Or.inr (hx.symm.trans hb)
        | exact absurd (hℓ.symm.trans hb).symm hBne
    rcases hxcase with rfl | rfl
    · rw [hs₀, hs₃]; exact hC0.2.symm.trans hC3.2
    · rw [hs₀, hs₃]; exact hRB0.symm.trans hRB3
  have hunfold : unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) t₂ = leafEdge hLeaf :=
    (ValencyThreeResolutionMatch.label_unfold L 0).trans hT0
  have hrel : ∀ v, ((t₂ : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1
      = v ∨ (t₂ : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 = v) →
      (w.limit.vertexPartition v).Rel s₀ s₃ := by
    intro v hv
    have hends := fold_unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) t₂
    rw [hunfold] at hends
    rcases hv with hv | hv
    · have h1 := (congrArg Prod.fst hends).trans hv
      rw [← h1]
      exact (vertexPartition_refines w.frame.data _ _).rel (hInRel _ (Or.inl rfl))
    · have h1 := (congrArg Prod.snd hends).trans hv
      rw [← h1]
      exact (vertexPartition_refines w.frame.data _ _).rel (hInRel _ (Or.inr rfl))
  refine ⟨swapIso w.limit t₂ s₀ s₃ hdisc hrel, fun _ ↦ rfl, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (t₂, (if t₂ = t₂ then Equiv.swap s₀ s₃ else Equiv.refl _) s₀) = (L.e 3).1
    rw [ite_eq_left rfl, Equiv.swap_apply_left]
    exact Prod.ext h30.symm rfl
  · apply Subtype.ext
    change ((L.e 3).1.1, (if (L.e 3).1.1 = t₂ then Equiv.swap s₀ s₃ else Equiv.refl _) s₃) =
      (L.e 0).1
    rw [ite_eq_left h30, Equiv.swap_apply_right]
    exact Prod.ext h30 rfl
  · apply Subtype.ext
    change ((L.e 1).1.1, (if (L.e 1).1.1 = t₂ then Equiv.swap s₀ s₃ else Equiv.refl _)
      (L.e 1).1.2) = (L.e 1).1
    rw [ite_eq_right L.dir3]
    rfl
  · apply Subtype.ext
    change ((L.e 2).1.1, (if (L.e 2).1.1 = t₂ then Equiv.swap s₀ s₃ else Equiv.refl _)
      (L.e 2).1.2) = (L.e 2).1
    rw [ite_eq_right L.dir4]
    rfl

/-- The limit stable path of a labelled survivor. -/
noncomputable def lpath {T : CFGraph} {D : GluingDatum T degree} {A : D.SourceVertex}
    (L : AnchorLabelling D A) (i : Fin 4) : StablePath D :=
  NonDanglingEdge.stablePath (⟨L.e i, ((mem_ndAt _ _ _).mp (L.mem i)).1⟩ : NonDanglingEdge D)

/-- **On the loop side, `e₂` and `e₅` lie on one limit stable path (the loop) and `e₃`, `e₄` do
not.**  The loop row has exactly two occurrences (`card_rowEdges_eq_two_of_loopRow`). -/
theorem loop_lpaths (H : RegrowthAnchor w block) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) {f : Fin p} (hLoop : core.tail f = core.head f)
    (hend : core.tail f = core.tail e₀ ∨ core.tail f = core.head e₀)
    (L : AnchorLabelling w.limit (anchorOf w block)) :
    lpath L 0 = lpath L 3 ∧ lpath L 1 ≠ lpath L 0 ∧ lpath L 2 ≠ lpath L 0 := by
  classical
  obtain ⟨-, hlab⟩ := loop_labels H hpt hLoop hend L
  obtain ⟨⟨h0s, h0⟩, -, -⟩ := hlab 0 (Or.inl rfl)
  obtain ⟨⟨h3s, h3⟩, -, -⟩ := hlab 3 (Or.inr rfl)
  have W := WallRows.ofAnchor H
  have hin : ∀ i, inRow W (lpath L i) = pathOf H.compat L i := fun i ↦ rfl
  have hinj := StablePathFacetContraction.incomingRow_injective w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) W.compat W.forest
    W.noReturn
  have hp0 : pathOf H.compat L 0 = w.frame.ident.row.symm f := h0
  have hp3 : pathOf H.compat L 3 = w.frame.ident.row.symm f := h3
  have h03 : lpath L 0 = lpath L 3 := hinj ((hin 0).trans (hp0.trans (hp3.symm.trans (hin 3).symm)))
  -- a third occurrence on the loop row is impossible
  have hcard := PassOnceLollipopWitness.card_rowEdges_eq_two_of_loopRow w.frame.fullDim
    (LollipopDivalent.three_le_loopBranch (w.frame.member y) hLoop)
    (LollipopLeafRow.incidenceCount_eq_two_of_core_loop (w.frame.member y) hLoop)
    (loopLeafOf w hLoop) (LollipopLeafRow.leafRow_loopLeaf (w.frame.member y) hLoop)
  have hnot : ∀ k, k ≠ 0 → k ≠ 3 → lpath L k ≠ lpath L 0 := by
    intro k hk0 hk3 hk
    have hpk : pathOf H.compat L k = w.frame.ident.row.symm f := by
      rw [← hin k, hk, hin 0, hp0]
    have hmem : ∀ j, pathOf H.compat L j = w.frame.ident.row.symm f →
        lift L j ∈ EdgeDenominator.rowEdges w.frame.fullDim.labelling
          (w.frame.fullDim.labelling.row (w.frame.ident.row.symm f)) := by
      intro j hj
      exact (EdgeDenominator.mem_rowEdges _ _ _).mpr ⟨lift_survives H.compat L j, by
        rw [← hj]; rfl⟩
    have hsub : ({lift L 0, lift L 3, lift L k} : Finset w.frame.data.SourceEdge) ⊆
        EdgeDenominator.rowEdges w.frame.fullDim.labelling
          (w.frame.fullDim.labelling.row (w.frame.ident.row.symm f)) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact hmem 0 hp0
      · exact hmem 3 hp3
      · exact hmem k hpk
    have h3card : ({lift L 0, lift L 3, lift L k} : Finset w.frame.data.SourceEdge).card = 3 := by
      have i03 : lift L 0 ≠ lift L 3 := fun h ↦ absurd (lift_injective L h) (by decide)
      have i0k : lift L 0 ≠ lift L k := fun h ↦ hk0 (lift_injective L h).symm
      have i3k : lift L 3 ≠ lift L k := fun h ↦ hk3 (lift_injective L h).symm
      rw [Finset.card_insert_of_notMem (by simp [i03, i0k]),
        Finset.card_pair i3k]
    have := Finset.card_le_card hsub
    have hcard' : (EdgeDenominator.rowEdges w.frame.fullDim.labelling
        (w.frame.fullDim.labelling.row (w.frame.ident.row.symm f))).card = 2 := hcard
    omega
  exact ⟨h03, hnot 1 (by decide) (by decide), hnot 2 (by decide) (by decide)⟩

end LoopSide

/-! ## 2.  Carrying the loop side across a limit isomorphism -/

section Transport

variable {n p degree : ℕ} {c cL : Core n p} {y : Fin p → ℚ}

/-- The limit path of a transported label is the transported limit path. -/
theorem lpath_transport {T₁ T₂ : CFGraph} {D₁ : GluingDatum T₁ degree} {D₂ : GluingDatum T₂ degree}
    {A₁ : D₁.SourceVertex} {A₂ : D₂.SourceVertex} (χ : GeometricDatumIso D₁ D₂)
    (hConn : D₁.Connected) (L₁ : AnchorLabelling D₁ A₁) (L₂ : AnchorLabelling D₂ A₂)
    (hL : ∀ i, L₂.e i = χ.sourceEdgeEquiv (L₁.e i)) (i : Fin 4) :
    lpath L₂ i = χ.stablePathEquiv hConn (lpath L₁ i) := by
  unfold lpath
  refine Eq.trans ?_ (GeometricDatumIso.stablePathEquiv_mk χ hConn _).symm
  exact congrArg NonDanglingEdge.stablePath (Subtype.ext (hL i))

/-- **The loop data at any regrowth whose limit is isomorphic to a loop-side regrowth's.**  For
every labelling of the limit: `e₂`, `e₅` share a limit stable path which `e₃`, `e₄` avoid, and
there is a geometric automorphism of the limit, fixing every target occurrence, exchanging `e₂`
and `e₅` and fixing `e₃`, `e₄` (the loop side's sheet swap, conjugated by the isomorphism). -/
theorem loopData_of_limitIso {w : Regrowth c y degree} {wL : Regrowth cL y degree}
    {block blockL} (H : RegrowthAnchor w block) (HL : RegrowthAnchor wL blockL) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) {f : Fin p} (hLoop : cL.tail f = cL.head f)
    (hend : cL.tail f = cL.tail e₀ ∨ cL.tail f = cL.head e₀)
    (χ : GeometricDatumIso w.limit wL.limit) (L : AnchorLabelling w.limit (anchorOf w block)) :
    (lpath L 0 = lpath L 3 ∧ lpath L 1 ≠ lpath L 0 ∧ lpath L 2 ≠ lpath L 0) ∧
      ∃ σ : GeometricDatumIso w.limit w.limit, (∀ e, σ.targetEdge e = e) ∧
        σ.sourceEdgeEquiv (L.e 0) = L.e 3 ∧ σ.sourceEdgeEquiv (L.e 3) = L.e 0 ∧
        σ.sourceEdgeEquiv (L.e 1) = L.e 1 ∧ σ.sourceEdgeEquiv (L.e 2) = L.e 2 := by
  have hψ := sourceVertexEquiv_limA w wL H HL χ
  obtain ⟨LL, hLL⟩ := exists_transport χ hψ (connected_limit w) L
  have htr := lpath_transport χ (connected_limit w) L LL hLL
  obtain ⟨h03, h10, h20⟩ := loop_lpaths HL hpt hLoop hend LL
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · apply (χ.stablePathEquiv (connected_limit w)).injective
    rw [← htr, ← htr]; exact h03
  · intro h
    apply h10
    rw [htr, htr, h]
  · intro h
    apply h20
    rw [htr, htr, h]
  · obtain ⟨σ, hσT, h0, h3, h1, h2⟩ := exists_loopSwap HL hpt hLoop hend LL
    have hback : ∀ i j, σ.sourceEdgeEquiv (LL.e i) = LL.e j →
        (χ.trans (σ.trans χ.symm)).sourceEdgeEquiv (L.e i) = L.e j := by
      intro i j hij
      change χ.symm.sourceEdgeEquiv (σ.sourceEdgeEquiv (χ.sourceEdgeEquiv (L.e i))) = L.e j
      have e1 : χ.sourceEdgeEquiv (L.e i) = LL.e i := (hLL i).symm
      have e2 : σ.sourceEdgeEquiv (LL.e i) = χ.sourceEdgeEquiv (L.e j) := hij.trans (hLL j)
      erw [e1, e2]
      exact StarCensusEngine.symm_sourceEdgeEquiv_apply χ (L.e j)
    refine ⟨χ.trans (σ.trans χ.symm), fun e ↦ ?_, hback 0 3 h0, hback 3 0 h3, hback 1 1 h1,
      hback 2 2 h2⟩
    change χ.targetEdge.symm (σ.targetEdge (χ.targetEdge e)) = e
    rw [hσT, Equiv.symm_apply_apply]

end Transport

/-! ## 3.  Cubic cores: at most one slot parallel to `e₀`, and no loop beside one -/

section CubicCore

variable {n p : ℕ} {core : Core n p}

theorem sum_coreIncidence (hcub : core.Cubic) (v : Fin n) :
    ∑ t, coreIncidence core v t = 3 := hcub v

theorem sum_le_three (hcub : core.Cubic) (v : Fin n) (S : Finset (Fin p)) :
    ∑ t ∈ S, coreIncidence core v t ≤ 3 := by
  rw [← sum_coreIncidence hcub v]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ ↦ Nat.zero_le _)

theorem coreIncidence_tail_pos (e : Fin p) : 0 < coreIncidence core (core.tail e) e := by
  unfold coreIncidence; simp

theorem coreIncidence_head_pos (e : Fin p) : 0 < coreIncidence core (core.head e) e := by
  unfold coreIncidence; split_ifs <;> simp_all

/-- Three distinct slots at one vertex exhaust it: none of them has a second incidence there,
and no other slot meets it. -/
theorem three_slots (hcub : core.Cubic) (v : Fin n) {t₁ t₂ t₃ : Fin p} (h12 : t₁ ≠ t₂)
    (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) (h1 : 0 < coreIncidence core v t₁)
    (h2 : 0 < coreIncidence core v t₂) (h3 : 0 < coreIncidence core v t₃) :
    coreIncidence core v t₁ = 1 ∧ coreIncidence core v t₂ = 1 ∧ coreIncidence core v t₃ = 1 ∧
      ∀ t, t ≠ t₁ → t ≠ t₂ → t ≠ t₃ → coreIncidence core v t = 0 := by
  classical
  have hS := sum_le_three hcub v {t₁, t₂, t₃}
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23] at hS
  refine ⟨by omega, by omega, by omega, fun t ht1 ht2 ht3 ↦ ?_⟩
  have hS' := sum_le_three hcub v {t, t₁, t₂, t₃}
  rw [Finset.sum_insert (by simp [ht1, ht2, ht3]), Finset.sum_insert (by simp [h12, h13]),
    Finset.sum_pair h23] at hS'
  omega

/-- A slot is **parallel** to `e₀` when it is another slot meeting both ends of `e₀`. -/
def Parallel (core : Core n p) (e₀ s : Fin p) : Prop :=
  s ≠ e₀ ∧ 0 < coreIncidence core (core.tail e₀) s ∧ 0 < coreIncidence core (core.head e₀) s

/-- **A connected cubic core with at least three vertices has at most one slot parallel to a
non-loop slot.** -/
theorem parallel_unique (hcub : core.Cubic) (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (he₀ : core.tail e₀ ≠ core.head e₀) {s s' : Fin p} (hs : Parallel core e₀ s)
    (hs' : Parallel core e₀ s') : s = s' := by
  by_contra hne
  have hU := three_slots hcub (core.tail e₀) (Ne.symm hs.1) (Ne.symm hs'.1) hne
    (coreIncidence_tail_pos e₀) hs.2.1 hs'.2.1
  have hV := three_slots hcub (core.head e₀) (Ne.symm hs.1) (Ne.symm hs'.1) hne
    (coreIncidence_head_pos e₀) hs.2.2 hs'.2.2
  apply he₀
  apply ValencyThreeRigidity.eq_of_coreIncidence_eq hconn hn
  intro t
  by_cases h1 : t = e₀
  · rw [h1, hU.1, hV.1]
  by_cases h2 : t = s
  · rw [h2, hU.2.1, hV.2.1]
  by_cases h3 : t = s'
  · rw [h3, hU.2.2.1, hV.2.2.1]
  rw [hU.2.2.2 t h1 h2 h3, hV.2.2.2 t h1 h2 h3]

/-- **Beside a parallel slot, no slot has two incidences at an end of `e₀`.** -/
theorem incidence_lt_two_of_parallel (hcub : core.Cubic) {e₀ s₁ s : Fin p}
    (hs₁ : Parallel core e₀ s₁) (hs : s ≠ e₀) (hss : s ≠ s₁) {x : Fin n}
    (hx : x = core.tail e₀ ∨ x = core.head e₀) : coreIncidence core x s < 2 := by
  classical
  have h0 : 0 < coreIncidence core x e₀ := by
    rcases hx with rfl | rfl
    · exact coreIncidence_tail_pos e₀
    · exact coreIncidence_head_pos e₀
  have h1 : 0 < coreIncidence core x s₁ := by
    rcases hx with rfl | rfl
    · exact hs₁.2.1
    · exact hs₁.2.2
  have hS := sum_le_three hcub x {e₀, s, s₁}
  rw [Finset.sum_insert (by simp [Ne.symm hs, Ne.symm hs₁.1]), Finset.sum_pair hss] at hS
  omega

end CubicCore

/-! ## 4.  The pairing is "same home", and it is a perfect matching of the labels -/

section Homes

variable {target : CFGraph.{0}} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (Fr : AnchorFrame data hc hab hOne block)
  (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- An occurrence meeting three source vertices meets two of them twice over. -/
theorem eq_of_three_incident {e : data.SourceEdge} {X Y Z : data.SourceVertex}
    (hX : Incident data e X) (hY : Incident data e Y) (hZ : Incident data e Z) (hXZ : X ≠ Z)
    (hYZ : Y ≠ Z) : X = Y := by
  unfold Incident at hX hY hZ
  rcases hX with hX | hX <;> rcases hY with hY | hY <;> rcases hZ with hZ | hZ
  all_goals first
    | exact hX.symm.trans hY
    | exact absurd (hX.symm.trans hZ) hXZ
    | exact absurd (hY.symm.trans hZ) hYZ

theorem mem_fib_of_R_or_Y {B : data.SourceVertex} (hB : B = Fr.R ∨ B = Fr.Y) :
    B ∈ fib data hc hab hOne block := by
  rcases hB with rfl | rfl
  · exact Fr.R_mem
  · exact Fr.Y_mem

/-- **Homes are unique.** -/
theorem homed_unique {i : Fin 4} {B B' : data.SourceVertex} (hB : B = Fr.R ∨ B = Fr.Y)
    (hB' : B' = Fr.R ∨ B' = Fr.Y) (h : Homed L i B) (h' : Homed L i B') : B = B' := by
  classical
  have hBm := mem_fib_of_R_or_Y Fr hB
  have hB'm := mem_fib_of_R_or_Y Fr hB'
  have h3 := nd_of_R_or_Y Fr hB
  have h3' := nd_of_R_or_Y Fr hB'
  have hhome : ∀ {X X' : data.SourceVertex}, X ∈ fib data hc hab hOne block →
      X' ∈ fib data hc hab hOne block → lift L i ∈ ndAt data X → lift L i ∈ ndAt data X' →
      X = X' := fun hX hX' hi hi' ↦ home_unique (lift_ne L i) hX hX'
        ((mem_ndAt data _ _).mp hi).2 ((mem_ndAt data _ _).mp hi').2
  rcases h with h | ⟨Z, hZ, hZ2, hiZ, e, he, heZ, heB⟩ <;>
    rcases h' with h' | ⟨Z', hZ', hZ2', hiZ', e', he', heZ', heB'⟩
  · exact hhome hBm hB'm h h'
  · have := hhome hBm hZ' h hiZ'
    subst this; omega
  · have := hhome hB'm hZ h' hiZ
    subst this; omega
  · have hZZ := hhome hZ hZ' hiZ hiZ'
    subst hZZ
    have hlne : ∀ {x : data.SourceEdge}, x ∈ intl data hc hab hOne block → lift L i ≠ x := by
      intro x hx hEq
      exact lift_ne L i (hEq ▸ (intl_ends data hc hab hOne block hx).2.2.2.2.1)
    have hee : e = e' := by
      by_contra hne
      have hsub : ({lift L i, e, e'} : Finset data.SourceEdge) ⊆ ndAt data Z := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hiZ
        · exact heZ
        · exact heZ'
      have hc3 : ({lift L i, e, e'} : Finset data.SourceEdge).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hlne he, hlne he']), Finset.card_pair hne]
      have := Finset.card_le_card hsub
      rw [card_ndAt, hZ2] at this
      omega
    subst hee
    have hZB : Z ≠ B := fun h ↦ by subst h; omega
    have hZB' : Z ≠ B' := fun h ↦ by subst h; omega
    exact eq_of_three_incident ((mem_ndAt data _ _).mp heB).2 ((mem_ndAt data _ _).mp heB').2
      ((mem_ndAt data _ _).mp heZ).2 (Ne.symm hZB) (Ne.symm hZB')

/-- Paired labels share their (unique) home. -/
theorem home_eq_of_paired (fd : FullDimensionalSourcePresentation data coordinate) {i j : Fin 4}
    (h : Paired L i j) {B B' : data.SourceVertex} (hB : B = Fr.R ∨ B = Fr.Y)
    (hB' : B' = Fr.R ∨ B' = Fr.Y) (hi : Homed L i B) (hj : Homed L j B') : B = B' := by
  obtain ⟨C, hC, hiC, hjC⟩ := homed_of_paired fd Fr L h
  exact (homed_unique Fr L hB hC hi hiC).trans (homed_unique Fr L hC hB' hjC hj)

/-- Two of `R`, `Y` different from a third are equal. -/
theorem eq_of_ne_of_ne {B₁ B₂ B₀ : data.SourceVertex} (h1 : B₁ = Fr.R ∨ B₁ = Fr.Y)
    (h2 : B₂ = Fr.R ∨ B₂ = Fr.Y) (h0 : B₀ = Fr.R ∨ B₀ = Fr.Y) (h10 : B₁ ≠ B₀) (h20 : B₂ ≠ B₀) :
    B₁ = B₂ := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h0 with rfl | rfl <;>
    first | rfl | exact absurd rfl h10 | exact absurd rfl h20

open ValencyThreeGeneral.Split7 in
include Fr in
/-- **The complementary pair is paired**: the two labels other than `e₂` and its type partner
share a home. -/
theorem paired_compl (fd : FullDimensionalSourcePresentation data coordinate)
    (H : AnchorInput data hc hab hOne block) {s : Split} (hs : Reads L (divEnd a b) s)
    {j k : Fin 4} (hj0 : j ≠ 0) (hk0 : k ≠ 0) (hjt : j ≠ typePartner s.type)
    (hkt : k ≠ typePartner s.type) : Paired L j k := by
  obtain ⟨B₀, hB₀, h0⟩ := exists_homed fd Fr L H.compat 0
  obtain ⟨Bj, hBj, hj⟩ := exists_homed fd Fr L H.compat j
  obtain ⟨Bk, hBk, hk⟩ := exists_homed fd Fr L H.compat k
  have hne : ∀ {m : Fin 4} {Bm : data.SourceVertex}, m ≠ 0 → m ≠ typePartner s.type →
      (Bm = Fr.R ∨ Bm = Fr.Y) → Homed L m Bm → Bm ≠ B₀ := by
    intro m Bm hm0 hmt hBm hm hEq
    subst hEq
    exact hmt ((paired_iff fd H L hs m hm0).mp (paired_of_homed Fr L hBm h0 hm))
  have := eq_of_ne_of_ne Fr hBj hBk hB₀ (hne hj0 hjt hBj hj) (hne hk0 hkt hBk hk)
  subst this
  exact paired_of_homed Fr L hBj hj hk

open ValencyThreeGeneral.Split7 in
include Fr in
/-- **Type III is the pairing of `e₃` with `e₄`.** -/
theorem paired12_iff (fd : FullDimensionalSourcePresentation data coordinate)
    (H : AnchorInput data hc hab hOne block) {s : Split} (hs : Reads L (divEnd a b) s) :
    Paired L 1 2 ↔ s.type = VType.III := by
  constructor
  · intro h12
    by_contra hIII
    have htp : typePartner s.type = 1 ∨ typePartner s.type = 2 := by
      cases ht : s.type
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd ht hIII
    obtain ⟨B₀, hB₀, h0⟩ := exists_homed fd Fr L H.compat 0
    obtain ⟨B₁, hB₁, h1⟩ := exists_homed fd Fr L H.compat 1
    obtain ⟨B₂, hB₂, h2⟩ := exists_homed fd Fr L H.compat 2
    have h12' := home_eq_of_paired Fr L fd h12 hB₁ hB₂ h1 h2
    rcases htp with ht | ht
    · have hp := (paired_iff fd H L hs 1 (by decide)).mpr ht.symm
      have h01 := home_eq_of_paired Fr L fd hp hB₀ hB₁ h0 h1
      have hp2 := paired_of_homed Fr L hB₀ h0 (h01 ▸ h12' ▸ h2)
      have := (paired_iff fd H L hs 2 (by decide)).mp hp2
      rw [ht] at this; exact absurd this (by decide)
    · have hp := (paired_iff fd H L hs 2 (by decide)).mpr ht.symm
      have h02 := home_eq_of_paired Fr L fd hp hB₀ hB₂ h0 h2
      have hp1 := paired_of_homed Fr L hB₀ h0 (h02 ▸ h12'.symm ▸ h1)
      have := (paired_iff fd H L hs 1 (by decide)).mp hp1
      rw [ht] at this; exact absurd this (by decide)
  · intro hIII
    have ht : typePartner s.type = 3 := by rw [hIII]; rfl
    exact paired_compl Fr L fd H hs (by decide) (by decide) (by rw [ht]; decide)
      (by rw [ht]; decide)

end Homes

/-! ### Relabelling: the transposition of `e₂` and `e₅` exchanges Types I and II -/

section Relabel

variable {target : CFGraph.{0}} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

theorem paired_symm {L : AnchorLabelling (contractDatum data hc hab hOne)
    (limA data hc hab hOne block)} {i j : Fin 4} (h : Paired L i j) : Paired L j i := by
  obtain ⟨X, hX, X', hX', hi, hj, hjoin⟩ := h
  refine ⟨X', hX', X, hX, hj, hi, ?_⟩
  rcases hjoin with rfl | ⟨e, he, h1, h2, h3⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨e, he, h2, h1, h3.symm⟩

/-- Relabelling the survivors relabels the pairing. -/
theorem paired_relabel {L L₂ : AnchorLabelling (contractDatum data hc hab hOne)
    (limA data hc hab hOne block)} (π : Fin 4 → Fin 4) (hπ : ∀ i, L₂.e i = L.e (π i))
    (i j : Fin 4) : Paired L₂ i j ↔ Paired L (π i) (π j) := by
  have hl : ∀ k, lift L₂ k = lift L (π k) := fun k ↦ by unfold lift; rw [hπ k]
  unfold Paired
  rw [hl i, hl j]

/-- The transposition of `e₂` and `e₅`. -/
def swap03 : Fin 4 → Fin 4 := fun i ↦ if i = 0 then 3 else if i = 3 then 0 else i

open ValencyThreeGeneral.Split7 in
/-- **Exchanging `e₂` and `e₅` in the labelling exchanges Types I and II.** -/
theorem type_swap03 (fd : FullDimensionalSourcePresentation data coordinate)
    (H : AnchorInput data hc hab hOne block)
    {L L₂ : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block)}
    (hπ : ∀ i, L₂.e i = L.e (swap03 i)) {s s₂ : Split} (hs : Reads L (divEnd a b) s)
    (hs₂ : Reads L₂ (divEnd a b) s₂) (hI : s.type ≠ VType.III) : s₂.type ≠ s.type := by
  obtain ⟨Fr⟩ := nonempty_anchorFrame fd H
  have htp : typePartner s.type = 1 ∨ typePartner s.type = 2 := by
    cases ht : s.type
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd ht hI
  intro heq
  rcases htp with ht | ht
  · -- type I: `e₄ ~ e₅`, so after the swap `e₂ ~ e₄`
    have h23 := paired_compl Fr L fd H hs (j := 2) (k := 3) (by decide) (by decide)
      (by rw [ht]; decide) (by rw [ht]; decide)
    have h02 : Paired L₂ 0 2 := (paired_relabel swap03 hπ 0 2).mpr (paired_symm h23)
    have := (paired_iff fd H L₂ hs₂ 2 (by decide)).mp h02
    rw [heq, ht] at this
    exact absurd this (by decide)
  · have h13 := paired_compl Fr L fd H hs (j := 1) (k := 3) (by decide) (by decide)
      (by rw [ht]; decide) (by rw [ht]; decide)
    have h01 : Paired L₂ 0 1 := (paired_relabel swap03 hπ 0 1).mpr (paired_symm h13)
    have := (paired_iff fd H L₂ hs₂ 1 (by decide)).mp h01
    rw [heq, ht] at this
    exact absurd this (by decide)

end Relabel

/-! ## 5.  The core reading, one slot at a time -/

section SlotReading

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
variable {w : Regrowth core y degree}
  {block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks}

/-- A slot meets **at most one** end of `e₀`. -/
def NonPar (core : Core n p) (e₀ s : Fin p) : Prop :=
  coreIncidence core (core.tail e₀) s = 0 ∨ coreIncidence core (core.head e₀) s = 0

theorem eq_of_nonPar {e₀ s : Fin p} (h : NonPar core e₀ s) {x x' : Fin n}
    (hx : x = core.tail e₀ ∨ x = core.head e₀) (hx' : x' = core.tail e₀ ∨ x' = core.head e₀)
    (h1 : 0 < coreIncidence core x s) (h2 : 0 < coreIncidence core x' s) : x = x' := by
  rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
  · rfl
  · rcases h with h0 | h0 <;> omega
  · rcases h with h0 | h0 <;> omega
  · rfl

/-- The core slot of a labelled survivor at a regrowth. -/
noncomputable abbrev slotOf (H : RegrowthAnchor w block)
    (L : AnchorLabelling w.limit (anchorOf w block)) (i : Fin 4) : Fin p :=
  w.frame.ident.row (pathOf H.compat L i)

/-- **`paired_iff_coreShare` with the no-parallel hypothesis only on the two slots read.** -/
theorem paired_iff_coreShare_of (H : RegrowthAnchor w block) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (L : AnchorLabelling w.limit (anchorOf w block))
    (i j : Fin 4) (hi : NonPar core e₀ (slotOf H L i)) (hj : NonPar core e₀ (slotOf H L j)) :
    Paired L i j ↔ CoreShare core e₀ (slotOf H L i) (slotOf H L j) := by
  obtain ⟨Fr⟩ := nonempty_anchorFrame w.frame.fullDim H
  have he₁ := row_e₁ Fr hpt.1
  constructor
  · intro h
    obtain ⟨B, hB, hiB, hjB⟩ := homed_of_paired w.frame.fullDim Fr L h
    have h3 := nd_of_R_or_Y Fr hB
    refine ⟨vertexOf w.frame.ident B h3, vertexOf_end Fr w.frame.ident he₁ B hB h3, ?_, ?_⟩
    · rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed H.compat L hiB
    · rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed H.compat L hjB
  · rintro ⟨x, hx, hxi, hxj⟩
    obtain ⟨Bi, hBi, hiB⟩ := exists_homed w.frame.fullDim Fr L H.compat i
    obtain ⟨Bj, hBj, hjB⟩ := exists_homed w.frame.fullDim Fr L H.compat j
    have hi3 := nd_of_R_or_Y Fr hBi
    have hj3 := nd_of_R_or_Y Fr hBj
    have hvi : vertexOf w.frame.ident Bi hi3 = x := by
      refine eq_of_nonPar hi (vertexOf_end Fr w.frame.ident he₁ Bi hBi hi3) hx ?_ hxi
      rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed H.compat L hiB
    have hvj : vertexOf w.frame.ident Bj hj3 = x := by
      refine eq_of_nonPar hj (vertexOf_end Fr w.frame.ident he₁ Bj hBj hj3) hx ?_ hxj
      rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed H.compat L hjB
    have hB : Bi = Bj := by
      have := w.frame.ident.vertex.injective (hvi.trans hvj.symm)
      exact congrArg Subtype.val this
    subst hB
    exact paired_of_homed Fr L hBi hiB hjB

end SlotReading

/-! ### Two labels of one home on one stable path meet the home twice -/

section Incidence

variable {target : CFGraph.{0}} {degree : ℕ}
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (hCompat : WallDegeneration.DanglingCompatible data hc hab hOne)
  (Fr : AnchorFrame data hc hab hOne block)
  (L : AnchorLabelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

/-- The occurrence at the home through which a survivor's stable path reaches it. -/
theorem witness_of_homed {i : Fin 4} {B : data.SourceVertex} (h : Homed L i B) :
    ∃ x : NonDanglingEdge data, Incident data x.1 B ∧ x.stablePath = pathOf hCompat L i ∧
      (x.1 = lift L i ∨ ∃ Z ∈ fib data hc hab hOne block, nonDanglingValency data Z = 2 ∧
        lift L i ∈ ndAt data Z ∧ x.1 ∈ intl data hc hab hOne block ∧ x.1 ∈ ndAt data Z) := by
  rcases h with h | ⟨Z, hZ, hZ2, hiZ, e, he, heZ, heB⟩
  · exact ⟨⟨lift L i, lift_survives hCompat L i⟩, ((mem_ndAt data B _).mp h).2, rfl, Or.inl rfl⟩
  · have heS := ((mem_ndAt data B _).mp heB).1
    have hne : (⟨lift L i, lift_survives hCompat L i⟩ : NonDanglingEdge data) ≠ ⟨e, heS⟩ := by
      intro h
      apply lift_ne L i
      have := congrArg (fun x : NonDanglingEdge data ↦ x.1.1.1) h
      simp only at this
      rw [this]
      exact (intl_ends data hc hab hOne block he).2.2.2.2.1
    have hcons : Consecutive data ⟨lift L i, lift_survives hCompat L i⟩ ⟨e, heS⟩ :=
      ⟨hne, Z, ((mem_ndAt data Z _).mp hiZ).2, ((mem_ndAt data Z _).mp heZ).2, hZ2⟩
    exact ⟨⟨e, heS⟩, ((mem_ndAt data B _).mp heB).2, (stablePath_eq_of_consecutive hcons).symm,
      Or.inr ⟨Z, hZ, hZ2, hiZ, he, heZ⟩⟩

theorem lift_ne_of_intl {i : Fin 4} {e : data.SourceEdge}
    (he : e ∈ intl data hc hab hOne block) : lift L i ≠ e := by
  intro h
  exact lift_ne L i (h ▸ (intl_ends data hc hab hOne block he).2.2.2.2.1)

include Fr in
/-- **Two labels homed at one branch constituent, on one incoming stable path, meet it twice.** -/
theorem two_le_incidence {i j : Fin 4} (hij : i ≠ j) {B : data.SourceVertex}
    (hi : Homed L i B) (hj : Homed L j B) (hP : pathOf hCompat L i = pathOf hCompat L j) :
    2 ≤ StablePathCount.incidenceCount data B (pathOf hCompat L i) := by
  classical
  obtain ⟨x, hxB, hxP, hx⟩ := witness_of_homed hCompat L hi
  obtain ⟨x', hx'B, hx'P, hx'⟩ := witness_of_homed hCompat L hj
  have hne : x ≠ x' := by
    intro hxx
    have h1 : x.1 = x'.1 := congrArg Subtype.val hxx
    rcases hx with hx | ⟨Z, hZ, hZ2, hiZ, hxI, hxZ⟩ <;>
      rcases hx' with hx' | ⟨Z', hZ', hZ2', hjZ', hx'I, hx'Z'⟩
    · exact hij (lift_injective L (hx.symm.trans (h1.trans hx')))
    · exact lift_ne_of_intl L hx'I (hx.symm.trans h1)
    · exact lift_ne_of_intl L hxI (hx'.symm.trans h1.symm)
    · have hZZ := Fr.two_unique Z hZ Z' hZ' hZ2 hZ2'
      subst hZZ
      have hsub : ({lift L i, lift L j, x.1} : Finset data.SourceEdge) ⊆ ndAt data Z := by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl
        · exact hiZ
        · exact hjZ'
        · exact hxZ
      have hc3 : ({lift L i, lift L j, x.1} : Finset data.SourceEdge).card = 3 := by
        have i1 : lift L i ≠ lift L j := fun h ↦ hij (lift_injective L h)
        rw [Finset.card_insert_of_notMem (by simp [i1, lift_ne_of_intl L hxI]),
          Finset.card_pair (lift_ne_of_intl L hxI)]
      have := Finset.card_le_card hsub
      rw [card_ndAt, hZ2] at this
      omega
  unfold StablePathCount.incidenceCount
  have hsub : ({x, x'} : Finset (NonDanglingEdge data)) ⊆
      (StablePathCount.incidentEdges data B).filter
        fun edge ↦ edge.stablePath = pathOf hCompat L i := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges]
    rcases he with rfl | rfl
    · exact ⟨hxB, hxP⟩
    · exact ⟨hx'B, hx'P.trans hP.symm⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  exact this

end Incidence

/-! ## 6.  The loop merge: Types I and II over the digon core are one class -/

section Digon

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
variable {w : Regrowth core y degree}
  {block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks}

/-- **Beside a loop pair, the other two survivors have non-parallel slots.**  At a regrowth over a
connected cubic core with at least three vertices, if `e₂` and `e₅` share a limit stable path and
the survivor `k` does not, then the slot of `k` meets only one end of `e₀`.  (If it met both, the
slot `s` of the shared path would be a second parallel slot when `e₂`, `e₅` have different homes,
and a loop beside a parallel slot when they have one home; the core is cubic.) -/
theorem nonPar_of_lpaths (hcub : core.Cubic) (hconn : core.Connected) (hn : 3 ≤ n)
    (H : RegrowthAnchor w block) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (he₀ : core.tail e₀ ≠ core.head e₀) (L : AnchorLabelling w.limit (anchorOf w block))
    (h03 : lpath L 0 = lpath L 3) {k : Fin 4} (hk : lpath L k ≠ lpath L 0) :
    NonPar core e₀ (slotOf H L k) := by
  classical
  obtain ⟨Fr⟩ := nonempty_anchorFrame w.frame.fullDim H
  have he₁ := row_e₁ Fr hpt.1
  have W := WallRows.ofAnchor H
  have hinj := StablePathFacetContraction.incomingRow_injective w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) W.compat W.forest
    W.noReturn
  have hin : ∀ i, inRow W (lpath L i) = pathOf H.compat L i := fun i ↦ rfl
  have hP : pathOf H.compat L 0 = pathOf H.compat L 3 := by
    rw [← hin 0, ← hin 3, h03]
  have hslot : slotOf H L k ≠ slotOf H L 0 := by
    intro h
    apply hk
    exact hinj (w.frame.ident.row.injective h)
  by_contra hnp
  unfold NonPar at hnp
  push Not at hnp
  have hsk : Parallel core e₀ (slotOf H L k) :=
    ⟨slot_ne H.compat L Fr w.frame.ident he₁ k, Nat.pos_of_ne_zero hnp.1,
      Nat.pos_of_ne_zero hnp.2⟩
  have hs0e : slotOf H L 0 ≠ e₀ := slot_ne H.compat L Fr w.frame.ident he₁ 0
  obtain ⟨B₀, hB₀, h0⟩ := exists_homed w.frame.fullDim Fr L H.compat 0
  obtain ⟨B₃, hB₃, h3⟩ := exists_homed w.frame.fullDim Fr L H.compat 3
  have i0 : 0 < coreIncidence core (vertexOf w.frame.ident B₀ (nd_of_R_or_Y Fr hB₀))
      (slotOf H L 0) := by
    rw [coreIncidence_vertexOf]; exact incidence_pos_of_homed H.compat L h0
  have i3 : 0 < coreIncidence core (vertexOf w.frame.ident B₃ (nd_of_R_or_Y Fr hB₃))
      (slotOf H L 0) := by
    rw [slotOf, hP, coreIncidence_vertexOf]; exact incidence_pos_of_homed H.compat L h3
  have x0 := vertexOf_end Fr w.frame.ident he₁ B₀ hB₀ (nd_of_R_or_Y Fr hB₀)
  have x3 := vertexOf_end Fr w.frame.ident he₁ B₃ hB₃ (nd_of_R_or_Y Fr hB₃)
  by_cases hBB : B₀ = B₃
  · subst hBB
    have h2 := two_le_incidence H.compat Fr L (i := 0) (j := 3) (by decide) h0 h3 hP
    have h2' : 2 ≤ coreIncidence core (vertexOf w.frame.ident B₀ (nd_of_R_or_Y Fr hB₀))
        (slotOf H L 0) := by
      rw [coreIncidence_vertexOf]; exact h2
    have := incidence_lt_two_of_parallel hcub hsk hs0e (Ne.symm hslot) x0
    omega
  · have hx : vertexOf w.frame.ident B₀ (nd_of_R_or_Y Fr hB₀) ≠
        vertexOf w.frame.ident B₃ (nd_of_R_or_Y Fr hB₃) := by
      intro h
      exact hBB (congrArg Subtype.val (w.frame.ident.vertex.injective h))
    have hpar0 : Parallel core e₀ (slotOf H L 0) := by
      refine ⟨hs0e, ?_, ?_⟩ <;> rcases x0 with h | h <;> rcases x3 with h' | h'
      all_goals first
        | (rw [← h]; exact i0)
        | (rw [← h']; exact i3)
        | exact absurd (h.trans h'.symm) hx
    exact hslot (parallel_unique hcub hconn hn he₀ hpar0 hsk).symm

open ValencyThreeGeneral.Split7 in
open DraismaVargas.Count.CrossCoreTransport (FrameClass) in
/-- **The loop merge: stage 3--5 uniqueness over a core with a slot parallel to `e₀`.**  Two
anchored regrowths of a connected cubic core (at least three vertices, `e₀` not a loop) with
labelled-metric isomorphic limits are one class, provided the limit is *also* presented by an
anchored regrowth of a core with a loop at an end of `e₀` (any geometric limit isomorphism `χ`).

The loop presenter gives the sheet swap `σ'` of `e₂`, `e₅` on the second limit and shows that
the slots of `e₃`, `e₄` are not parallel (`nonPar_of_lpaths`), so Type III is read off the core
on both sides; Types I and II are exchanged by `σ'`, so `ψ` or `ψ ≫ σ'` matches the types, and
stages 4--5 conclude (`ValencyThreeCoreSlots.frameClass_eq_of_reads`). -/
theorem frameClass_eq_of_loopPresenter (hcub : core.Cubic) (hconn : core.Connected)
    (hn : 3 ≤ n) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (he₀ : core.tail e₀ ≠ core.head e₀) (w w' : Regrowth core y degree) {block block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block')
    (hsame : ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ)
    {cL : Core n p} {wL : Regrowth cL y degree} {blockL} (HL : RegrowthAnchor wL blockL)
    {f : Fin p} (hLoop : cL.tail f = cL.head f)
    (hend : cL.tail f = cL.tail e₀ ∨ cL.tail f = cL.head e₀)
    (χ : GeometricDatumIso w.limit wL.limit) :
    FrameClass.mk w.frame = FrameClass.mk w'.frame := by
  classical
  obtain ⟨ψ, hψ⟩ := hsame
  obtain ⟨L⟩ := nonempty_anchorLabelling w.frame.fullDim H
  obtain ⟨L', hL, hsplit⟩ := regrowth_split_eq w w' H H' ψ L
  obtain ⟨s, hsR, -, -⟩ := existsUnique_reads w.frame.fullDim H L
  obtain ⟨s', hsR', -, -⟩ := existsUnique_reads w'.frame.fullDim H' L'
  obtain ⟨⟨h03, h10, h20⟩, -⟩ := loopData_of_limitIso H HL hpt hLoop hend χ L
  obtain ⟨-, σ, hσT, hσ0, hσ3, hσ1, hσ2⟩ :=
    loopData_of_limitIso H' HL hpt hLoop hend (ψ.symm.trans χ) L'
  obtain ⟨Fr⟩ := nonempty_anchorFrame w.frame.fullDim H
  obtain ⟨Fr'⟩ := nonempty_anchorFrame w'.frame.fullDim H'
  -- the slots of `e₃` and `e₄` meet one end of `e₀` each, on both sides
  have hn1 := nonPar_of_lpaths hcub hconn hn H hpt he₀ L h03 h10
  have hn2 := nonPar_of_lpaths hcub hconn hn H hpt he₀ L h03 h20
  have hs1 := slot_transport H H' hpt ψ hψ L L' hL 1
  have hs2 := slot_transport H H' hpt ψ hψ L L' hL 2
  have hn1' : NonPar core e₀ (slotOf H' L' 1) := by
    show NonPar core e₀ (w'.frame.ident.row (pathOf H'.compat L' 1)); rw [hs1]; exact hn1
  have hn2' : NonPar core e₀ (slotOf H' L' 2) := by
    show NonPar core e₀ (w'.frame.ident.row (pathOf H'.compat L' 2)); rw [hs2]; exact hn2
  have hIII : s.type = VType.III ↔ s'.type = VType.III := by
    rw [← paired12_iff Fr L w.frame.fullDim H hsR, ← paired12_iff Fr' L' w'.frame.fullDim H' hsR',
      paired_iff_coreShare_of H hpt L 1 2 hn1 hn2,
      paired_iff_coreShare_of H' hpt L' 1 2 hn1' hn2']
    show CoreShare core e₀ (slotOf H L 1) (slotOf H L 2) ↔
      CoreShare core e₀ (w'.frame.ident.row (pathOf H'.compat L' 1))
        (w'.frame.ident.row (pathOf H'.compat L' 2))
    rw [hs1, hs2]
  by_cases hty : s.type = s'.type
  · have hss : s = s' := hsplit s s' hsR hsR' hty
    subst hss
    exact frameClass_eq_of_reads hconn hn hpt.1 w w' H H' ψ hψ L L' hL s hsR hsR'
  · -- compose with the sheet swap of `e₂` and `e₅`
    have hψ₂ : IsMetricIso w w' (ψ.trans σ) := by
      intro e
      have : (ψ.trans σ).targetEdge e = ψ.targetEdge e := by
        change σ.targetEdge (ψ.targetEdge e) = ψ.targetEdge e
        exact hσT _
      rw [this]
      exact hψ e
    obtain ⟨L₂, hL₂, hsplit₂⟩ := regrowth_split_eq w w' H H' (ψ.trans σ) L
    obtain ⟨s₂, hs₂R, -, -⟩ := existsUnique_reads w'.frame.fullDim H' L₂
    have hπ : ∀ i, L₂.e i = L'.e (swap03 i) := by
      intro i
      have hi : L₂.e i = σ.sourceEdgeEquiv (L'.e i) := by
        rw [hL₂ i, hL i]; rfl
      rw [hi]
      fin_cases i
      · exact hσ0
      · exact hσ1
      · exact hσ2
      · exact hσ3
    have hs'III : s'.type ≠ VType.III := fun h ↦ hty ((hIII.mpr h).trans h.symm)
    have hsIII : s.type ≠ VType.III := fun h ↦ hs'III (hIII.mp h)
    have hs₂III : s₂.type ≠ VType.III := by
      intro h
      apply hs'III
      rw [← paired12_iff Fr' L' w'.frame.fullDim H' hsR']
      have := (paired12_iff Fr' L₂ w'.frame.fullDim H' hs₂R).mpr h
      exact (paired_relabel swap03 hπ 1 2).mp this
    have hne := type_swap03 w'.frame.fullDim H' hπ hsR' hs₂R hs'III
    have htype : s.type = s₂.type := by
      revert hty hsIII hs'III hs₂III hne
      cases s.type <;> cases s'.type <;> cases s₂.type <;> decide
    have hss : s = s₂ := hsplit₂ s s₂ hsR hs₂R htype
    subst hss
    exact frameClass_eq_of_reads hconn hn hpt.1 w w' H H' (ψ.trans σ) hψ₂ L L₂ hL₂ s hsR hs₂R

end Digon

/-! ## 7.  The `MetricCensus` clause at a step with a parallel slot -/

section Census

open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.FacetMachine (FacetDatum)
open DraismaVargas.Count.FacetAdapterPilot (farCore revMove revMove_base farCore_revMove
  facetDatum_rev)
open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight SameMetricLimit)
open ValencyThreeCensus (FibreLeft FibreRight exists_mSpecializesLeft exists_mSpecializesRight
  far_nonloop exists_regrowthAnchor_of_limitIso)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)

variable {n p degree : ℕ}

/-- The core `c` has a self-loop at an end of `e₀`. -/
def LoopAtEnd (c : Core n p) (e₀ : Fin p) : Prop :=
  ∃ f, c.tail f = c.head f ∧ (c.tail f = c.tail e₀ ∨ c.tail f = c.head e₀)

instance (c : Core n p) (e₀ : Fin p) : Decidable (LoopAtEnd c e₀) := by
  unfold LoopAtEnd; infer_instance

/-- **The per-side hypothesis of the loop merge**: either `c` has no slot parallel to `e₀`
(the case of `ValencyThreeCensus`), or the *other* core `c'` of the step has a self-loop at an end of `e₀`, so
that every limit of `c` is also presented over a loop core (the loop merge, this file).  It fails
only at a *digon--digon* step, where both cores have a slot parallel to `e₀`, neither has the
loop (the third resolution of the merged vertex). -/
def LoopMerge (c c' : Core n p) (e₀ : Fin p) : Prop :=
  NoParallel c e₀ ∨ LoopAtEnd c' e₀

instance (c c' : Core n p) (e₀ : Fin p) : Decidable (LoopMerge c c' e₀) := by
  unfold LoopMerge; infer_instance

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- The near core's copy of the contracted slot is not a loop. -/
theorem near_nonloop (m' : c.graph.MoveData) : c.core.tail m'.base.1 ≠ c.core.head m'.base.1 :=
  FacetCommonMultiplicity.tail_ne_head_of_shared
    (FacetAdapterPilot.sharedContractionSlot_of_move m' (FacetAdapterPilot.farCore_graph m'))

/-! ### The general form: a loop presenter from any third core -/

/-- **Every regrowth of `c` at `y₀` has a loop presenter**: a regrowth, at the same `y₀`, of a
core with a self-loop at an end of `e₀` (and `e₀` itself not a loop), whose limit is
geometrically isomorphic.  Supplied by `LoopMerge` at the step itself
(`loopPresented_of_move`), and, at a digon--digon step, by a facet datum *at the same `y₀`* for
the third resolution of the merged vertex. -/
def LoopPresented (c : Core n p) (e₀ : Fin p) (y₀ : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ w : Regrowth c y₀ degree, ∃ (cL : Core n p) (f : Fin p), cL.tail f = cL.head f ∧
    (cL.tail f = cL.tail e₀ ∨ cL.tail f = cL.head e₀) ∧ cL.tail e₀ ≠ cL.head e₀ ∧
      ∃ wL : Regrowth cL y₀ degree, Nonempty (GeometricDatumIso w.limit wL.limit)

/-- **A move to a loop core supplies loop presenters** (the existence transfer of
`ColumnReceiptExport`): if the
far core of `m''` has a loop at an end of the contracted slot, every regrowth of the near core
at the datum's `y₀` has a far partner at the same metric limit. -/
theorem loopPresented_of_move (m'' : c.graph.MoveData)
    (hd'' : FacetDatum c.core (farCore m'').core degree m''.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (hloop : LoopAtEnd (farCore m'').core m''.base.1) :
    LoopPresented c.core m''.base.1 y₀ degree := by
  intro w
  obtain ⟨f, hLoop, hend⟩ := hloop
  obtain ⟨-, wL, -, hwL⟩ := exists_mSpecializesRight m'' hd'' hG hDegree
    (MetricFacetLimit.ofLeft w) (FrameClass.mk w.frame) ⟨w, rfl, rfl⟩
  obtain ⟨χ, -⟩ : SameMetricLimit (c := c.core) (c' := (farCore m'').core) (Sum.inl w)
      (Sum.inr wL) := Quotient.exact hwL.symm
  exact ⟨_, f, hLoop, hend, far_nonloop m'', wL, ⟨χ⟩⟩

/-- **The reversed move supplies loop presenters on the far side** when the near core has a
loop at an end of `e₀`. -/
theorem loopPresented_far (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (hloop : LoopAtEnd c.core m'.base.1) :
    LoopPresented (farCore m').core m'.base.1 y₀ degree := by
  have h := loopPresented_of_move (revMove m') (facetDatum_rev m' hd) hG hDegree
    (by rw [farCore_revMove, revMove_base]; exact hloop)
  rwa [revMove_base] at h

/-- **One side, general form**: two anchored regrowths of a connected cubic core with
labelled-metric isomorphic limits are one class when the core has no slot parallel to `e₀` or
its regrowths have loop presenters. -/
theorem frameClass_eq_of_side {core : Core n p} (hcub : core.Cubic) (hconn : core.Connected)
    (hn : 3 ≤ n) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y₀)
    (he₀ : core.tail e₀ ≠ core.head e₀)
    (hP : NoParallel core e₀ ∨ LoopPresented core e₀ y₀ degree)
    (w w' : Regrowth core y₀ degree) {block block'} (H : RegrowthAnchor w block)
    (H' : RegrowthAnchor w' block')
    (hsame : ∃ ψ : GeometricDatumIso w.limit w'.limit, IsMetricIso w w' ψ) :
    FrameClass.mk w.frame = FrameClass.mk w'.frame := by
  rcases hP with hpar | hP
  · exact frameClass_eq_of_metricIso hconn hn hpt hpar w w' H H' hsame
  obtain ⟨cL, f, hLoop, hend, hnl, wL, ⟨χ⟩⟩ := hP w
  obtain ⟨blockL, HL⟩ := exists_regrowthAnchor_of_limitIso H hpt hnl χ
  exact frameClass_eq_of_loopPresenter hcub hconn hn hpt he₀ w w' H H' hsame HL hLoop hend χ

/-- **The valency-three `MetricCensus` clause, general form** (index `Unit`, every class): each
core either has no slot parallel to `e₀` or has loop presenters.  `metricCensus_clause_of_v3'`
is the case where the loop presenters come from the step itself; at a digon--digon step they
must come from a third core (`loopPresented_of_move`). -/
theorem metricCensus_clause_of_presented (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (hP : NoParallel c.core m'.base.1 ∨ LoopPresented c.core m'.base.1 y₀ degree)
    (hP' : NoParallel (farCore m').core m'.base.1 ∨
      LoopPresented (farCore m').core m'.base.1 y₀ degree)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (hm : V3Limit m) :
    ∃ (ι : Type) (τL : {x : FrameClass c.core degree // MSpecializesLeft x m} → ι)
      (τR : {x : FrameClass (farCore m').core degree // MSpecializesRight x m} → ι),
      Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR := by
  refine ⟨Unit, fun _ ↦ (), fun _ ↦ (), fun a b _ ↦ Subtype.ext ?_, fun a b _ ↦ Subtype.ext ?_,
    ?_⟩
  · obtain ⟨w, hw, hwm⟩ := a.2
    obtain ⟨w', hw', hwm'⟩ := b.2
    obtain ⟨block, H⟩ := hm w hwm
    obtain ⟨block', H'⟩ := hm w' hwm'
    have hsame : SameMetricLimit (c := c.core) (c' := (farCore m').core) (Sum.inl w)
        (Sum.inl w') := Quotient.exact (hwm.trans hwm'.symm)
    rw [← hw, ← hw']
    exact frameClass_eq_of_side c.cubic c.connected hn hd.point (near_nonloop m') hP w w' H H'
      ((ValencyThreeSplit.sameMetricLimit_iff w w').mp hsame)
  · obtain ⟨-, w₀, -, hw₀⟩ := exists_mSpecializesLeft m' hd hG hDegree m a.1 a.2
    obtain ⟨block₀, H₀⟩ := hm w₀ hw₀
    obtain ⟨w, hw, hwm⟩ := a.2
    obtain ⟨w', hw', hwm'⟩ := b.2
    obtain ⟨ψ, -⟩ : SameMetricLimit (c := c.core) (c' := (farCore m').core) (Sum.inl w₀)
        (Sum.inr w) := Quotient.exact (hw₀.trans hwm.symm)
    obtain ⟨ψ', -⟩ : SameMetricLimit (c := c.core) (c' := (farCore m').core) (Sum.inl w₀)
        (Sum.inr w') := Quotient.exact (hw₀.trans hwm'.symm)
    obtain ⟨block, H⟩ := exists_regrowthAnchor_of_limitIso H₀ hd.point (far_nonloop m') ψ
    obtain ⟨block', H'⟩ := exists_regrowthAnchor_of_limitIso H₀ hd.point (far_nonloop m') ψ'
    obtain ⟨χ, hχ⟩ : SameMetricLimit (c := c.core) (c' := (farCore m').core) (Sum.inr w)
        (Sum.inr w') := Quotient.exact (hwm.trans hwm'.symm)
    rw [← hw, ← hw']
    exact frameClass_eq_of_side (farCore m').cubic (farCore m').connected hn hd.point
      (far_nonloop m') hP' w w' H H' ⟨χ, hχ⟩
  · ext u
    constructor
    · rintro ⟨x, -⟩
      obtain ⟨x', hs'⟩ := exists_mSpecializesRight m' hd hG hDegree m x.1 x.2
      exact ⟨⟨x', hs'⟩, rfl⟩
    · rintro ⟨x', -⟩
      obtain ⟨x, hs⟩ := exists_mSpecializesLeft m' hd hG hDegree m x'.1 x'.2
      exact ⟨⟨x, hs⟩, rfl⟩

/-- **The valency-three `MetricCensus` clause, with the loop merge** (index `Unit`, every
class).  At a Whitehead step's facet datum, at every metric facet limit `m` whose near-side
presentations carry the valency-three anchor input: the near and far fibres at `m` are each
empty or a single class, and empty together -- provided each core either has no slot parallel
to `e₀` or faces a loop core (`LoopMerge`, both ways).  This drops the `NoParallel`
hypotheses: `NoParallel c e₀ → LoopMerge c c' e₀`, so `metricCensus_clause_of_v3` is the case
`Or.inl`, `Or.inl`, and the parallel case is `Or.inr`.  Only digon--digon steps are left. -/
theorem metricCensus_clause_of_v3' (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (hmL : LoopMerge c.core (farCore m').core m'.base.1)
    (hmR : LoopMerge (farCore m').core c.core m'.base.1)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (hm : V3Limit m) :
    ∃ (ι : Type) (τL : {x : FrameClass c.core degree // MSpecializesLeft x m} → ι)
      (τR : {x : FrameClass (farCore m').core degree // MSpecializesRight x m} → ι),
      Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR :=
  metricCensus_clause_of_presented m' hd hG hDegree hn
    (hmL.imp id (loopPresented_of_move m' hd hG hDegree))
    (hmR.imp id (loopPresented_far m' hd hG hDegree)) m hm

/-- **`MetricCensus` at a step all of whose metric limits are of valency three**, with the loop
merge. -/
theorem metricCensus_of_forall_v3' (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (hmL : LoopMerge c.core (farCore m').core m'.base.1)
    (hmR : LoopMerge (farCore m').core c.core m'.base.1)
    (hv3 : ∀ m : MetricFacetLimit c.core (farCore m').core y₀ degree, V3Limit m) :
    FacetCensus.MetricCensus c.core (farCore m').core degree y₀ :=
  fun m ↦ metricCensus_clause_of_v3' m' hd hG hDegree hn hmL hmR m (hv3 m)

end Census

/-! ## 8.  `cat_step`: the loop merge is exactly what the far side needs -/

section Cat

open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)
open DraismaVargas.Count.FacetMachine (catLoopMove catLoopCore FacetDatum)
open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight)
open ValencyThreeCensus (far_nonloop)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.FacetAdapterPilot (farCore)

/-- **The loop merge applies at `cat_step`**: the near core has no parallel slot, the far core has one
(`ValencyThreeCensus.not_noParallel_catLoop`), and the caterpillar has a loop at an end of the
contracted slot, so both `LoopMerge` hypotheses hold where `NoParallel` fails. -/
theorem loopMerge_cat :
    LoopMerge catCubicCore.core catLoopCore.core catLoopMove.base.1 ∧
      LoopMerge catLoopCore.core catCubicCore.core catLoopMove.base.1 ∧
        ¬ NoParallel catLoopCore.core catLoopMove.base.1 := by
  decide

/-- **The valency-three `MetricCensus` clause at `cat_step`**, at every metric limit of
valency three: the metric-limit, census form of uniqueness on the far side of `cat_step`, for
every class. -/
theorem metricCensus_clause_cat {y₀ : Fin (6 * 2 + 3) → ℚ} {ε : ℚ}
    (hd : FacetDatum catCubicCore.core catLoopCore.core (2 + 2) catLoopMove.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric (2 + 2) y₀)
    (m : MetricFacetLimit catCubicCore.core catLoopCore.core y₀ (2 + 2)) (hm : V3Limit m) :
    ∃ (ι : Type) (τL : {x : FrameClass catCubicCore.core (2 + 2) // MSpecializesLeft x m} → ι)
      (τR : {x : FrameClass catLoopCore.core (2 + 2) // MSpecializesRight x m} → ι),
      Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR :=
  metricCensus_clause_of_v3' catLoopMove hd hG (by norm_num) (by norm_num) loopMerge_cat.1
    loopMerge_cat.2.1 m hm

/-- **The per-step obligation at `cat_step`** from valency three at every metric limit. -/
theorem cat_obligation_of_forall_v3 {y₀ : Fin (6 * 2 + 3) → ℚ} {ε : ℚ}
    (hd : FacetDatum catCubicCore.core catLoopCore.core (2 + 2) catLoopMove.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric (2 + 2) y₀)
    (hv3 : ∀ m : MetricFacetLimit catCubicCore.core catLoopCore.core y₀ (2 + 2), V3Limit m) :
    ∃ y y' : Fin (6 * 2 + 3) → ℚ, SimpleWallSupply.PositiveGeneral catCubicCore.core (2 + 2) y ∧
      SimpleWallSupply.PositiveGeneral catLoopCore.core (2 + 2) y' ∧
        CountTransportLink.CountLink (2 + 2) catCubicCore.core y catLoopCore.core y' :=
  FacetCensus.cat_obligation_of_metricCensus hd (far_nonloop catLoopMove)
    (metricCensus_of_forall_v3' catLoopMove hd hG (by norm_num) (by norm_num) loopMerge_cat.1
      loopMerge_cat.2.1 hv3)

/-- **A digon--digon step out of `catLoopCore`** at the spine slot `1` (vertices `0`, `1`, with
slot `0` parallel): slot `2`'s dart at vertex `0` and slot `4`'s dart at vertex `1` change ends.
Both resolutions keep slot `0` parallel to slot `1`. -/
def digonMove : catLoopCore.graph.MoveData where
  base := (1, false)
  left := (2, false)
  right := (4, false)
  nonloop := by decide
  left_vert := by decide
  left_ne := by decide
  right_vert := by decide
  right_ne := by decide

/-- **`LoopMerge` is not automatic.**  At the digon--digon step `digonMove` (a genuine
genus-six Whitehead step) it fails on both sides, so `metricCensus_clause_of_v3'` does not
apply there; this is the one case the loop merge leaves (handled in `ValencyThreeDigon` by a
jointly generic `y₀`). -/
theorem not_loopMerge_digon :
    ¬ LoopMerge catLoopCore.core (farCore digonMove).core digonMove.base.1 ∧
      ¬ LoopMerge (farCore digonMove).core catLoopCore.core digonMove.base.1 := by
  decide

end Cat

end DraismaVargas.Count.ValencyThreeLoopMerge
