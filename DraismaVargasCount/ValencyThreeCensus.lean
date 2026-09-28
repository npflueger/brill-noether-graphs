import DraismaVargasCount.ValencyThreeCoreSlots
import DraismaVargasCount.FacetCensus

set_option autoImplicit false

/-!
# The valency-three `MetricCensus` clause

`FacetCensus.MetricCensus` asks, at every labelled metric facet limit `m`, for an index type and
injective labellings of the **whole** near and far fibres at `m` (all classes, odd or even) with
equal ranges.  This file proves that clause at every metric limit whose near-side presentations
carry the valency-three anchor input (`V3Limit m`), with index `Unit`, at every Whitehead
step's facet datum at which neither core has a slot parallel to the contracted slot
(`metricCensus_clause_of_v3`).  It is part of the type-change step, step 3 of `Assembly`; the
stages are those of `ValencyThreeSplit`.

## How

* **Injectivity, near side** (`subsingleton_left`): two classes of `c` at `m` are presented by
  anchored regrowths with labelled-metric isomorphic limits, so they are one class
  (`ValencyThreeCoreSlots.frameClass_eq_of_metricIso`: stage 3 from the core's pairing, stages
  4--5 from `ValencyThreeResolutionMatch`, no oddness).
* **Injectivity, far side** (`subsingleton_right`): a far-side class at `m` forces a near-side
  presentation of `m` (the reverse existence transfer), whose valency-three anchor is carried to
  every far-side presentation by the limit isomorphism (`exists_regrowthAnchor_of_limitIso`: the
  anchor goes to a vertex of surviving valency four, which lies over the merged vertex,
  `over_merged_of_nd_four`); then as on the near side, over the far core.  So `V3Limit m` alone
  is the valency hypothesis, as a per-valency dispatch wants.
* **Equal ranges** (`exists_mSpecializesRight`, `exists_mSpecializesLeft`): the unconditional
  existence transfers of `ColumnReceiptExport` with the oddness bookkeeping dropped -- a class on
  one side at `m` has a class on the other side at `m`.

One might expect to have to construct the "positions" (a member of each of Types I, II, III)
here.  They are the splits: at such a limit the unique class of each side (if any) reads the
unique valid split whose type is that core's pairing of the survivors' slots
(`ValencyThreeCoreSlots.coreShare_iff_typePartner` and `ValencyThreeGeneral`'s
`Split7.existsUnique`); no position has to be *built*, because existence is the transfer of
`ColumnReceiptExport`.

## What is proved

* §1 `over_merged_of_nd_four`, `valency_of_limitIso`, **`exists_regrowthAnchor_of_limitIso`**.
* §2 `FibreLeft`, `FibreRight`, **`subsingleton_left`**, **`subsingleton_right`**.
* §3 `exists_mSpecializesRight_of_receipts`, `exists_mSpecializesLeft_of_receipts`,
  **`exists_mSpecializesRight`**, **`exists_mSpecializesLeft`** (every class), `far_nonloop`
  (the far core's copy of the move's slot is not a loop).
* §4 **`metricCensus_clause_of_v3`** (the clause, `ι = Unit`), `nonempty_equiv_of_v3` (its
  `metricCensus_iff` form), `metricCensus_of_forall_v3`.
* §5 `noParallel_cat`, `not_noParallel_catLoop` (the far core of `cat_step` has a parallel
  slot), `catStemMove` and `noParallel_stem` (both cores of a genus-six step satisfy
  `NoParallel`), `typeMatch_cat'`, and an `example` (the clause's binders are inhabited at the
  stem step).

## Hypotheses

* **`NoParallel` on each core.**  Where the contracted core has a loop at the merged vertex
  from a slot parallel to `e₀` on one side (the far core of `cat_step`), that side's stage 3 is
  the loop merge of `ValencyThreeLoopMerge`, not this file.  Only
  `subsingleton_left`/`subsingleton_right` use it; the existence half does not.
* **`V3Limit m`**, the anchor input of each near-side presentation (the dispatch hypothesis):
  `ValencyThreeSplit.v3Limit_of_facetPoint` reduces it to the trivalence of the merged target
  vertex, and `CensusAssembly.valency_trichotomy` dispatches every metric facet limit into
  exactly one of `V2Limit`, `V3Limit`, `V4Limit`.
* `3 ≤ degree` (for the member seed, `MemberSeedExists.nonempty_memberSeed_of_member`),
  `3 ≤ n` (stage 5), `FacetGeneric` (for the link receipts
  `ColumnReceiptExport.metricLinkReceipts`).
* `MetricCensus` at limits of valency two and four is not treated here (see `ValencyTwoPairing`,
  `ValencyFourRealisation` and `CensusAssembly`).
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

namespace DraismaVargas.Count.ValencyThreeCensus

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification W4StableSource
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.FacetMachine (FacetDatum)
open DraismaVargas.Count.FacetAdapterPilot (farCore)
open ValencyThreeSplit (V3Limit TypeMatch RegrowthAnchor anchorOf IsMetricIso)
open ValencyThreeRigidity (endA)
open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight metricSwap
  SameMetricLimit)
open ValencyThreeCoreSlots (NoParallel)

variable {n p degree : ℕ}

/-! ## 1.  A limit isomorphism carries the valency-three anchor across cores -/

section Transfer

variable {c c' : Core n p} {y : Fin p → ℚ}

/-- **A source vertex of surviving valency four lies over the merged vertex**: away from the
wall a limit vertex keeps its incoming surviving valency, which is at most three. -/
theorem over_merged_of_nd_four (w : Regrowth c y degree)
    (hCompat : WallDegeneration.DanglingCompatible w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column))
    (X : w.limit.SourceVertex) (hX : nonDanglingValency w.limit X = 4) :
    X.1.1 = ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ := by
  classical
  by_contra hXw
  obtain ⟨Y, rfl⟩ := GluingContraction.sourceVertexMap_surjective w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) X
  have hYa : Y.1.1 ≠ endA w := fun h ↦
    hXw (ContractionFibre.fold_eq_of_eq_or (fst_ne_snd (w.frame.edgeOf w.column)) (Or.inl h))
  have hYb : Y.1.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2 :=
    fun h ↦ hXw (ContractionFibre.fold_eq_of_eq_or (fst_ne_snd (w.frame.edgeOf w.column))
      (Or.inr h))
  have h4 : nonDanglingValency w.frame.data Y = 4 :=
    (WallDegeneration.nonDanglingValency_sourceVertexMap w.frame.data hCompat Y hYa hYb).symm.trans
      hX
  have := w.frame.fullDim.trivalent Y
  omega

/-- **The merged vertex's valency is carried by a limit isomorphism** from a regrowth with a
valency-three anchor to any facet regrowth, over either core: the anchor goes to a vertex of
surviving valency four, hence over the merged vertex. -/
theorem valency_of_limitIso {w : Regrowth c y degree} {w' : Regrowth c' y degree} {block}
    (H : RegrowthAnchor w block)
    (hCompat' : WallDegeneration.DanglingCompatible w'.frame.data rfl
      (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column))
    (ψ : GeometricDatumIso w.limit w'.limit) :
    (GluingDatum.incidentEdges (target := w'.frame.limitTarget w'.column)
      ⟨(w'.frame.edgeOf w'.column : w'.frame.target.V × w'.frame.target.V).1,
        fst_ne_snd (w'.frame.edgeOf w'.column)⟩).card = 3 := by
  have h4 : nonDanglingValency w'.limit (ψ.sourceVertexEquiv (anchorOf w block)) = 4 :=
    (ψ.nonDanglingValency_map (ValencyThreeSplit.connected_limit w) _).trans H.nd4
  have hwall : ψ.targetVertex ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩ =
      ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ :=
    over_merged_of_nd_four w' hCompat' _ h4
  have := ψ.incidentEdges_card_map ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
  rw [hwall] at this
  exact this.trans H.valency

/-- **The anchor input transfers along a limit isomorphism** to a facet regrowth of a core at
which the slot is not a loop. -/
theorem exists_regrowthAnchor_of_limitIso {w : Regrowth c y degree} {w' : Regrowth c' y degree}
    {block} (H : RegrowthAnchor w block) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop' : c'.tail e₀ ≠ c'.head e₀) (ψ : GeometricDatumIso w.limit w'.limit) :
    ∃ block', RegrowthAnchor w' block' :=
  ValencyThreeSplit.exists_regrowthAnchor w' e₀ hpt hloop'
    (valency_of_limitIso H (WallAdmissibility.danglingCompatible_of_contractionForest
      w'.frame.data rfl _ _ (ValencyThreeCoreSlots.forest_of_facetPoint w' hpt hloop')) ψ)

end Transfer

/-! ## 2.  One core: at most one class per valency-three metric limit -/

section OneSide

variable {c c' : Core n p} {y : Fin p → ℚ}

/-- The classes of the near core specialising to a metric facet limit (the whole fibre). -/
abbrev FibreLeft (m : MetricFacetLimit c c' y degree) :=
  {x : FrameClass c degree // MSpecializesLeft x m}

/-- The classes of the far core specialising to a metric facet limit. -/
abbrev FibreRight (m : MetricFacetLimit c c' y degree) :=
  {x : FrameClass c' degree // MSpecializesRight x m}

/-- **At most one near-side class at a valency-three metric limit** (every class, odd or
even), over a connected core with at least three vertices and no slot parallel to `e₀`. -/
theorem subsingleton_left (hconn : c.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hpar : NoParallel c e₀)
    (m : MetricFacetLimit c c' y degree) (hm : V3Limit m) : Subsingleton (FibreLeft m) := by
  refine ⟨fun a b ↦ Subtype.ext ?_⟩
  obtain ⟨w, hw, hwm⟩ := a.2
  obtain ⟨w', hw', hwm'⟩ := b.2
  obtain ⟨block, H⟩ := hm w hwm
  obtain ⟨block', H'⟩ := hm w' hwm'
  have hsame : SameMetricLimit (c := c) (c' := c') (Sum.inl w) (Sum.inl w') :=
    Quotient.exact (hwm.trans hwm'.symm)
  rw [← hw, ← hw']
  exact ValencyThreeCoreSlots.frameClass_eq_of_metricIso hconn hn hpt hpar w w' H H'
    ((ValencyThreeSplit.sameMetricLimit_iff w w').mp hsame)

/-- **At most one far-side class at a metric limit carrying a valency-three near-side
presentation**: each far-side presentation inherits the anchor input along the limit
isomorphism (`exists_regrowthAnchor_of_limitIso`). -/
theorem subsingleton_right (hconn' : c'.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop' : c'.tail e₀ ≠ c'.head e₀)
    (hpar' : NoParallel c' e₀) (m : MetricFacetLimit c c' y degree)
    {w₀ : Regrowth c y degree} {block₀} (H₀ : RegrowthAnchor w₀ block₀)
    (hw₀ : MetricFacetLimit.ofLeft w₀ = m) : Subsingleton (FibreRight m) := by
  refine ⟨fun a b ↦ Subtype.ext ?_⟩
  obtain ⟨w, hw, hwm⟩ := a.2
  obtain ⟨w', hw', hwm'⟩ := b.2
  obtain ⟨ψ, -⟩ : SameMetricLimit (c := c) (c' := c') (Sum.inl w₀) (Sum.inr w) :=
    Quotient.exact (hw₀.trans hwm.symm)
  obtain ⟨ψ', -⟩ : SameMetricLimit (c := c) (c' := c') (Sum.inl w₀) (Sum.inr w') :=
    Quotient.exact (hw₀.trans hwm'.symm)
  obtain ⟨block, H⟩ := exists_regrowthAnchor_of_limitIso H₀ hpt hloop' ψ
  obtain ⟨block', H'⟩ := exists_regrowthAnchor_of_limitIso H₀ hpt hloop' ψ'
  obtain ⟨χ, hχ⟩ : SameMetricLimit (c := c) (c' := c') (Sum.inr w) (Sum.inr w') :=
    Quotient.exact (hwm.trans hwm'.symm)
  rw [← hw, ← hw']
  exact ValencyThreeCoreSlots.frameClass_eq_of_metricIso hconn' hn hpt hpar' w w' H H' ⟨χ, hχ⟩

end OneSide

/-! ## 3.  Existence, every class: the transfers of `ColumnReceiptExport` without the oddness
bookkeeping -/

section Existence

open DraismaVargas.Count.FacetAdapterPilot (farFrame farRegrowth revMove farCore_revMove
  facetDatum_rev)

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- A class of the near core at `m` has a far-side class at `m`, given the metric link
receipts `ValencyThreeGeneral.MetricLinkReceipts` (as in
`ValencyThreeGeneral.exists_odd_mSpecializesRight`, whose oddness clause is bookkeeping
only). -/
theorem exists_mSpecializesRight_of_receipts {c : CubicCore n p} (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (hrec : ValencyThreeGeneral.MetricLinkReceipts m' hd hG (by omega))
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (x : FrameClass c.core degree)
    (hs : MSpecializesLeft x m) :
    ∃ x' : FrameClass (farCore m').core degree, MSpecializesRight x' m := by
  obtain ⟨w, rfl, rfl⟩ := hs
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member (w.frame.member y₀) hDegree
  obtain ⟨link, hlink⟩ := hrec w ms
  exact ⟨FrameClass.mk (farFrame m' hd hG (by omega) w ms link),
    farRegrowth m' hd hG (by omega) w ms link, rfl, (Quotient.sound hlink).symm⟩

/-- The reverse transfer from receipts, by exchanging the two cores
(`ValencyThreeGeneral.exists_odd_mSpecializesLeft` without oddness). -/
theorem exists_mSpecializesLeft_of_receipts {c₁ c₂ : CubicCore n p} (m'' : c₁.graph.MoveData)
    (hback : farCore m'' = c₂)
    (hd : FacetDatum c₁.core (farCore m'').core degree m''.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (hrec : ValencyThreeGeneral.MetricLinkReceipts m'' hd hG (by omega))
    (m : MetricFacetLimit c₂.core c₁.core y₀ degree) (x' : FrameClass c₁.core degree)
    (hs : MSpecializesRight x' m) : ∃ x : FrameClass c₂.core degree, MSpecializesLeft x m := by
  subst hback
  obtain ⟨x, hxs⟩ := exists_mSpecializesRight_of_receipts m'' hd hG hDegree hrec
    (metricSwap m) x' (ValencyThreeGeneral.mSpecializesRight_swap_iff.mp hs)
  refine ⟨x, ?_⟩
  have := ValencyThreeGeneral.mSpecializesRight_swap_iff.mp hxs
  rwa [ValencyThreeGeneral.metricSwap_swap] at this

/-- **Existence transfer, forward, every class, unconditional** (the receipts
`ColumnReceiptExport.metricLinkReceipts`). -/
theorem exists_mSpecializesRight (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (x : FrameClass c.core degree)
    (hs : MSpecializesLeft x m) :
    ∃ x' : FrameClass (farCore m').core degree, MSpecializesRight x' m :=
  exists_mSpecializesRight_of_receipts m' hd hG hDegree
    (ColumnReceiptExport.metricLinkReceipts m' hd hG (by omega)) m x hs

/-- **Existence transfer, reverse, every class, unconditional.** -/
theorem exists_mSpecializesLeft (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree)
    (x' : FrameClass (farCore m').core degree) (hs : MSpecializesRight x' m) :
    ∃ x : FrameClass c.core degree, MSpecializesLeft x m :=
  exists_mSpecializesLeft_of_receipts (revMove m') (farCore_revMove m') (facetDatum_rev m' hd)
    hG hDegree (ColumnReceiptExport.metricLinkReceipts_rev m' hd hG (by omega)) m x' hs

/-- The far core's copy of the contracted slot is not a loop (the reversed move's slot). -/
theorem far_nonloop (m' : c.graph.MoveData) :
    (farCore m').core.tail m'.base.1 ≠ (farCore m').core.head m'.base.1 := by
  have hshared := FacetAdapterPilot.sharedContractionSlot_of_move (revMove m')
    (FacetAdapterPilot.farCore_graph _)
  rw [farCore_revMove, FacetAdapterPilot.revMove_base] at hshared
  exact FacetCommonMultiplicity.tail_ne_head_of_shared hshared

end Existence

/-! ## 4.  The `MetricCensus` clause at a valency-three metric limit -/

section Census

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **The census at a valency-three metric limit, index `Unit`, every class.**  At a
Whitehead step's facet datum at which neither core has a slot parallel to the contracted slot,
at every metric facet limit `m` whose near-side presentations carry the valency-three anchor
input (`V3Limit m`): the whole near fibre and the whole far fibre at `m` are each empty or a
single class, and they are empty together.  This is exactly `FacetCensus.MetricCensus`'s clause
at `m`, with `ι = Unit`. -/
theorem metricCensus_clause_of_v3 (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (hpar : NoParallel c.core m'.base.1) (hpar' : NoParallel (farCore m').core m'.base.1)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (hm : V3Limit m) :
    ∃ (ι : Type) (τL : {x : FrameClass c.core degree // MSpecializesLeft x m} → ι)
      (τR : {x : FrameClass (farCore m').core degree // MSpecializesRight x m} → ι),
      Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR := by
  have hL := subsingleton_left c.connected hn hd.point hpar m hm
  refine ⟨Unit, fun _ ↦ (), fun _ ↦ (), fun a b _ ↦ Subsingleton.elim a b, fun a b _ ↦ ?_, ?_⟩
  · -- a far-side class forces a near-side presentation, hence the anchor on the far side
    obtain ⟨x, w₀, -, hw₀⟩ := exists_mSpecializesLeft m' hd hG hDegree m a.1 a.2
    obtain ⟨block₀, H₀⟩ := hm w₀ hw₀
    exact (subsingleton_right (farCore m').connected hn hd.point (far_nonloop m') hpar' m H₀
      hw₀).elim a b
  · ext u
    constructor
    · rintro ⟨x, -⟩
      obtain ⟨x', hs'⟩ := exists_mSpecializesRight m' hd hG hDegree m x.1 x.2
      exact ⟨⟨x', hs'⟩, rfl⟩
    · rintro ⟨x', -⟩
      obtain ⟨x, hs⟩ := exists_mSpecializesLeft m' hd hG hDegree m x'.1 x'.2
      exact ⟨⟨x, hs⟩, rfl⟩

/-- **The interface form**: at such a limit the two whole fibres are in bijection
(`FacetCensus.metricCensus_iff`'s clause). -/
theorem nonempty_equiv_of_v3 (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (hpar : NoParallel c.core m'.base.1) (hpar' : NoParallel (farCore m').core m'.base.1)
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (hm : V3Limit m) :
    Nonempty ({x : FrameClass c.core degree // MSpecializesLeft x m} ≃
      {x : FrameClass (farCore m').core degree // MSpecializesRight x m}) := by
  obtain ⟨ι, τL, τR, hL, hR, hrange⟩ :=
    metricCensus_clause_of_v3 m' hd hG hDegree hn hpar hpar' m hm
  exact ⟨FacetCensus.equivOfIndex τL τR hL hR hrange⟩

/-- **`MetricCensus` at a step all of whose metric limits are of valency three** (the
dispatch-free corollary; in general `CensusAssembly` dispatches per limit). -/
theorem metricCensus_of_forall_v3 (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (hpar : NoParallel c.core m'.base.1) (hpar' : NoParallel (farCore m').core m'.base.1)
    (hv3 : ∀ m : MetricFacetLimit c.core (farCore m').core y₀ degree, V3Limit m) :
    FacetCensus.MetricCensus c.core (farCore m').core degree y₀ :=
  fun m ↦ metricCensus_clause_of_v3 m' hd hG hDegree hn hpar hpar' m (hv3 m)

end Census

/-! ## 5.  Instances: where `NoParallel` holds and where it fails -/

section Instances

open DraismaVargas.Count.StepSupplyGenusSix (catCubicCore)
open DraismaVargas.Count.FacetMachine (catLoopMove catLoopCore)

/-- The caterpillar has no slot parallel to the contracted slot of `cat_step`. -/
theorem noParallel_cat : NoParallel catCubicCore.core catLoopMove.base.1 := by decide

/-- **The far core of `cat_step` *has* a slot parallel to the contracted slot** (the digon the
move creates): `NoParallel` fails there, the loop merge of `ValencyThreeLoopMerge` is genuinely
needed, and the census clause here does not apply. -/
theorem not_noParallel_catLoop : ¬ NoParallel catLoopCore.core catLoopMove.base.1 := by decide

/-- **A Whitehead step out of the caterpillar at the stem slot `4`** (vertices `1`, `3`): the
dart of slot `2` at vertex `1` and the dart of slot `5` at vertex `3` change ends. -/
def catStemMove : catCubicCore.graph.MoveData where
  base := (4, false)
  left := (2, false)
  right := (5, false)
  nonloop := by decide
  left_vert := by decide
  left_ne := by decide
  right_vert := by decide
  right_ne := by decide

/-- At the stem step both cores satisfy `NoParallel`, so the census clause's core
hypotheses are inhabited at a genus-six Whitehead step. -/
theorem noParallel_stem :
    NoParallel catCubicCore.core catStemMove.base.1 ∧
      NoParallel (farCore catStemMove).core catStemMove.base.1 := by
  decide

variable {c' : Core (4 * 2 + 2) (6 * 2 + 3)} {y₀ : Fin (6 * 2 + 3) → ℚ} {ε : ℚ}

/-- **`TypeMatch` at the near core of `cat_step`**, by the general route (stage 3 from the
core's pairing, `typeMatch_of_noParallel`). -/
theorem typeMatch_cat' (hd : FacetDatum catCubicCore.core c' (2 + 2) catLoopMove.base.1 y₀ ε) :
    TypeMatch catCubicCore.core y₀ (2 + 2) :=
  ValencyThreeCoreSlots.typeMatch_of_noParallel hd.point noParallel_cat

/-- Every binder of `metricCensus_clause_of_v3` but the limit is inhabited at the stem
step: a Lemma-G facet datum at its slot, and `NoParallel` on both cores. -/
example : ∃ (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
    FacetDatum catCubicCore.core (farCore catStemMove).core (2 + 2) catStemMove.base.1 y₀ ε ∧
      FacetGenericity.FacetGeneric (2 + 2) y₀ ∧ NoParallel catCubicCore.core catStemMove.base.1 ∧
        NoParallel (farCore catStemMove).core catStemMove.base.1 := by
  obtain ⟨y₀, ε, hd, hG⟩ := FacetAdapterPilot.exists_facetDatum_generic catStemMove
    (FacetAdapterPilot.farCore_graph catStemMove) (2 + 2)
  exact ⟨y₀, ε, hd, hG, noParallel_stem⟩

end Instances

end DraismaVargas.Count.ValencyThreeCensus
