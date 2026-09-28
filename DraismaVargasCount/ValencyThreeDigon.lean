import DraismaVargasCount.ValencyThreeLoopMerge

set_option autoImplicit false

/-!
# The valency-three census at digon--digon steps

`ValencyThreeLoopMerge.metricCensus_clause_of_presented` proves the `FacetCensus.MetricCensus`
clause at a valency-three metric limit when each core of the step has no slot parallel to `e₀`
or has *loop presenters* (`LoopPresented`), and `loopPresented_of_move` supplies them from any
move to a core with a loop at an end of `e₀` that has a facet datum **at the same `y₀`**.  At a
digon--digon step neither core of the step is such a loop core.  This file makes the choice:
the per-step consumer (`FacetCensus.typeChangeSupplyPositive_of_metricCensus`) is existential
in `e₀ y₀ ε`, so `y₀` is chosen general for the step **and** for the loop resolutions of both
sides at once.  It is part of the type-change step, step 3 of `Assembly`.

## How

* **The loop resolution is a Whitehead move at the same base dart** (`exists_loopMove`).  On a
  cubic core, if the slot of the non-loop dart `b` at `u` has a parallel slot `s` (darts
  `s_u` at `u`, `s_v` at the other end `v`), the move with `left` the third dart at `u` and
  `right := s_v` makes `s` a loop at `u`.  `e₀` stays a non-loop of the new core (as of every far
  core, `ValencyThreeCensus.far_nonloop`), so `FacetDatum c c''` has the usual shape; the loop at
  an end of `e₀` is `s`, not `e₀`.
* **One finite avoidance for any finite family of cores** (`exists_facetPoint_general_family`,
  `exists_facetStable_family`): the exceptional walls are the proper facet walls of every core's
  normal-form frames plus the universal atlas's facet row walls -- a finite union, as in
  `FacetAdapterPilot.exists_facetPoint_general_generic` for two cores.  The family here is
  `c`, `c'`, and the loop resolutions of `c` and of `c'` (four cores; a side with no parallel slot
  contributes the step's own far core again).
* The step datum, the two resolution data and Lemma G (facet genericity,
  `FacetGenericity.FacetGeneric`) at one `y₀` give `NoParallel ∨ LoopPresented` on both sides,
  and the clause of `ValencyThreeLoopMerge` applies (`exists_facetDatum_v3Clause`).

## What is proved

* §1 `exists_facetPoint_general_family`, `exists_facetStable_family`.
* §2 **`exists_loopMove`**, `exists_loopMove_side`.
* §3 `V3Clause` (the `MetricCensus` clause at one limit), **`exists_facetDatum_v3Clause`** (at a
  named move), **`exists_facetDatum_v3Clause_of_step`** (at a `Step`, in the consumer's shape:
  slot non-loop in the far core, Lemma G, the clause at every valency-three metric limit).
* §4 `exists_loopMove_digon` (at `ValencyThreeLoopMerge.digonMove` the loop resolution exists
  and `e₀` is not a loop of it) and an `example` (the clause at every valency-three limit of the
  digon--digon step, where `LoopMerge` fails on both sides).

## Hypotheses

* **`V3Limit`**, limit by limit.  `exists_facetDatum_v3Clause_of_step` needs nothing else
  (`3 ≤ degree`, `3 ≤ n` aside).  The valency-two and valency-four clauses must be added at the
  same facet datum.  `CensusAssembly` does this at a family-general datum
  (`CensusAssembly.ResolvedDatum`): `CensusAssembly.valency_trichotomy` dispatches every metric
  facet limit on its valency, the valency-two and valency-four clauses are theorems with no
  hypothesis (`ValencyTwoPairing.v2ClauseSupply`,
  `ValencyFourRealisation.v4ClauseSupply_genusSix`), and `CensusAssembly.metricCensus_of_resolved`
  proves `MetricCensus` at every resolved datum.
* Valency-two and valency-four limits are not treated here.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

namespace DraismaVargas.Count.ValencyThreeDigon

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open DraismaVargas.Count.SegmentWalls (Frame NFFrame)
open DraismaVargas.Count.FacetMachine
open DraismaVargas.Count.FacetAdapterPilot (farCore revMove revMove_base farCore_revMove
  farCore_graph sharedContractionSlot_of_move)
open ValencyThreeCoreSlots (NoParallel)
open ValencyThreeLoopMerge (LoopAtEnd LoopPresented)

variable {n p : ℕ}

/-! ## 1.  One facet point, general for any finite family of cores -/

section Family

open FacetGenericity FiniteAtlasMarch

/-- **Facet generality (`FacetGeneral`) and Lemma G (`FacetGeneric`) for a finite family of
cores at once**: one finite avoidance over the
union of every core's proper facet walls and the universal atlas's facet row walls.  This is
`FacetAdapterPilot.exists_facetPoint_general_generic` with the pair of cores replaced by a
family. -/
theorem exists_facetPoint_general_family {ι : Type} [Fintype ι] (cs : ι → Core n p)
    (degree : ℕ) (e₀ : Fin p) :
    ∃ y₀ : Fin p → ℚ, FacetPoint e₀ y₀ ∧ (∀ i, FacetGeneral (cs i) degree e₀ y₀) ∧
      FacetGeneric degree y₀ := by
  classical
  let _ : ∀ i, Fintype (NFFrame (cs i) degree) := fun _ ↦ Fintype.ofFinite _
  let W : (Σ i, NFFrame (cs i) degree × Fin p) ⊕ (MatrixAtlas.chart (Fin p) degree × Fin p) →
      RationalAffineWall (Fin p) :=
    Sum.elim (fun x ↦ facetWall (NFFrame.toFrame x.2.1) e₀ x.2.2)
      (fun x ↦ facetRowWall (MatrixAtlas.atlasMatrix x.1) e₀ x.2)
  obtain ⟨z, hpos, havoid⟩ :=
    RationalAffineWall.exists_avoids_preserving_positive
      (fun x : {x // (W x).Proper} ↦ W x.1) SegmentWalls.coordinateWall (fun _ ↦ 1)
      (fun x ↦ x.2) (by intro l; rw [SegmentWalls.eval_coordinateWall]; norm_num)
  refine ⟨Function.update z e₀ 0, ⟨Function.update_self e₀ 0 z, fun e he ↦ ?_⟩,
    fun i ↦ ?_, ?_⟩
  · rw [Function.update_of_ne he]
    have h := hpos e
    rwa [SegmentWalls.eval_coordinateWall] at h
  · exact facetGeneral_of_avoid (cs i) degree e₀ z fun r col hprop ↦
      havoid ⟨Sum.inl ⟨i, r, col⟩, hprop⟩
  · refine facetGeneric_of_avoids degree e₀ _ (Function.update_self _ _ _) ?_
    intro event
    rw [eval_update_of_coefficient_eq_zero _ e₀ (facetRowWall_coefficient_facet _ e₀ event.2)]
    exact havoid ⟨Sum.inr event, facetRowWall_proper _ e₀ event.2⟩

/-- **One radius of stability for a finite family of cores**: the minimum of the radii of
`FacetMachine.exists_facetStable`. -/
theorem exists_facetStable_family {ι : Type} [Finite ι] (cs : ι → Core n p) {degree : ℕ}
    {e₀ : Fin p} {y₀ : Fin p → ℚ} (hy₀ : y₀ e₀ = 0)
    (hgen : ∀ i, FacetGeneral (cs i) degree e₀ y₀) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ i, FacetStable (cs i) degree e₀ y₀ ε := by
  choose ε₀ hε₀ hst using fun i ↦ exists_facetStable (cs i) degree hy₀ (hgen i)
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_of_finite ε₀ hε₀
  exact ⟨δ, hδ, fun i ↦ hst i δ hδ (hle i)⟩

end Family

/-! ## 2.  The loop resolution of a digon is a Whitehead move at the same base dart -/

section LoopMove

/-- **The loop resolution exists.**  If the slot of a non-loop dart `b` of a cubic core has a
parallel slot `s`, then the move at `b` that sends the third dart `a` at `b`'s vertex `u` across
and brings `s`'s dart at the other end to `u` makes `s` a loop at `u`, an end of `b`'s slot. -/
theorem exists_loopMove (c : CubicCore n p) (b : Fin p × Bool)
    (hb : c.graph.vert (c.graph.op b) ≠ c.graph.vert b) (hpar : ¬ NoParallel c.core b.1) :
    ∃ m'' : c.graph.MoveData, m''.base = b ∧ LoopAtEnd (farCore m'').core b.1 := by
  classical
  obtain ⟨e₀, β⟩ := b
  simp only [NoParallel, not_forall, not_or] at hpar
  obtain ⟨s, hs, h1, h2⟩ := hpar
  have hvf : ∀ e, c.graph.vert (e, false) = c.core.tail e := fun _ ↦ rfl
  have hvt : ∀ e, c.graph.vert (e, true) = c.core.head e := fun _ ↦ rfl
  have hop : c.graph.op (e₀, β) = (e₀, !β) := rfl
  rw [hop] at hb
  -- the two ends `u`, `v` of `e₀` both meet `s`
  have huv : 0 < coreIncidence c.core (c.graph.vert (e₀, β)) s ∧
      0 < coreIncidence c.core (c.graph.vert (e₀, !β)) s := by
    cases β
    · exact ⟨Nat.pos_of_ne_zero h1, Nat.pos_of_ne_zero h2⟩
    · exact ⟨Nat.pos_of_ne_zero h2, Nat.pos_of_ne_zero h1⟩
  obtain ⟨hu, hv⟩ := huv
  -- `s`'s dart at `u`, and its opposite at `v`
  obtain ⟨γ, hγ, hγ'⟩ : ∃ γ : Bool, c.graph.vert (s, γ) = c.graph.vert (e₀, β) ∧
      c.graph.vert (s, !γ) = c.graph.vert (e₀, !β) := by
    unfold coreIncidence at hu hv
    by_cases ht : c.core.tail s = c.graph.vert (e₀, β)
    · refine ⟨false, ht, ?_⟩
      show c.core.head s = _
      by_contra hh
      rw [if_neg hh] at hv
      have : c.core.tail s = c.graph.vert (e₀, !β) := by
        by_contra ht'; rw [if_neg ht'] at hv; omega
      exact hb (this.symm.trans ht)
    · rw [if_neg ht] at hu
      have hh : c.core.head s = c.graph.vert (e₀, β) := by
        by_contra hh; rw [if_neg hh] at hu; omega
      refine ⟨true, hh, ?_⟩
      show c.core.tail s = _
      by_contra ht'
      rw [if_neg ht'] at hv
      have : c.core.head s = c.graph.vert (e₀, !β) := by
        by_contra hh'; rw [if_neg hh'] at hv; omega
      exact hb (this.symm.trans hh)
  -- the third dart at `u`
  obtain ⟨a, ha⟩ : (((Finset.univ.filter fun d ↦ c.graph.vert d = c.graph.vert (e₀, β)).erase
      (e₀, β)).erase (s, γ)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem, Finset.card_erase_of_mem,
      c.graph.card_fibre]
    · simp
    · simp
    · simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ hs (congrArg Prod.fst h), hγ⟩
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨has, hae, hau⟩ := ha
  let m'' : c.graph.MoveData :=
    { base := (e₀, β)
      left := a
      right := (s, !γ)
      nonloop := by rw [hop]; exact hb
      left_vert := hau
      left_ne := hae
      right_vert := by rw [hop]; exact hγ'
      right_ne := by rw [hop]; exact fun h ↦ hs (congrArg Prod.fst h) }
  have hsu : ∀ γ' : Bool, (c.graph.move m'').vert (s, γ') = c.graph.vert (e₀, β) := by
    intro γ'
    rw [CubicDarts.CubicDartGraph.move_vert]
    by_cases hg : γ' = γ
    · subst hg
      rw [m''.perm_of_ne (fun h ↦ has h.symm) (by simp [m''])]
      exact hγ
    · have : γ' = !γ := by cases γ <;> cases γ' <;> simp_all
      subst this
      exact (congrArg c.graph.vert m''.perm_right).trans hau
  have hbase : (c.graph.move m'').vert (e₀, β) = c.graph.vert (e₀, β) := by
    rw [CubicDarts.CubicDartGraph.move_vert]
    exact congrArg c.graph.vert m''.perm_base
  refine ⟨m'', rfl, s, ?_, ?_⟩
  · show (c.graph.move m'').vert (s, false) = (c.graph.move m'').vert (s, true)
    rw [hsu, hsu]
  · show (c.graph.move m'').vert (s, false) = (c.graph.move m'').vert (e₀, false) ∨
      (c.graph.move m'').vert (s, false) = (c.graph.move m'').vert (e₀, true)
    rw [hsu]
    cases β
    · exact Or.inl hbase.symm
    · exact Or.inr hbase.symm

/-- **A side of a step always has a move to use**: either the side has no slot parallel to the
contracted slot, or there is a move at the same base dart to a core with a loop at an end of it
(the loop resolution, `exists_loopMove`). -/
theorem exists_loopMove_side (c : CubicCore n p) (m : c.graph.MoveData) :
    ∃ mL : c.graph.MoveData, mL.base = m.base ∧
      (NoParallel c.core m.base.1 ∨ LoopAtEnd (farCore mL).core m.base.1) := by
  by_cases h : NoParallel c.core m.base.1
  · exact ⟨m, rfl, Or.inl h⟩
  · obtain ⟨mL, hb, hl⟩ := exists_loopMove c m.base m.nonloop h
    exact ⟨mL, hb, Or.inr hl⟩

end LoopMove

/-! ## 3.  One facet datum for the step and both loop resolutions -/

section Step

open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight)
open ValencyThreeSplit (V3Limit)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyThreeLoopMerge (loopPresented_of_move metricCensus_clause_of_presented)

variable {degree : ℕ}

/-- The valency-three `MetricCensus` clause at one metric limit (the shape of
`FacetCensus.MetricCensus`, index `Unit`). -/
def V3Clause {c c' : Core n p} {y₀ : Fin p → ℚ} (m : MetricFacetLimit c c' y₀ degree) : Prop :=
  ∃ (ι : Type) (τL : {x : FrameClass c degree // MSpecializesLeft x m} → ι)
    (τR : {x : FrameClass c' degree // MSpecializesRight x m} → ι),
    Function.Injective τL ∧ Function.Injective τR ∧ Set.range τL = Set.range τR

/-- **The simultaneous choice.**  At every Whitehead move `m` there is one facet point `y₀`
(with Lemma G) and one radius `ε` giving a facet datum for the step **and** for the loop
resolution of each side that has a slot parallel to `e₀` (`exists_loopMove_side`): four cores,
one finite avoidance (`exists_facetPoint_general_family`).  Both sides then satisfy
`NoParallel ∨ LoopPresented` (`ValencyThreeLoopMerge.loopPresented_of_move`), and
`ValencyThreeLoopMerge.metricCensus_clause_of_presented` gives the clause at every
valency-three metric limit --
digon--digon steps included. -/
theorem exists_facetDatum_v3Clause {c : CubicCore n p} (m : c.graph.MoveData)
    (hDegree : 3 ≤ degree) (hn : 3 ≤ n) :
    ∃ (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core (farCore m).core degree m.base.1 y₀ ε ∧
      FacetGenericity.FacetGeneric degree y₀ ∧
      ∀ ml : MetricFacetLimit c.core (farCore m).core y₀ degree, V3Limit ml → V3Clause ml := by
  obtain ⟨mL, hbL, hL⟩ := exists_loopMove_side c m
  obtain ⟨mR, hbR, hR⟩ := exists_loopMove_side (farCore m) (revMove m)
  rw [revMove_base] at hbR hR
  let cs : Fin 4 → Core n p :=
    ![c.core, (farCore m).core, (farCore mL).core, (farCore mR).core]
  obtain ⟨y₀, hpt, hgen, hG⟩ := exists_facetPoint_general_family cs degree m.base.1
  obtain ⟨ε, hε, hst⟩ := exists_facetStable_family cs hpt.1 hgen
  have hd : FacetDatum c.core (farCore m).core degree m.base.1 y₀ ε :=
    ⟨sharedContractionSlot_of_move m (farCore_graph m), hpt, hgen 0, hgen 1, hε, hst 0, hst 1⟩
  have hdL : FacetDatum c.core (farCore mL).core degree mL.base.1 y₀ ε := by
    rw [hbL]
    have hsh := sharedContractionSlot_of_move mL (farCore_graph mL)
    rw [hbL] at hsh
    exact ⟨hsh, hpt, hgen 0, hgen 2, hε, hst 0, hst 2⟩
  have hdR : FacetDatum (farCore m).core (farCore mR).core degree mR.base.1 y₀ ε := by
    rw [hbR]
    have hsh := sharedContractionSlot_of_move mR (farCore_graph mR)
    rw [hbR] at hsh
    exact ⟨hsh, hpt, hgen 1, hgen 3, hε, hst 1, hst 3⟩
  have hP : NoParallel c.core m.base.1 ∨ LoopPresented c.core m.base.1 y₀ degree := by
    refine hL.imp id fun hl ↦ ?_
    have h := loopPresented_of_move mL hdL hG hDegree (by rw [hbL]; exact hl)
    rwa [hbL] at h
  have hP' : NoParallel (farCore m).core m.base.1 ∨
      LoopPresented (farCore m).core m.base.1 y₀ degree := by
    refine hR.imp id fun hl ↦ ?_
    have h := loopPresented_of_move mR hdR hG hDegree (by rw [hbR]; exact hl)
    rwa [hbR] at h
  exact ⟨y₀, ε, hd, hG, fun ml hml ↦
    metricCensus_clause_of_presented m hd hG hDegree hn hP hP' ml hml⟩

/-- **The same at a step, in the per-step consumer's shape**: a facet datum at a slot that is
not a loop of the far core, with Lemma G, at which the valency-three clause holds at every
valency-three metric limit.  This is the dispatch-ready form: the clause is stated limit by
limit, so the valency-two and valency-four clauses can be added at the same `y₀`. -/
theorem exists_facetDatum_v3Clause_of_step {c c' : CubicCore n p} (h : Step c c')
    (hDegree : 3 ≤ degree) (hn : 3 ≤ n) :
    ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core c'.core degree e₀ y₀ ε ∧
      c'.core.tail e₀ ≠ c'.core.head e₀ ∧ FacetGenericity.FacetGeneric degree y₀ ∧
      ∀ ml : MetricFacetLimit c.core c'.core y₀ degree, V3Limit ml → V3Clause ml := by
  obtain ⟨m, hm⟩ := h
  have hc' : c' = farCore m := CubicCore.graph_injective (hm.trans (farCore_graph m).symm)
  subst hc'
  obtain ⟨y₀, ε, hd, hG, hcl⟩ := exists_facetDatum_v3Clause m hDegree hn
  exact ⟨m.base.1, y₀, ε, hd, ValencyThreeCensus.far_nonloop m, hG, hcl⟩

end Step

/-! ## 4.  The genus-six digon--digon step -/

section Instances

open DraismaVargas.Count.FacetMachine (catLoopCore)
open ValencyThreeLoopMerge (digonMove LoopMerge)
open ValencyThreeGeneral (MetricFacetLimit)
open ValencyThreeSplit (V3Limit)

/-- **The loop resolution exists at the digon--digon step**, as a Whitehead
move of `catLoopCore` at the same base dart, and its slot `e₀` is not a loop of the loop core
(so `FacetDatum catLoopCore c''` has the step consumer's shape). -/
theorem exists_loopMove_digon :
    ∃ mL : catLoopCore.graph.MoveData, mL.base = digonMove.base ∧
      LoopAtEnd (farCore mL).core digonMove.base.1 ∧
      (farCore mL).core.tail digonMove.base.1 ≠ (farCore mL).core.head digonMove.base.1 := by
  obtain ⟨mL, hb, hl⟩ := exists_loopMove catLoopCore digonMove.base digonMove.nonloop
    (by decide)
  refine ⟨mL, hb, hl, ?_⟩
  have := ValencyThreeCensus.far_nonloop mL
  rwa [hb] at this

/-- **The clause's hypotheses are inhabited at the digon--digon step**: the step datum, the
loop resolutions and the
valency-three clause at every valency-three metric limit, where `LoopMerge` fails on both sides
(`ValencyThreeLoopMerge.not_loopMerge_digon`). -/
example : ∃ (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
    FacetDatum catLoopCore.core (farCore digonMove).core (2 + 2) digonMove.base.1 y₀ ε ∧
      FacetGenericity.FacetGeneric (2 + 2) y₀ ∧
      ∀ ml : MetricFacetLimit catLoopCore.core (farCore digonMove).core y₀ (2 + 2),
        V3Limit ml → V3Clause ml :=
  exists_facetDatum_v3Clause digonMove (by norm_num) (by norm_num)

end Instances

end DraismaVargas.Count.ValencyThreeDigon
