import DraismaVargasCount.ValencyTwoResolutionMatch
import DraismaVargasCount.CensusAssembly

/-!
# Valency-two census clause at a resolved datum

**Source.**  Vargas, Part II (arXiv:2609.09109), the valency-two limits, Case `{v2-nd4}`
(`subsec-case-v2`).  Target: `CensusAssembly.V2ClauseSupply`.  Builds on `ValencyTwoSplit`
(stages 1, 2 and the existence halves; `censusAt_of_stages`) and `ValencyTwoResolutionMatch`
(stages 4--5: `splitRigidity`, unconditional at a facet).  It is part of the type-change step,
step 3 of `Assembly`.

## What is proved

* **`v2Limit_of_limitValency`** (the bridge between the two notions of valency-two limit): the
  two-sided `CensusAssembly.V2Limit m` (`LimitValency m 2`) gives the one-sided
  `ValencyTwoSplit.V2Limit m` (from `.1`) and `ValencyTwoSplit.V2Limit (metricSwap m)` (from
  `.2`, through `ofLeft_eq_metricSwap_iff`), at any facet point of a slot that is a non-loop of
  both cores.  Both go through `ValencyTwoSplit.v2Limit_of_facetPoint`, whose divalence
  hypothesis is `mergedValency w = 2` verbatim.
* **`v3Clause_of_resolved_of_pairingMatch`**: at every `ResolvedDatum` (in particular at every
  `FacetDatum` with `FacetGeneric`: the loop resolutions are not used), at every metric facet
  limit of valency two, the census clause (index `Unit`) holds, given stage 3
  (`ValencyTwoSplit.PairingMatch`) on both cores at `y₀`.
* **`v2ClauseSupply_of_pairingMatch`**: `V2ClauseSupply n p degree` from
  `PairingMatchSupply n p degree`, for `3 ≤ degree` and `3 ≤ n`.

## The hypothesis `PairingMatchSupply`

* **`PairingMatchSupply n p degree`** (stage 3 of the valency-two count; Part II's
  Configuration A of Case `{v2-nd4}` read as a reconstruction): at every resolved datum, on
  both cores, two metric isomorphic regrowths with valency-two anchors admit a metric
  isomorphism under which transported labellings are paired alike.  The valency-three analogue
  is `ValencyThreeCoreSlots` (through `NoParallel` and `WallRows`) and `ValencyThreeLoopMerge`;
  at valency two `WallRows` fails at the leaf split, so neither route transfers verbatim.  It is
  the only hypothesis: stage 1 is `v2Limit_of_limitValency`, stage 2 is
  `ValencyTwoSplit.split_eq_of_paired`, stages 4--5 are `ValencyTwoResolutionMatch.splitRigidity`,
  and existence both ways is the link transfer of `ColumnReceiptExport`
  (`ValencyTwoSplit.exists_mSpecializesRight`/`Left`).
* `ValencyTwoPairing.pairingMatchSupply` proves it for `3 ≤ degree`, `3 ≤ n`; hence
  `V2ClauseSupply n p degree` holds with no further hypothesis
  (`ValencyTwoPairing.v2ClauseSupply`), in particular in genus six.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.
-/

namespace DraismaVargas.Count.ValencyTwoCensus

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open FacetAdapterPilot (farCore farCore_graph)
open ValencyThreeGeneral (MetricFacetLimit metricSwap metricSwap_swap)
open CensusAssembly (ResolvedDatum V2ClauseSupply V4ClauseSupply mergedValency LimitValency)

variable {n p degree : ℕ}

/-- A near-side presentation of the swapped limit is a far-side presentation of the limit. -/
theorem ofLeft_eq_metricSwap_iff {c c' : Core n p} {y : Fin p → ℚ}
    (m : MetricFacetLimit c c' y degree) (w : Regrowth c' y degree) :
    MetricFacetLimit.ofLeft (c' := c) w = metricSwap m ↔
      MetricFacetLimit.ofRight (c := c) w = m := by
  constructor
  · intro h
    have := congrArg metricSwap h
    rw [metricSwap_swap] at this
    exact this
  · rintro rfl
    rfl

/-- **The bridge**: the two-sided `CensusAssembly.V2Limit` gives the near-side
`ValencyTwoSplit.V2Limit` at the limit and at its swap. -/
theorem v2Limit_of_limitValency {c c' : Core n p} {y : Fin p → ℚ} {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop : c.tail e₀ ≠ c.head e₀)
    (hloop' : c'.tail e₀ ≠ c'.head e₀)
    (m : MetricFacetLimit c c' y degree) (h : CensusAssembly.V2Limit m) :
    ValencyTwoSplit.V2Limit m ∧ ValencyTwoSplit.V2Limit (metricSwap m) :=
  ⟨ValencyTwoSplit.v2Limit_of_facetPoint m e₀ hpt hloop fun w hw ↦ h.1 w hw,
    ValencyTwoSplit.v2Limit_of_facetPoint (metricSwap m) e₀ hpt hloop' fun w hw ↦
      h.2 w ((ofLeft_eq_metricSwap_iff m w).mp hw)⟩

/-- **Stage 3 on both cores at every resolved datum** -- the one hypothesis of the
valency-two clause.  Interface: consumed by `v2ClauseSupply_of_pairingMatch`; proved by
`ValencyTwoPairing.pairingMatchSupply`; the valency-three analogue is the pairing match of
`ValencyThreeCoreSlots` and `ValencyThreeLoopMerge`. -/
def PairingMatchSupply (n p degree : ℕ) : Prop :=
  ∀ (c c' : CubicCore n p) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
    ResolvedDatum c c' degree e₀ y₀ ε →
      ValencyTwoSplit.PairingMatch c.core y₀ degree ∧
        ValencyTwoSplit.PairingMatch c'.core y₀ degree

/-- **The valency-two census clause at a resolved datum**, from stage 3 on both cores. -/
theorem v3Clause_of_resolved_of_pairingMatch {c c' : CubicCore n p} {e₀ : Fin p}
    {y₀ : Fin p → ℚ} {ε : ℚ} (R : ResolvedDatum c c' degree e₀ y₀ ε) (hDegree : 3 ≤ degree)
    (hn : 3 ≤ n) (h3 : ValencyTwoSplit.PairingMatch c.core y₀ degree)
    (h3' : ValencyTwoSplit.PairingMatch c'.core y₀ degree)
    (ml : MetricFacetLimit c.core c'.core y₀ degree) (hml : CensusAssembly.V2Limit ml) :
    ValencyThreeDigon.V3Clause ml := by
  obtain ⟨hm, hm'⟩ := v2Limit_of_limitValency R.datum.point R.nonloop R.nonloop' ml hml
  have hy : y₀ e₀ = 0 := R.datum.point.1
  have h45 := ValencyTwoResolutionMatch.splitRigidity (core := c.core) (degree := degree)
    c.connected hn hy
  have h45' := ValencyTwoResolutionMatch.splitRigidity (core := c'.core) (degree := degree)
    c'.connected hn hy
  obtain ⟨m, hmv, rfl⟩ := R.move
  have hc' : c' = farCore m := CubicCore.graph_injective (hmv.trans (farCore_graph m).symm)
  subst hc'
  exact ValencyTwoSplit.censusAt_of_stages m R.datum R.generic hDegree h3 h45 h3' h45' ml hm hm'

/-- **Headline: the valency-two clause supply, modulo stage 3.** -/
theorem v2ClauseSupply_of_pairingMatch (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (h : PairingMatchSupply n p degree) : V2ClauseSupply n p degree :=
  fun c c' e₀ y₀ ε R ml hml ↦
    let ⟨h3, h3'⟩ := h c c' e₀ y₀ ε R
    v3Clause_of_resolved_of_pairingMatch R hDegree hn h3 h3' ml hml

end DraismaVargas.Count.ValencyTwoCensus
