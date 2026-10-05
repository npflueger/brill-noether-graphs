module

public import DraismaVargasCount.ValencyThreeDigon
public import DraismaVargasCount.ValencyFourSplit

@[expose] public section

set_option autoImplicit false

/-!
# The type-change census: valency dispatch, and the valency-two and valency-four clauses

Step 3 of the genus-six assembly (`Assembly.typeChanges_genusSix`) applies
`FacetCensus.typeChangeSupplyPositive_of_metricCensus`, which needs, at every Whitehead step
between cubic genus-six cores, *some* facet datum with a non-loop far slot at which
`FacetCensus.MetricCensus` holds.  This file proves that input (`stepCensus_of_supplies`) from
three per-limit clauses, one for each possible valency of the merged target vertex: the
valency-three clause is proved here (`v3Clause_of_resolved`), and the valency-two and
valency-four clauses are named (`V2ClauseSupply`, `V4ClauseSupply`) and proved elsewhere.

## The valency dispatch

At a facet point of a slot that is a non-loop of the regrowth's core, the merged target vertex
of every regrowth has valency two, three or four (`mergedValency_cases`, from
`MonovalentWall.card_incidentEdges_merge_eq_two_three_or_four`: Equation (C) of Part I at the
merged vertex bounds it by four, connectivity by one, and a leaf--divalent endpoint pair
contradicts the contraction forest).  **The valency is an invariant of the metric facet limit,
on both sides** (`mergedValency_eq_of_iso`, `limitValency_iff_exists`): every limit has a source
vertex of surviving valency four -- at every valency, by the producers
`NonTrivalentAnchorValency.exists_wallBlock_nonDanglingValency_eq_four_of_twoStar`,
`ValencyThreeSplit.exists_regrowthAnchor`, `ValencyFourSplit.exists_regrowthAnchor4` -- every
such vertex lies over the merged vertex (`ValencyThreeCensus.over_merged_of_nd_four`), and any
geometric isomorphism of limits preserves surviving valency and target valency.  The argument
uses only a `GeometricDatumIso`, so the valency is already an invariant of the *coarse*
`FacetLimit`.  Hence `valency_trichotomy`: every metric facet limit is a valency-two limit
(`V2Limit := LimitValency m 2`), a `V3Limit`, or a `V4Limit`, exclusively
(`limitValency_unique`).

## The datum

`ResolvedDatum` is the datum chosen by `ValencyThreeDigon.exists_facetDatum_v3Clause` (one
finite avoidance over four cores: the step's two and the loop resolutions of each side), kept
as data: the move, the step's facet datum, facet genericity
(`FacetGenericity.FacetGeneric`) at `y₀`, and a loop resolution of each side at the same
`(y₀, ε)`.  `exists_resolvedDatum` produces it at every step; `v3Clause_of_resolved` proves
the valency-three clause at **every** resolved datum.  The valency-two and valency-four
clauses are required at the same data.

## What is proved

* §1 `mergedValency`, `mergedValency_cases`, `exists_nd_four`, **`mergedValency_eq_of_iso`**.
* §2 `LimitValency`, `repValency`, `repValency_eq_of_same`, **`limitValency_iff_exists`**,
  `limitValency_unique`, **`exists_limitValency`**, `v3Limit_of_limitValency`,
  `v4Limit_of_limitValency`, `V2Limit`, **`valency_trichotomy`**.
* §3 `ResolvedSide`, **`ResolvedDatum`** (`step`, `nonloop`, `nonloop'`, `toGeneric`),
  **`exists_resolvedDatum`**, `noParallel_or_loopPresented`, **`v3Clause_of_resolved`**.
* §4 the clauses **`V2ClauseSupply`**, **`V4ClauseSupply`**, `V4InputsSupply` (the two
  inputs of the valency-four clause, `v4ClauseSupply_of_inputs`),
  **`metricCensus_of_resolved`**, **`supplies_iff`** (the two clauses are *equivalent* to
  `MetricCensus` at every resolved datum: nothing is lost), and **`stepCensus_of_supplies`**
  (the input of `FacetCensus.typeChangeSupplyPositive_of_metricCensus`).
* §5 `digon_resolved` (the genus-six digon--digon step) and an `example`.

## Remarks on the dispatch

* **Every metric limit at a genus-six facet point has valency two, three or four**, and more
  generally at any genus and any degree, at any facet point of a slot that is a non-loop of
  both cores (true at every step datum).  The bound four is Equation (C) at the merged vertex
  (`WallProgress.card_incidentEdges_merge_le_four`), with endpoint valencies in `[1, 3]` by
  change-minimality: the target tree has leaves and divalent vertices, and the merged valency
  is `val a + val b - 2` over the splits `(1,3)`, `(2,2)` [two], `(2,3)` [three], `(3,3)`
  [four].  Valency one is excluded by `MonovalentWall.card_incidentEdges_merge_ne_one` (no
  genus-six input, no facet genericity).  **Valency two does not arise from the loop or digon
  collapse**: it is a property of the target (a `(2,2)` or leaf split), and the core's loops
  and digons (`NoParallel`, `LoopPresented`) are an orthogonal issue that arises at every
  valency.  The near-side-only `V3Limit` is harmless: `LimitValency` is two-sided and implies
  it.
* **The clauses are required only at resolved data.**  A resolved datum is a generic step
  facet datum (`ResolvedDatum.toGeneric`), so clauses holding at every generic facet datum
  would imply them.  The valency-three clause is itself proved only at resolved data (the
  loop merge needs the loop resolution's facet datum at the same `y₀`).  At valency four no
  loop merge occurs: at a valency-four facet the core never has a slot parallel to the
  vanishing slot (`ValencyFourRigidity.noParallel_of_anchor4`).

## Where the two named clauses are proved

At genus six both hold with no hypothesis.  `V2ClauseSupply (4*2+2) (6*2+3) (2+2)` is
`ValencyTwoPairing.v2ClauseSupply` (with `ValencyTwoResolutionMatch`), and
`V4ClauseSupply (4*2+2) (6*2+3) (2+2)` is `ValencyFourRealisation.v4ClauseSupply_genusSix`
(`K`-injectivity is `ValencyFourRigidity`, per-`K` realisation is
`ValencyFourRealisation.hex_of_resolved`).  Hence `stepCensus_of_supplies` holds at genus six
with no hypothesis, which is how `Assembly.typeChanges_genusSix` uses it.  The antecedent of
both clauses, `ResolvedDatum`, is inhabited at the genus-six digon--digon step
(`digon_resolved`).
-/

namespace DraismaVargas.Count.CensusAssembly

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification W4StableSource
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft MSpecializesRight
  SameMetricLimit)

variable {n p degree : ℕ}

section Valency

variable {core : Core n p} {y : Fin p → ℚ}

/-- The valency of the merged target vertex of a regrowth's limit. -/
noncomputable def mergedValency (w : Regrowth core y degree) : ℕ :=
  (GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
    ⟨(w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1,
      fst_ne_snd (w.frame.edgeOf w.column)⟩).card

/-- **The merged valency is two, three or four** at a facet regrowth of a non-loop slot. -/
theorem mergedValency_cases (w : Regrowth core y degree) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop : core.tail e₀ ≠ core.head e₀) :
    mergedValency w = 2 ∨ mergedValency w = 3 ∨ mergedValency w = 4 :=
  MonovalentWall.card_incidentEdges_merge_eq_two_three_or_four w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) w.frame.fullDim
    (ValencyThreeCoreSlots.forest_of_facetPoint w hpt hloop)

/-- **Every facet regrowth of a non-loop slot has a limit vertex of surviving valency four**
(the anchor), at each of the three valencies. -/
theorem exists_nd_four (w : Regrowth core y degree) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (hloop : core.tail e₀ ≠ core.head e₀) :
    ∃ X : w.limit.SourceVertex, nonDanglingValency w.limit X = 4 := by
  rcases mergedValency_cases w hpt hloop with h | h | h
  · obtain ⟨hRows, hFacetZero, hZero, hPos⟩ := ValencyFourSplit.facet_rows w e₀ hpt
    obtain ⟨anchor, hFour⟩ :=
      NonTrivalentAnchorValency.exists_wallBlock_nonDanglingValency_eq_four_of_twoStar
        w.frame.data w.frame.fullDim rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) (W2R1Target.TwoStar.of_card h)
        (ValencyThreeCoreSlots.forest_of_facetPoint w hpt hloop) (w.frame.coordsAt y)
        (w.frame.slot.symm e₀) hRows hZero hPos hFacetZero
    exact ⟨_, hFour⟩
  · obtain ⟨block, H⟩ := ValencyThreeSplit.exists_regrowthAnchor w e₀ hpt hloop h
    exact ⟨_, H.nd4⟩
  · obtain ⟨block, H⟩ := ValencyFourSplit.exists_regrowthAnchor4 w e₀ hpt hloop h
    exact ⟨_, H.nd4⟩

/-- **The merged valency is carried by any isomorphism of limits**, between facet regrowths of
two cores (either may equal the other) at which the slot is not a loop: the limit of the first
has a vertex of surviving valency four (`exists_nd_four`), every such vertex lies over the
merged vertex (`ValencyThreeCensus.over_merged_of_nd_four`), and the isomorphism preserves
surviving valency and target valency. -/
theorem mergedValency_eq_of_iso {c₁ c₂ : Core n p} (w₁ : Regrowth c₁ y degree)
    (w₂ : Regrowth c₂ y degree) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop₁ : c₁.tail e₀ ≠ c₁.head e₀) (hloop₂ : c₂.tail e₀ ≠ c₂.head e₀)
    (ψ : GeometricDatumIso w₁.limit w₂.limit) : mergedValency w₂ = mergedValency w₁ := by
  obtain ⟨X, hX⟩ := exists_nd_four w₁ hpt hloop₁
  have hc₁ := WallAdmissibility.danglingCompatible_of_contractionForest w₁.frame.data rfl
    (fst_ne_snd (w₁.frame.edgeOf w₁.column)) (w₁.frame.numEdges_edgeOf w₁.column)
    (ValencyThreeCoreSlots.forest_of_facetPoint w₁ hpt hloop₁)
  have hc₂ := WallAdmissibility.danglingCompatible_of_contractionForest w₂.frame.data rfl
    (fst_ne_snd (w₂.frame.edgeOf w₂.column)) (w₂.frame.numEdges_edgeOf w₂.column)
    (ValencyThreeCoreSlots.forest_of_facetPoint w₂ hpt hloop₂)
  have h1 := ValencyThreeCensus.over_merged_of_nd_four w₁ hc₁ X hX
  have h4 : nonDanglingValency w₂.limit (ψ.sourceVertexEquiv X) = 4 :=
    (ψ.nonDanglingValency_map (ValencyThreeSplit.connected_limit w₁) X).trans hX
  have h2 := ValencyThreeCensus.over_merged_of_nd_four w₂ hc₂ _ h4
  have h2' : ψ.targetVertex X.1.1 = _ := h2
  rw [h1] at h2'
  unfold mergedValency
  rw [← h2']
  exact ψ.incidentEdges_card_map _

end Valency

/-! ## 2.  The valency of a metric facet limit -/

section LimitValency

variable {c c' : Core n p} {y : Fin p → ℚ}

/-- **The valency of a metric facet limit is `k`**: every regrowth presenting it, on either
side, has merged valency `k`.  At a facet point of a slot that is a non-loop of both cores
this is equivalent to "some regrowth presenting `m` has merged valency `k`"
(`limitValency_iff_exists`). -/
def LimitValency (m : MetricFacetLimit c c' y degree) (k : ℕ) : Prop :=
  (∀ w : Regrowth c y degree, MetricFacetLimit.ofLeft (c' := c') w = m → mergedValency w = k) ∧
  (∀ w : Regrowth c' y degree, MetricFacetLimit.ofRight (c := c) w = m → mergedValency w = k)

/-- The merged valency of any representative of a metric facet limit. -/
noncomputable def repValency :
    FacetMachine.FacetRegrowth c c' y degree → ℕ
  | Sum.inl w => mergedValency w
  | Sum.inr w => mergedValency w

/-- Representatives of one metric facet limit have one merged valency. -/
theorem repValency_eq_of_same {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop : c.tail e₀ ≠ c.head e₀) (hloop' : c'.tail e₀ ≠ c'.head e₀)
    (a b : FacetMachine.FacetRegrowth c c' y degree) (h : SameMetricLimit a b) :
    repValency b = repValency a := by
  obtain ⟨ψ, -⟩ := h
  rcases a with w₁ | w₁ <;> rcases b with w₂ | w₂
  · exact mergedValency_eq_of_iso w₁ w₂ hpt hloop hloop ψ
  · exact mergedValency_eq_of_iso w₁ w₂ hpt hloop hloop' ψ
  · exact mergedValency_eq_of_iso w₁ w₂ hpt hloop' hloop ψ
  · exact mergedValency_eq_of_iso w₁ w₂ hpt hloop' hloop' ψ

/-- **Valency is an invariant of the metric facet limit, on both sides.** -/
theorem limitValency_iff_exists {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop : c.tail e₀ ≠ c.head e₀) (hloop' : c'.tail e₀ ≠ c'.head e₀)
    (m : MetricFacetLimit c c' y degree) (k : ℕ) :
    LimitValency m k ↔
      ∃ a : FacetMachine.FacetRegrowth c c' y degree, Quotient.mk _ a = m ∧
        repValency a = k := by
  constructor
  · rintro ⟨hL, hR⟩
    obtain ⟨a, ha⟩ := Quotient.exists_rep m
    refine ⟨a, ha, ?_⟩
    rcases a with w | w
    · exact hL w ha
    · exact hR w ha
  · rintro ⟨a, rfl, hk⟩
    refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
    · have := repValency_eq_of_same hpt hloop hloop' a (Sum.inl w) (Quotient.exact hw.symm)
      exact this.trans hk
    · have := repValency_eq_of_same hpt hloop hloop' a (Sum.inr w) (Quotient.exact hw.symm)
      exact this.trans hk

/-- **The valency is unique**: a metric facet limit has at most one valency. -/
theorem limitValency_unique {m : MetricFacetLimit c c' y degree} {k k' : ℕ}
    (h : LimitValency m k) (h' : LimitValency m k') : k = k' := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep m
  rcases a with w | w
  · exact (h.1 w ha).symm.trans (h'.1 w ha)
  · exact (h.2 w ha).symm.trans (h'.2 w ha)

/-- **The valency dispatch**: at a facet point of a slot that is a non-loop of both cores,
every metric facet limit has a valency, and it is two, three or four. -/
theorem exists_limitValency {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop : c.tail e₀ ≠ c.head e₀) (hloop' : c'.tail e₀ ≠ c'.head e₀)
    (m : MetricFacetLimit c c' y degree) :
    ∃ k, (k = 2 ∨ k = 3 ∨ k = 4) ∧ LimitValency m k := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep m
  refine ⟨repValency a, ?_, (limitValency_iff_exists hpt hloop hloop' m _).mpr ⟨a, ha, rfl⟩⟩
  rcases a with w | w
  · exact mergedValency_cases w hpt hloop
  · exact mergedValency_cases w hpt hloop'

/-- A valency-three metric facet limit is a `V3Limit`. -/
theorem v3Limit_of_limitValency {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop : c.tail e₀ ≠ c.head e₀) {m : MetricFacetLimit c c' y degree}
    (h : LimitValency m 3) : ValencyThreeSplit.V3Limit m :=
  ValencyThreeSplit.v3Limit_of_facetPoint m e₀ hpt hloop h.1

/-- A valency-four metric facet limit is a `V4Limit`. -/
theorem v4Limit_of_limitValency {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop : c.tail e₀ ≠ c.head e₀) (hloop' : c'.tail e₀ ≠ c'.head e₀)
    {m : MetricFacetLimit c c' y degree} (h : LimitValency m 4) : ValencyFourSplit.V4Limit m :=
  ValencyFourSplit.v4Limit_of_facetPoint m e₀ hpt hloop hloop' h.1 h.2

/-- **A valency-two metric facet limit**: every presenting regrowth, on either side, has a
divalent merged target vertex; this is `LimitValency m 2`.  The near-side anchor predicate
`ValencyTwoSplit.V2Limit` follows from it, at `m` from the first half and at `metricSwap m`
from the second (`ValencyTwoCensus.v2Limit_of_limitValency`, through
`ValencyTwoSplit.v2Limit_of_facetPoint`). -/
abbrev V2Limit (m : MetricFacetLimit c c' y degree) : Prop := LimitValency m 2

/-- **The trichotomy**: every metric facet limit at such a facet point is a valency-two limit,
a valency-three `V3Limit`, or a valency-four `V4Limit`, and these are exclusive. -/
theorem valency_trichotomy {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hloop : c.tail e₀ ≠ c.head e₀) (hloop' : c'.tail e₀ ≠ c'.head e₀)
    (m : MetricFacetLimit c c' y degree) :
    V2Limit m ∨ (LimitValency m 3 ∧ ValencyThreeSplit.V3Limit m) ∨
      (LimitValency m 4 ∧ ValencyFourSplit.V4Limit m) := by
  obtain ⟨k, hk, h⟩ := exists_limitValency hpt hloop hloop' m
  rcases hk with rfl | rfl | rfl
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, v3Limit_of_limitValency hpt hloop h⟩)
  · exact Or.inr (Or.inr ⟨h, v4Limit_of_limitValency hpt hloop hloop' h⟩)

end LimitValency

/-! ## 3.  The resolved step datum: one facet point for the step and both loop resolutions -/

section Resolved

open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open FacetMachine (FacetDatum)
open FacetAdapterPilot (farCore revMove revMove_base farCore_graph sharedContractionSlot_of_move)
open ValencyThreeCoreSlots (NoParallel)
open ValencyThreeLoopMerge (LoopAtEnd LoopPresented loopPresented_of_move
  metricCensus_clause_of_presented)

/-- **A loop-resolved side** at a facet point: either the core has no slot parallel to `e₀`,
or some Whitehead move at `e₀` reaches a core with a loop at an end of `e₀` and has a facet
datum at the same `(y₀, ε)`.  This is the per-side input of `ValencyThreeDigon`
(`ValencyThreeDigon.exists_loopMove_side` plus the family choice). -/
def ResolvedSide (c : CubicCore n p) (degree : ℕ) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ) :
    Prop :=
  NoParallel c.core e₀ ∨ ∃ mL : c.graph.MoveData, mL.base.1 = e₀ ∧
    LoopAtEnd (farCore mL).core e₀ ∧ FacetDatum c.core (farCore mL).core degree e₀ y₀ ε

/-- **The resolved step datum.**  A Whitehead move from `c` to `c'` at base slot `e₀`, a facet
datum for the step at `(e₀, y₀, ε)`, facet genericity (`FacetGenericity.FacetGeneric`) at
`y₀`, and both sides loop-resolved at the same `(y₀, ε)`.  This is exactly what
`ValencyThreeDigon.exists_facetDatum_v3Clause` chooses (four cores, one finite avoidance),
made a named datum so that the valency-two and valency-four clauses can be required at the
**same** points as the valency-three clause is proved at.

It is produced at every step (`exists_resolvedDatum`) and consumed by `v3Clause_of_resolved`
and by the two clauses.  Strictly stronger than a generic step facet datum
(`ResolvedDatum.toGeneric`), since the loop resolutions' cores must also be general at `y₀`. -/
structure ResolvedDatum (c c' : CubicCore n p) (degree : ℕ) (e₀ : Fin p) (y₀ : Fin p → ℚ)
    (ε : ℚ) : Prop where
  move : ∃ m : c.graph.MoveData, c'.graph = c.graph.move m ∧ m.base.1 = e₀
  datum : FacetDatum c.core c'.core degree e₀ y₀ ε
  generic : FacetGenericity.FacetGeneric degree y₀
  resolvedL : ResolvedSide c degree e₀ y₀ ε
  resolvedR : ResolvedSide c' degree e₀ y₀ ε

namespace ResolvedDatum

variable {c c' : CubicCore n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}

theorem step (R : ResolvedDatum c c' degree e₀ y₀ ε) : Step c c' := by
  obtain ⟨m, hm, -⟩ := R.move
  exact ⟨m, hm⟩

theorem nonloop (R : ResolvedDatum c c' degree e₀ y₀ ε) : c.core.tail e₀ ≠ c.core.head e₀ := by
  obtain ⟨m, -, rfl⟩ := R.move
  exact ValencyThreeLoopMerge.near_nonloop m

theorem nonloop' (R : ResolvedDatum c c' degree e₀ y₀ ε) :
    c'.core.tail e₀ ≠ c'.core.head e₀ := by
  obtain ⟨m, hm, rfl⟩ := R.move
  have hc' : c' = farCore m := CubicCore.graph_injective (hm.trans (farCore_graph m).symm)
  subst hc'
  exact ValencyThreeCensus.far_nonloop m

/-- A resolved datum is in particular a generic step facet datum. -/
theorem toGeneric (R : ResolvedDatum c c' degree e₀ y₀ ε) :
    Step c c' ∧ FacetDatum c.core c'.core degree e₀ y₀ ε ∧ c'.core.tail e₀ ≠ c'.core.head e₀ ∧
      FacetGenericity.FacetGeneric degree y₀ :=
  ⟨R.step, R.datum, R.nonloop', R.generic⟩

end ResolvedDatum

/-- **The chooser**: every Whitehead step has a resolved datum.  (`ValencyThreeDigon`'s
`exists_facetDatum_v3Clause`, with the conclusion kept as data rather than consumed.) -/
theorem exists_resolvedDatum {c c' : CubicCore n p} (h : Step c c') :
    ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ), ResolvedDatum c c' degree e₀ y₀ ε := by
  obtain ⟨m, hm⟩ := h
  have hc' : c' = farCore m := CubicCore.graph_injective (hm.trans (farCore_graph m).symm)
  subst hc'
  obtain ⟨mL, hbL, hL⟩ := ValencyThreeDigon.exists_loopMove_side c m
  obtain ⟨mR, hbR, hR⟩ := ValencyThreeDigon.exists_loopMove_side (farCore m) (revMove m)
  rw [revMove_base] at hbR hR
  let cs : Fin 4 → Core n p :=
    ![c.core, (farCore m).core, (farCore mL).core, (farCore mR).core]
  obtain ⟨y₀, hpt, hgen, hG⟩ :=
    ValencyThreeDigon.exists_facetPoint_general_family cs degree m.base.1
  obtain ⟨ε, hε, hst⟩ := ValencyThreeDigon.exists_facetStable_family cs hpt.1 hgen
  refine ⟨m.base.1, y₀, ε, ⟨⟨m, farCore_graph m, rfl⟩,
    ⟨sharedContractionSlot_of_move m (farCore_graph m), hpt, hgen 0, hgen 1, hε, hst 0, hst 1⟩,
    hG, ?_, ?_⟩⟩
  · refine hL.imp id fun hl ↦ ⟨mL, congrArg Prod.fst hbL, hl, ?_⟩
    have hsh := sharedContractionSlot_of_move mL (farCore_graph mL)
    rw [hbL] at hsh
    exact ⟨hsh, hpt, hgen 0, hgen 2, hε, hst 0, hst 2⟩
  · refine hR.imp id fun hl ↦ ⟨mR, congrArg Prod.fst hbR, hl, ?_⟩
    have hsh := sharedContractionSlot_of_move mR (farCore_graph mR)
    rw [hbR] at hsh
    exact ⟨hsh, hpt, hgen 1, hgen 3, hε, hst 1, hst 3⟩

/-- A loop-resolved side gives the per-side input of
`ValencyThreeLoopMerge.metricCensus_clause_of_presented`. -/
theorem noParallel_or_loopPresented {c : CubicCore n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (h : ResolvedSide c degree e₀ y₀ ε) :
    NoParallel c.core e₀ ∨ LoopPresented c.core e₀ y₀ degree := by
  refine h.imp id ?_
  rintro ⟨mL, rfl, hl, hdL⟩
  exact loopPresented_of_move mL hdL hG hDegree hl

/-- **The valency-three clause at every resolved datum.** -/
theorem v3Clause_of_resolved {c c' : CubicCore n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}
    (R : ResolvedDatum c c' degree e₀ y₀ ε) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (ml : MetricFacetLimit c.core c'.core y₀ degree) (hml : ValencyThreeSplit.V3Limit ml) :
    ValencyThreeDigon.V3Clause ml := by
  have hP := noParallel_or_loopPresented R.generic hDegree R.resolvedL
  have hP' := noParallel_or_loopPresented R.generic hDegree R.resolvedR
  obtain ⟨m, hm, rfl⟩ := R.move
  have hc' : c' = farCore m := CubicCore.graph_injective (hm.trans (farCore_graph m).symm)
  subst hc'
  exact metricCensus_clause_of_presented m R.datum R.generic hDegree hn hP hP' ml hml

end Resolved

/-! ## 4.  The two named clauses, and the assembly -/

section Supplies

open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open FacetMachine (FacetDatum)
open ValencyThreeDigon (V3Clause)
open ValencyFourSplit (V4Limit kIndexL kIndexR RegrowthAnchor4 Labelling4)

/-- **The valency-two clause.**  At every resolved datum of every Whitehead
step, at every metric facet limit of valency two, the classes of the two sides are labelled
injectively by one index with equal ranges (the clause of `FacetCensus.MetricCensus`, in the
shape of `V3Clause`).

Given the valency-four clause it is equivalent to `MetricCensus` at every resolved datum
(`supplies_iff`).  It is consumed by `metricCensus_of_resolved`, and proved at genus six by
`ValencyTwoPairing.v2ClauseSupply`. -/
def V2ClauseSupply (n p degree : ℕ) : Prop :=
  ∀ (c c' : CubicCore n p) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
    ResolvedDatum c c' degree e₀ y₀ ε →
      ∀ m : MetricFacetLimit c.core c'.core y₀ degree, V2Limit m → V3Clause m

/-- **The valency-four clause.**  The same at every metric facet limit of
valency four (`ValencyFourSplit.V4Limit`, two-sided).

Given the valency-two clause it is equivalent to `MetricCensus` at every resolved datum
(`supplies_iff`).  It follows from its input form by `v4ClauseSupply_of_inputs`, and is proved
at genus six by `ValencyFourRealisation.v4ClauseSupply_genusSix`. -/
def V4ClauseSupply (n p degree : ℕ) : Prop :=
  ∀ (c c' : CubicCore n p) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
    ResolvedDatum c c' degree e₀ y₀ ε →
      ∀ m : MetricFacetLimit c.core c'.core y₀ degree, V4Limit m → V3Clause m

/-- **The valency-four clause at the level of its two inputs**: `K`-injectivity on both
sides and per-`K` realisation on both sides, relative to the anchor indices of every
presenting regrowth -- exactly the hypotheses of `ValencyFourSplit.metricCensus_clause_of_realised`.

It implies `V4ClauseSupply` (`v4ClauseSupply_of_inputs`); the converse fails in
general only because `V4ClauseSupply` allows any index, not `K`. -/
def V4InputsSupply (n p degree : ℕ) : Prop :=
  ∀ (c c' : CubicCore n p) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ)
    (R : ResolvedDatum c c' degree e₀ y₀ ε) (m : MetricFacetLimit c.core c'.core y₀ degree)
    (hm : V4Limit m),
    Function.Injective (kIndexL hm e₀ R.datum.point) ∧
    Function.Injective (kIndexR hm e₀ R.datum.point) ∧
    (∀ (w₀ : Regrowth c.core y₀ degree), MetricFacetLimit.ofLeft (c' := c'.core) w₀ = m →
      ∀ {block₀} (_ : RegrowthAnchor4 w₀ block₀)
        (L₀ : Labelling4 w₀.limit (ValencyThreeSplit.anchorOf w₀ block₀)) (K : ℕ),
        L₀.indices.KAdmissible K →
          (∃ x, kIndexL hm e₀ R.datum.point x = K) ∧ ∃ x, kIndexR hm e₀ R.datum.point x = K) ∧
    (∀ (w₀ : Regrowth c'.core y₀ degree), MetricFacetLimit.ofRight (c := c.core) w₀ = m →
      ∀ {block₀} (_ : RegrowthAnchor4 w₀ block₀)
        (L₀ : Labelling4 w₀.limit (ValencyThreeSplit.anchorOf w₀ block₀)) (K : ℕ),
        L₀.indices.KAdmissible K →
          (∃ x, kIndexL hm e₀ R.datum.point x = K) ∧ ∃ x, kIndexR hm e₀ R.datum.point x = K)

/-- The reduction `ValencyFourSplit.metricCensus_clause_of_realised`, in supply form. -/
theorem v4ClauseSupply_of_inputs (h : V4InputsSupply n p degree) : V4ClauseSupply n p degree :=
  fun c c' e₀ y₀ ε R m hm ↦
    let ⟨hinjL, hinjR, hexL, hexR⟩ := h c c' e₀ y₀ ε R m hm
    ValencyFourSplit.metricCensus_clause_of_realised hm e₀ R.datum.point hinjL hinjR hexL hexR

/-- **The census at a resolved datum, from the two named clauses**: dispatch every metric
facet limit on its valency (`valency_trichotomy`); valency three is proved
(`v3Clause_of_resolved`). -/
theorem metricCensus_of_resolved (h2 : V2ClauseSupply n p degree)
    (h4 : V4ClauseSupply n p degree) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    {c c' : CubicCore n p} {e₀ : Fin p} {y₀ : Fin p → ℚ} {ε : ℚ}
    (R : ResolvedDatum c c' degree e₀ y₀ ε) : FacetCensus.MetricCensus c.core c'.core degree y₀ := by
  intro m
  rcases valency_trichotomy R.datum.point R.nonloop R.nonloop' m with h | ⟨-, h⟩ | ⟨-, h⟩
  · exact h2 c c' e₀ y₀ ε R m h
  · exact v3Clause_of_resolved R hDegree hn m h
  · exact h4 c c' e₀ y₀ ε R m h

/-- **The two named clauses are exactly what `MetricCensus` needs beyond valency three**:
together they are equivalent to `MetricCensus` at every resolved datum. -/
theorem supplies_iff (hDegree : 3 ≤ degree) (hn : 3 ≤ n) :
    V2ClauseSupply n p degree ∧ V4ClauseSupply n p degree ↔
      ∀ (c c' : CubicCore n p) (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ),
        ResolvedDatum c c' degree e₀ y₀ ε → FacetCensus.MetricCensus c.core c'.core degree y₀ :=
  ⟨fun h _ _ _ _ _ R ↦ metricCensus_of_resolved h.1 h.2 hDegree hn R,
    fun h ↦ ⟨fun c c' e₀ y₀ ε R m _ ↦ h c c' e₀ y₀ ε R m,
      fun c c' e₀ y₀ ε R m _ ↦ h c c' e₀ y₀ ε R m⟩⟩

/-- **The per-step consumer's input, from the two named clauses** -- exactly the hypothesis of
`FacetCensus.typeChangeSupplyPositive_of_metricCensus`. -/
theorem stepCensus_of_supplies (h2 : V2ClauseSupply n p degree)
    (h4 : V4ClauseSupply n p degree) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    {c c' : CubicCore n p} (h : Step c c') :
    ∃ (e₀ : Fin p) (y₀ : Fin p → ℚ) (ε : ℚ), FacetDatum c.core c'.core degree e₀ y₀ ε ∧
      c'.core.tail e₀ ≠ c'.core.head e₀ ∧ FacetCensus.MetricCensus c.core c'.core degree y₀ := by
  obtain ⟨e₀, y₀, ε, R⟩ := exists_resolvedDatum (degree := degree) h
  exact ⟨e₀, y₀, ε, R.datum, R.nonloop', metricCensus_of_resolved h2 h4 hDegree hn R⟩

end Supplies

/-! ## 5.  The genus-six digon--digon step -/

section Instances

open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open FacetAdapterPilot (farCore farCore_graph)
open DraismaVargas.Count.FacetMachine (catLoopCore)
open ValencyThreeLoopMerge (digonMove)

/-- **A resolved datum exists at the genus-six digon--digon step** (where `LoopMerge`
fails on both sides, `ValencyThreeLoopMerge.not_loopMerge_digon`), so the antecedents of both
clauses are inhabited at the hardest instance, and every metric facet limit there has
exactly one valency among two, three and four. -/
theorem digon_resolved :
    ∃ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
      ResolvedDatum catLoopCore (farCore digonMove) (2 + 2) e₀ y₀ ε ∧
      ∀ m : MetricFacetLimit catLoopCore.core (farCore digonMove).core y₀ (2 + 2),
        ∃ k, (k = 2 ∨ k = 3 ∨ k = 4) ∧ LimitValency m k ∧ ∀ k', LimitValency m k' → k' = k := by
  obtain ⟨e₀, y₀, ε, R⟩ :=
    exists_resolvedDatum (degree := 2 + 2) (c := catLoopCore) (c' := farCore digonMove)
      ⟨digonMove, farCore_graph digonMove⟩
  refine ⟨e₀, y₀, ε, R, fun m ↦ ?_⟩
  obtain ⟨k, hk, h⟩ := exists_limitValency R.datum.point R.nonloop R.nonloop' m
  exact ⟨k, hk, h, fun k' h' ↦ limitValency_unique h' h⟩

/-- **The valency-three clause at every resolved datum of the digon--digon step.** -/
example : ∀ (e₀ : Fin (6 * 2 + 3)) (y₀ : Fin (6 * 2 + 3) → ℚ) (ε : ℚ),
    ResolvedDatum catLoopCore (farCore digonMove) (2 + 2) e₀ y₀ ε →
      ∀ m : MetricFacetLimit catLoopCore.core (farCore digonMove).core y₀ (2 + 2),
        LimitValency m 3 → ValencyThreeDigon.V3Clause m :=
  fun _ _ _ R m h ↦ v3Clause_of_resolved R (by norm_num) (by norm_num) m
    (v3Limit_of_limitValency R.datum.point R.nonloop h)

end Instances

end DraismaVargas.Count.CensusAssembly
