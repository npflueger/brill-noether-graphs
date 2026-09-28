import DraismaVargasCount.CrossCoreParity
import DraismaVargasCount.SimpleWallSupply

/-!
# The positive type-change obligation, and the shared contraction of a Whitehead move

The type-change step of the count (step 3 of `DraismaVargasCount.Assembly`) proves
`SimpleWallSupply.TypeChangeSupplyPositive`: across every Whitehead move between cores there are
positive general requests on the two sides whose open odd counts have the same parity.  This
module records what that obligation does and does not say, and proves the combinatorial fact
about a Whitehead move from which the proof of step 3 starts.

* §1, `step_obligation_of_opposite_parity`: the per-step existential is met outright as soon as
  *either* core of the step carries two positive general requests of **opposite** parity; the
  move itself is not used.  Contrapositively (`parityConstant_of_not_typeChangeSupplyPositive`),
  a failure of the obligation hands back a step at both of whose cores the parity is constant
  among positive general requests -- the invariance that the trivalent walls (step 2,
  `SimpleWallSupply.InConeSupplySimple`) provide.
* §2, `typeChangeSupplyPositive_of_uniform`, `typeChangeSupplyPositive_of_odd`,
  `typeChangeSupplyPositive_of_not_odd`, `exists_positiveGeneral_parity_split_of_not`: the
  obligation follows from either uniform parity, so it carries no information about *which*
  parity the count has.  The oddness of step 4 comes from the base count of step 1.
* §3, `typeChangeSupplyPositive_iff_global_parity`: given `InConeSupplySimple` and the genus
  bound, the obligation is *equivalent* to "any two connected cubic cores of these indices, at
  any two positive general requests, have open odd counts of the same parity".  No `Step`, no
  wall and no schedule survives on the right-hand side.
* §4, `countLink_iff_exists_fibrewiseParity`: the fibrewise-parity interface
  `CrossCoreParity.countLink_of_fibrewiseParity` -- "two invariants with a common value type, and
  a parity of the two fibres over each value" -- is an **equivalence**, by the trivial
  invariant.  As an interface it is free; the whole content is the *construction* of a geometric
  invariant.  In step 3 the invariant is the limit at the facet of the contracted slot that a
  class specialises to (`FacetMachine.FacetLimit`).
* §5, `contractVertex`, `ends_of_vertex`, `exists_shared_contraction`,
  `exists_shared_contraction_core`: every Whitehead step has a shared contraction.  The two cores
  of a `CoreOfDarts.Step` have literally the same dart-to-vertex map once the two ends
  `v₀ ≠ v₁` of the contracted slot `e₀` are identified:
  `contractVertex v₀ v₁ ∘ vertex c'.core = contractVertex v₀ v₁ ∘ vertex c.core`.  That common
  contraction is the non-trivalent core at which the two chambers meet, along the facet
  `y e₀ = 0` of the positive orthant, and Part II's `lm:change-comb-type` is a statement about
  the morphisms specialising to it.  The contracted core itself is built in `Utilities`
  (`DegSpec.contractedCore` in `Utilities.Subdivision.DegenerateSeparator`: one vertex per class
  of the vanishing-slot collapse, one slot per surviving slot; `ContractionData` in
  `Utilities.Subdivision.ClosedContraction` certifies that one core is the contraction of another
  along a forest of slots).  Here it is described only through its vertex map, with no length,
  no request and no fibre.

`CountTransportLink.CountLink` binds its two cores at *independent* index pairs `n p` and
`n' p'`, so a link between a `Core n p` and a contracted `Core (n-1) (p-1)` can be stated.

The source is A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space and a
count*, arXiv:2609.09109.
-/

namespace DraismaVargas.Count.TypeChangePositiveProbe

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CubicCoreDarts (vertex opposite)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.CoreRelabel (Relabel)
open DraismaVargas.Count.OpenOddRung (OpenOdd)
open DraismaVargas.Count.SimpleWallSupply (PositiveGeneral InConeSupplySimple
  TypeChangeSupplyPositive exists_positiveGeneral)

variable {n p degree : ℕ}

/-! ## 1.  The existential of the obligation: a parity split at one core meets it -/

/-- **The per-step existential of `SimpleWallSupply.TypeChangeSupplyPositive` is
met as soon as one of the two cores carries two positive general requests of
opposite parity.**

`CoreOfDarts.Step` is not a hypothesis here and is not used: the second core `c'`
is arbitrary, and all that is asked of it is that it carry *some* positive
general request, which `SimpleWallSupply.exists_positiveGeneral` supplies over
every core.  The existential, not the geometry of the move, is doing the
work. -/
theorem step_obligation_of_opposite_parity (c c' : Core n p) (degree : ℕ)
    {y₁ y₂ : Fin p → ℚ} (h₁ : PositiveGeneral c degree y₁) (h₂ : PositiveGeneral c degree y₂)
    (hopp : ¬ CountTransportLink.CountLink degree c y₁ c y₂) :
    ∃ y y' : Fin p → ℚ, PositiveGeneral c degree y ∧ PositiveGeneral c' degree y' ∧
      CountTransportLink.CountLink degree c y c' y' := by
  classical
  obtain ⟨z, hz⟩ := exists_positiveGeneral c' degree
  by_cases hC : Odd (GeometricFibre.openOddCount c' z degree)
  · by_cases hA : Odd (GeometricFibre.openOddCount c y₁ degree)
    · exact ⟨y₁, z, h₁, hz, iff_of_true hA hC⟩
    · have hB : Odd (GeometricFibre.openOddCount c y₂ degree) := by
        by_contra hB
        exact hopp (iff_of_false hA hB)
      exact ⟨y₂, z, h₂, hz, iff_of_true hB hC⟩
  · by_cases hA : Odd (GeometricFibre.openOddCount c y₁ degree)
    · have hB : ¬ Odd (GeometricFibre.openOddCount c y₂ degree) := by
        intro hB
        exact hopp (iff_of_true hA hB)
      exact ⟨y₂, z, h₂, hz, iff_of_false hB hC⟩
    · exact ⟨y₁, z, h₁, hz, iff_of_false hA hC⟩

/-- **The positive type-change obligation can only fail where the parity is
locally constant.**  A failure of `SimpleWallSupply.TypeChangeSupplyPositive`
hands back a Whitehead step at whose *two* cores the parity of
`GeometricFibre.openOddCount` is constant among positive general requests --
the per-core form of the parity invariance that the trivalent walls
(`SimpleWallSupply.InConeSupplySimple`, step 2 of `DraismaVargasCount.Assembly`)
provide.

So the two halves of `CoreChainSites.StepSupply` are not independent once
positivity is in the binder: a failure of the type-change half would require
local instances of the in-cone half. -/
theorem parityConstant_of_not_typeChangeSupplyPositive
    (h : ¬ TypeChangeSupplyPositive degree n p) :
    ∃ c c' : CubicCore n p, Step c c' ∧
      (∀ y y' : Fin p → ℚ, PositiveGeneral c.core degree y → PositiveGeneral c.core degree y' →
        CountTransportLink.CountLink degree c.core y c.core y') ∧
      (∀ y y' : Fin p → ℚ, PositiveGeneral c'.core degree y →
        PositiveGeneral c'.core degree y' →
        CountTransportLink.CountLink degree c'.core y c'.core y') := by
  classical
  have hfail : ∃ c c' : CubicCore n p, Step c c' ∧
      ¬ ∃ y y' : Fin p → ℚ, PositiveGeneral c.core degree y ∧
        PositiveGeneral c'.core degree y' ∧
        CountTransportLink.CountLink degree c.core y c'.core y' := by
    by_contra hcon
    push Not at hcon
    exact h fun c c' hstep ↦ hcon c c' hstep
  obtain ⟨c, c', hstep, hno⟩ := hfail
  refine ⟨c, c', hstep, ?_, ?_⟩
  · intro y y' hy hy'
    by_contra hopp
    exact hno (step_obligation_of_opposite_parity c.core c'.core degree hy hy' hopp)
  · intro y y' hy hy'
    by_contra hopp
    obtain ⟨u, u', hu, hu', hlink⟩ :=
      step_obligation_of_opposite_parity c'.core c.core degree hy hy' hopp
    exact hno ⟨u', u, hu', hu, hlink.symm⟩

/-! ## 2.  The obligation is parity-blind -/

/-- **Any uniformly achieved parity discharges the positive type-change
obligation.**  If over every connected cubic core of these indices some positive
general request realises the same truth value `b` of "the open odd count is odd",
the obligation holds.  `b` is unconstrained, so the obligation cannot distinguish
the two parities. -/
theorem typeChangeSupplyPositive_of_uniform {b : Prop}
    (h : ∀ c : CubicCore n p, ∃ y : Fin p → ℚ, PositiveGeneral c.core degree y ∧
      (Odd (GeometricFibre.openOddCount c.core y degree) ↔ b)) :
    TypeChangeSupplyPositive degree n p := by
  intro c c' _
  obtain ⟨y, hy, hby⟩ := h c
  obtain ⟨y', hy', hby'⟩ := h c'
  exact ⟨y, y', hy, hy', hby.trans hby'.symm⟩

/-- **From the conclusion of the propagation step.**  If every positive general
count over a connected cubic core is odd -- which is what `CountSchedule.C34`
asserts -- then the positive type-change obligation holds.  This is not how the
obligation is proved: the propagation step uses it, so reading this as a proof
of the obligation would be circular. -/
theorem typeChangeSupplyPositive_of_odd
    (h : ∀ (c : CubicCore n p) (y : Fin p → ℚ), PositiveGeneral c.core degree y →
      Odd (GeometricFibre.openOddCount c.core y degree)) :
    TypeChangeSupplyPositive degree n p := by
  refine typeChangeSupplyPositive_of_uniform (b := True) fun c ↦ ?_
  obtain ⟨y, hy⟩ := exists_positiveGeneral c.core degree
  exact ⟨y, hy, iff_true_intro (h c y hy)⟩

/-- **And from the exact negation of that conclusion.**  If every positive
general count over a connected cubic core is *even*, the positive type-change
obligation also holds.  Together with `typeChangeSupplyPositive_of_odd` this is
the precise sense in which the obligation carries no information about which
parity the count has: it is implied by each of two contradictory hypotheses.
Nothing routed through the type changes can therefore contribute the oddness
that `CountSchedule.C34` needs; that comes from the base count (step 1 of
`DraismaVargasCount.Assembly`), carried by the trivalent walls and the type
changes. -/
theorem typeChangeSupplyPositive_of_not_odd
    (h : ∀ (c : CubicCore n p) (y : Fin p → ℚ), PositiveGeneral c.core degree y →
      ¬ Odd (GeometricFibre.openOddCount c.core y degree)) :
    TypeChangeSupplyPositive degree n p := by
  refine typeChangeSupplyPositive_of_uniform (b := False) fun c ↦ ?_
  obtain ⟨y, hy⟩ := exists_positiveGeneral c.core degree
  exact ⟨y, hy, iff_false_intro (h c y hy)⟩

/-- **What a failure of the positive type-change obligation would supply.**  A
failure supplies, at these indices, both a connected cubic core with a positive
general request of **even** count and one with a positive general request of
**odd** count.  The first conjunct alone already contradicts the conclusion of
`CountSchedule.C34`. -/
theorem exists_positiveGeneral_parity_split_of_not
    (h : ¬ TypeChangeSupplyPositive degree n p) :
    (∃ (c : CubicCore n p) (y : Fin p → ℚ), PositiveGeneral c.core degree y ∧
      ¬ Odd (GeometricFibre.openOddCount c.core y degree)) ∧
    (∃ (c : CubicCore n p) (y : Fin p → ℚ), PositiveGeneral c.core degree y ∧
      Odd (GeometricFibre.openOddCount c.core y degree)) := by
  classical
  constructor
  · by_contra hcon
    push Not at hcon
    exact h (typeChangeSupplyPositive_of_odd fun c y hy ↦ hcon c y hy)
  · by_contra hcon
    push Not at hcon
    exact h (typeChangeSupplyPositive_of_not_odd fun c y hy ↦ hcon c y hy)

/-! ## 3.  Given the trivalent walls, the Whitehead move drops out -/

/-- **The conditional collapse.**  Assume `SimpleWallSupply.InConeSupplySimple`
(the trivalent walls, step 2 of `DraismaVargasCount.Assembly`) and the genus
bound.  Then
`SimpleWallSupply.TypeChangeSupplyPositive` is *equivalent* to the assertion
that **any** two connected cubic cores of these indices, at **any** two positive
general requests, have open odd counts of the same parity.

`CoreOfDarts.Step` has vanished from the right-hand side, together with the
wall, the schedule and `WallSwitchingBridge.SimpleAt`.  The forward direction is
`SimpleWallSupply.odd_of_positiveGeneral` -- the Whitehead chain of
`LocalCases.CoreOfDarts.exists_chain` -- read as an `Iff`; the converse needs
only `SimpleWallSupply.exists_positiveGeneral`.

**This is a conditional equivalence between existing statements, not a new
predicate, and it does not weaken the obligation.**  What the collapse says is
where the difficulty is *not*: given the trivalent walls, it is not in the
combinatorics of the Whitehead move, but in propagating one parity across the
whole chain -- which is what a local wall-crossing argument at a single step does
inductively. -/
theorem typeChangeSupplyPositive_iff_global_parity
    (hcone : InConeSupplySimple degree n p) (hGenus : 2 ≤ p + 1 - n) :
    TypeChangeSupplyPositive degree n p ↔
      ∀ (c c' : CubicCore n p) (y y' : Fin p → ℚ),
        PositiveGeneral c.core degree y → PositiveGeneral c'.core degree y' →
          CountTransportLink.CountLink degree c.core y c'.core y' := by
  constructor
  · intro htype c c' y y' hy hy'
    exact ⟨fun hodd ↦ SimpleWallSupply.odd_of_positiveGeneral hcone htype hGenus c c' y y'
        hy hy' hodd,
      fun hodd ↦ SimpleWallSupply.odd_of_positiveGeneral hcone htype hGenus c' c y' y
        hy' hy hodd⟩
  · intro hall c c' _
    obtain ⟨y, hy⟩ := exists_positiveGeneral c.core degree
    obtain ⟨y', hy'⟩ := exists_positiveGeneral c'.core degree
    exact ⟨y, y', hy, hy', hall c c' y y' hy hy'⟩

/-! ## 4.  The price of the fibrewise-parity interface -/

/-- **`CrossCoreParity.countLink_of_fibrewiseParity` is an equivalence.**  "Two
invariants on the two sides' open odd classes with a common value type, and an
even sum of the two fibre cardinalities over each value" is neither more nor
less than the link itself: the trivial invariant into `Unit` supplies the
converse.

So the interface costs nothing and buys nothing, exactly as
`CrossCoreParity.countLink_iff_exists_freeInvolution` prices the involution
interface and `Count.SwitchingParity` prices the in-cone one.  The entire content
of a producer in this shape is the *construction* of the invariant from the
geometry of the Whitehead move.  In step 3 of `DraismaVargasCount.Assembly` the
invariant is the limit at the facet of the contracted slot (§5) that a class
specialises to (`FacetMachine.FacetLimit`). -/
theorem countLink_iff_exists_fibrewiseParity (c c' : Core n p) (degree : ℕ)
    (y y' : Fin p → ℚ) :
    CountTransportLink.CountLink degree c y c' y' ↔
      ∃ (L : Type) (μ : OpenOdd c degree y → L) (μ' : OpenOdd c' degree y' → L),
        ∀ l : L, Even (Nat.card {a : OpenOdd c degree y // μ a = l} +
          Nat.card {b : OpenOdd c' degree y' // μ' b = l}) := by
  constructor
  · intro hlink
    refine ⟨Unit, fun _ ↦ (), fun _ ↦ (), fun l ↦ ?_⟩
    have e₁ : {a : OpenOdd c degree y // (fun _ ↦ ()) a = l} ≃ OpenOdd c degree y :=
      Equiv.subtypeUnivEquiv fun _ ↦ Subsingleton.elim _ _
    have e₂ : {b : OpenOdd c' degree y' // (fun _ ↦ ()) b = l} ≃ OpenOdd c' degree y' :=
      Equiv.subtypeUnivEquiv fun _ ↦ Subsingleton.elim _ _
    rw [Nat.card_congr e₁, Nat.card_congr e₂, ← Nat.card_sum]
    exact (CrossCoreParity.countLink_iff_evenSum c c' degree y y').mp hlink
  · rintro ⟨L, μ, μ', h⟩
    exact CrossCoreParity.countLink_of_fibrewiseParity μ μ' h

/-! ## 5.  The shared contraction of a Whitehead step -/

/-- Identify the vertex `v₁` with the vertex `v₀`, fixing everything else.  This
is the vertex map of the contraction of one non-loop slot, written without
constructing the contracted core (which `DegSpec.contractedCore` in `Utilities`
builds from a degenerate length vector). -/
def contractVertex (v₀ v₁ v : Fin n) : Fin n := if v = v₁ then v₀ else v

theorem contractVertex_snd (v₀ v₁ : Fin n) : contractVertex v₀ v₁ v₁ = v₀ := if_pos rfl

theorem contractVertex_fst (v₀ v₁ : Fin n) : contractVertex v₀ v₁ v₀ = v₀ := ite_self _

/-- A dart and its opposite read off the two ends of the dart's slot. -/
theorem ends_of_vertex (core : Core n p) (d : Fin p × Bool) :
    (core.tail d.1 = vertex core d ∧ core.head d.1 = vertex core (opposite d)) ∨
      (core.tail d.1 = vertex core (opposite d) ∧ core.head d.1 = vertex core d) := by
  obtain ⟨e, b⟩ := d
  cases b
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **Every Whitehead step has a shared contraction.**  The two cores of a
`CoreOfDarts.Step` carry *the same* dart-to-vertex map once the two (distinct)
ends `v₀`, `v₁` of the contracted slot are identified.

This is the combinatorial content of the premise of Part II's
`lm:change-comb-type` -- the two cubic types meet along the facet of the length
cone where the
contracted slot's length vanishes -- stated with no length, no request and no
fibre.  The proof is the definition of `CubicDarts.CubicDartGraph.move`: the move
is the transposition `Equiv.swap m.left m.right`, which moves exactly one dart
from each end of the base edge to the other, so every dart's vertex either is
unchanged or swaps `v₀` with `v₁`. -/
theorem exists_shared_contraction {c c' : CubicCore n p} (h : Step c c') :
    ∃ (d₀ : Fin p × Bool) (v₀ v₁ : Fin n),
      v₀ ≠ v₁ ∧ vertex c.core d₀ = v₀ ∧ vertex c.core (opposite d₀) = v₁ ∧
      ∀ d : Fin p × Bool,
        contractVertex v₀ v₁ (vertex c'.core d) = contractVertex v₀ v₁ (vertex c.core d) := by
  obtain ⟨m, hm⟩ := h
  have hvc : vertex c.core = c.graph.vert := CoreOfDarts.vertex_coreOf c.graph
  have hvc' : vertex c'.core = c'.graph.vert := CoreOfDarts.vertex_coreOf c'.graph
  refine ⟨m.base, c.graph.vert m.base, c.graph.vert (c.graph.op m.base), m.nonloop.symm,
    by rw [hvc], by rw [hvc]; rfl, ?_⟩
  intro d
  rw [hvc, hvc', hm]
  show contractVertex _ _ (c.graph.vert (m.perm d)) = _
  by_cases hl : d = m.left
  · subst hl
    rw [m.perm_left, m.right_vert, m.left_vert]
    exact (contractVertex_snd _ _).trans (contractVertex_fst _ _).symm
  · by_cases hr : d = m.right
    · subst hr
      rw [m.perm_right, m.left_vert, m.right_vert]
      exact (contractVertex_fst _ _).trans (contractVertex_snd _ _).symm
    · rw [m.perm_of_ne hl hr]

/-- **The same, in core language**: the contracted slot `e₀`, its two ends, and
the two cores' tails and heads agreeing after the identification.  This is the
statement a contraction operation `Core n p → Core (n-1) (p-1)` would turn into
"the two cores of a step have the same contraction along `e₀`".  The contracted
core is built in `Utilities` (`DegSpec.contractedCore` in
`Utilities.Subdivision.DegenerateSeparator`, indexed by a degenerate length
vector rather than by a slot); it is not built from a `Step` here, so the
statement is given in this quantifier-free form. -/
theorem exists_shared_contraction_core {c c' : CubicCore n p} (h : Step c c') :
    ∃ (e₀ : Fin p) (v₀ v₁ : Fin n), v₀ ≠ v₁ ∧
      ((c.core.tail e₀ = v₀ ∧ c.core.head e₀ = v₁) ∨
        (c.core.tail e₀ = v₁ ∧ c.core.head e₀ = v₀)) ∧
      (∀ e : Fin p, contractVertex v₀ v₁ (c'.core.tail e) =
        contractVertex v₀ v₁ (c.core.tail e)) ∧
      (∀ e : Fin p, contractVertex v₀ v₁ (c'.core.head e) =
        contractVertex v₀ v₁ (c.core.head e)) := by
  obtain ⟨d₀, v₀, v₁, hne, h₀, h₁, hall⟩ := exists_shared_contraction h
  refine ⟨d₀.1, v₀, v₁, hne, ?_, fun e ↦ hall (e, false), fun e ↦ hall (e, true)⟩
  rcases ends_of_vertex c.core d₀ with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · exact Or.inl ⟨ht.trans h₀, hh.trans h₁⟩
  · exact Or.inr ⟨ht.trans h₁, hh.trans h₀⟩

end DraismaVargas.Count.TypeChangePositiveProbe
