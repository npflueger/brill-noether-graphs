module

public import DraismaVargasCount.OddWitness
public import DraismaVargasCount.ClosedBoundaryMember
public import DraismaVargasCount.SimpleWallSupply
public import DraismaVargasCount.BallotFarEndSwap
public import DraismaVargasCount.BaseCountParity
public import DraismaVargas.LocalCases.RequestedExpandedEndpoints
public import DraismaVargasCount.DegenerateBigDivisor

@[expose] public section

/-!
# The graph side and the member half of the genus-six witness

The endgame of the genus-six assembly (step 5 of `DraismaVargasCount/Assembly.lean`,
`CorePencilCoverProducer.witness_of_c34_and_markerFreePencilCover`) proves that every
connected graph `H` of genus six has a regular subdivision of odd order carrying a divisor of
degree four and rank at least one -- the per-graph clause of
`GenusSixOddDescent.GenusSixOddSubdivisionWitness`, stated unfolded.  This file supplies its
graph-side facts and records the member half of the argument.

## The route: no cubic / non-cubic case split

One might expect the witness to split into a cubic branch (a closed odd member over the core
of `UnitSubdivisionPresentation.spec H` itself) and a non-cubic branch (through a cubic
expansion).  **The expansion route alone covers every graph**, because nothing in it needs
the requested specification to be non-cubic.  For a connected genus-six `H`:

1. `spec H := UnitSubdivisionPresentation.spec H` has a connected core
   (`coreConnected_unitSpec`) and `|E| - |V| = 5` (`card_edges_sub_card_vertices`).
2. `RequestedExpandedEndpoints.exists_expansionModel` — **no trivalence hypothesis** —
   returns a reduced specification `spec₀` and an expansion datum `D` whose `bigCore`
   is cubic, connected, loopless and of genus six, with Brill--Noether existence
   transported `spec₀ ↔ spec H` at every uniform scale.
3. The closed-cone member of the count
   (`ClosedBoundaryMember.genusSix_exists_closed_hasOddMult_of_nonneg`)
   applies at the **degenerate** request `degenerateLength D spec₀`, which is a
   natural-number cast and so non-negative, giving a closed member over `D.bigCore`
   with `HasOddMult`, i.e. `Odd oddMult` (`Count.hasOddMult_iff_odd_oddMult`).
   Steps 1–3 are `exists_supplyInstance_of_c34`.
4. `DegenerateBigDivisor.bnExists_of_degenerateMember`, with the rank statement of
   `CorePencilCoverProducer`, turns that member into `BNExists (spec₀.scale u _).graph 1 4`
   at the odd part `u` of the member's scale
   (`CorePencilCoverProducer.exists_odd_bnExists_of_markerFreePencilCoverSupply`).
5. The transport clause of step 2 carries it to `spec H`, whose scaled graph **is**
   `Utilities.Gonality.regularSubdivision H u _` by `rfl`.

The price is that the covering statement for the pencil
(`CorePencilCoverProducer.MarkerFreePencilCoverSupply`) must hold **for every graph, cubic
ones included**.  For a cubic `H` the expansion returned in step 2 may have an empty
contraction forest, and there the covering statement carries all of the rank content.  §4
exhibits exactly such an expansion (the identity expansion of a loopless core).  A
two-branch assembly would not shrink this: `exists_expansionModel` is existential, so a
supply fed by it must be stated for every datum it could return.

## What is proved

* `coreConnected_unitSpec`, `card_edges_sub_card_vertices` — the graph side, used by
  `CorePencilCoverProducer.exists_supplyInstance_of_c34_loopDoubles` and
  `CorePencilCoverProducer.witness_of_c34_and_markerFreePencilCover`.
* `exists_supplyInstance_of_c34` — given `C34 2`, every connected genus-six graph
  produces every premise of `CorePencilCoverProducer.MarkerFreePencilCoverSupply` except
  `LoopDoubles`, at a genuine member.  The endgame uses the same proof with `LoopDoubles`
  added (`CorePencilCoverProducer.exists_supplyInstance_of_c34_loopDoubles`).
* §3: a positive general request exists over the caterpillar core
  (`SimpleWallSupply.exists_positiveGeneral`), so the base point of the propagation is not
  an extra hypothesis.
* §4: `idExpansion`, `idExpansion_conditions` (the identity expansion of any loopless core
  with no isolated vertex, proved once for an abstract core) and
  `degenerateLength_idExpansion` (over it the degenerate request is the specification's own
  length vector).

## What is not proved here

* **`CountSchedule.C34 2`** is a hypothesis of `exists_supplyInstance_of_c34`; it is
  `Assembly.c34_genusSix` (step 4 of the assembly).
* The covering statement `CorePencilCoverProducer.MarkerFreePencilCoverSupply` is not
  proved here; it is `PencilTransportProducer.markerFreePencilCoverSupply`.
* §4 does not prove the covering statement over the identity expansion; it only shows that
  such expansions satisfy `ExpansionData.Conditions`.

No request occurs free in a statement here: the request of §3 is existentially quantified,
and the degenerate request is determined by `(D, spec₀)` and is a natural-number cast.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.WitnessAssembly

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Count.RowRealizedPosition (memberScale memberScale_pos)
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open DraismaVargas.Count.FibreCaterpillar (catCore)
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)

universe u

/-! ## 1.  The graph side -/

/-- **Connectivity reaches the core of the unit presentation.**  The same statement as
`Utilities.Gonality.coreConnected_unitSpec`, proved the same way from the same two lemmas. -/
theorem coreConnected_unitSpec (H : CFGraph.{u}) (hconn : graph_connected H) :
    (UnitSubdivisionPresentation.spec H).core.Connected :=
  PseudocorePresentation.core_connected_of_graph_connected _
    ((UnitSubdivisionPresentation.laplacianEquiv H).graphConnected hconn)

/-- At genus six there are exactly five more edge occurrences than vertices. -/
theorem card_edges_sub_card_vertices (H : CFGraph.{u}) (hgenus : genus H = 6) :
    (Multiset.card H.edges : ℤ) - Fintype.card H.V = 5 := by
  have hgen : (Multiset.card H.edges : ℤ) - Fintype.card H.V + 1 = 6 := hgenus
  omega

/-! ## 2.  The member half: `C34 2` produces the supply's antecedent at every graph -/

/-- **Steps 1–3 of the header.**  Given `C34 2`, a connected genus-six graph yields a
reduced specification, a cubic genus-six expansion datum onto it with Brill--Noether
existence transported back to the graph's own unit presentation at every scale, and a
closed member of odd multiplicity over the expanded core at the degenerate request —
that is, every premise of `CorePencilCoverProducer.MarkerFreePencilCoverSupply` except
`LoopDoubles`, at a genuine member. -/
theorem exists_supplyInstance_of_c34 (hC34 : CountSchedule.C34 2) (H : CFGraph.{u})
    (hconn : graph_connected H) (hgenus : genus H = 6) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀))),
      0 < 2 * (p₀ - n₀) ∧ (∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e) ∧
        D.Conditions spec₀.core ∧ spec₀.core.Connected ∧ D.bigCore.Cubic ∧
        D.bigCore.Connected ∧ 3 * (p₀ - n₀) + 1 - 2 * (p₀ - n₀) = 6 ∧
        (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
          BNExists (spec₀.scale k hk).graph r d ↔
            BNExists ((UnitSubdivisionPresentation.spec H).scale k hk).graph r d) ∧
        ∃ member : FibreMember D.bigCore (fun e ↦ (degenerateLength D spec₀ e : ℚ)) 4,
          member.Closed ∧ Odd member.oddMult := by
  have hE := card_edges_sub_card_vertices H hgenus
  obtain ⟨n₀, p₀, spec₀, D, hCond, hCubic, hConnBig, hL, hN, hc₀, hlt₀, hg₀, -, hbns₀⟩ :=
    DraismaVargas.LocalCases.RequestedExpandedEndpoints.exists_expansionModel
      (UnitSubdivisionPresentation.spec H) (coreConnected_unitSpec H hconn) (by omega)
  have hgenusBig : 3 * (p₀ - n₀) + 1 - 2 * (p₀ - n₀) = 6 := by omega
  obtain ⟨member, hClosed, hHasOdd⟩ :=
    ClosedBoundaryMember.genusSix_exists_closed_hasOddMult_of_nonneg hC34 D.bigCore hCubic
      hConnBig hgenusBig (fun e ↦ (degenerateLength D spec₀ e : ℚ))
      (fun _ ↦ Nat.cast_nonneg _)
  exact ⟨n₀, p₀, spec₀, D, hN, hL, hCond, hc₀, hCubic, hConnBig, hgenusBig, hbns₀, member,
    hClosed, (hasOddMult_iff_odd_oddMult member).mp hHasOdd⟩

/-! ## 3.  A positive general request over the caterpillar core

`CountSchedule.C34 2` itself is `Assembly.c34_genusSix`. -/

/-- A positive general request exists over the caterpillar core `catCore 2`: the base point
of the propagation is not an extra hypothesis. -/
example : ∃ request : Fin (6 * 2 + 3) → ℚ,
    SimpleWallSupply.PositiveGeneral (catCore 2) (2 + 2) request :=
  SimpleWallSupply.exists_positiveGeneral _ _

/-! ## 4.  The identity expansion

`catCore` has self-loops, so it is never the `bigCore` of an expansion (`Conditions`
demands looplessness).  Over a **loopless** cubic core the identity expansion is available:
it satisfies `ExpansionData.Conditions`, its contraction forest is empty, and over it the
degenerate request is the specification's own length vector.  This is the situation, noted
in the header, in which the covering statement carries all of the rank content. -/

section NonVacuity

/-- **The identity expansion** of a core onto itself: every slot single, no slot
contracted, no marker. -/
def idExpansion {n p : ℕ} (C : Core n p) : ExpansionData n p n p where
  bigCore := C
  fib := id
  kind e := .single e
  owner := id
  side _ := false

@[simp] theorem idExpansion_kind {n p : ℕ} (C : Core n p) (e : Fin p) :
    (idExpansion C).kind e = .single e := rfl

/-- The identity expansion satisfies `ExpansionData.Conditions` as soon as the core is
loopless and has no isolated vertex.  Proved once, for an abstract core. -/
theorem idExpansion_conditions {n p : ℕ} (C : Core n p)
    (hLoop : ∀ e : Fin p, C.tail e ≠ C.head e)
    (hInc : ∀ w : Fin n, ∃ j : Fin p, C.tail j = w ∨ C.head j = w) :
    (idExpansion C).Conditions C := by
  refine ⟨hLoop, fun e ↦ ?_, fun e ↦ ?_, fun j ↦ ?_, fun e ↦ ?_, hInc, ?_⟩
  · refine ⟨fun h ↦ by simp at h, fun j hj ↦ ?_, fun j₁ j₂ hj ↦ by simp at hj⟩
    simp only [idExpansion_kind, SlotKind.single.injEq] at hj
    subst hj
    exact ⟨rfl, rfl⟩
  · refine ⟨fun j hj ↦ ?_, fun j₁ j₂ hj ↦ by simp at hj⟩
    simp only [idExpansion_kind, SlotKind.single.injEq] at hj
    subst hj
    exact ⟨rfl, rfl⟩
  · refine ⟨fun h ↦ by simp [idExpansion] at h, fun j' hj' ↦ ?_,
      fun j₁ j₂ hj ↦ by simp [idExpansion] at hj⟩
    simp only [idExpansion, SlotKind.single.injEq] at hj'
    subst hj'
    exact ⟨rfl, rfl⟩
  · intro j₁ j₂ hj
    simp at hj
  · rintro w T ⟨a, haT, rfl⟩ ⟨b, hbT, hb⟩
    have hba : b = a := hb
    subst hba
    exact absurd haT hbT

/-- Over the identity expansion the degenerate request is the specification's own
length vector. -/
theorem degenerateLength_idExpansion {n p : ℕ} (small : Spec n p) (e : Fin p) :
    degenerateLength (idExpansion small.core) small e = small.length e := by
  rw [DegenerateBigDivisor.degenerateLength_of_ne _ _ (by simp)]
  rfl

end NonVacuity

end DraismaVargas.Count.WitnessAssembly
