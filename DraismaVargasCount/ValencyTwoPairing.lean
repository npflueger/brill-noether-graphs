import DraismaVargasCount.ValencyTwoCensus
import DraismaVargasCount.ValencyThreeLoopMerge
import DraismaVargas.LocalCases.LeafFacetNoReturn

/-!
# Valency-two stage 3: the pairing is read on the core

**Source.**  Vargas, Part II (arXiv:2609.09109), the valency-two limits `{v2-nd4}` (subsection
`subsec-case-v2`), and labelling convention (1) of the setup subsection
`subsec-setup-determinants` (away from the contracting edge, the edges of each specialising
combinatorial type correspond bijectively to those of the limit).  This module proves
`ValencyTwoCensus.PairingMatchSupply`, stage 3 of the valency-two census set out in
`DraismaVargasCount.ValencyTwoSplit` and the one remaining input of
`CensusAssembly.V2ClauseSupply`.  It builds on `ValencyTwoSplit`, `ValencyTwoResolutionMatch`
and `ValencyTwoCensus`, and transplants to valency two the row pinning and the core reading of
`ValencyThreeCoreSlots` and the loop presenters and sheet swap of `ValencyThreeLoopMerge`.

## The result, in one paragraph

Stage 3 holds at valency two at every resolved datum (`pairingMatchSupply`), so
`CensusAssembly.V2ClauseSupply n p degree` holds for `3 ≤ degree`, `3 ≤ n` (`v2ClauseSupply`),
the valency-two clause of the type changes (`Assembly.typeChanges_genusSix`, step 3 of
`DraismaVargasCount.Assembly`).  The argument is the valency-three one of
`ValencyThreeCoreSlots`, made valency-two.  **(i) Row pinning** (§4): a labelled-metric
isomorphism of two regrowths' limits carries every limit stable path to the one over the same
core slot (`row_inRow_map`).  The valency-three proof uses `ValencyThreeCoreSlots.WallRows` (no
contracted return at all), which fails at the leaf valency-two wall; its only use is the row
dictionary, and the weaker `LeafFacetNoReturn.NoContractedReturnOffRow` (returns only on the
vanishing row) feeds the same dictionary (`matrix_wallLabelling'`).  It holds at **every** facet
wall (`noReturnOffRow`, §1: a leaf end by the fold argument, at either end of the contracted
occurrence, a non-leaf end by the ramification bound).  **(ii) The stable frame** (§2--§3): both
valency-two pictures have exactly two trivalent constituents `B₁ ≠ B₂`, joined by an incoming
stable path all of whose occurrences lie over the contracted target occurrence (`A_a`–`e₁`–`A_b`
at a `(2,2)` split; `Y`–fold–`Z` at a leaf split), every other constituent divalent, and the
pairing is "homed at one of `B₁`, `B₂`" (`StableFrame`, `nonempty_stableFrame`).  That path is
the vanishing core slot (`row_P₀`), so `B₁`, `B₂` lie over the two ends of `e₀`, and the pairing
is "same end of `e₀`" (`paired_iff_vtx`).  **(iii) The core** (§5): each survivor's end of `e₀`
is met by its core slot, which (i) transports.  With no slot parallel to `e₀` the slot fixes
the end, so *every* labelled-metric isomorphism matches the pairings
(`pairingMatch_of_noParallel`, the universal form).  Beside a parallel slot, the ends are fixed
up to exchanging the two survivors on the parallel slot (`vtx_cases_of_parallel`); a loop
presenter's sheet swap (`swapAt_loop`: the loop row's two survivors lie over one leaf edge,
which is never the contracted one) transports to every presentation (`swapAt_of_limitIso`) and
exchanges exactly those two, so `ψ` or `ψ ≫ σ'` matches (`pairingMatch_of_swap`).
`ResolvedDatum`'s loop resolutions supply the presenters (`CensusAssembly.noParallel_or_loopPresented`).

## What is proved

* §1 `incident_of_leaf_fold'`, **`noReturnOffRow`** (no contracted return off the facet row, at
  every wall with every facet-row occurrence over the contracted occurrence; unlike
  `LeafFacetNoReturn.noReturn_off_facet`, which treats a leaf at the first end only, it covers a
  leaf at either end and a non-leaf end in one statement).
* §2 `Homed`, **`StableFrame`** (+ `mem_of`, `nd_of`, `inc_of`, `nonleaf_of`), `lift_survives`,
  `pathOf`, `lift_ne_of_intl`, `witness_of_homed`, `incidence_pos_of_homed`,
  `eq_of_three_incident`, `card_three_ndAt`, **`homed_unique`**, **`two_le_incidence`**.
* §3 `sum_excess` (any valency-two anchor), `nd_two_of_ne`, `side_ne_of_intl`,
  **`nonempty_divFrame`**, **`nonempty_leafFrame`**, **`nonempty_stableFrame`**.
* §4 `facetOver`, `offRow`, `inRow`, `inRow_ne_facet`, **`natural_limit_eq`**,
  **`row_inRow_map`**, `RegrowthFrame`, **`row_P₀`**, `pathOf_eq_inRow`, `slotOf`,
  **`slot_transport`**.
* §5 `inc_lt_two`, `exists_parallel`, **`vtx_eq_of_noParallel`**, **`vtx_cases_of_parallel`**
  (pure core combinatorics).
* §6 `lift_congr`, `homed_congr`, `paired_congr`, `pathOf_congr`, `At`, `vertexOf_end`,
  `eq_of_vertexOf_eq`, `exists_at`, `at_unique`, `at_congr`, `vtxOf`, `at_vtxOf`, `vtxOf_congr`,
  **`paired_iff_vtx`**, `vtxOf_end`, `vtxOf_inc`, `slotOf_ne`, `vtxOf_two_le`.
* §7 `match_of_one`, **`pairingMatch_of_noParallel`**.
* §8 `SwapAt`, `label_edgePartition`, **`swapAt_loop`**, **`swapAt_of_limitIso`**.
* §9 **`pairingMatch_of_swap`**, **`pairingMatch_of_side`**, **`pairingMatchSupply`**,
  **`v2ClauseSupply`**.
* §10 non-vacuity: the headline instantiated at genus six.

## What is not proved here (every hypothesis, explicitly)

* `pairingMatchSupply` and `v2ClauseSupply` keep `3 ≤ degree`
  (`ValencyThreeLoopMerge.loopPresented_of_move`, through `noParallel_or_loopPresented`) and
  `3 ≤ n` (parallel slots are unique, and stage 5); both hold at genus six (`n = 10`,
  `degree = 4`).
* The valency-four clause `CensusAssembly.V4ClauseSupply 10 15 4` is not proved here; it is
  `ValencyFourRealisation.v4ClauseSupply_genusSix`, with no hypothesis.  The two clauses meet
  in `Assembly.typeChanges_genusSix`.
* Non-vacuity: the new `Prop`s are `Homed`, `At` (equivalent to `Paired` through
  `paired_iff_vtx`), `SwapAt` (produced at every loop presenter, `swapAt_loop`) and the
  structure `StableFrame` (inhabited at every valency-two anchor, `nonempty_stableFrame`).  As
  for the stage predicates of `ValencyTwoSplit`, no valency-two facet regrowth over a literal
  gluing datum is constructed here, so none is evaluated at a concrete cover; §10 instantiates
  the headline.
* No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`, no `#eval`.

## Remarks

* The failure of `ValencyThreeCoreSlots.WallRows` at the leaf valency-two wall is harmless:
  `WallRows.noReturn` enters the valency-three argument only through `natural_limit_eq`, and
  the weaker off-row condition, true at every wall, feeds the same row dictionary.  Neither
  split breaks the argument: the `(2,2)` and the leaf pictures both carry a stable frame, and
  the reading of the pairing on the core does not see the split.
* The only freedom stage 3 has is beside a parallel slot, where the two survivors on the
  parallel slot can sit at either end; the loop presenter's sheet swap exchanges exactly them.
  At a core with no parallel slot the two leaf cross pairings (Types I and II over Base I) are
  never read over one labelled core: the pairing is the core's.
* The universal form (every limit isomorphism matches) holds at cores with no slot parallel to
  `e₀`; beside a parallel slot only the existential form holds, and that is what
  `PairingMatch` states.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.ValencyTwoPairing

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction ContractionRamification W4StableSource WallDegeneration
open FullDimensionalSource PrunedFibreValency PrunedFibreTree FullContractionFibre
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyThreeSplit (ndAt mem_ndAt card_ndAt fib intl mem_fib_iff intl_ends
  mem_intl_of_ndAt bdAt mem_bdAt limA)
open ValencyTwoSplit (AnchorInput DivInput LeafInput Labelling lift lift_ne lift_injective Paired
  PairedE)

/-! ## 1.  No contracted return off the facet row, at every wall -/

section OffRow

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)

include fd in
/-- `LeafFacetNoReturn.incident_of_leaf_fold` at either end of the contracted occurrence. -/
theorem incident_of_leaf_fold' {x : target.V} {contracted : target.edges}
    (hx : (contracted : target.V × target.V).1 = x ∨ (contracted : target.V × target.V).2 = x)
    (fold : data.SourceVertex) (hAbove : fold.1.1 = x)
    (hLeaf : (GluingDatum.incidentEdges x).card = 1)
    (hNd : nonDanglingValency data fold = 2)
    (edge : data.SourceEdge) (hTarget : edge.1.1 = contracted)
    (hSurvives : ¬ IsDangling data edge) : Incident data edge fold := by
  rcases hx with hx | hx
  · exact LeafFacetNoReturn.incident_of_leaf_fold data fd hx fold hAbove hLeaf hNd edge hTarget
      hSurvives
  · have hEndTarget : ((data.sourceEnds edge).2).1.1 = fold.1.1 := by
      show (edge.1.1 : target.V × target.V).2 = fold.1.1
      rw [hTarget, hx, hAbove]
    have hActive : nonDanglingValency data (data.sourceEnds edge).2 ≠ 0 :=
      ClassInjectivity.nonDanglingValency_ne_zero_of_incident data hSurvives
        (incident_right data edge)
    have hEqVertex : (data.sourceEnds edge).2 = fold := by
      by_contra hNe
      exact hActive (LeafFacetNoReturn.nonDanglingValency_eq_zero_of_ne_fold data fd fold
        ((data.sourceEnds edge).2) hEndTarget (by rw [hAbove]; exact hLeaf) hNd hNe)
    rw [← hEqVertex]
    exact incident_right data edge

include fd in
/-- **No contracted return off the facet row, at every wall** (either end a leaf or not): the
leaf-end argument of `LeafFacetNoReturn.noReturn_off_facet` and the non-leaf argument of
`StablePathFacetContraction.noContractedReturn_of_nonleaf`, read at the end the divalent vertex
lies over. -/
theorem noReturnOffRow {contracted : target.edges} (facetRow : StablePath data)
    (hFacetOver : ∀ e : NonDanglingEdge data, e.stablePath = facetRow → e.1.1.1 = contracted) :
    LeafFacetNoReturn.NoContractedReturnOffRow data contracted facetRow := by
  intro vertex hNd first second hFirstT hSecondT hFirstI hSecondI
  by_cases hEq : first = second
  · exact Or.inl hEq
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hEq (Subtype.ext h)
  have hAt := ((incident_iff_target_mem_and_rel data first.1 vertex).mp hFirstI).1
  rw [hFirstT] at hAt
  have hEnd : (contracted : target.V × target.V).1 = vertex.1.1 ∨
      (contracted : target.V × target.V).2 = vertex.1.1 := by
    simpa [GluingDatum.incidentEdges] using hAt
  by_cases hLeaf : (GluingDatum.incidentEdges vertex.1.1).card = 1
  · right
    have hCons : Consecutive data first second := ⟨hEq, vertex, hFirstI, hSecondI, hNd⟩
    have hSamePath : first.stablePath = second.stablePath := stablePath_eq_of_consecutive hCons
    obtain ⟨g, hg⟩ := Quot.exists_rep facetRow
    have hgPath : g.stablePath = facetRow := hg
    have hgT : g.1.1.1 = contracted := hFacetOver g hgPath
    have hgInc : Incident data g.1 vertex :=
      incident_of_leaf_fold' data fd hEnd vertex rfl hLeaf hNd g.1 hgT g.2
    rcases StablePathFacetContraction.eq_or_eq_of_nonDanglingValency_eq_two data hNd first.2
      second.2 hFirstI hSecondI hNeVal g.2 hgInc with h | h
    · have hgf : g = first := Subtype.ext h
      rw [hgf] at hgPath
      exact ⟨hgPath, hSamePath.symm.trans hgPath⟩
    · have hgf : g = second := Subtype.ext h
      rw [hgf] at hgPath
      exact ⟨hSamePath.trans hgPath, hgPath⟩
  · exfalso
    apply hEq
    apply Subtype.ext
    have hpos : 0 < (GluingDatum.incidentEdges vertex.1.1).card := Finset.card_pos.mpr ⟨_, hAt⟩
    refine DivalentSourceLocal.sourceEdge_eq_of_same_target data fd.danglingEdgeNoGlue
      vertex hNd ?_ first.1 second.1 first.2 second.2 hFirstI hSecondI
      (hFirstT.trans hSecondT.symm)
    exact DivalentSourceLocal.localRamification_le_one_of_nonleaf data fd.valid vertex
      (fd.changeMinimal vertex.1.1) (by omega)

end OffRow

/-! ## 2.  The stable frame of a valency-two anchor fibre -/

section Frame

variable {target : CFGraph} {degree : ℕ}
  {data : GluingDatum target degree}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

/-- **Where a survivor lives** (`ValencyThreeCoreSlots.Homed`, for valency-two labellings): at the
constituent `B`, or at a divalent constituent joined to `B` by an internal occurrence. -/
def Homed (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (i : Fin 4) (B : data.SourceVertex) : Prop :=
  lift L i ∈ ndAt data B ∨ ∃ Z ∈ fib data hc hab hOne block, nonDanglingValency data Z = 2 ∧
    lift L i ∈ ndAt data Z ∧ ∃ e ∈ intl data hc hab hOne block, e ∈ ndAt data Z ∧ e ∈ ndAt data B

variable (data hc hab hOne block) in
/-- **The stable frame of a valency-two anchor fibre**: the two branch constituents `B₁`, `B₂`
(the two incoming stable vertices, over the two ends of the vanishing core slot), the incoming
stable path `P₀` joining them (the contracting one, all of whose occurrences lie over the
contracted target occurrence), every other active constituent divalent, and the pairing read as
"homed at one branch constituent".  Both valency-two pictures carry one (`nonempty_stableFrame`:
`A_a`, `A_b` and `e₁` at a `(2,2)` split; `Y`, `Z` and the fold path at a leaf split). -/
structure StableFrame where
  B₁ : data.SourceVertex
  B₂ : data.SourceVertex
  mem₁ : B₁ ∈ fib data hc hab hOne block
  mem₂ : B₂ ∈ fib data hc hab hOne block
  nd₁ : nonDanglingValency data B₁ = 3
  nd₂ : nonDanglingValency data B₂ = 3
  ne : B₁ ≠ B₂
  nonleaf₁ : 2 ≤ (GluingDatum.incidentEdges B₁.1.1).card
  nonleaf₂ : 2 ≤ (GluingDatum.incidentEdges B₂.1.1).card
  two : ∀ X ∈ fib data hc hab hOne block, X ≠ B₁ → X ≠ B₂ → nonDanglingValency data X = 2
  P₀ : StablePath data
  inc₁ : ∃ x : NonDanglingEdge data, Incident data x.1 B₁ ∧ x.stablePath = P₀
  inc₂ : ∃ x : NonDanglingEdge data, Incident data x.1 B₂ ∧ x.stablePath = P₀
  overC : ∀ x : NonDanglingEdge data, x.stablePath = P₀ → x.1.1.1 = contracted
  homed : ∀ (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (i : Fin 4), ∃ B, (B = B₁ ∨ B = B₂) ∧ Homed L i B
  paired_iff : ∀ (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))
    (i j : Fin 4), Paired L i j ↔ ∃ B, (B = B₁ ∨ B = B₂) ∧ Homed L i B ∧ Homed L j B

namespace StableFrame

variable (Fr : StableFrame data hc hab hOne block)

theorem mem_of {B : data.SourceVertex} (hB : B = Fr.B₁ ∨ B = Fr.B₂) :
    B ∈ fib data hc hab hOne block := by
  rcases hB with rfl | rfl
  · exact Fr.mem₁
  · exact Fr.mem₂

theorem nd_of {B : data.SourceVertex} (hB : B = Fr.B₁ ∨ B = Fr.B₂) :
    nonDanglingValency data B = 3 := by
  rcases hB with rfl | rfl
  · exact Fr.nd₁
  · exact Fr.nd₂

theorem inc_of {B : data.SourceVertex} (hB : B = Fr.B₁ ∨ B = Fr.B₂) :
    ∃ x : NonDanglingEdge data, Incident data x.1 B ∧ x.stablePath = Fr.P₀ := by
  rcases hB with rfl | rfl
  · exact Fr.inc₁
  · exact Fr.inc₂

theorem nonleaf_of {B : data.SourceVertex} (hB : B = Fr.B₁ ∨ B = Fr.B₂) :
    2 ≤ (GluingDatum.incidentEdges B.1.1).card := by
  rcases hB with rfl | rfl
  · exact Fr.nonleaf₁
  · exact Fr.nonleaf₂

end StableFrame

variable (hCompat : DanglingCompatible data hc hab hOne)
  (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block))

include hCompat in
/-- A labelled survivor's incoming occurrence survives. -/
theorem lift_survives (i : Fin 4) : ¬ IsDangling data (lift L i) := by
  obtain ⟨X, -, hbd⟩ := ValencyTwoSplit.exists_home L hCompat i
  exact ((mem_ndAt data X _).mp ((mem_bdAt data X _).mp hbd).1).1

/-- The incoming stable path of the survivor `i`. -/
noncomputable def pathOf (i : Fin 4) : StablePath data :=
  NonDanglingEdge.stablePath ⟨lift L i, lift_survives hCompat L i⟩

theorem lift_ne_of_intl {i : Fin 4} {e : data.SourceEdge}
    (he : e ∈ intl data hc hab hOne block) : lift L i ≠ e := by
  intro h
  exact lift_ne L i (h ▸ (intl_ends data hc hab hOne block he).2.2.2.2.1)

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
      exact lift_ne_of_intl L he (congrArg Subtype.val h)
    have hcons : Consecutive data ⟨lift L i, lift_survives hCompat L i⟩ ⟨e, heS⟩ :=
      ⟨hne, Z, ((mem_ndAt data Z _).mp hiZ).2, ((mem_ndAt data Z _).mp heZ).2, hZ2⟩
    exact ⟨⟨e, heS⟩, ((mem_ndAt data B _).mp heB).2, (stablePath_eq_of_consecutive hcons).symm,
      Or.inr ⟨Z, hZ, hZ2, hiZ, he, heZ⟩⟩

/-- A survivor's stable path reaches its home. -/
theorem incidence_pos_of_homed {i : Fin 4} {B : data.SourceVertex} (h : Homed L i B) :
    0 < StablePathCount.incidenceCount data B (pathOf hCompat L i) := by
  obtain ⟨x, hxB, hxP, -⟩ := witness_of_homed hCompat L h
  exact (StablePathCount.incidenceCount_pos_iff _ _ _).mpr ⟨x, hxB, hxP⟩

/-- An occurrence meets at most two vertices (`ValencyThreeLoopMerge.eq_of_three_incident`, in
any universe). -/
theorem eq_of_three_incident {e : data.SourceEdge} {X Y Z : data.SourceVertex}
    (hX : Incident data e X) (hY : Incident data e Y) (hZ : Incident data e Z) (hXZ : X ≠ Z)
    (hYZ : Y ≠ Z) : X = Y := by
  unfold Incident at hX hY hZ
  rcases hX with hX | hX <;> rcases hY with hY | hY <;> rcases hZ with hZ | hZ
  all_goals first
    | exact hX.symm.trans hY
    | exact absurd (hX.symm.trans hZ) hXZ
    | exact absurd (hY.symm.trans hZ) hYZ

/-- Three distinct occurrences at a divalent vertex are impossible. -/
theorem card_three_ndAt {Z : data.SourceVertex} (hZ2 : nonDanglingValency data Z = 2)
    {e₁ e₂ e₃ : data.SourceEdge} (h1 : e₁ ∈ ndAt data Z) (h2 : e₂ ∈ ndAt data Z)
    (h3 : e₃ ∈ ndAt data Z) (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) : False := by
  classical
  have hsub : ({e₁, e₂, e₃} : Finset data.SourceEdge) ⊆ ndAt data Z := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hc3 : ({e₁, e₂, e₃} : Finset data.SourceEdge).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
  have := Finset.card_le_card hsub
  rw [card_ndAt, hZ2] at this
  omega

/-- **A survivor has one home among the trivalent constituents.** -/
theorem homed_unique {i : Fin 4} {B B' : data.SourceVertex}
    (hB : B ∈ fib data hc hab hOne block) (hB3 : nonDanglingValency data B = 3)
    (hB' : B' ∈ fib data hc hab hOne block) (hB'3 : nonDanglingValency data B' = 3)
    (h : Homed L i B) (h' : Homed L i B') : B = B' := by
  rcases h with h | ⟨Z, hZ, hZ2, hiZ, e, he, heZ, heB⟩ <;>
    rcases h' with h' | ⟨Z', hZ', hZ2', hiZ', e', he', heZ', heB'⟩
  · exact ValencyTwoSplit.home_eq L hB hB' h h'
  · have := ValencyTwoSplit.home_eq L hB hZ' h hiZ'
    subst this
    omega
  · have := ValencyTwoSplit.home_eq L hZ hB' hiZ h'
    subst this
    omega
  · have hZZ := ValencyTwoSplit.home_eq L hZ hZ' hiZ hiZ'
    subst hZZ
    have hee : e = e' := by
      by_contra hne
      exact card_three_ndAt hZ2 hiZ heZ heZ' (lift_ne_of_intl L he) (lift_ne_of_intl L he') hne
    subst hee
    have hBZ : B ≠ Z := fun h ↦ by rw [h] at hB3; omega
    have hB'Z : B' ≠ Z := fun h ↦ by rw [h] at hB'3; omega
    exact eq_of_three_incident ((mem_ndAt data _ _).mp heB).2
      ((mem_ndAt data _ _).mp heB').2 ((mem_ndAt data _ _).mp heZ).2 hBZ hB'Z

/-- **Two labels homed at one trivalent constituent, on one incoming stable path, meet it
twice.** -/
theorem two_le_incidence {i j : Fin 4} (hij : i ≠ j) {B : data.SourceVertex}
    (hB3 : nonDanglingValency data B = 3)
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
    · have hBZ : B ≠ Z := fun h ↦ by rw [h] at hB3; omega
      have hBZ' : B ≠ Z' := fun h ↦ by rw [h] at hB3; omega
      have hZZ : Z = Z' := by
        by_contra hne
        have := eq_of_three_incident ((mem_ndAt data _ _).mp hxZ).2
          (h1 ▸ ((mem_ndAt data _ _).mp hx'Z').2) hxB (Ne.symm hBZ) (Ne.symm hBZ')
        exact hne this
      subst hZZ
      exact card_three_ndAt hZ2 hiZ hjZ' hxZ (fun h ↦ hij (lift_injective L h))
        (lift_ne_of_intl L hxI) (lift_ne_of_intl L hxI)
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

end Frame

/-! ## 3.  Both valency-two pictures carry a stable frame -/

section Pictures

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]
  {data : GluingDatum target degree} (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  (H : AnchorInput data hc hab hOne block)

omit [Fintype coordinate] [DecidableEq coordinate] in
include H in
/-- `Σ (nd - 2) = 2` over the pruned fibre at any valency-two anchor (the tree count and the
occurrence accounting; `DivInput.sum_excess` without the split). -/
theorem sum_excess :
    ∑ X ∈ fib data hc hab hOne block, ((nonDanglingValency data X : ℤ) - 2) = 2 := by
  classical
  have hNe : (fib data hc hab hOne block).Nonempty :=
    activeFibreVertices_nonempty_of_nonDanglingValency_ne_zero data hc hab hOne H.compat _
      (by rw [H.nd4]; norm_num)
  have hTree := internalEdges_card_add_one_eq_activeFibreVertices_card data hc hab hOne
    H.forest block hNe
  have hSum := sum_nonDanglingValency_activeFibre data hc hab hOne H.compat
    (mergedVertex data hc hab hOne block)
  have h4 : nonDanglingValency (contractDatum data hc hab hOne)
      (mergedVertex data hc hab hOne block) = 4 := H.nd4
  rw [h4] at hSum
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hSum' : ∑ X ∈ fib data hc hab hOne block, (nonDanglingValency data X : ℤ) =
      4 + 2 * ((internalEdges data hc hab hOne (mergedVertex data hc hab hOne block)).card : ℤ) := by
    exact_mod_cast hSum
  rw [hSum', fib, ← hTree]
  push_cast
  ring

include fd H in
/-- **Two trivalent constituents exhaust the excess**: every other active constituent is
divalent. -/
theorem nd_two_of_ne {Y Z : data.SourceVertex} (hY : Y ∈ fib data hc hab hOne block)
    (hZ : Z ∈ fib data hc hab hOne block) (hYZ : Y ≠ Z) (hY3 : nonDanglingValency data Y = 3)
    (hZ3 : nonDanglingValency data Z = 3) :
    ∀ X ∈ fib data hc hab hOne block, X ≠ Y → X ≠ Z → nonDanglingValency data X = 2 := by
  classical
  intro X hX hXY hXZ
  have hsum := sum_excess H
  have hnn : ∀ W ∈ fib data hc hab hOne block, (0 : ℤ) ≤ (nonDanglingValency data W : ℤ) - 2 :=
    fun W hW ↦ by
      have := ValencyThreeSplit.nonDanglingValency_two_le data fd
        ((mem_fib_iff data hc hab hOne block W).mp hW).2.2
      omega
  have hsub : ({Y, Z, X} : Finset data.SourceVertex) ⊆ fib data hc hab hOne block := by
    intro W hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl | rfl
    · exact hY
    · exact hZ
    · exact hX
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun W hW _ ↦ hnn W hW)
  rw [Finset.sum_insert (by simp [hYZ, Ne.symm hXY]), Finset.sum_pair (Ne.symm hXZ), hsum,
    hY3, hZ3] at hle
  have := ValencyThreeSplit.nonDanglingValency_two_le data fd
    ((mem_fib_iff data hc hab hOne block X).mp hX).2.2
  push_cast at hle
  omega

omit [Fintype coordinate] [DecidableEq coordinate] in
/-- The two ends of an internal occurrence lie over different endpoints. -/
theorem side_ne_of_intl {e : data.SourceEdge} (he : e ∈ intl data hc hab hOne block)
    {X Y : data.SourceVertex} (hX : Incident data e X) (hY : Incident data e Y) (hXY : X ≠ Y) :
    X.1.1 ≠ Y.1.1 := by
  obtain ⟨-, -, -, -, -, ha, hb⟩ := intl_ends data hc hab hOne block he
  unfold Incident at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · exact absurd rfl hXY
  · rw [ha, hb]; exact hab
  · rw [ha, hb]; exact hab.symm
  · exact absurd rfl hXY

include fd H in
/-- **The `(2,2)` picture's stable frame**: `A_a`, `A_b`, joined by the single occurrence `e₁`;
a pass-through hangs on the trivalent constituent over the other endpoint. -/
theorem nonempty_divFrame (Hd : DivInput data hc hab hOne block) :
    Nonempty (StableFrame data hc hab hOne block) := by
  classical
  obtain ⟨Ra, Rb, hRa, hRb, hRaa, hRbb, hRa3, hRb3⟩ := Hd.exists_R fd
  obtain ⟨e₁, he₁, he₁a, he₁b⟩ := Hd.exists_join fd hRa hRb hRaa hRbb hRb3
  have hinc : ∀ {e X}, e ∈ ndAt data X → Incident data e X := fun h ↦ ((mem_ndAt data _ _).mp h).2
  have hRab : Ra ≠ Rb := fun h ↦ hab (hRaa.symm.trans ((congrArg (·.1.1) h).trans hRbb))
  have he₁S : ¬ IsDangling data e₁ := ((mem_ndAt data _ _).mp he₁a).1
  have hend : ∀ {V}, Incident data e₁ V → V = Ra ∨ V = Rb := by
    intro V hV
    by_cases h1 : V = Ra
    · exact Or.inl h1
    by_cases h2 : V = Rb
    · exact Or.inr h2
    exact absurd (eq_of_three_incident (hinc he₁a) (hinc he₁b) hV (Ne.symm h1) (Ne.symm h2)) hRab
  have hClosed : ∀ x y : NonDanglingEdge data, Consecutive data x y → x.1 = e₁ → y.1 = e₁ := by
    rintro x y ⟨-, V, hxV, -, hV2⟩ hx
    rw [hx] at hxV
    rcases hend hxV with rfl | rfl
    · omega
    · omega
  have hover : ∀ x : NonDanglingEdge data,
      x.stablePath = NonDanglingEdge.stablePath ⟨e₁, he₁S⟩ → x.1.1.1 = contracted := by
    intro x hx
    have h := (eqvGen_iff_of_closed (property := fun x : NonDanglingEdge data ↦ x.1 = e₁) hClosed
      ((stablePath_eq_iff _ _).mp hx.symm)).mp rfl
    rw [h]
    exact (intl_ends data hc hab hOne block he₁).2.2.2.2.1
  have three : ∀ {Z}, Z ∈ fib data hc hab hOne block → nonDanglingValency data Z = 3 →
      Z = Ra ∨ Z = Rb := fun hZ h3 ↦ Hd.eq_R fd hRa hRb hRaa hRbb hRa3 hRb3 hZ h3
  have n23 : ∀ {Z}, Z ∈ fib data hc hab hOne block →
      nonDanglingValency data Z = 2 ∨ nonDanglingValency data Z = 3 := fun hZ ↦ by
    have := DivInput.nd_bounds fd hZ
    omega
  have attach : ∀ X ∈ fib data hc hab hOne block, nonDanglingValency data X = 2 →
      ∃ Q, (Q = Ra ∨ Q = Rb) ∧ ∃ e ∈ intl data hc hab hOne block, e ∈ ndAt data X ∧
        e ∈ ndAt data Q := by
    intro X hX hX2
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp (Hd.pass_cards fd hX hX2).1
    have heO : e ∈ ValencyThreeSplit.ndOver data X contracted := by
      rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨heX, heT⟩ := (ValencyThreeSplit.mem_ndOver data _ _ _).mp heO
    have heI := mem_intl_of_ndAt data hc hab hOne block hX heX heT
    obtain ⟨Q, hQ, heQ, -, hQX⟩ := DivInput.exists_other_end heI (hinc heX)
    have hQ3 := Hd.nd_three_of_attach fd hX hX2 hQ heI heX heQ hQX.symm
    exact ⟨Q, three hQ hQ3, e, heI, heX, heQ⟩
  have homedDiv : ∀ (L : Labelling (contractDatum data hc hab hOne)
      (limA data hc hab hOne block)) (i : Fin 4), ∃ B, (B = Ra ∨ B = Rb) ∧ Homed L i B := by
    intro L i
    obtain ⟨X, hX, hbd⟩ := ValencyTwoSplit.exists_home L H.compat i
    have hiX := ((mem_bdAt data _ _).mp hbd).1
    rcases n23 hX with hX2 | hX3
    · obtain ⟨Q, hQB, e, he, heX, heQ⟩ := attach X hX hX2
      exact ⟨Q, hQB, Or.inr ⟨X, hX, hX2, hiX, e, he, heX, heQ⟩⟩
    · exact ⟨X, three hX hX3, Or.inl hiX⟩
  have pairedDiv : ∀ (L : Labelling (contractDatum data hc hab hOne)
      (limA data hc hab hOne block)) (i j : Fin 4),
      Paired L i j ↔ ∃ B, (B = Ra ∨ B = Rb) ∧ Homed L i B ∧ Homed L j B := by
    intro L i j
    constructor
    · rintro ⟨X, hX, X', hX', hi, hj, hP⟩
      have viaTwo : ∀ {Z}, Z ∈ fib data hc hab hOne block → nonDanglingValency data Z = 2 →
          lift L i ∈ ndAt data Z → lift L j ∈ ndAt data Z →
          ∃ B, (B = Ra ∨ B = Rb) ∧ Homed L i B ∧ Homed L j B := by
        intro Z hZ hZ2 hiZ hjZ
        obtain ⟨Q, hQB, e, he, heZ, heQ⟩ := attach Z hZ hZ2
        exact ⟨Q, hQB, Or.inr ⟨Z, hZ, hZ2, hiZ, e, he, heZ, heQ⟩,
          Or.inr ⟨Z, hZ, hZ2, hjZ, e, he, heZ, heQ⟩⟩
      rcases hP with rfl | ⟨e, he, heX, heX', hdiv⟩
      · rcases n23 hX with h2 | h3
        · exact viaTwo hX h2 hi hj
        · exact ⟨X, three hX h3, Or.inl hi, Or.inl hj⟩
      · rcases n23 hX with h2 | h3 <;> rcases n23 hX' with h2' | h3'
        · by_cases hXX : X = X'
          · subst hXX
            exact viaTwo hX h2 hi hj
          · have := Hd.nd_three_of_attach fd hX h2 hX' he heX heX' hXX
            omega
        · exact ⟨X', three hX' h3', Or.inr ⟨X, hX, h2, hi, e, he, heX, heX'⟩, Or.inl hj⟩
        · exact ⟨X, three hX h3, Or.inl hi, Or.inr ⟨X', hX', h2', hj, e, he, heX', heX⟩⟩
        · rcases hdiv with h | h <;> omega
    · rintro ⟨B, hB, hi, hj⟩
      have hBmem : B ∈ fib data hc hab hOne block := by
        rcases hB with rfl | rfl
        · exact hRa
        · exact hRb
      have hB3 : nonDanglingValency data B = 3 := by
        rcases hB with rfl | rfl
        · exact hRa3
        · exact hRb3
      rcases hi with hi | ⟨Z, hZ, hZ2, hiZ, e, he, heZ, heB⟩ <;>
        rcases hj with hj | ⟨Z', hZ', hZ2', hjZ, e', he', heZ', heB'⟩
      · exact ⟨B, hBmem, B, hBmem, hi, hj, Or.inl rfl⟩
      · exact ⟨B, hBmem, Z', hZ', hi, hjZ, Or.inr ⟨e', he', heB', heZ', Or.inr hZ2'⟩⟩
      · exact ⟨Z, hZ, B, hBmem, hiZ, hj, Or.inr ⟨e, he, heZ, heB, Or.inl hZ2⟩⟩
      · have hZB : Z ≠ B := fun h ↦ by rw [h] at hZ2; omega
        have hZ'B : Z' ≠ B := fun h ↦ by rw [h] at hZ2'; omega
        have hs : Z.1.1 ≠ B.1.1 := side_ne_of_intl he (hinc heZ) (hinc heB) hZB
        have hs' : Z'.1.1 ≠ B.1.1 := side_ne_of_intl he' (hinc heZ') (hinc heB') hZ'B
        have hside : Z.1.1 = Z'.1.1 := by
          rcases DivInput.side hZ with h | h <;> rcases DivInput.side hZ' with h' | h' <;>
            rcases DivInput.side hBmem with h'' | h''
          all_goals first
            | exact h.trans h'.symm
            | exact absurd (h.trans h''.symm) hs
            | exact absurd (h'.trans h''.symm) hs'
        have := Hd.pass_unique fd hZ hZ' hZ2 hZ2' hside
        subst this
        exact ⟨Z, hZ, Z, hZ, hiZ, hjZ, Or.inl rfl⟩
  refine ⟨{ B₁ := Ra, B₂ := Rb, mem₁ := hRa, mem₂ := hRb, nd₁ := hRa3, nd₂ := hRb3, ne := hRab
            nonleaf₁ := by rw [hRaa, Hd.a2], nonleaf₂ := by rw [hRbb, Hd.b2], two := ?_
            P₀ := NonDanglingEdge.stablePath ⟨e₁, he₁S⟩
            inc₁ := ⟨⟨e₁, he₁S⟩, hinc he₁a, rfl⟩, inc₂ := ⟨⟨e₁, he₁S⟩, hinc he₁b, rfl⟩
            overC := hover, homed := homedDiv, paired_iff := pairedDiv }⟩
  intro X hX hXa hXb
  rcases n23 hX with h2 | h3
  · exact h2
  · rcases three hX h3 with h | h
    · exact absurd h hXa
    · exact absurd h hXb

include fd H in
/-- **The leaf picture's stable frame**: the two trivalent constituents `Y`, `Z` over the
trivalent endpoint, joined through the fold over the leaf by a two-occurrence stable path. -/
theorem nonempty_leafFrame {u v : target.V} (Hl : LeafInput data hc hab hOne block u v) :
    Nonempty (StableFrame data hc hab hOne block) := by
  classical
  have hinc : ∀ {e X}, e ∈ ndAt data X → Incident data e X := fun h ↦ ((mem_ndAt data _ _).mp h).2
  obtain ⟨F, hF, hFu⟩ := ValencyTwoResolutionMatch.exists_fold fd H Hl
  have hF2le : 2 ≤ nonDanglingValency data F := ValencyThreeSplit.nonDanglingValency_two_le data fd
    ((mem_fib_iff data hc hab hOne block F).mp hF).2.2
  have hcard : 1 < (ndAt data F).card := by rw [card_ndAt]; omega
  obtain ⟨e, he, e', he', hee'⟩ := Finset.one_lt_card.mp hcard
  have hoverU : ∀ {X : data.SourceVertex} {g : data.SourceEdge}, X.1.1 = u → Incident data g X →
      g.1.1 = contracted := by
    intro X g hXu hg
    have hgu := ValencyThreeSplit.target_mem_incidentEdges data hg
    rw [hXu] at hgu
    have hcu := ValencyThreeSplit.contracted_mem_incidentEdges hc
      (ValencyThreeSplit.side_of_huv hab Hl.huv).1
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp Hl.u1
    rw [ht, Finset.mem_singleton] at hgu hcu
    exact hgu.trans hcu.symm
  have heT := hoverU hFu (hinc he)
  have he'T := hoverU hFu (hinc he')
  have heI := mem_intl_of_ndAt data hc hab hOne block hF he heT
  have he'I := mem_intl_of_ndAt data hc hab hOne block hF he' he'T
  obtain ⟨Y, hY, heY, hYs, hYF⟩ := DivInput.exists_other_end heI (hinc he)
  obtain ⟨Z, hZ, he'Z, hZs, hZF⟩ := DivInput.exists_other_end he'I (hinc he')
  have hYv : Y.1.1 = v := (Hl.side hY).resolve_left fun h ↦ hYs (h.trans hFu.symm)
  have hZv : Z.1.1 = v := (Hl.side hZ).resolve_left fun h ↦ hZs (h.trans hFu.symm)
  have hY3 := Hl.nd_three fd hY hYv
  have hZ3 := Hl.nd_three fd hZ hZv
  have hYZ : Y ≠ Z := by
    intro h
    subst h
    exact hee' (ValencyTwoResolutionMatch.eq_of_same_ends data hc hab hOne block H.forest hF hY
      hYF.symm (hinc he) (hinc heY) (hinc he') (hinc he'Z))
  have htwo := nd_two_of_ne fd H hY hZ hYZ hY3 hZ3
  have hF2 : nonDanglingValency data F = 2 := htwo F hF hYF.symm hZF.symm
  have heS : ¬ IsDangling data e := ((mem_ndAt data _ _).mp he).1
  have he'S : ¬ IsDangling data e' := ((mem_ndAt data _ _).mp he').1
  have hcons : Consecutive data ⟨e, heS⟩ ⟨e', he'S⟩ :=
    ⟨fun h ↦ hee' (congrArg Subtype.val h), F, hinc he, hinc he', hF2⟩
  have hClosed : ∀ x y : NonDanglingEdge data, Consecutive data x y →
      x.1 ∈ intl data hc hab hOne block → y.1 ∈ intl data hc hab hOne block := by
    rintro x y ⟨-, V, hxV, hyV, hV2⟩ hx
    have hV : V ∈ fib data hc hab hOne block := by
      obtain ⟨h1, h2, -⟩ := intl_ends data hc hab hOne block hx
      rcases hxV with h | h
      · rw [← h]; exact h1
      · rw [← h]; exact h2
    have hVu : V.1.1 = u := by
      rcases Hl.side hV with h | h
      · exact h
      · have := Hl.nd_three fd hV h
        omega
    exact mem_intl_of_ndAt data hc hab hOne block hV ((mem_ndAt data _ _).mpr ⟨y.2, hyV⟩)
      (hoverU hVu hyV)
  have hover : ∀ x : NonDanglingEdge data,
      x.stablePath = NonDanglingEdge.stablePath ⟨e, heS⟩ → x.1.1.1 = contracted := by
    intro x hx
    have hxI := (eqvGen_iff_of_closed
      (property := fun x : NonDanglingEdge data ↦ x.1 ∈ intl data hc hab hOne block) hClosed
      ((stablePath_eq_iff _ _).mp hx.symm)).mp heI
    exact (intl_ends data hc hab hOne block hxI).2.2.2.2.1
  have three : ∀ {X}, X ∈ fib data hc hab hOne block → nonDanglingValency data X = 3 →
      X = Y ∨ X = Z := by
    intro X hX hX3
    by_contra hne
    simp only [not_or] at hne
    have := htwo X hX hne.1 hne.2
    omega
  have bd3 : ∀ {X} {f : data.SourceEdge}, X ∈ fib data hc hab hOne block → f ∈ ndAt data X →
      f.1.1 ≠ contracted → nonDanglingValency data X = 3 := fun hX hf hfT ↦
    (Hl.home fd hX ((mem_bdAt data _ _).mpr ⟨hf, hfT⟩)).2.1
  have direct : ∀ (L : Labelling (contractDatum data hc hab hOne)
      (limA data hc hab hOne block)) (i : Fin 4) (B : data.SourceVertex),
      Homed L i B → lift L i ∈ ndAt data B := by
    rintro L i B (h | ⟨Z', hZ', hZ2', hiZ', -⟩)
    · exact h
    · have := bd3 hZ' hiZ' (lift_ne L i)
      omega
  refine ⟨{ B₁ := Y, B₂ := Z, mem₁ := hY, mem₂ := hZ, nd₁ := hY3, nd₂ := hZ3, ne := hYZ
            nonleaf₁ := by rw [hYv, Hl.v3]; norm_num, nonleaf₂ := by rw [hZv, Hl.v3]; norm_num
            two := htwo, P₀ := NonDanglingEdge.stablePath ⟨e, heS⟩
            inc₁ := ⟨⟨e, heS⟩, hinc heY, rfl⟩
            inc₂ := ⟨⟨e', he'S⟩, hinc he'Z, (stablePath_eq_of_consecutive hcons).symm⟩
            overC := hover, homed := ?_, paired_iff := ?_ }⟩
  · intro L i
    obtain ⟨X, hX, hbd⟩ := ValencyTwoSplit.exists_home L H.compat i
    have hiX := ((mem_bdAt data _ _).mp hbd).1
    exact ⟨X, three hX (bd3 hX hiX (lift_ne L i)), Or.inl hiX⟩
  · intro L i j
    constructor
    · rintro ⟨X, hX, X', hX', hi, hj, hP⟩
      have hX3 := bd3 hX hi (lift_ne L i)
      have hX'3 := bd3 hX' hj (lift_ne L j)
      rcases hP with rfl | ⟨-, -, -, -, hdiv⟩
      · exact ⟨X, three hX hX3, Or.inl hi, Or.inl hj⟩
      · rcases hdiv with h | h <;> omega
    · rintro ⟨B, hB, hi, hj⟩
      have hBmem : B ∈ fib data hc hab hOne block := by
        rcases hB with rfl | rfl
        · exact hY
        · exact hZ
      exact ⟨B, hBmem, B, hBmem, direct L i B hi, direct L j B hj, Or.inl rfl⟩

include fd H in
/-- **Every valency-two anchor fibre carries a stable frame.** -/
theorem nonempty_stableFrame : Nonempty (StableFrame data hc hab hOne block) := by
  rcases H.cases fd with Hd | Hl | Hl
  · exact nonempty_divFrame fd H Hd
  · exact nonempty_leafFrame fd H Hl
  · exact nonempty_leafFrame fd H Hl

end Pictures

/-! ## 4.  A labelled-metric isomorphism pins the core slot of every survivor -/

section Rows

open ValencyThreeGeneral (slotColumn limitCol)
open ValencyThreeSplit (IsMetricIso)
open ValencyTwoSplit (RegrowthAnchor anchorOf)
open DraismaVargas.Count.SegmentWalls (Frame)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- Every occurrence of a regrowth's vanishing row lies over the contracted target
occurrence. -/
theorem facetOver (w : Regrowth core y degree) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) :
    ∀ x : NonDanglingEdge w.frame.data,
      x.stablePath = w.frame.fullDim.labelling.row.symm (w.frame.slot.symm e₀) →
        x.1.1.1 = w.frame.edgeOf w.column :=
  LeafFacetNoReturn.facetRow_over_contracted w.frame.data w.frame.fullDim (w.frame.coordsAt y)
    (w.frame.slot.symm e₀) (InheritedLimitRows.zero_coordinate w)
    (ValencyThreeCoreSlots.posCoord w) (ValencyThreeCoreSlots.facetZero w hpt)

/-- **No contracted return off the vanishing row, at every facet regrowth.** -/
theorem offRow (w : Regrowth core y degree) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y) :
    LeafFacetNoReturn.NoContractedReturnOffRow w.frame.data (w.frame.edgeOf w.column)
      (w.frame.fullDim.labelling.row.symm (w.frame.slot.symm e₀)) :=
  noReturnOffRow w.frame.data w.frame.fullDim _ (facetOver w hpt)

variable {w : Regrowth core y degree}
  {block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks}

/-- **The incoming stable path of a limit stable path** (Part II §5.1, convention (1)). -/
noncomputable abbrev inRow (H : RegrowthAnchor w block) :
    StablePath w.limit → StablePath w.frame.data :=
  StablePathFacetContraction.incomingRow w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) H.compat H.forest

/-- The incoming row of a limit row is not the vanishing row. -/
theorem inRow_ne_facet (H : RegrowthAnchor w block) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (Q : StablePath w.limit) :
    w.frame.fullDim.labelling.row (inRow H Q) ≠ w.frame.slot.symm e₀ := by
  intro h
  refine StablePathFacetContraction.incomingRow_ne_facet w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) H.compat H.forest
    (w.frame.coordsAt y) (w.frame.slot.symm e₀) (InheritedLimitRows.zero_coordinate w)
    (ValencyThreeCoreSlots.posCoord w) (ValencyThreeCoreSlots.facetZero w hpt) Q ?_
  rw [← h, Equiv.symm_apply_apply]

/-- **A limit entry is the incoming entry of the incoming row** (as
`ValencyThreeCoreSlots.natural_limit_eq`, but through `LeafFacetNoReturn.matrix_wallLabelling'`,
so that it holds at the leaf valency-two wall too). -/
theorem natural_limit_eq (H : RegrowthAnchor w block) {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (Q : StablePath w.limit)
    (t : (w.frame.limitTarget w.column).edges) :
    StableSourceMatrix.matrix w.limit Q t =
      w.frame.matrix (w.frame.fullDim.labelling.row (inRow H Q)) (limitCol w t) := by
  classical
  have hne : limitCol w t ≠
      w.frame.fullDim.labelling.targetEdge.symm (w.frame.edgeOf w.column) := by
    intro h
    apply unfoldEdge_ne_contracted rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) t
    have := congrArg w.frame.fullDim.labelling.targetEdge h
    simpa [limitCol] using this
  have hW := LeafFacetNoReturn.matrix_wallLabelling' w.frame.data w.frame.fullDim rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) H.compat H.forest
    (w.frame.coordsAt y) (w.frame.slot.symm e₀) (offRow w hpt)
    (ValencyThreeCoreSlots.rows_ne w hpt) (InheritedLimitRows.zero_coordinate w)
    (ValencyThreeCoreSlots.posCoord w) (ValencyThreeCoreSlots.facetZero w hpt) Q
    ⟨limitCol w t, hne⟩
  rw [StableSourceMatrix.labelling_matrix_eq] at hW
  refine Eq.trans ?_ hW
  congr 1
  · exact (Equiv.symm_apply_apply _ Q).symm
  · show t = StablePathFacetContraction.punctureTargetEquiv w.frame.fullDim.labelling rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
        ⟨limitCol w t, hne⟩
    rw [StablePathFacetContraction.punctureTargetEquiv_apply]
    have hT : w.frame.fullDim.labelling.targetEdge (limitCol w t) =
        unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
          t := by
      simp [limitCol]
    refine (foldEdge_unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) t (unfoldEdge_ne_contracted _ _ _ t)).symm.trans ?_
    exact congrArg _ (Subtype.ext hT.symm)

/-- **Limit-level pinning at a valency-two anchor** (as `ValencyThreeCoreSlots.row_inRow_map`,
with the leaf-wall row dictionary): a labelled-metric isomorphism of two regrowths' limits
carries every limit stable path to the one over the same core slot. -/
theorem row_inRow_map (w w' : Regrowth core y degree) {block block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block') {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (ψ : GeometricDatumIso w.limit w'.limit)
    (hψ : IsMetricIso w w' ψ) (Q : StablePath w.limit) :
    w'.frame.ident.row (inRow H' (ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) Q)) =
      w.frame.ident.row (inRow H Q) := by
  classical
  set s := w'.frame.ident.row (inRow H' (ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) Q))
    with hs
  set r := w.frame.fullDim.labelling.row (inRow H Q) with hr
  have hslot' : w'.frame.slot.symm s =
      w'.frame.fullDim.labelling.row
        (inRow H' (ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) Q)) := by
    rw [hs]
    simp [Frame.slot]
  have hagree : ∀ j, j ≠ w.column →
      w.frame.matrix r j = w.frame.matrix (w.frame.slot.symm s) j := by
    intro j hj
    obtain ⟨t, rfl⟩ := ValencyThreeCoreSlots.exists_limitCol_eq w j hj
    rw [← natural_limit_eq H hpt Q t,
      ← GeometricDatumIso.matrix_map ψ (ValencyThreeSplit.connected_limit w) Q t,
      natural_limit_eq H' hpt _ (ψ.targetEdge t), ← hslot']
    have hm := congrFun (hψ t).2 s
    simpa only [slotColumn] using hm
  have hrs : r = w.frame.slot.symm s := by
    by_contra hne
    exact w.frame.det_ne_zero (ValencyThreeRigidity.det_eq_zero_of_agree_off w.frame.matrix
      w.column r (w.frame.slot.symm s) (w.frame.slot.symm e₀) hne (inRow_ne_facet H hpt Q)
      (ValencyThreeRigidity.row_supported w hpt.1)
      (ValencyThreeCoreSlots.corner_ne_zero w hpt.1) hagree)
  have h1 : w.frame.slot r = w.frame.ident.row (inRow H Q) := by
    rw [hr]; simp [Frame.slot]
  rw [← h1, hrs, Equiv.apply_symm_apply]

/-- The stable frame of a regrowth's anchor. -/
abbrev RegrowthFrame (w : Regrowth core y degree)
    (block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks) :=
  StableFrame w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) block

/-- **The contracting stable path of a regrowth is the vanishing core slot**: all its
occurrences lie over the contracted target occurrence, so its matrix row is supported on the
degenerate column, as is the vanishing request row; in a nonsingular matrix they coincide. -/
theorem row_P₀ (Fr : RegrowthFrame w block) {e₀ : Fin p} (hy : y e₀ = 0) :
    w.frame.ident.row Fr.P₀ = e₀ := by
  classical
  set r := w.frame.fullDim.labelling.row Fr.P₀ with hr
  have hsupp : ∀ j, j ≠ w.column → w.frame.matrix r j = 0 := by
    intro j hj
    show GluingDatum.LengthMatrixPresentation.matrix _ r j = 0
    rw [StableSourceMatrix.labelling_matrix_eq, hr, Equiv.symm_apply_apply]
    unfold StableSourceMatrix.matrix
    refine Finset.sum_eq_zero fun e he ↦ absurd ?_ hj
    obtain ⟨⟨hS, hP⟩, hT⟩ := (StableSourceMatrix.mem_occurrences _ _ _).mp he
    apply w.frame.fullDim.labelling.targetEdge.injective
    rw [← hT]
    exact Fr.overC ⟨e, hS⟩ hP
  have hrs : r = w.frame.slot.symm e₀ := by
    by_contra hne
    exact w.frame.det_ne_zero (ValencyThreeRigidity.det_eq_zero_of_two_supported w.frame.matrix
      w.column r _ hne hsupp (ValencyThreeRigidity.row_supported w hy)
      (ValencyThreeCoreSlots.corner_ne_zero w hy))
  have h1 : w.frame.slot r = w.frame.ident.row Fr.P₀ := by
    rw [hr]; simp [Frame.slot]
  rw [← h1, hrs, Equiv.apply_symm_apply]

/-- The incoming path of a survivor is the incoming row of its limit stable path. -/
theorem pathOf_eq_inRow (H : RegrowthAnchor w block) (L : Labelling w.limit (anchorOf w block))
    (i : Fin 4) :
    pathOf H.compat L i = inRow H (NonDanglingEdge.stablePath
      (⟨L.e i, ((mem_ndAt _ _ _).mp (L.mem i)).1⟩ : NonDanglingEdge w.limit)) :=
  rfl

/-- The core slot of a labelled survivor. -/
noncomputable abbrev slotOf (H : RegrowthAnchor w block) (L : Labelling w.limit (anchorOf w block))
    (i : Fin 4) : Fin p :=
  w.frame.ident.row (pathOf H.compat L i)

/-- **A labelled-metric limit isomorphism preserves the core slot of every survivor**, for
labellings transported along it. -/
theorem slot_transport {w' : Regrowth core y degree} {block'}
    (H : RegrowthAnchor w block) (H' : RegrowthAnchor w' block') {e₀ : Fin p}
    (hpt : FacetMachine.FacetPoint e₀ y) (ψ : GeometricDatumIso w.limit w'.limit)
    (hψ : IsMetricIso w w' ψ) (L : Labelling w.limit (anchorOf w block))
    (L' : Labelling w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) (i : Fin 4) :
    slotOf H' L' i = slotOf H L i := by
  have hQ : NonDanglingEdge.stablePath
      (⟨L'.e i, ((mem_ndAt _ _ _).mp (L'.mem i)).1⟩ : NonDanglingEdge w'.limit) =
      ψ.stablePathEquiv (ValencyThreeSplit.connected_limit w) (NonDanglingEdge.stablePath
        (⟨L.e i, ((mem_ndAt _ _ _).mp (L.mem i)).1⟩ : NonDanglingEdge w.limit)) := by
    refine Eq.trans ?_ (GeometricDatumIso.stablePathEquiv_mk ψ _ _).symm
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext (hL i))
  show w'.frame.ident.row (pathOf H'.compat L' i) = w.frame.ident.row (pathOf H.compat L i)
  rw [pathOf_eq_inRow H' L' i, hQ, row_inRow_map w w' H H' hpt ψ hψ]
  rfl

end Rows

/-! ## 5.  The ends of `e₀` a labelling's survivors live at, and how two labellings can differ -/

section CoreCombinatorics

open ValencyThreeCoreSlots (NoParallel end_of_coreIncidence_pos eq_of_noParallel)
open ValencyThreeLoopMerge (Parallel parallel_unique incidence_lt_two_of_parallel NonPar
  eq_of_nonPar)

variable {n p : ℕ} {core : Core n p}

/-- **Beside a parallel slot, no slot other than `e₀` meets an end of `e₀` twice** (the parallel
slot itself included: meeting one end twice makes it a loop, which misses the other end). -/
theorem inc_lt_two (hcub : core.Cubic) {e₀ s₁ σ : Fin p} (he₀ : core.tail e₀ ≠ core.head e₀)
    (hs₁ : Parallel core e₀ s₁) (hσ : σ ≠ e₀) {x : Fin n}
    (hx : x = core.tail e₀ ∨ x = core.head e₀) : coreIncidence core x σ < 2 := by
  by_cases hσs : σ = s₁
  · subst hσs
    by_contra hge
    have h2 : coreIncidence core x σ = 2 := by
      have := coreIncidence_le_two core x σ
      omega
    unfold coreIncidence at h2
    have ht : core.tail σ = x := by
      by_contra h
      rw [if_neg h] at h2
      split_ifs at h2 <;> omega
    have hh : core.head σ = x := by
      by_contra h
      rw [if_pos ht, if_neg h] at h2
      omega
    obtain ⟨-, h1, h2'⟩ := hs₁
    unfold coreIncidence at h1 h2'
    rcases hx with rfl | rfl
    · have : core.tail σ ≠ core.head e₀ := by rw [ht]; exact he₀
      have : core.head σ ≠ core.head e₀ := by rw [hh]; exact he₀
      simp_all
    · have : core.tail σ ≠ core.tail e₀ := by rw [ht]; exact he₀.symm
      have : core.head σ ≠ core.tail e₀ := by rw [hh]; exact he₀.symm
      simp_all
  · exact incidence_lt_two_of_parallel hcub hs₁ hσ hσs hx

/-- A core without `NoParallel` has a parallel slot. -/
theorem exists_parallel {e₀ : Fin p} (h : ¬ NoParallel core e₀) : ∃ s, Parallel core e₀ s := by
  unfold NoParallel at h
  simp only [not_forall, not_or] at h
  obtain ⟨s, hs, h1, h2⟩ := h
  exact ⟨s, hs, Nat.pos_of_ne_zero h1, Nat.pos_of_ne_zero h2⟩

variable (slot : Fin 4 → Fin p) (vtx vtx' : Fin 4 → Fin n) {e₀ : Fin p}

/-- **At a core with no slot parallel to `e₀`, the slots fix the ends.** -/
theorem vtx_eq_of_noParallel (hpar : NoParallel core e₀)
    (hV1 : ∀ i, vtx i = core.tail e₀ ∨ vtx i = core.head e₀)
    (hV1' : ∀ i, vtx' i = core.tail e₀ ∨ vtx' i = core.head e₀)
    (hV2 : ∀ i, 0 < coreIncidence core (vtx i) (slot i))
    (hV2' : ∀ i, 0 < coreIncidence core (vtx' i) (slot i)) (hV4 : ∀ i, slot i ≠ e₀) :
    vtx' = vtx :=
  funext fun i ↦ eq_of_noParallel hpar (hV4 i) (hV1' i) (hV1 i) (hV2' i) (hV2 i)

/-- **Beside a parallel slot, the slots fix the ends up to exchanging the two survivors on the
parallel slot.** -/
theorem vtx_cases_of_parallel (hcub : core.Cubic) (hconn : core.Connected) (hn : 3 ≤ n)
    (he₀ : core.tail e₀ ≠ core.head e₀) (hpar : ¬ NoParallel core e₀)
    (hV1 : ∀ i, vtx i = core.tail e₀ ∨ vtx i = core.head e₀)
    (hV1' : ∀ i, vtx' i = core.tail e₀ ∨ vtx' i = core.head e₀)
    (hV2 : ∀ i, 0 < coreIncidence core (vtx i) (slot i))
    (hV2' : ∀ i, 0 < coreIncidence core (vtx' i) (slot i)) (hV4 : ∀ i, slot i ≠ e₀)
    (hV5 : ∀ i j, i ≠ j → slot i = slot j → vtx i = vtx j →
      2 ≤ coreIncidence core (vtx i) (slot i))
    (hV5' : ∀ i j, i ≠ j → slot i = slot j → vtx' i = vtx' j →
      2 ≤ coreIncidence core (vtx' i) (slot i))
    {i₁ i₂ : Fin 4} (h12 : i₁ ≠ i₂) (hs12 : slot i₁ = slot i₂) :
    (∀ k, k ≠ i₁ → k ≠ i₂ → vtx' k = vtx k) ∧
      ((vtx' i₁ = vtx i₁ ∧ vtx' i₂ = vtx i₂) ∨ (vtx' i₁ = vtx i₂ ∧ vtx' i₂ = vtx i₁)) := by
  obtain ⟨s₁, hs₁⟩ := exists_parallel hpar
  -- same slot, same end is impossible
  have sep : ∀ (f : Fin 4 → Fin n), (∀ i, f i = core.tail e₀ ∨ f i = core.head e₀) →
      (∀ i j, i ≠ j → slot i = slot j → f i = f j → 2 ≤ coreIncidence core (f i) (slot i)) →
      ∀ i j, i ≠ j → slot i = slot j → f i ≠ f j := by
    intro f hf1 hf5 i j hij hs hf
    have := hf5 i j hij hs hf
    have := inc_lt_two hcub he₀ hs₁ (hV4 i) (hf1 i)
    omega
  have ends : ∀ (f : Fin 4 → Fin n), (∀ i, f i = core.tail e₀ ∨ f i = core.head e₀) →
      f i₁ ≠ f i₂ → ∀ x, (x = core.tail e₀ ∨ x = core.head e₀) → x = f i₁ ∨ x = f i₂ := by
    intro f hf1 hne x hx
    rcases hf1 i₁ with h1 | h1 <;> rcases hf1 i₂ with h2 | h2 <;> rcases hx with rfl | rfl
    all_goals first
      | exact Or.inl h1.symm
      | exact Or.inr h2.symm
      | exact absurd (h1.trans h2.symm) hne
  have hne := sep vtx hV1 hV5 i₁ i₂ h12 hs12
  have hne' := sep vtx' hV1' hV5' i₁ i₂ h12 hs12
  -- the shared slot is the parallel one
  have hσpar : Parallel core e₀ (slot i₁) := by
    refine ⟨hV4 i₁, ?_, ?_⟩
    · rcases ends vtx hV1 hne (core.tail e₀) (Or.inl rfl) with h | h
      · rw [h]; exact hV2 i₁
      · rw [h, hs12]; exact hV2 i₂
    · rcases ends vtx hV1 hne (core.head e₀) (Or.inr rfl) with h | h
      · rw [h]; exact hV2 i₁
      · rw [h, hs12]; exact hV2 i₂
  refine ⟨fun k hk1 hk2 ↦ ?_, ?_⟩
  · have hsk : slot k ≠ slot i₁ := by
      intro hs
      rcases ends vtx hV1 hne (vtx k) (hV1 k) with h | h
      · exact sep vtx hV1 hV5 k i₁ hk1 hs h
      · exact sep vtx hV1 hV5 k i₂ hk2 (hs.trans hs12) h
    have hnp : NonPar core e₀ (slot k) := by
      unfold NonPar
      by_contra hc
      simp only [not_or] at hc
      exact hsk (parallel_unique hcub hconn hn he₀
        ⟨hV4 k, Nat.pos_of_ne_zero hc.1, Nat.pos_of_ne_zero hc.2⟩ hσpar)
    exact eq_of_nonPar hnp (hV1' k) (hV1 k) (hV2' k) (hV2 k)
  · rcases ends vtx hV1 hne (vtx' i₁) (hV1' i₁) with h | h
    · left
      refine ⟨h, ?_⟩
      rcases ends vtx hV1 hne (vtx' i₂) (hV1' i₂) with h' | h'
      · exact absurd (h.trans h'.symm) hne'
      · exact h'
    · right
      refine ⟨h, ?_⟩
      rcases ends vtx hV1 hne (vtx' i₂) (hV1' i₂) with h' | h'
      · exact h'
      · exact absurd (h.trans h'.symm) hne'

end CoreCombinatorics

/-! ## 6.  Reading the pairing on the core at a regrowth -/

section Reading

open ValencyThreeSplit (IsMetricIso)
open ValencyTwoSplit (RegrowthAnchor anchorOf)
open ValencyThreeCoreSlots (vertexOf coreIncidence_vertexOf end_of_coreIncidence_pos NoParallel)
open DraismaVargas.Count.SegmentWalls (Frame)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

section Congr

variable {target : CFGraph} {degree' : ℕ}
  {data : GluingDatum target degree'}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}
  {L L₂ : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block)}

theorem lift_congr {i k : Fin 4} (h : L.e i = L₂.e k) : lift L i = lift L₂ k := by
  unfold lift
  rw [h]

theorem homed_congr {i k : Fin 4} (h : L.e i = L₂.e k) (B : data.SourceVertex) :
    Homed L i B ↔ Homed L₂ k B := by
  unfold Homed
  rw [lift_congr h]

theorem paired_congr {i j k l : Fin 4} (h₁ : L.e i = L₂.e k) (h₂ : L.e j = L₂.e l) :
    Paired L i j ↔ Paired L₂ k l := by
  unfold Paired
  rw [lift_congr h₁, lift_congr h₂]

theorem pathOf_congr (hCompat : DanglingCompatible data hc hab hOne) {i k : Fin 4}
    (h : L.e i = L₂.e k) : pathOf hCompat L i = pathOf hCompat L₂ k := by
  unfold pathOf
  congr 1
  exact Subtype.ext (lift_congr h)

end Congr

variable {w : Regrowth core y degree}
  {block : (mergedPartition w.frame.data (w.frame.edgeOf w.column : w.frame.target.V ×
      w.frame.target.V).1 (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2).Blocks}

/-- **The survivor `i` lives at the end `x` of `e₀`**: its home is the branch constituent over
the core vertex `x`. -/
def At (Fr : RegrowthFrame w block) (L : Labelling w.limit (anchorOf w block)) (i : Fin 4)
    (x : Fin n) : Prop :=
  ∃ B, ∃ hB : B = Fr.B₁ ∨ B = Fr.B₂, Homed L i B ∧ vertexOf w.frame.ident B (Fr.nd_of hB) = x

variable (Fr : RegrowthFrame w block)

/-- Both branch constituents lie over ends of `e₀`. -/
theorem vertexOf_end {e₀ : Fin p} (hy : y e₀ = 0) {B : w.frame.data.SourceVertex}
    (hB : B = Fr.B₁ ∨ B = Fr.B₂) :
    vertexOf w.frame.ident B (Fr.nd_of hB) = core.tail e₀ ∨
      vertexOf w.frame.ident B (Fr.nd_of hB) = core.head e₀ := by
  apply end_of_coreIncidence_pos
  rw [← row_P₀ Fr hy, coreIncidence_vertexOf, StablePathCount.incidenceCount_pos_iff]
  exact Fr.inc_of hB

theorem eq_of_vertexOf_eq {B B' : w.frame.data.SourceVertex} (hB : B = Fr.B₁ ∨ B = Fr.B₂)
    (hB' : B' = Fr.B₁ ∨ B' = Fr.B₂)
    (h : vertexOf w.frame.ident B (Fr.nd_of hB) = vertexOf w.frame.ident B' (Fr.nd_of hB')) :
    B = B' :=
  congrArg Subtype.val (w.frame.ident.vertex.injective h)

variable (L : Labelling w.limit (anchorOf w block))

theorem exists_at (i : Fin 4) : ∃ x, At Fr L i x := by
  obtain ⟨B, hB, h⟩ := Fr.homed L i
  exact ⟨_, B, hB, h, rfl⟩

theorem at_unique {i : Fin 4} {x x' : Fin n} (h : At Fr L i x) (h' : At Fr L i x') : x = x' := by
  obtain ⟨B, hB, hi, rfl⟩ := h
  obtain ⟨B', hB', hi', rfl⟩ := h'
  have := homed_unique L (Fr.mem_of hB) (Fr.nd_of hB) (Fr.mem_of hB') (Fr.nd_of hB') hi hi'
  subst this
  rfl

theorem at_congr {L₂ : Labelling w.limit (anchorOf w block)} {i k : Fin 4} (h : L.e i = L₂.e k)
    (x : Fin n) : At Fr L i x ↔ At Fr L₂ k x := by
  unfold At
  simp only [homed_congr h]

/-- The end of `e₀` a survivor lives at. -/
noncomputable def vtxOf (i : Fin 4) : Fin n := (exists_at Fr L i).choose

theorem at_vtxOf (i : Fin 4) : At Fr L i (vtxOf Fr L i) := (exists_at Fr L i).choose_spec

theorem vtxOf_congr {L₂ : Labelling w.limit (anchorOf w block)} {i k : Fin 4}
    (h : L.e i = L₂.e k) : vtxOf Fr L i = vtxOf Fr L₂ k :=
  at_unique Fr L (at_vtxOf Fr L i) ((at_congr Fr L h _).mpr (at_vtxOf Fr L₂ k))

/-- **The pairing is "same end of `e₀`"**, as in Part II's valency-three case
(`subsec-case-v3`), where a combinatorial type records which edges meet at `A_u` and which at
`A_v`. -/
theorem paired_iff_vtx (i j : Fin 4) : Paired L i j ↔ vtxOf Fr L i = vtxOf Fr L j := by
  rw [Fr.paired_iff L i j]
  constructor
  · rintro ⟨B, hB, hi, hj⟩
    exact (at_unique Fr L (at_vtxOf Fr L i) ⟨B, hB, hi, rfl⟩).trans
      (at_unique Fr L ⟨B, hB, hj, rfl⟩ (at_vtxOf Fr L j))
  · intro h
    obtain ⟨B, hB, hi, hBi⟩ := at_vtxOf Fr L i
    obtain ⟨B', hB', hj, hBj⟩ := at_vtxOf Fr L j
    have := eq_of_vertexOf_eq Fr hB hB' (hBi.trans (h.trans hBj.symm))
    subst this
    exact ⟨B, hB, hi, hj⟩

theorem vtxOf_end {e₀ : Fin p} (hy : y e₀ = 0) (i : Fin 4) :
    vtxOf Fr L i = core.tail e₀ ∨ vtxOf Fr L i = core.head e₀ := by
  obtain ⟨B, hB, -, h⟩ := at_vtxOf Fr L i
  rw [← h]
  exact vertexOf_end Fr hy hB

theorem vtxOf_inc (H : RegrowthAnchor w block) (i : Fin 4) :
    0 < coreIncidence core (vtxOf Fr L i) (slotOf H L i) := by
  obtain ⟨B, hB, hi, h⟩ := at_vtxOf Fr L i
  rw [← h, coreIncidence_vertexOf]
  exact incidence_pos_of_homed H.compat L hi

theorem slotOf_ne (H : RegrowthAnchor w block) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (i : Fin 4) : slotOf H L i ≠ e₀ := by
  intro h
  apply inRow_ne_facet H hpt (NonDanglingEdge.stablePath
    (⟨L.e i, ((mem_ndAt _ _ _).mp (L.mem i)).1⟩ : NonDanglingEdge w.limit))
  rw [← pathOf_eq_inRow, ← h]
  simp [Frame.slot]

theorem vtxOf_two_le (H : RegrowthAnchor w block) {i j : Fin 4} (hij : i ≠ j)
    (hs : slotOf H L i = slotOf H L j) (hv : vtxOf Fr L i = vtxOf Fr L j) :
    2 ≤ coreIncidence core (vtxOf Fr L i) (slotOf H L i) := by
  obtain ⟨B, hB, hi, h⟩ := at_vtxOf Fr L i
  obtain ⟨B', hB', hj, h'⟩ := at_vtxOf Fr L j
  have := eq_of_vertexOf_eq Fr hB hB' (h.trans (hv.trans h'.symm))
  subst this
  rw [← h, coreIncidence_vertexOf]
  exact two_le_incidence H.compat L hij (Fr.nd_of hB) hi hj (w.frame.ident.row.injective hs)

end Reading

/-! ## 7.  Stage 3 at a core with no slot parallel to `e₀` -/

section NoParallelStage

open ValencyThreeSplit (IsMetricIso)
open ValencyTwoSplit (RegrowthAnchor anchorOf PairingMatch)
open ValencyThreeCoreSlots (NoParallel)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Matching one labelling matches all**: whether an isomorphism of limits carries the pairing
of one cover to the other's does not depend on the labelling. -/
theorem match_of_one {w w' : Regrowth core y degree} {block block'}
    (H : RegrowthAnchor w block) (ψ : GeometricDatumIso w.limit w'.limit)
    (L₀ : Labelling w.limit (anchorOf w block)) (L₀' : Labelling w'.limit (anchorOf w' block'))
    (hL₀ : ∀ i, L₀'.e i = ψ.sourceEdgeEquiv (L₀.e i))
    (hmatch : ∀ i j, Paired L₀ i j ↔ Paired L₀' i j)
    (L : Labelling w.limit (anchorOf w block)) (L' : Labelling w'.limit (anchorOf w' block'))
    (hL : ∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) (i j : Fin 4) :
    Paired L i j ↔ Paired L' i j := by
  classical
  have hπ : ∀ i, ∃ k, L.e i = L₀.e k := by
    intro i
    have hm := L.mem i
    rw [L₀.ndAt_eq H.nd4] at hm
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hm
    exact ⟨k, hk.symm⟩
  obtain ⟨k, hk⟩ := hπ i
  obtain ⟨l, hl⟩ := hπ j
  have hk' : L'.e i = L₀'.e k := by rw [hL i, hL₀ k, hk]
  have hl' : L'.e j = L₀'.e l := by rw [hL j, hL₀ l, hl]
  rw [paired_congr hk hl, paired_congr hk' hl']
  exact hmatch k l

/-- **Stage 3 at valency two, at every facet point of a core with no slot parallel to the
vanishing slot**, in its universal form: *every* labelled-metric isomorphism of two anchored
regrowths' limits carries the pairing of one cover to the other's.  Both pairings are
"same end of `e₀`" (`paired_iff_vtx`), and the end of each survivor is read off its core slot
(`vtx_eq_of_noParallel`), which the isomorphism preserves (`slot_transport`). -/
theorem pairingMatch_of_noParallel {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    (hpar : NoParallel core e₀) : PairingMatch core y degree := by
  intro w w' block block' H H' hsame
  obtain ⟨ψ, hψ⟩ := hsame
  refine ⟨ψ, hψ, fun L L' hL i j ↦ ?_⟩
  obtain ⟨Fr⟩ := nonempty_stableFrame w.frame.fullDim H
  obtain ⟨Fr'⟩ := nonempty_stableFrame w'.frame.fullDim H'
  have hslot := slot_transport H H' hpt ψ hψ L L' hL
  have hv := vtx_eq_of_noParallel (slotOf H L) (vtxOf Fr L) (vtxOf Fr' L') hpar
    (vtxOf_end Fr L hpt.1) (vtxOf_end Fr' L' hpt.1) (vtxOf_inc Fr L H)
    (fun k ↦ by rw [← hslot k]; exact vtxOf_inc Fr' L' H' k) (slotOf_ne L H hpt)
  rw [paired_iff_vtx Fr L, paired_iff_vtx Fr' L', hv]

end NoParallelStage

/-! ## 8.  The label-moving automorphism of a loop presenter, at valency two -/

section LoopSwap

open ValencyTwoSplit (RegrowthAnchor anchorOf)
open ValencyThreeCoreSlots (vertexOf)

variable {n p degree : ℕ} {y : Fin p → ℚ}

/-- **A label-moving automorphism** of a labelled limit: it fixes every target occurrence,
exchanges two labels and fixes the other two. -/
def SwapAt {T : CFGraph} {D : GluingDatum T degree} {A : D.SourceVertex} (L : Labelling D A) :
    Prop :=
  ∃ i i', i ≠ i' ∧ ∃ σ : GeometricDatumIso D D, (∀ e, σ.targetEdge e = e) ∧
    σ.sourceEdgeEquiv (L.e i) = L.e i' ∧ σ.sourceEdgeEquiv (L.e i') = L.e i ∧
    ∀ k, k ≠ i → k ≠ i' → σ.sourceEdgeEquiv (L.e k) = L.e k

section Label

variable {target : CFGraph} {degree' : ℕ}
  {data : GluingDatum target degree'}
  {a b : target.V} {contracted : target.edges}
  {hc : (contracted : target.V × target.V) = (a, b)} {hab : a ≠ b}
  {hOne : num_edges target a b = 1} {block : (mergedPartition data a b).Blocks}

/-- The limit partition over a label's target occurrence is the incoming one. -/
theorem label_edgePartition
    (L : Labelling (contractDatum data hc hab hOne) (limA data hc hab hOne block)) (i : Fin 4) :
    (contractDatum data hc hab hOne).edgePartition (L.e i).1.1 =
      data.edgePartition (lift L i).1.1 := by
  rw [← ValencyTwoSplit.sourceEdgeMap_lift L i]
  exact contractDatum_edgePartition_foldEdge data hc hab hOne ⟨_, lift_ne L i⟩

end Label

/-- **The loop swap at a valency-two anchor** (`ValencyThreeLoopMerge.exists_loopSwap`, at
valency two): over a core with a loop slot `f` at an end of the vanishing slot, the two
survivors on the loop row lie over one leaf edge (`PassOnceLollipopWitness.loopRowLengthTwo`),
which is not the contracted one, and the sheet swap `ValencyThreeSplit.swapIso` over it
exchanges them and fixes the other two survivors. -/
theorem swapAt_loop {cL : Core n p} {wL : Regrowth cL y degree} {blockL}
    (HL : RegrowthAnchor wL blockL) {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y)
    {f : Fin p} (hLoop : cL.tail f = cL.head f)
    (hend : cL.tail f = cL.tail e₀ ∨ cL.tail f = cL.head e₀)
    (L : Labelling wL.limit (anchorOf wL blockL)) : SwapAt L := by
  classical
  obtain ⟨Fr⟩ := nonempty_stableFrame wL.frame.fullDim HL
  set B := (wL.frame.ident.vertex.symm (cL.tail f)).1 with hBdef
  have hBB : B = Fr.B₁ ∨ B = Fr.B₂ := by
    have h1 := vertexOf_end Fr hpt.1 (Or.inl rfl : Fr.B₁ = Fr.B₁ ∨ Fr.B₁ = Fr.B₂)
    have h2 := vertexOf_end Fr hpt.1 (Or.inr rfl : Fr.B₂ = Fr.B₁ ∨ Fr.B₂ = Fr.B₂)
    have hne : vertexOf wL.frame.ident Fr.B₁ Fr.nd₁ ≠ vertexOf wL.frame.ident Fr.B₂ Fr.nd₂ :=
      fun h ↦ Fr.ne (congrArg Subtype.val (wL.frame.ident.vertex.injective h))
    have key : cL.tail f = vertexOf wL.frame.ident Fr.B₁ Fr.nd₁ ∨
        cL.tail f = vertexOf wL.frame.ident Fr.B₂ Fr.nd₂ := by
      rcases hend with h | h <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      all_goals first
        | exact Or.inl (h.trans h1.symm)
        | exact Or.inr (h.trans h2.symm)
        | exact absurd (h1.trans h2.symm) hne
    rcases key with h | h
    · left
      rw [hBdef, h]
      exact congrArg Subtype.val (Equiv.symm_apply_apply wL.frame.ident.vertex _)
    · right
      rw [hBdef, h]
      exact congrArg Subtype.val (Equiv.symm_apply_apply wL.frame.ident.vertex _)
  have hBfib := Fr.mem_of hBB
  -- the two occurrences of the loop row at its branch vertex
  have hcount := LollipopLeafRow.incidenceCount_eq_two_of_core_loop (wL.frame.member y) hLoop
  change ((StablePathCount.incidentEdges wL.frame.data B).filter
    fun edge ↦ edge.stablePath = wL.frame.ident.row.symm f).card = 2 at hcount
  obtain ⟨x, x', hxx', hEq⟩ := Finset.card_eq_two.mp hcount
  have hx : x ∈ (StablePathCount.incidentEdges wL.frame.data B).filter
      fun edge ↦ edge.stablePath = wL.frame.ident.row.symm f := by rw [hEq]; simp
  have hx' : x' ∈ (StablePathCount.incidentEdges wL.frame.data B).filter
      fun edge ↦ edge.stablePath = wL.frame.ident.row.symm f := by rw [hEq]; simp
  rw [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hx hx'
  set hLeaf := ValencyThreeLoopMerge.loopLeafOf wL hLoop
  have hT : ∀ z : NonDanglingEdge wL.frame.data, Incident wL.frame.data z.1 B →
      z.stablePath = wL.frame.ident.row.symm f → z.1.1.1 = leafEdge hLeaf :=
    fun z hInc hRow ↦ PassOnceLollipopWitness.loopRowLengthTwo (wL.frame.member y) hLoop z.1
      ⟨z.2, hRow⟩ hInc
  have hBne : B.1.1 ≠ LollipopLeafRow.loopLeaf (wL.frame.member y) hLoop := by
    intro h
    have h2 := Fr.nonleaf_of hBB
    have h1 : (GluingDatum.incidentEdges (target := wL.frame.target) B.1.1).card = 1 := by
      rw [h]; exact hLeaf
    omega
  have hℓ := leafEdge_mem hLeaf
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
  -- the leaf edge is not the contracted occurrence
  have hlc : leafEdge hLeaf ≠ wL.frame.edgeOf wL.column := by
    intro hlc
    have hover : ∀ z : NonDanglingEdge wL.frame.data, Incident wL.frame.data z.1 B →
        z.stablePath = wL.frame.ident.row.symm f →
        ∃ V ∈ fib wL.frame.data rfl (fst_ne_snd (wL.frame.edgeOf wL.column))
          (wL.frame.numEdges_edgeOf wL.column) blockL, Incident wL.frame.data z.1 V ∧ V ≠ B ∧
          V.1.1 = LollipopLeafRow.loopLeaf (wL.frame.member y) hLoop := by
      intro z hz hzR
      have hzT : z.1.1.1 = wL.frame.edgeOf wL.column := (hT z hz hzR).trans hlc
      have hzI := mem_intl_of_ndAt wL.frame.data rfl _ _ blockL hBfib
        ((mem_ndAt _ _ _).mpr ⟨z.2, hz⟩) hzT
      obtain ⟨V, hV, hzV, hVs, hVB⟩ := DivInput.exists_other_end hzI hz
      refine ⟨V, hV, ((mem_ndAt _ _ _).mp hzV).2, hVB, ?_⟩
      have h1 := ValencyThreeSplit.target_mem_incidentEdges wL.frame.data
        ((mem_ndAt _ _ _).mp hzV).2
      have h2 := ValencyThreeSplit.target_mem_incidentEdges wL.frame.data hz
      rw [hT z hz hzR] at h1 h2
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases hℓ with h3 | h3
      all_goals first
        | exact h1.symm.trans h3
        | exact absurd (h1.symm.trans h2) hVs
        | exact absurd (h2.symm.trans h3) hBne
    obtain ⟨V, hV, hxV, hVB, hVl⟩ := hover x hx.1 hx.2
    obtain ⟨V', hV', hx'V, hV'B, hV'l⟩ := hover x' hx'.1 hx'.2
    have hnot : ∀ {W}, W.1.1 = LollipopLeafRow.loopLeaf (wL.frame.member y) hLoop →
        W ≠ Fr.B₁ ∧ W ≠ Fr.B₂ := by
      intro W hW
      have h1 : (GluingDatum.incidentEdges (target := wL.frame.target) W.1.1).card = 1 := by
        rw [hW]; exact hLeaf
      constructor
      · rintro rfl
        have := Fr.nonleaf₁
        omega
      · rintro rfl
        have := Fr.nonleaf₂
        omega
    have hV2 : nonDanglingValency wL.frame.data V = 2 :=
      Fr.two V hV (hnot hVl).1 (hnot hVl).2
    have hVV : V' = V := by
      by_contra hne
      have h0 := LeafFacetNoReturn.nonDanglingValency_eq_zero_of_ne_fold wL.frame.data
        wL.frame.fullDim V V' (hV'l.trans hVl.symm) (by rw [hVl]; exact hLeaf) hV2 hne
      exact ((mem_fib_iff _ _ _ _ _ _).mp hV').2.2 h0
    subst hVV
    exact hxx' (Subtype.ext (ValencyTwoResolutionMatch.eq_of_same_ends wL.frame.data rfl
      (fst_ne_snd (wL.frame.edgeOf wL.column)) (wL.frame.numEdges_edgeOf wL.column) blockL
      HL.forest hBfib hV' (Ne.symm hVB) hx.1 hxV hx'.1 hx'V))
  -- the two loop survivors are labels
  have hbd : ∀ z : NonDanglingEdge wL.frame.data, Incident wL.frame.data z.1 B →
      z.stablePath = wL.frame.ident.row.symm f → z.1 ∈ bdAt wL.frame.data
        (wL.frame.edgeOf wL.column) B := fun z hz hzR ↦
    (mem_bdAt _ _ _).mpr ⟨(mem_ndAt _ _ _).mpr ⟨z.2, hz⟩, by rw [hT z hz hzR]; exact hlc⟩
  obtain ⟨i, hi⟩ := ValencyTwoSplit.exists_lift_eq L HL.compat HL.nd4 hBfib (hbd x hx.1 hx.2)
  obtain ⟨i', hi'⟩ := ValencyTwoSplit.exists_lift_eq L HL.compat HL.nd4 hBfib (hbd x' hx'.1 hx'.2)
  have hii' : i ≠ i' := by
    intro h
    subst h
    exact hxx' (Subtype.ext (hi.symm.trans hi'))
  have hTi : (lift L i).1.1 = leafEdge hLeaf := by rw [hi]; exact hT x hx.1 hx.2
  have hTi' : (lift L i').1.1 = leafEdge hLeaf := by rw [hi']; exact hT x' hx'.1 hx'.2
  set t₂ := (L.e i).1.1 with ht₂
  have h30 : (L.e i').1.1 = t₂ :=
    (ValencyTwoSplit.lift_target_eq_iff L i' i).mp (hTi'.trans hTi.symm)
  -- the leaf edge is discrete
  have hdiscIn : ∀ k, (wL.frame.data.edgePartition (leafEdge hLeaf)).repr k = k := by
    intro k
    apply ValencyThreeLoopMerge.repr_eq_of_blockCard
    exact LeafFibre.sourceEdgeIndex_eq_one_above_leaf wL.frame.fullDim hLeaf
      (edge := ⟨(leafEdge hLeaf, (wL.frame.data.edgePartition (leafEdge hLeaf)).repr k),
        (wL.frame.data.edgePartition (leafEdge hLeaf)).repr_idem k⟩) rfl
  have hdisc : ∀ k, (wL.limit.edgePartition t₂).repr k = k := by
    intro k
    have h := label_edgePartition L i
    change wL.limit.edgePartition t₂ = _ at h
    rw [h, hTi]
    exact hdiscIn k
  -- the two sheets are related at both ends of the leaf edge
  set s₀ := (L.e i).1.2
  set s₃ := (L.e i').1.2
  have hs₀ : s₀ = (lift L i).1.2 := ValencyTwoResolutionMatch.label_sheet L i
  have hs₃ : s₃ = (lift L i').1.2 := ValencyTwoResolutionMatch.label_sheet L i'
  have hIi : Incident wL.frame.data (lift L i) B := by rw [hi]; exact hx.1
  have hIi' : Incident wL.frame.data (lift L i') B := by rw [hi']; exact hx'.1
  obtain ⟨hTB, hRB0⟩ := (incident_iff_target_mem_and_rel wL.frame.data _ _).mp hIi
  obtain ⟨-, hRB3⟩ := (incident_iff_target_mem_and_rel wL.frame.data _ _).mp hIi'
  have hC0 := (incident_iff_target_mem_and_rel wL.frame.data _ _).mp
    (LeafFibre.incident_coreVertex_of_mem_leafSurvivors wL.frame.fullDim hLeaf
      ((LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨lift_survives HL.compat L i, hTi⟩))
  have hC3 := (incident_iff_target_mem_and_rel wL.frame.data _ _).mp
    (LeafFibre.incident_coreVertex_of_mem_leafSurvivors wL.frame.fullDim hLeaf
      ((LeafFibre.mem_leafSurvivors hLeaf).mpr ⟨lift_survives HL.compat L i', hTi'⟩))
  rw [hTi] at hTB
  have hInRel : ∀ z, ((leafEdge hLeaf : wL.frame.target.V × wL.frame.target.V).1 = z ∨
      (leafEdge hLeaf : wL.frame.target.V × wL.frame.target.V).2 = z) →
      (wL.frame.data.vertexPartition z).Rel s₀ s₃ := by
    intro z hz
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hTB
    have hzcase : z = LollipopLeafRow.loopLeaf (wL.frame.member y) hLoop ∨ z = B.1.1 := by
      rcases hz with hz | hz <;> rcases hℓ with h3 | h3 <;> rcases hTB with hb | hb
      all_goals first
        | exact Or.inl (hz.symm.trans h3)
        | exact Or.inr (hz.symm.trans hb)
        | exact absurd (h3.symm.trans hb).symm hBne
    rcases hzcase with rfl | rfl
    · rw [hs₀, hs₃]; exact hC0.2.symm.trans hC3.2
    · rw [hs₀, hs₃]; exact hRB0.symm.trans hRB3
  have hunfold : unfoldEdge rfl (fst_ne_snd (wL.frame.edgeOf wL.column))
      (wL.frame.numEdges_edgeOf wL.column) t₂ = leafEdge hLeaf :=
    (ValencyTwoResolutionMatch.label_unfold L i).trans hTi
  have hrel : ∀ v, ((t₂ : (wL.frame.limitTarget wL.column).V ×
      (wL.frame.limitTarget wL.column).V).1 = v ∨
      (t₂ : (wL.frame.limitTarget wL.column).V × (wL.frame.limitTarget wL.column).V).2 = v) →
      (wL.limit.vertexPartition v).Rel s₀ s₃ := by
    intro v hv
    have hends := fold_unfoldEdge rfl (fst_ne_snd (wL.frame.edgeOf wL.column))
      (wL.frame.numEdges_edgeOf wL.column) t₂
    rw [hunfold] at hends
    rcases hv with hv | hv
    · have h1 := (congrArg Prod.fst hends).trans hv
      rw [← h1]
      exact (vertexPartition_refines wL.frame.data _ _).rel (hInRel _ (Or.inl rfl))
    · have h1 := (congrArg Prod.snd hends).trans hv
      rw [← h1]
      exact (vertexPartition_refines wL.frame.data _ _).rel (hInRel _ (Or.inr rfl))
  refine ⟨i, i', hii', ValencyThreeSplit.swapIso wL.limit t₂ s₀ s₃ hdisc hrel, fun _ ↦ rfl,
    ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (t₂, (if t₂ = t₂ then Equiv.swap s₀ s₃ else Equiv.refl _) s₀) = (L.e i').1
    rw [if_pos rfl, Equiv.swap_apply_left]
    exact Prod.ext h30.symm rfl
  · apply Subtype.ext
    change ((L.e i').1.1, (if (L.e i').1.1 = t₂ then Equiv.swap s₀ s₃ else Equiv.refl _) s₃) =
      (L.e i).1
    rw [if_pos h30, Equiv.swap_apply_right]
    exact Prod.ext h30 rfl
  · intro k hk hk'
    apply Subtype.ext
    change ((L.e k).1.1, (if (L.e k).1.1 = t₂ then Equiv.swap s₀ s₃ else Equiv.refl _)
      (L.e k).1.2) = (L.e k).1
    split_ifs with hkt
    · have h0 : (L.e k).1.2 ≠ s₀ := fun h ↦ hk (L.inj (Subtype.ext (Prod.ext hkt h)))
      have h3 : (L.e k).1.2 ≠ s₃ := fun h ↦
        hk' (L.inj (Subtype.ext (Prod.ext (hkt.trans h30.symm) h)))
      rw [Equiv.swap_apply_of_ne_of_ne h0 h3]
    · rfl

/-- **The loop swap transports along any geometric isomorphism of limits.** -/
theorem swapAt_of_limitIso {c cL : Core n p} {w : Regrowth c y degree}
    {wL : Regrowth cL y degree} {block blockL} (H : RegrowthAnchor w block)
    (HL : RegrowthAnchor wL blockL)
    (hL : ∀ LL : Labelling wL.limit (anchorOf wL blockL), SwapAt LL)
    (χ : GeometricDatumIso w.limit wL.limit) (L : Labelling w.limit (anchorOf w block)) :
    SwapAt L := by
  obtain ⟨LL, hLL⟩ := ValencyTwoSplit.exists_transport w wL H HL χ L
  obtain ⟨i, i', hii', σ, hσT, h1, h2, h3⟩ := hL LL
  have hback : ∀ i j, σ.sourceEdgeEquiv (LL.e i) = LL.e j →
      (χ.trans (σ.trans χ.symm)).sourceEdgeEquiv (L.e i) = L.e j := by
    intro i j hij
    change χ.symm.sourceEdgeEquiv (σ.sourceEdgeEquiv (χ.sourceEdgeEquiv (L.e i))) = L.e j
    have e1 : χ.sourceEdgeEquiv (L.e i) = LL.e i := (hLL i).symm
    have e2 : σ.sourceEdgeEquiv (LL.e i) = χ.sourceEdgeEquiv (L.e j) := hij.trans (hLL j)
    erw [e1, e2]
    exact StarCensusEngine.symm_sourceEdgeEquiv_apply χ (L.e j)
  refine ⟨i, i', hii', χ.trans (σ.trans χ.symm), fun e ↦ ?_, hback i i' h1, hback i' i h2,
    fun k hk hk' ↦ hback k k (h3 k hk hk')⟩
  change χ.targetEdge.symm (σ.targetEdge (χ.targetEdge e)) = e
  rw [hσT, Equiv.symm_apply_apply]

end LoopSwap

/-! ## 9.  Stage 3 beside a parallel slot, and the supply -/

section Assembly

open ValencyThreeSplit (IsMetricIso)
open ValencyTwoSplit (RegrowthAnchor anchorOf PairingMatch)
open ValencyThreeCoreSlots (NoParallel)
open ValencyThreeLoopMerge (LoopPresented)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **Stage 3 at valency two beside a parallel slot, given label-moving automorphisms.**  The
two survivors exchanged by the automorphism share a core slot (`slot_transport` along the
automorphism), which is then the parallel slot; every other survivor's end of `e₀` is read off
its slot, and the two on the parallel slot are either at the same ends on both covers (then `ψ`
matches the pairings) or at exchanged ends (then `ψ ≫ σ'` does) -- `vtx_cases_of_parallel`. -/
theorem pairingMatch_of_swap (hcub : core.Cubic) (hconn : core.Connected) (hn : 3 ≤ n)
    {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y) (he₀ : core.tail e₀ ≠ core.head e₀)
    (hswap : ∀ (w : Regrowth core y degree) (block) (_H : RegrowthAnchor w block)
      (L : Labelling w.limit (anchorOf w block)), SwapAt L) :
    PairingMatch core y degree := by
  classical
  by_cases hpar : NoParallel core e₀
  · exact pairingMatch_of_noParallel hpt hpar
  intro w w' block block' H H' hsame
  obtain ⟨ψ, hψ⟩ := hsame
  obtain ⟨Fr⟩ := nonempty_stableFrame w.frame.fullDim H
  obtain ⟨Fr'⟩ := nonempty_stableFrame w'.frame.fullDim H'
  obtain ⟨L₀⟩ := ValencyTwoSplit.nonempty_labelling _ _ H.nd4
  obtain ⟨L₀', hL₀⟩ := ValencyTwoSplit.exists_transport w w' H H' ψ L₀
  obtain ⟨j₁, j₂, h12, σ, hσT, hσ1, hσ2, hσk⟩ := hswap w' block' H' L₀'
  have hσm : IsMetricIso w' w' σ := fun e ↦ by rw [hσT]; exact ⟨rfl, rfl⟩
  have hslot := slot_transport H H' hpt ψ hψ L₀ L₀' hL₀
  -- the exchanged survivors share a core slot
  have hs12 : slotOf H L₀ j₁ = slotOf H L₀ j₂ := by
    obtain ⟨Lσ, hLσ⟩ := ValencyTwoSplit.exists_transport w' w' H' H' σ L₀'
    have h1 := slot_transport H' H' hpt σ hσm L₀' Lσ hLσ j₁
    have h2 : slotOf H' Lσ j₁ = slotOf H' L₀' j₂ := by
      show w'.frame.ident.row (pathOf H'.compat Lσ j₁) =
        w'.frame.ident.row (pathOf H'.compat L₀' j₂)
      rw [pathOf_congr H'.compat ((hLσ j₁).trans hσ1)]
    rw [← hslot j₁, ← hslot j₂, ← h1, h2]
  have hV2' : ∀ k, 0 < coreIncidence core (vtxOf Fr' L₀' k) (slotOf H L₀ k) := fun k ↦ by
    rw [← hslot k]; exact vtxOf_inc Fr' L₀' H' k
  have hV5 : ∀ i j, i ≠ j → slotOf H L₀ i = slotOf H L₀ j → vtxOf Fr L₀ i = vtxOf Fr L₀ j →
      2 ≤ coreIncidence core (vtxOf Fr L₀ i) (slotOf H L₀ i) :=
    fun i j hij hs hv ↦ vtxOf_two_le Fr L₀ H hij hs hv
  have hV5' : ∀ i j, i ≠ j → slotOf H L₀ i = slotOf H L₀ j →
      vtxOf Fr' L₀' i = vtxOf Fr' L₀' j →
      2 ≤ coreIncidence core (vtxOf Fr' L₀' i) (slotOf H L₀ i) := by
    intro i j hij hs hv
    rw [← hslot i]
    exact vtxOf_two_le Fr' L₀' H' hij (by rw [hslot i, hslot j]; exact hs) hv
  obtain ⟨hoff, hcase⟩ := vtx_cases_of_parallel (slotOf H L₀) (vtxOf Fr L₀) (vtxOf Fr' L₀')
    hcub hconn hn he₀ hpar (vtxOf_end Fr L₀ hpt.1) (vtxOf_end Fr' L₀' hpt.1)
    (vtxOf_inc Fr L₀ H) hV2' (slotOf_ne L₀ H hpt) hV5 hV5' h12 hs12
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hv : ∀ k, vtxOf Fr' L₀' k = vtxOf Fr L₀ k := by
      intro k
      by_cases hk1 : k = j₁
      · rw [hk1]; exact e1
      by_cases hk2 : k = j₂
      · rw [hk2]; exact e2
      exact hoff k hk1 hk2
    refine ⟨ψ, hψ, match_of_one H ψ L₀ L₀' hL₀ fun i j ↦ ?_⟩
    rw [paired_iff_vtx Fr L₀, paired_iff_vtx Fr' L₀', hv i, hv j]
  · have hψ₂ : IsMetricIso w w' (ψ.trans σ) := by
      intro e
      have : (ψ.trans σ).targetEdge e = ψ.targetEdge e := by
        change σ.targetEdge (ψ.targetEdge e) = ψ.targetEdge e
        exact hσT _
      rw [this]
      exact hψ e
    obtain ⟨L₂, hL₂⟩ := ValencyTwoSplit.exists_transport w w' H H' (ψ.trans σ) L₀
    have hL₂e : ∀ k, L₂.e k = σ.sourceEdgeEquiv (L₀'.e k) := fun k ↦ by
      rw [hL₂ k, hL₀ k]; rfl
    have hv : ∀ k, vtxOf Fr' L₂ k = vtxOf Fr L₀ k := by
      intro k
      by_cases hk1 : k = j₁
      · subst hk1
        rw [vtxOf_congr Fr' L₂ ((hL₂e k).trans hσ1)]
        exact e2
      by_cases hk2 : k = j₂
      · subst hk2
        rw [vtxOf_congr Fr' L₂ ((hL₂e k).trans hσ2)]
        exact e1
      rw [vtxOf_congr Fr' L₂ ((hL₂e k).trans (hσk k hk1 hk2))]
      exact hoff k hk1 hk2
    refine ⟨ψ.trans σ, hψ₂, match_of_one H (ψ.trans σ) L₀ L₂ hL₂ fun i j ↦ ?_⟩
    rw [paired_iff_vtx Fr L₀, paired_iff_vtx Fr' L₂, hv i, hv j]

/-- **Stage 3 at valency two over a cubic core with no slot parallel to `e₀` or with loop
presenters** (the per-side input, from `CensusAssembly.noParallel_or_loopPresented`). -/
theorem pairingMatch_of_side (hcub : core.Cubic) (hconn : core.Connected) (hn : 3 ≤ n)
    {e₀ : Fin p} (hpt : FacetMachine.FacetPoint e₀ y) (he₀ : core.tail e₀ ≠ core.head e₀)
    (hP : NoParallel core e₀ ∨ LoopPresented core e₀ y degree) :
    PairingMatch core y degree := by
  rcases hP with hpar | hP
  · exact pairingMatch_of_noParallel hpt hpar
  refine pairingMatch_of_swap hcub hconn hn hpt he₀ fun w block H L ↦ ?_
  obtain ⟨cL, f, hLoop, hend, hnl, wL, ⟨χ⟩⟩ := hP w
  have hval : CensusAssembly.mergedValency wL = 2 :=
    (CensusAssembly.mergedValency_eq_of_iso w wL hpt he₀ hnl χ).trans H.valency
  obtain ⟨blockL, HL⟩ := ValencyTwoSplit.exists_regrowthAnchor wL e₀ hpt hnl hval
  exact swapAt_of_limitIso H HL (fun LL ↦ swapAt_loop HL hpt hLoop hend LL) χ L

/-- **Headline: stage 3 of the valency-two count at every resolved datum.** -/
theorem pairingMatchSupply (hDegree : 3 ≤ degree) (hn : 3 ≤ n) :
    ValencyTwoCensus.PairingMatchSupply n p degree := by
  intro c c' e₀ y₀ ε R
  exact ⟨pairingMatch_of_side c.cubic c.connected hn R.datum.point R.nonloop
      (CensusAssembly.noParallel_or_loopPresented R.generic hDegree R.resolvedL),
    pairingMatch_of_side c'.cubic c'.connected hn R.datum.point R.nonloop'
      (CensusAssembly.noParallel_or_loopPresented R.generic hDegree R.resolvedR)⟩

/-- **Headline: the valency-two clause supply**, unconditionally for `3 ≤ degree`,
`3 ≤ n`. -/
theorem v2ClauseSupply (hDegree : 3 ≤ degree) (hn : 3 ≤ n) :
    CensusAssembly.V2ClauseSupply n p degree :=
  ValencyTwoCensus.v2ClauseSupply_of_pairingMatch hDegree hn (pairingMatchSupply hDegree hn)

end Assembly

/-! ## 10.  Non-vacuity: the headline at genus six -/

example : CensusAssembly.V2ClauseSupply (4 * 2 + 2) (6 * 2 + 3) (2 + 2) :=
  v2ClauseSupply (by norm_num) (by norm_num)

example : ValencyTwoCensus.PairingMatchSupply (4 * 2 + 2) (6 * 2 + 3) (2 + 2) :=
  pairingMatchSupply (by norm_num) (by norm_num)

end DraismaVargas.Count.ValencyTwoPairing
