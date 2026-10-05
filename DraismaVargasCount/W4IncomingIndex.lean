module

public import DraismaVargasCount.RowGeodesic
public import DraismaVargasCount.W4UnitBalance

@[expose] public section

/-!
# The `{w4}` wall index hypothesis, and Equation (1)

**Source.**  Vargas, Part II (arXiv:2609.09109), `lemma-edge-deno` case (b), **lower** half,
and `prop-signed-mult` (1) with its proof; Draisma--Vargas Part I (arXiv:1909.12924), case
`{w4}`, Figures 26--27 and **Equation (1)**.  `Count.W4UnitBalance` proves the leaf half of
Equation (1) unconditionally and reduces its balance half to a single named hypothesis,
`hIndex`.  This file discharges `hIndex` and instantiates `Count.W4UnitBalance`'s three
conditional theorems.

## The hypothesis `hIndex`, and what discharges it

`Count.W4UnitBalance`'s hypothesis is

    hIndex : ∀ (pairing : Fin 3) (sourceBlock : WallBlock data wall)
               (path : StablePath data),
      W4OutgoingLimitMatrix.blockRegrownRow input pairing sourceBlock = some path →
        data.sourceEdgeIndex
            (W4OutgoingStableRows.blockOldSourceEdge input pairing sourceBlock) ∣
          Count.TrivalentWeight.incomingRowDenominator data path

-- *the dilation index of a regrowing wall block's canonical incoming
occurrence divides the incoming row denominator of the row that occurrence
carries.*  By
`Count.TrivalentWeight.dvd_incomingRowDenominator_of_occurrences_eq_singleton`
it follows from the **census**: that occurrence is alone in its
`(row, star edge)` fibre of the incoming matrix `A₀`.

The census has a local half and a global half, and this file separates them.

* **Local half, unconditional** (`eq_of_mem_occurrences_of_sameBlock`): a
  second element of that fibre lying above the *same* old wall block is the
  same occurrence.  This is exactly the content of the auxiliary source
  pictures' `only_surviving` fields (`W4StableSource.AuxR0Nd2Picture`,
  `AuxR0Nd3Picture`), i.e. of `NonDanglingStarInjective` at the wall block.  No
  genus, no walk, no receipt.
* **Global half**: nothing local forbids the row from returning to the wall
  through a *different* old wall block above the same star edge.  That is the
  row-geodesic statement, and it is discharged here from `graph_connected
  target` and `genus target = 0` through `Count.TargetGeodesic`, in two shapes
  that between them cover both regrowing pictures **without `HasPathEnds`**:
  * `rowTargetInjective_of_pathEnd_of_genusZero` -- `Count.RowGeodesic`'s
    `rowTargetInjective_of_genusZero` with `HasPathEnds data` replaced by *one
    named end of the row in question*.  An **nd3** wall block supplies such an
    end for free: its old wall vertex is trivalent
    (`W4OutgoingStableRows.nd3_old_nonDanglingValency`), so the row ends there.
  * `occurrences_eq_singleton_of_junction_of_genusZero` -- the simple column at
    a surviving valency-**two** vertex, where the row passes *through* and no
    end is available.  The row is covered by the two traversals leaving the
    junction, each started with the opposite survivor already marked visited so
    that neither can run back through the junction (`cover`, `arm`); the near
    arm gives the fibre by occurrence-injectivity of a walk, and the far arm by
    `TargetGeodesic.not_isEnd_of_mem_tail_of_genusZero`.  An **nd2** wall block
    is exactly this situation: its old wall vertex is divalent
    (`nd2_old_nonDanglingValency`) and its two branch occurrences lie over two
    *different* star edges.

## What is proved

* `onRow_blockOldSourceEdge`, `blockOldSourceEdge_star` -- **unconditional**:
  a regrowing block's canonical incoming occurrence is displayed on the row its
  regrown occurrence carries, lies over a star edge, lies above that block, and
  is incident to the block's old wall vertex.
* `eq_of_mem_occurrences_of_sameBlock` -- **unconditional**: the local census.
* `rowTargetInjective_of_pathEnd_of_genusZero`,
  `occurrences_eq_singleton_of_junction_of_genusZero` -- the two case-independent
  geodesic statements above, for an arbitrary `GluingDatum` over a connected
  genus-zero target.
* `occurrences_blockOldSourceEdge_eq_singleton` -- **the census at the `{w4}`
  wall**, for every pairing and every regrowing block.
* `index_dvd_incomingRowDenominator`, `hIndex_of_genusZero`,
  `hIndex_of_regrownRows_tame` -- **the hypothesis `hIndex`**, in exactly the shape
  `Count.W4UnitBalance` consumes; the last asks for the row hypothesis only on
  the rows regrowing blocks actually carry.
* `denominatorProduct_eq_incoming`, `sum_signedMult_eq_zero`,
  `sum_signedMult_canonical_eq_zero` -- `Count.W4UnitBalance`'s three
  conditional theorems with `hIndex` removed: `D⁽ᵠ⁾ = D₀` for each of the
  three members `W4OutgoingStableRows.member` that
  `AuxR0SourceInput.presentedFamily` builds, and `Σ_q Mult φ_q = 0`.

## What is NOT proved: the hypotheses that remain explicit

The hypothesis `hIndex` is **discharged**, but not from nothing.  What replaces it
is the standing target hypotheses of the genus-six count plus one row hypothesis:

* **`graph_connected target` and `genus target = 0`.**  The target of the
  genus-six count is `Infrastructure.CaterpillarTree.catTree`, which satisfies
  both (`catTree_connected`, `catTree_genus`); they enter only through
  `Count.TargetGeodesic`.  These are hypotheses about the *target*, not about
  any constructed member, and are the same two that
  `Count.RowGeodesic.sum_signedMult_canonical_eq_zero_of_genusZero` carries for
  `{w2-r2-nd3-M-1k}`.
* **`RowRamificationAtMostOne data path`** on the rows carried by regrowing
  blocks: `r_φ ≤ 1` at every surviving valency-two vertex of the row.  It is
  what forbids the hairpin above a leaf and is used only through
  `Count.RowWalk.target_ne_of_row`.  `rowRamificationAtMostOne_of_targetChange` reduces it to `ch(v) ≤ 1` at the
  target vertices the row meets, which on a change-minimal datum says exactly
  that the row meets no leaf of the target; it is the same hypothesis
  `Count.RowGeodesic.sum_signedMult_canonical_eq_zero_of_genusZero` carries
  under the name `hTame`, and it is **not** discharged here (`W4FullDimensionalBalance`
  removes it on the actual family).
* **`HasPathEnds data` is *not* used**, and neither is `RowUnramified`, the
  upper half `d₀ ∣ k`, the sharp value `d₀ = k`, or the member row calculus of
  `OutgoingRowCalculus`.  No incoming row denominator is
  evaluated: only divisibility into it is proved.
* Nothing here is conditional on integrality of the multiplicity, on the genus
  or the degree of the source, or on nonsingularity of any member.  The `{w4}`
  source input enters only as a `W4StableSource.AuxR0SourceInput`: directly
  through its field `dangling_no_glue`, and through
  `AuxR0SourceInput.blockPicture`, which is the input's own classification of
  its wall blocks.  No `FullDimensionalSourcePresentation` appears -- there is
  none at this wall
  (`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`) -- and no
  path list, determinant receipt or cardinality bijection is read.

## Non-vacuity

No structure and no new predicate is introduced.  §6 checks that
`rowTargetInjective_of_pathEnd_of_genusZero` reproduces
`Count.RowGeodesic.rowTargetInjective_of_genusZero`, and instantiates it on the
caterpillar target `T^CL_g` and datum `caterpillarDatum` of the base count, where it
reproduces `Count.RowWalk.rowTargetInjective_cat`.

## Consumers

`W4FullDimensionalBalance`, and through it `RegrowthWallInput.w4_sum_signedMult_eq_zero`,
part of the multiplicity input of the star parity in step 2 (trivalent walls) of
`DraismaVargasCount/Assembly.lean`.  Equation (1) is one of the four unit-weight cases,
with Equations (4), (5) and (10).
-/

namespace DraismaVargas.Count.W4IncomingIndex

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Count
open DraismaVargas.Count.TrivalentWeight
open DraismaVargas.Count.TargetGeodesic
open DraismaVargas.Count.RowWalk
open DraismaVargas.Count.RowGeodesic
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource

/-! ## 0.  Two list facts about a traversal and its head -/

private theorem notMem_tail_of_head? {α : Type*} {l : List α} {a : α}
    (hNodup : l.Nodup) (hHead : l.head? = some a) : a ∉ l.tail := by
  cases l with
  | nil => simp at hHead
  | cons head rest =>
      have hEq : head = a := by simpa using hHead
      subst hEq
      exact (List.nodup_cons.mp hNodup).1

private theorem mem_tail_of_mem_of_ne {α : Type*} {l : List α} {a b : α}
    (hMem : a ∈ l) (hHead : l.head? = some b) (hNe : a ≠ b) : a ∈ l.tail := by
  cases l with
  | nil => simp at hMem
  | cons head rest =>
      have hEq : head = b := by simpa using hHead
      subst hEq
      rcases List.mem_cons.mp hMem with h | h
      · exact absurd h hNe
      · exact h

/-- For a list with no duplicates, consecutive entries are distinct. -/
private theorem isChain_ne_of_nodup {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Nodup → l.IsChain R → l.IsChain fun a b ↦ R a b ∧ a ≠ b := by
  intro l
  induction l with
  | nil => intro _ _; exact List.isChain_nil
  | cons a t ih =>
      intro hNodup hChain
      cases t with
      | nil => exact List.isChain_singleton _
      | cons b t' =>
          rw [List.isChain_cons_cons] at hChain ⊢
          refine ⟨⟨hChain.1, ?_⟩, ih (List.Nodup.of_cons hNodup) hChain.2⟩
          intro hEq
          exact (List.nodup_cons.mp hNodup).1 (by rw [hEq]; simp)

/-! ## 1.  The geodesic statements, from one end or from one junction -/

section Geodesic

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}

/-- **`RowTargetInjective` from one named end of the row.**
`Count.RowGeodesic.rowTargetInjective_of_genusZero` asks for `HasPathEnds data`,
which the codimension-one wall datum does not carry; all its proof uses is an
end of the one row in question, and the traversal started there. -/
theorem rowTargetInjective_of_pathEnd_of_genusZero (hConn : graph_connected target)
    (hGenus : genus target = 0) (hNoGlue : DanglingEdgeNoGlue data)
    {path : StablePath data} (hTame : RowRamificationAtMostOne data path)
    {start : data.SourceEdge} {vertex : data.SourceVertex}
    (hEnd : IsPathEnd data start vertex) (hStart : OnRow data path start) :
    RowTargetInjective data path := by
  classical
  obtain ⟨hStartSurvives, hStartPath⟩ := hStart
  have hMem : ∀ edge, edge ∈ traverse data ∅ start vertex ↔ OnRow data path edge := by
    intro edge
    constructor
    · intro hEdge
      obtain ⟨hSurvives, hPath⟩ :=
        traverse_stablePath data ∅ start vertex hStartSurvives edge hEdge
      exact ⟨hSurvives, hPath.trans hStartPath⟩
    · rintro ⟨hSurvives, hPath⟩
      exact mem_traverse_of_stablePath_eq data hEnd ⟨edge, hSurvives⟩
        (hPath.trans hStartPath.symm)
  have hNodup : (traverse data ∅ start vertex).Nodup :=
    (traverse_nodup_notMem data ∅ start vertex).1
  have hChain : (traverse data ∅ start vertex).IsChain
      fun first second ↦ (∃ meet : data.SourceVertex,
        Incident data first meet ∧ Incident data second meet ∧
          nonDanglingValency data meet = 2) ∧
        (first.1.1 : target.edges) ≠ second.1.1 := by
    refine (isChain_ne_of_nodup hNodup
      (traverse_chain data ∅ start vertex)).imp_of_mem_imp ?_
    intro a b ha hb hab
    obtain ⟨⟨meet, hAMeet, hBMeet, hValency⟩, hNe⟩ := hab
    exact ⟨⟨meet, hAMeet, hBMeet, hValency⟩,
      target_ne_of_row hNoGlue hTame hValency ((hMem a).mp ha) hAMeet
        ((hMem b).mp hb) hBMeet hNe⟩
  have hWalk : IsWalkFrom vertex.1.1
      ((traverse data ∅ start vertex).map fun edge ↦ (edge.1.1 : target.edges)) := by
    refine isWalkFrom_of_isChain _ vertex hNodup
      (fun edge hedge ↦ ((hMem edge).mp hedge).survives) hChain (fun head hhead ↦ ?_)
      (Or.inl hEnd.2)
    have hheadEq : head = start := by
      rw [traverse_head?_eq_some data ∅ start vertex (by simp)] at hhead
      simpa using hhead.symm
    rw [hheadEq]
    exact hEnd.1
  have hTargets := nodup_of_isWalkFrom_of_genusZero hConn hGenus hWalk
  intro first second hFirst hSecond hTargetEq
  exact List.inj_on_of_nodup_map hTargets ((hMem first).mpr hFirst)
    ((hMem second).mpr hSecond) hTargetEq

section Junction

variable {path : StablePath data} {first second : data.SourceEdge}
  {vertex : data.SourceVertex}

/-- At a surviving valency-two vertex the two named survivors are the only
ones. -/
private theorem survivor_eq (hValency : nonDanglingValency data vertex = 2)
    (hFirstSurv : ¬ IsDangling data first) (hFirstInc : Incident data first vertex)
    (hSecondSurv : ¬ IsDangling data second) (hSecondInc : Incident data second vertex)
    (hNe : first ≠ second) (edge : data.SourceEdge) (hSurv : ¬ IsDangling data edge)
    (hInc : Incident data edge vertex) : edge = first ∨ edge = second := by
  by_cases hF : edge = first
  · exact Or.inl hF
  by_cases hS : edge = second
  · exact Or.inr hS
  exact absurd (not_three_survivors hValency hNe (Ne.symm hF) (Ne.symm hS)
    hFirstSurv hFirstInc hSecondSurv hSecondInc hSurv hInc) not_false

/-- **The row is covered by the two arms leaving the junction.**  Each arm is
the traversal that starts at one survivor with the *other* already marked
visited, so no arm runs back through the junction and the pair is defined even
when the row closes up. -/
private theorem cover (hValency : nonDanglingValency data vertex = 2)
    (hFirstSurv : ¬ IsDangling data first) (hFirstInc : Incident data first vertex)
    (hSecondSurv : ¬ IsDangling data second) (hSecondInc : Incident data second vertex)
    (hNe : first ≠ second)
    (hRow : NonDanglingEdge.stablePath (⟨first, hFirstSurv⟩ : NonDanglingEdge data) = path)
    (edge : data.SourceEdge) (hEdge : OnRow data path edge) :
    edge ∈ traverse data {second} first vertex ∨
      edge ∈ traverse data {first} second vertex := by
  classical
  obtain ⟨hSurv, hPath⟩ := hEdge
  have hFirstMem : first ∈ traverse data {second} first vertex :=
    mem_traverse_self data _ _ vertex (by simp [hNe])
  have hSecondMem : second ∈ traverse data {first} second vertex :=
    mem_traverse_self data _ _ vertex (by simp [Ne.symm hNe])
  have hClosed : ∀ a b : NonDanglingEdge data, Consecutive data a b →
      (a.1 ∈ traverse data {second} first vertex ∨
        a.1 ∈ traverse data {first} second vertex) →
      (b.1 ∈ traverse data {second} first vertex ∨
        b.1 ∈ traverse data {first} second vertex) := by
    intro a b hCons hA
    obtain ⟨hAB, meet, hAMeet, hBMeet, hMeetValency⟩ := hCons
    have hBNe : b.1 ≠ a.1 := fun hEq ↦ hAB (Subtype.ext hEq).symm
    rcases hA with hA | hA
    · rcases traverse_closed data {second} first vertex hFirstSurv hFirstInc
        hMeetValency a.1 b.1 hA b.2 hBNe hAMeet hBMeet with h | h | h
      · exact Or.inl h
      · rw [Finset.mem_singleton.mp h]
        exact Or.inr hSecondMem
      · rcases survivor_eq hValency hFirstSurv hFirstInc hSecondSurv hSecondInc
          hNe b.1 b.2 h.1 with hEq | hEq
        · rw [hEq]; exact Or.inl hFirstMem
        · rw [hEq]; exact Or.inr hSecondMem
    · rcases traverse_closed data {first} second vertex hSecondSurv hSecondInc
        hMeetValency a.1 b.1 hA b.2 hBNe hAMeet hBMeet with h | h | h
      · exact Or.inr h
      · rw [Finset.mem_singleton.mp h]
        exact Or.inl hFirstMem
      · rcases survivor_eq hValency hFirstSurv hFirstInc hSecondSurv hSecondInc
          hNe b.1 b.2 h.1 with hEq | hEq
        · rw [hEq]; exact Or.inl hFirstMem
        · rw [hEq]; exact Or.inr hSecondMem
  have hEqv : Relation.EqvGen (Consecutive data)
      (⟨first, hFirstSurv⟩ : NonDanglingEdge data) ⟨edge, hSurv⟩ :=
    (stablePath_eq_iff _ _).mp (hRow.trans hPath.symm)
  exact (eqvGen_iff_of_closed (property := fun e ↦
    e.1 ∈ traverse data {second} first vertex ∨
      e.1 ∈ traverse data {first} second vertex) hClosed hEqv).mp (Or.inl hFirstMem)

/-- One arm of the junction: it stays on the row, starts at `first`, and is a
non-backtracking target walk read off from the junction. -/
private theorem arm (hNoGlue : DanglingEdgeNoGlue data)
    (hTame : RowRamificationAtMostOne data path)
    (hValency : nonDanglingValency data vertex = 2)
    (hFirstSurv : ¬ IsDangling data first) (hFirstInc : Incident data first vertex)
    (hSecondSurv : ¬ IsDangling data second) (hSecondInc : Incident data second vertex)
    (hNe : first ≠ second)
    (hRow : NonDanglingEdge.stablePath (⟨first, hFirstSurv⟩ : NonDanglingEdge data) = path) :
    (∀ edge ∈ traverse data {second} first vertex, OnRow data path edge) ∧
      (traverse data {second} first vertex).head? = some first ∧
      IsWalkFrom vertex.1.1 ((traverse data {second} first vertex).map
        fun e ↦ (e.1.1 : target.edges)) := by
  classical
  have hNotVisited : first ∉ ({second} : Finset data.SourceEdge) := by simp [hNe]
  have hNodupNot := traverse_nodup_notMem data {second} first vertex
  have hOnRow : ∀ edge ∈ traverse data {second} first vertex, OnRow data path edge := by
    intro edge hedge
    obtain ⟨hSurv, hPath⟩ :=
      traverse_stablePath data {second} first vertex hFirstSurv edge hedge
    exact ⟨hSurv, hPath.trans hRow⟩
  have hHead : (traverse data {second} first vertex).head? = some first :=
    traverse_head?_eq_some data {second} first vertex hNotVisited
  refine ⟨hOnRow, hHead, ?_⟩
  have hChain : (traverse data {second} first vertex).IsChain
      fun a b ↦ (∃ meet : data.SourceVertex,
        Incident data a meet ∧ Incident data b meet ∧
          nonDanglingValency data meet = 2) ∧ (a.1.1 : target.edges) ≠ b.1.1 := by
    refine (isChain_ne_of_nodup hNodupNot.1
      (traverse_chain data {second} first vertex)).imp_of_mem_imp ?_
    intro a b ha hb hab
    obtain ⟨⟨meet, hAMeet, hBMeet, hMeetValency⟩, hABNe⟩ := hab
    exact ⟨⟨meet, hAMeet, hBMeet, hMeetValency⟩,
      target_ne_of_row hNoGlue hTame hMeetValency (hOnRow a ha) hAMeet
        (hOnRow b hb) hBMeet hABNe⟩
  refine isWalkFrom_of_isChain _ vertex hNodupNot.1
    (fun edge hedge ↦ (hOnRow edge hedge).survives) hChain (fun head hhead ↦ ?_)
    (Or.inr ?_)
  · have hheadEq : head = first := by
      rw [hHead] at hhead
      simpa using hhead.symm
    rw [hheadEq]
    exact hFirstInc
  · intro edge hedge hInc
    have hMem : edge ∈ traverse data {second} first vertex :=
      List.mem_of_mem_tail hedge
    rcases survivor_eq hValency hFirstSurv hFirstInc hSecondSurv hSecondInc hNe
      edge (hOnRow edge hMem).survives hInc with hEq | hEq
    · exact notMem_tail_of_head? hNodupNot.1 hHead (hEq ▸ hedge)
    · exact hNodupNot.2 edge hMem (by simp [hEq])

/-- **The simple column at a junction.**  If the row passes through a surviving
valency-two vertex by two occurrences lying over *different* target
occurrences, then the first of the two is alone in its `(row, target
occurrence)` fibre.  No end of the row is named, so this covers a row that
never ends. -/
theorem occurrences_eq_singleton_of_junction_of_genusZero
    (hConn : graph_connected target) (hGenus : genus target = 0)
    (hNoGlue : DanglingEdgeNoGlue data)
    (hTame : RowRamificationAtMostOne data path)
    (hValency : nonDanglingValency data vertex = 2)
    (hFirstSurv : ¬ IsDangling data first) (hFirstInc : Incident data first vertex)
    (hSecondSurv : ¬ IsDangling data second) (hSecondInc : Incident data second vertex)
    (hNe : first ≠ second) (hTargetNe : (first.1.1 : target.edges) ≠ second.1.1)
    (hRow : NonDanglingEdge.stablePath (⟨first, hFirstSurv⟩ : NonDanglingEdge data) = path) :
    StableSourceMatrix.occurrences data path first.1.1 = {first} := by
  classical
  have hConsecutive : Consecutive data (⟨first, hFirstSurv⟩ : NonDanglingEdge data)
      ⟨second, hSecondSurv⟩ :=
    ⟨fun hEq ↦ hNe (congrArg Subtype.val hEq), vertex, hFirstInc, hSecondInc, hValency⟩
  have hRowSecond : NonDanglingEdge.stablePath
      (⟨second, hSecondSurv⟩ : NonDanglingEdge data) = path :=
    (stablePath_eq_of_consecutive hConsecutive).symm.trans hRow
  obtain ⟨_, _, hWalkOne⟩ := arm hNoGlue hTame hValency hFirstSurv hFirstInc
    hSecondSurv hSecondInc hNe hRow
  obtain ⟨_, hHeadTwo, hWalkTwo⟩ := arm hNoGlue hTame hValency hSecondSurv hSecondInc
    hFirstSurv hFirstInc (Ne.symm hNe) hRowSecond
  refine Finset.eq_singleton_iff_unique_mem.mpr
    ⟨(StableSourceMatrix.mem_occurrences path first.1.1 first).mpr ⟨⟨hFirstSurv, hRow⟩, rfl⟩, ?_⟩
  intro other hOther
  obtain ⟨hOtherRow, hOtherTarget⟩ :=
    (StableSourceMatrix.mem_occurrences path first.1.1 other).mp hOther
  rcases cover hValency hFirstSurv hFirstInc hSecondSurv hSecondInc hNe hRow other
    hOtherRow with hArm | hArm
  · have hNodupTargets := nodup_of_isWalkFrom_of_genusZero hConn hGenus hWalkOne
    have hFirstMem : first ∈ traverse data {second} first vertex :=
      mem_traverse_self data _ _ vertex (by simp [hNe])
    exact List.inj_on_of_nodup_map hNodupTargets hArm hFirstMem hOtherTarget
  · exfalso
    by_cases hEq : other = second
    · exact hTargetNe (hOtherTarget.symm.trans (congrArg (fun e : data.SourceEdge ↦
        (e.1.1 : target.edges)) hEq))
    · have hTailMem : other ∈ (traverse data {first} second vertex).tail :=
        mem_tail_of_mem_of_ne hArm hHeadTwo hEq
      refine not_isEnd_of_mem_tail_of_genusZero hConn hGenus hWalkTwo
        (edge := (first.1.1 : target.edges)) ?_ (isEnd_of_incident hFirstInc)
      have hMapMem := List.mem_map_of_mem
        (f := fun e : data.SourceEdge ↦ (e.1.1 : target.edges)) hTailMem
      rw [hOtherTarget] at hMapMem
      rw [← List.map_tail]
      exact hMapMem

end Junction

/-- **`RowRamificationAtMostOne` from the change budget below the row.**  Local
ramifications are nonnegative and sum to `ch(v)`, so a target vertex of change
at most one carries none above `1`.  This is a *reduction* of the one row
hypothesis this file keeps, not a discharge of it: on a change-minimal datum
`ch(v) = 3 - val(v)`, so `ch(v) ≤ 1` says exactly that `v` is not a leaf, and
the hypothesis below is "the row meets no leaf of the target", i.e.
`Count.RowWalk.RowAvoidsLeaves` read through change-minimality. -/
theorem rowRamificationAtMostOne_of_targetChange (hValid : data.Valid)
    {path : StablePath data}
    (hChange : ∀ (vertex : data.SourceVertex) (edge : data.SourceEdge), OnRow data path edge →
      Incident data edge vertex → nonDanglingValency data vertex = 2 →
      data.targetChange vertex.1.1 ≤ 1) :
    RowRamificationAtMostOne data path := by
  intro vertex edge hEdge hIncident hValency
  have hNonneg : 0 ≤ data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ :=
    data.localRamification_nonneg vertex.1.1 (hValid.2 vertex.1.1) _
  have hLe : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤
      data.targetChange vertex.1.1 :=
    Finset.single_le_sum
      (fun item _ ↦ data.localRamification_nonneg vertex.1.1 (hValid.2 vertex.1.1) item)
      (Finset.mem_univ _)
  have hBound := hChange vertex edge hEdge hIncident hValency
  omega

/-- The uniform form of the preceding reduction, in the shape
`hIndex_of_genusZero` consumes. -/
theorem rowRamificationAtMostOne_of_targetChange_le_one (hValid : data.Valid)
    (hChange : ∀ vertex : target.V, data.targetChange vertex ≤ 1)
    (path : StablePath data) : RowRamificationAtMostOne data path :=
  rowRamificationAtMostOne_of_targetChange hValid
    (fun vertex _ _ _ _ ↦ hChange vertex.1.1)

end Geodesic

/-! ## 2.  The regrowing block's canonical incoming occurrence -/

section Wall

open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4OutgoingStableRows
open DraismaVargas.LocalCases.W4OutgoingLimitMatrix
open DraismaVargas.Infrastructure.TargetExpansion

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}
  [DecidableEq target.edges]

omit [DecidableEq target.edges] in
/-- **The regrown row displays its block's canonical incoming occurrence.**
Above an opposite-side nd2 block that occurrence is the first active branch,
above an nd3 block the isolated branch; above a dangling block, and above a
same-side nd2 block, nothing regrows. -/
theorem onRow_blockOldSourceEdge (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (path : StablePath data)
    (hRow : blockRegrownRow input pairing sourceBlock = some path) :
    OnRow data path (blockOldSourceEdge input pairing sourceBlock) := by
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [blockRegrownRow_dangling input pairing sourceBlock old_dangling hPicture] at hRow
      exact absurd hRow (by simp)
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · rw [blockRegrownRow_nd2_same input pairing sourceBlock block picture
          hPicture hSame] at hRow
        exact absurd hRow (by simp)
      · rw [blockRegrownRow_nd2_ne input pairing sourceBlock block picture
          hPicture hSame] at hRow
        rw [blockOldSourceEdge_nd2 input pairing sourceBlock block picture hPicture]
        exact ⟨picture.first_survives, Option.some.inj hRow⟩
  | nd3 block picture =>
      rw [blockRegrownRow_nd3 input pairing sourceBlock block picture hPicture] at hRow
      rw [blockOldSourceEdge_nd3 input pairing sourceBlock block picture hPicture]
      exact ⟨picture.active_survives _ (block.singletonLabel_mem_activeLabels pairing),
        Option.some.inj hRow⟩

omit [DecidableEq target.edges] in
/-- **Where that occurrence sits**: over a star edge, above its own old wall
block, and incident to that block's old wall vertex. -/
theorem blockOldSourceEdge_star (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (path : StablePath data)
    (hRow : blockRegrownRow input pairing sourceBlock = some path) :
    ∃ label : Fin 4,
      (blockOldSourceEdge input pairing sourceBlock).1.1 = star.edge label ∧
      WallBlock.ofSheet data wall
        (blockOldSourceEdge input pairing sourceBlock).1.2 = sourceBlock ∧
      Incident data (blockOldSourceEdge input pairing sourceBlock)
        (WallBlock.sourceVertex data wall sourceBlock) := by
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [blockRegrownRow_dangling input pairing sourceBlock old_dangling hPicture] at hRow
      exact absurd hRow (by simp)
  | nd2 block picture =>
      refine ⟨block.first, ?_, ?_, ?_⟩ <;>
        rw [blockOldSourceEdge_nd2 input pairing sourceBlock block picture hPicture]
      · rfl
      · exact WallBlock.ofSourceEdge_eq_of_rel data star sourceBlock block.first
          sourceBlock.1 rfl
      · exact branch_incident_wallVertex data star sourceBlock block.first
          sourceBlock.1 rfl
  | nd3 block picture =>
      refine ⟨block.singletonLabel pairing, ?_, ?_, ?_⟩ <;>
        rw [blockOldSourceEdge_nd3 input pairing sourceBlock block picture hPicture]
      · rfl
      · exact WallBlock.ofSourceEdge_eq_of_rel data star sourceBlock _ _
          (picture.active_sheet _ (block.singletonLabel_mem_activeLabels pairing))
      · exact branch_incident_wallVertex data star sourceBlock _ _
          (picture.active_sheet _ (block.singletonLabel_mem_activeLabels pairing))

/-! ## 3.  The local half of the census, unconditional -/

omit [DecidableEq target.edges] in
/-- **The local census.**  A surviving occurrence lying over the same star edge
as a regrowing block's canonical incoming occurrence and **above the same old
wall block** *is* that occurrence.  This is the whole content of the auxiliary
source pictures' exhaustion fields, and it holds with no genus, no walk and no
receipt: the fibre can only be enlarged by occurrences above *other* wall
blocks. -/
theorem eq_of_mem_occurrences_of_sameBlock (input : AuxR0SourceInput data star)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (path : StablePath data)
    (hRow : blockRegrownRow input pairing sourceBlock = some path)
    (edge : data.SourceEdge)
    (hTarget : edge.1.1 = (blockOldSourceEdge input pairing sourceBlock).1.1)
    (hSurvives : ¬ IsDangling data edge)
    (hBlock : WallBlock.ofSheet data wall edge.1.2 = sourceBlock) :
    edge = blockOldSourceEdge input pairing sourceBlock := by
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [blockRegrownRow_dangling input pairing sourceBlock old_dangling hPicture] at hRow
      exact absurd hRow (by simp)
  | nd2 block picture =>
      rw [blockOldSourceEdge_nd2 input pairing sourceBlock block picture hPicture] at hTarget ⊢
      have hStar : ∃ label : Fin 4, star.edge label = edge.1.1 :=
        ⟨block.first, hTarget.symm⟩
      rcases picture.only_surviving edge hBlock hStar hSurvives with hEq | hEq
      · exact hEq
      · exfalso
        refine block.distinct (star.edge_injective ?_)
        have hSecondTarget : edge.1.1 = star.edge block.second := by
          rw [hEq, GluingDatum.sourceEdge_target]
        rw [← hSecondTarget, hTarget, GluingDatum.sourceEdge_target]
  | nd3 block picture =>
      rw [blockOldSourceEdge_nd3 input pairing sourceBlock block picture hPicture] at hTarget ⊢
      have hStar : ∃ label : Fin 4, star.edge label = edge.1.1 :=
        ⟨block.singletonLabel pairing, hTarget.symm⟩
      obtain ⟨label, _, hEq⟩ := picture.only_surviving edge hBlock hStar hSurvives
      have hLabel : label = block.singletonLabel pairing := by
        refine star.edge_injective ?_
        have hLabelTarget : edge.1.1 = star.edge label := by
          rw [hEq, GluingDatum.sourceEdge_target]
        rw [← hLabelTarget, hTarget, GluingDatum.sourceEdge_target]
      rw [hEq, hLabel]

/-! ## 4.  The census at the `{w4}` wall, and the hypothesis `hIndex` -/

omit [DecidableEq target.edges] in
/-- **The census**: a regrowing wall block's canonical incoming occurrence is
alone in its `(row, star edge)` fibre of `A₀`.  An nd3 block's old wall vertex
is trivalent, so the row *ends* there and
`rowTargetInjective_of_pathEnd_of_genusZero` applies; an nd2 block's is
divalent and its two branch occurrences lie over two different star edges, so
`occurrences_eq_singleton_of_junction_of_genusZero` applies. -/
theorem occurrences_blockOldSourceEdge_eq_singleton (input : AuxR0SourceInput data star)
    (hConn : graph_connected target) (hGenus : genus target = 0)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (path : StablePath data)
    (hRow : blockRegrownRow input pairing sourceBlock = some path)
    (hTame : RowRamificationAtMostOne data path) :
    StableSourceMatrix.occurrences data path
        (blockOldSourceEdge input pairing sourceBlock).1.1 =
      {blockOldSourceEdge input pairing sourceBlock} := by
  cases hPicture : input.blockPicture sourceBlock with
  | dangling old_dangling =>
      rw [blockRegrownRow_dangling input pairing sourceBlock old_dangling hPicture] at hRow
      exact absurd hRow (by simp)
  | nd2 block picture =>
      by_cases hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
      · rw [blockRegrownRow_nd2_same input pairing sourceBlock block picture
          hPicture hSame] at hRow
        exact absurd hRow (by simp)
      · rw [blockRegrownRow_nd2_ne input pairing sourceBlock block picture
          hPicture hSame] at hRow
        rw [blockOldSourceEdge_nd2 input pairing sourceBlock block picture hPicture]
        refine occurrences_eq_singleton_of_junction_of_genusZero hConn hGenus
          input.dangling_no_glue hTame (nd2_old_nonDanglingValency picture)
          picture.first_survives
          (branch_incident_wallVertex data star sourceBlock block.first sourceBlock.1 rfl)
          picture.second_survives
          (branch_incident_wallVertex data star sourceBlock block.second sourceBlock.1 rfl)
          (sourceEdge_ne_of_label_ne' data star block.distinct _ _)
          (fun hEq ↦ block.distinct (star.edge_injective hEq))
          (Option.some.inj hRow)
  | nd3 block picture =>
      rw [blockRegrownRow_nd3 input pairing sourceBlock block picture hPicture] at hRow
      rw [blockOldSourceEdge_nd3 input pairing sourceBlock block picture hPicture]
      refine occurrences_eq_singleton_of_rowTargetInjective
        (rowTargetInjective_of_pathEnd_of_genusZero hConn hGenus input.dangling_no_glue
          hTame (start := (nd3SingletonEdge picture pairing).1)
          (vertex := WallBlock.sourceVertex data wall sourceBlock)
          ⟨branch_incident_wallVertex data star sourceBlock _ _
            (picture.active_sheet _ (block.singletonLabel_mem_activeLabels pairing)),
            nd3_old_nonDanglingValency_ne_two picture⟩
          ⟨(nd3SingletonEdge picture pairing).2, Option.some.inj hRow⟩)
        ⟨(nd3SingletonEdge picture pairing).2, Option.some.inj hRow⟩ rfl

omit [DecidableEq target.edges] in
/-- **The hypothesis `hIndex`, discharged, one row at a time.** -/
theorem index_dvd_incomingRowDenominator (input : AuxR0SourceInput data star)
    (hConn : graph_connected target) (hGenus : genus target = 0)
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) (path : StablePath data)
    (hRow : blockRegrownRow input pairing sourceBlock = some path)
    (hTame : RowRamificationAtMostOne data path) :
    data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) ∣
      incomingRowDenominator data path :=
  dvd_incomingRowDenominator_of_occurrences_eq_singleton path
    (blockOldSourceEdge input pairing sourceBlock).1.1
    (occurrences_blockOldSourceEdge_eq_singleton input hConn hGenus pairing sourceBlock
      path hRow hTame)

omit [DecidableEq target.edges] in
/-- **The hypothesis `hIndex`, discharged, in exactly the shape
`Count.W4UnitBalance` consumes.** -/
theorem hIndex_of_genusZero (input : AuxR0SourceInput data star)
    (hConn : graph_connected target) (hGenus : genus target = 0)
    (hTame : ∀ path : StablePath data, RowRamificationAtMostOne data path) :
    ∀ (pairing : Fin 3) (sourceBlock : WallBlock data wall) (path : StablePath data),
      blockRegrownRow input pairing sourceBlock = some path →
        data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) ∣
          incomingRowDenominator data path :=
  fun pairing sourceBlock path hRow ↦
    index_dvd_incomingRowDenominator input hConn hGenus pairing sourceBlock path hRow
      (hTame path)

omit [DecidableEq target.edges] in
/-- The same, with the row hypothesis asked for only on the rows that regrowing
blocks actually carry.  This is the sharpest form of what replaces `hIndex`:
`graph_connected target`, `genus target = 0`, and `r_φ ≤ 1` along **those**
rows. -/
theorem hIndex_of_regrownRows_tame (input : AuxR0SourceInput data star)
    (hConn : graph_connected target) (hGenus : genus target = 0)
    (hTame : ∀ (pairing : Fin 3) (sourceBlock : WallBlock data wall)
      (path : StablePath data), blockRegrownRow input pairing sourceBlock = some path →
      RowRamificationAtMostOne data path) :
    ∀ (pairing : Fin 3) (sourceBlock : WallBlock data wall) (path : StablePath data),
      blockRegrownRow input pairing sourceBlock = some path →
        data.sourceEdgeIndex (blockOldSourceEdge input pairing sourceBlock) ∣
          incomingRowDenominator data path :=
  fun pairing sourceBlock path hRow ↦
    index_dvd_incomingRowDenominator input hConn hGenus pairing sourceBlock path hRow
      (hTame pairing sourceBlock path hRow)

/-! ## 5.  Equation (1): `Count.W4UnitBalance`'s three theorems, with `hIndex` discharged -/

variable (input : AuxR0SourceInput data star)
  (hConn : graph_connected target) (hGenus : genus target = 0)
  (hTame : ∀ path : StablePath data, RowRamificationAtMostOne data path)

include hConn hGenus hTame

section Square

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : StableLengthMatrixLabelling
    (W4OutgoingStableRows.member input 0).datum coordinate)

/-- **`D⁽ᵠ⁾ = D₀` for every member of Equation (1)**, with
`Count.W4UnitBalance`'s hypothesis `hIndex` discharged. -/
theorem denominatorProduct_eq_incoming (pairing : Fin 3) :
    denominatorProduct (W4CommonBalance.labelling input initial pairing).presentation =
      incomingDenominatorProduct data :=
  W4UnitBalance.denominatorProduct_eq_incoming input
    (hIndex_of_genusZero input hConn hGenus hTame) initial pairing

/-- **`prop-signed-mult`(1) for Equation (1)**, on the three members
`AuxR0SourceInput.presentedFamily` actually builds, with `hIndex`
discharged. -/
theorem sum_signedMult_eq_zero :
    ∑ pairing : Fin 3,
        signedMult (W4CommonBalance.labelling input initial pairing).presentation = 0 :=
  W4UnitBalance.sum_signedMult_eq_zero input
    (hIndex_of_genusZero input hConn hGenus hTame) initial

end Square

/-- **Equation (1).**  The three actual outgoing `{w4}` candidates, the
source input's own coordinate order, and no hypothesis about the constructed
family: only the connected genus-zero target and the row ramification bound
remain. -/
theorem sum_signedMult_canonical_eq_zero :
    ∑ pairing : Fin 3,
        signedMult (W4CommonBalance.labelling input
          (W4CommonBalance.canonicalInitialLabelling input) pairing).presentation = 0 :=
  W4UnitBalance.sum_signedMult_canonical_eq_zero input
    (hIndex_of_genusZero input hConn hGenus hTame)

end Wall

/-! ## 6.  Non-vacuity -/

section Witness

open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarRows
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.Infrastructure.CaterpillarTree

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}

/-- `Count.RowGeodesic.rowTargetInjective_of_genusZero` is the special case in
which the end is produced by `HasPathEnds`. -/
example (hConn : graph_connected target) (hGenus : genus target = 0)
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} (hTame : RowRamificationAtMostOne data path) :
    RowTargetInjective data path :=
  rowTargetInjective_of_pathEnd_of_genusZero hConn hGenus hNoGlue hTame
    (startEdge_isPathEnd hEnds path)
    ⟨(startEdge hEnds path).2, startEdge_stablePath hEnds path⟩

/-- On the caterpillar target `T^CL_g` and datum, the path-end form
reproduces `Count.RowWalk.rowTargetInjective_cat`. -/
example (m : ℕ) {i : Fin (6 * m + 3)} (hNotLeaf : ¬ IsLeafEdge m i) :
    RowTargetInjective (caterpillarDatum m) ((labelling m).row.symm i) :=
  rowTargetInjective_of_pathEnd_of_genusZero (catTree_connected m) (catTree_genus m)
    (fullDim m).danglingEdgeNoGlue
    (rowUnramified_cat m hNotLeaf).rowRamificationAtMostOne
    (startEdge_isPathEnd (fullDim m).pathEnds ((labelling m).row.symm i))
    ⟨(startEdge (fullDim m).pathEnds ((labelling m).row.symm i)).2,
      startEdge_stablePath (fullDim m).pathEnds ((labelling m).row.symm i)⟩

end Witness

end DraismaVargas.Count.W4IncomingIndex
