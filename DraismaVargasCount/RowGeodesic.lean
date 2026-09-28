import DraismaVargasCount.TargetGeodesic
import DraismaVargasCount.RowWalk
import DraismaVargasCount.IncomingSimpleColumn

/-!
# The stable row as a target walk: the three residues discharged

**Source.**  The image of a leaf-avoiding stable row is a geodesic of the target
tree.  This is the row form of the pass-once condition of Vargas, Part II
(arXiv:2609.09109, `def-auxiliary-conditions`), which full-rank change-minimal
morphisms satisfy (`lm:properties`).  This file is the datum-side half;
`TargetGeodesic` is the graph-side half (a non-backtracking walk in a tree is a
geodesic).

`RowWalk` builds the ordered walk of a stable row and reduces the sharp row
denominators to three named residues, all of them about the target.  This file
discharges all three from `graph_connected target` and `genus target = 0`, by
turning the ordered walk into a non-backtracking walk of the target and applying
`TargetGeodesic`.

## What is proved

* `simpleTarget_of_genusZero` -- **`Count.RowWalk.SimpleTarget target`**
  (residue 3), from connectivity and genus zero alone.  It gives
  `rowDenominator_trichotomy_of_genusZero`: `Count.EdgeDenominator`'s trichotomy
  with no hypothesis left beyond the target being a connected tree.
* `isWalkFrom_of_isChain` -- **the transfer**: a duplicate-free list of
  surviving source occurrences whose consecutive entries meet at a surviving
  valency-two vertex by different target occurrences is a non-backtracking
  target walk, read off from the vertex through which its first entry is
  entered.  The two hypotheses on that vertex are exactly what
  `W4StableSource.IsPathEnd` supplies.  `not_three_survivors` (three distinct
  survivors do not fit at a valency-two vertex) is what forces the walk to leave
  each occurrence by its far end.
* `rowTargetInjective_of_genusZero` -- **`Count.RowWalk.RowTargetInjective data
  path`** (residue 2) for every row of ramification at most one, hence
  `occurrences_eq_singleton_of_genusZero`,
  `dvd_incomingRowDenominator_of_genusZero` and the sharp
  `incomingRowDenominator_eq_of_rowUnramified_of_genusZero`.
* `secondRow_ne_thirdRow_of_genusZero` -- **`Count.IncomingSimpleColumn`'s
  `secondRow profile ≠ thirdRow profile`**, its only residue.  At a `{w2-r2}`
  wall block the surviving valency is three, so the stable row of `e₂` *ends* at
  the wall; if `e₃` lay on it the row would leave the wall along `t₂` and return
  along `t₃`, and `TargetGeodesic.not_isEnd_of_mem_tail` forbids a walk from
  touching its starting vertex again.  Hence
  `sum_signedMult_canonical_eq_zero_of_genusZero`: `prop-signed-mult`(1) on the
  actual `{w2-r2-nd3-M-1k}` family with no row-distinctness hypothesis left.

## What is NOT proved

* **`RowUnramified data path`** -- the first residue, "no transition on
  the row".  It is false in general (`lemma-edge-deno` (c)) and is untouched
  here; every statement that needs the upper half `d₀ ∣ k` carries it, or
  carries the index divisibility it yields, as an explicit hypothesis.
* **`HasPathEnds data`** at the codimension-one incoming datum: explicit,
  as in `RowWalk`.  The wall statements of §7 do **not** need it: the walk
  there starts at the wall block, which is a path end because its surviving
  valency is three.
* **`RowRamificationAtMostOne data path`**: explicit.  It follows from
  `RowUnramified` (`RowUnramified.rowRamificationAtMostOne`) and, on a
  full-dimensional morphism, from `RowAvoidsLeaves`
  (`RowWalk.rowRamificationAtMostOne_of_rowAvoidsLeaves`).
* Nothing here is conditional on integrality, on the genus of the source, on the
  degree, or on nonsingularity of any member of a limit family.  No statement of
  `Count.RowWalk` or `Count.IncomingSimpleColumn` is changed: both are used as
  they stand.

## Non-vacuity

No structure is introduced.  §8 checks that `simpleTarget_of_genusZero`
reproduces `Count.RowWalk.simpleTarget_catTree` on the caterpillar target
`T^CL_g`, where that module proves it by hand.

## Consumers

The row-denominator inputs of the multiplicity balances at walls and at type
changes (for example `IncomingSimpleColumn`, `OutgoingRowCalculus`,
`W4IncomingIndex`, `ValencyFourRigidity`), and the positions of
`RowTransitionPosition` and `LollipopLeafRow`.
-/

namespace DraismaVargas.Count.RowGeodesic

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.TargetGeodesic
open DraismaVargas.Count.RowWalk

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}

/-! ## 1. `SimpleTarget` from connectivity and genus zero -/

/-- **`Count.RowWalk.SimpleTarget`, discharged.**  A connected genus-zero target
has no two occurrences joining the same two vertices. -/
theorem simpleTarget_of_genusZero (hConn : graph_connected target)
    (hGenus : genus target = 0) : SimpleTarget target := by
  intro x y first second hxy hfx hfy hsx hsy
  refine eq_of_incident_of_genusZero hConn hGenus hxy ?_ ?_ ?_ ?_
  · exact (Finset.mem_filter.mp hfx).2
  · exact (Finset.mem_filter.mp hfy).2
  · exact (Finset.mem_filter.mp hsx).2
  · exact (Finset.mem_filter.mp hsy).2

/-! ## 2. The target ends of a source incidence -/

/-- A source incidence displays the source vertex over one stored end of the
target occurrence. -/
theorem isEnd_of_incident {edge : data.SourceEdge} {vertex : data.SourceVertex}
    (h : Incident data edge vertex) : IsEnd (edge.1.1 : target.edges) vertex.1.1 := by
  rcases h with h | h
  · exact Or.inl (congrArg (fun item : data.SourceVertex => item.1.1) h)
  · exact Or.inr (congrArg (fun item : data.SourceVertex => item.1.1) h)

/-- The far end of a source incidence lies over the far end of the target
occurrence. -/
theorem otherEndOf_eq {edge : data.SourceEdge} {vertex : data.SourceVertex}
    (h : Incident data edge vertex) :
    otherEndOf (edge.1.1 : target.edges) vertex.1.1
      = (otherEnd data edge vertex).1.1 := by
  have hLoop : ((edge.1.1 : target.edges) : target.V × target.V).1
      ≠ ((edge.1.1 : target.edges) : target.V × target.V).2 :=
    Dart.coe_fst_ne_snd (edge.1.1 : target.edges)
  unfold otherEndOf otherEnd
  by_cases hSplit : (data.sourceEnds edge).1 = vertex
  · have hvertex : ((edge.1.1 : target.edges) : target.V × target.V).1 = vertex.1.1 :=
      congrArg (fun item : data.SourceVertex => item.1.1) hSplit
    rw [if_pos hSplit, if_pos hvertex]
    rfl
  · rw [if_neg hSplit]
    have hSnd : (data.sourceEnds edge).2 = vertex := by
      rcases h with h | h
      · exact absurd h hSplit
      · exact h
    have hvertex : ((edge.1.1 : target.edges) : target.V × target.V).2 = vertex.1.1 :=
      congrArg (fun item : data.SourceVertex => item.1.1) hSnd
    rw [if_neg (fun hEq => hLoop (hEq.trans hvertex.symm))]
    rfl

/-! ## 3. Three survivors do not fit at a valency-two vertex -/

theorem not_three_survivors {vertex : data.SourceVertex}
    (hValency : nonDanglingValency data vertex = 2)
    {first second third : data.SourceEdge}
    (hFS : first ≠ second) (hFT : first ≠ third) (hST : second ≠ third)
    (hFSurv : ¬ IsDangling data first) (hFInc : Incident data first vertex)
    (hSSurv : ¬ IsDangling data second) (hSInc : Incident data second vertex)
    (hTSurv : ¬ IsDangling data third) (hTInc : Incident data third vertex) : False := by
  classical
  have hCard : ((Finset.univ : Finset data.SourceEdge).filter
      fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge vertex).card = 2 := by
    rw [← hValency, nonDanglingValency]
    congr 1
    ext edge
    simp
  have hsub : ({first, second, third} : Finset data.SourceEdge) ⊆
      ((Finset.univ : Finset data.SourceEdge).filter
        fun edge ↦ ¬ IsDangling data edge ∧ Incident data edge vertex) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact ⟨hFSurv, hFInc⟩
    · exact ⟨hSSurv, hSInc⟩
    · exact ⟨hTSurv, hTInc⟩
  have hthree : ({first, second, third} : Finset data.SourceEdge).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hFS, hFT]),
      Finset.card_insert_of_notMem (by simp [hST]), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hthree, hCard] at hle
  omega

/-! ## 4. The ordered row is a non-backtracking target walk -/

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

/-- **The transfer.**  A list of surviving source occurrences, without
duplicates, whose consecutive entries meet at a surviving valency-two vertex by
different *target* occurrences, is a non-backtracking target walk read off from
the vertex through which its first entry is entered.  The two hypotheses on the
entry vertex are what the end of a stable row supplies: the walk does not
continue there. -/
theorem isWalkFrom_of_isChain : ∀ (row : List data.SourceEdge)
    (vertex : data.SourceVertex), row.Nodup → (∀ edge ∈ row, ¬ IsDangling data edge) →
    (row.IsChain fun first second ↦ (∃ meet : data.SourceVertex,
      Incident data first meet ∧ Incident data second meet ∧
        nonDanglingValency data meet = 2) ∧
      (first.1.1 : target.edges) ≠ second.1.1) →
    (∀ first ∈ row.head?, Incident data first vertex) →
    (nonDanglingValency data vertex ≠ 2 ∨
      ∀ edge ∈ row.tail, ¬ Incident data edge vertex) →
    IsWalkFrom vertex.1.1 (row.map fun edge ↦ (edge.1.1 : target.edges)) := by
  intro row
  induction row with
  | nil => intro _ _ _ _ _ _; exact trivial
  | cons first rest ih =>
      intro vertex hNodup hSurv hChain hHead hEntry
      have hFirstInc : Incident data first vertex := hHead first rfl
      cases rest with
      | nil =>
          exact ⟨isEnd_of_incident hFirstInc, by simp, trivial⟩
      | cons second tail =>
          obtain ⟨⟨meet, hFirstMeet, hSecondMeet, hMeetValency⟩, hTargetNe⟩ :=
            (List.isChain_cons_cons.mp hChain).1
          have hMeet : meet = otherEnd data first vertex := by
            rcases eq_or_eq_otherEnd data hFirstInc hFirstMeet with hCase | hCase
            · exfalso
              rcases hEntry with hEntry | hEntry
              · exact hEntry (hCase ▸ hMeetValency)
              · exact hEntry second (by simp) (hCase ▸ hSecondMeet)
            · exact hCase
          subst hMeet
          refine ⟨isEnd_of_incident hFirstInc, ?_, ?_⟩
          · intro next hnext
            have hnextEq : next = (second.1.1 : target.edges) := by
              have h' := hnext
              simp at h'
              exact h'.symm
            rw [hnextEq]
            exact Ne.symm hTargetNe
          · rw [otherEndOf_eq hFirstInc]
            refine ih (otherEnd data first vertex) (List.Nodup.of_cons hNodup)
              (fun edge hedge ↦ hSurv edge (List.mem_cons_of_mem _ hedge))
              (List.IsChain.tail hChain) (fun head hhead ↦ ?_) (Or.inr ?_)
            · have hheadEq : head = second := by
                have h' := hhead
                simp at h'
                exact h'.symm
              rw [hheadEq]
              exact hSecondMeet
            · intro edge hedge hIncident
              have hMemTail : edge ∈ tail := hedge
              refine not_three_survivors hMeetValency (first := first) (second := second)
                (third := edge) ?_ ?_ ?_ ?_ hFirstMeet ?_ hSecondMeet ?_ hIncident
              · intro hEq
                exact (List.nodup_cons.mp hNodup).1 (by rw [hEq]; simp)
              · intro hEq
                exact (List.nodup_cons.mp hNodup).1
                  (by rw [hEq]; exact List.mem_cons_of_mem _ hMemTail)
              · intro hEq
                exact (List.nodup_cons.mp (List.Nodup.of_cons hNodup)).1
                  (by rw [hEq]; exact hMemTail)
              · exact hSurv first (by simp)
              · exact hSurv second (by simp)
              · exact hSurv edge (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hMemTail))

/-! ## 5. `RowTargetInjective`, discharged -/

/-- **`Count.RowWalk.RowTargetInjective`, discharged.**  The ordered walk of a
row with ramification at most one at every interior vertex meets each target
occurrence once, for a connected genus-zero target.  `RowWalk.target_ne_of_row`
is the local half; the global half is
`TargetGeodesic.nodup_of_isWalkFrom_of_genusZero`. -/
theorem rowTargetInjective_of_genusZero (hConn : graph_connected target)
    (hGenus : genus target = 0) (hNoGlue : DanglingEdgeNoGlue data)
    (hEnds : HasPathEnds data) {path : StablePath data}
    (hTame : RowRamificationAtMostOne data path) : RowTargetInjective data path := by
  classical
  set row := orderedRow hEnds path with hrow
  have hMem : ∀ edge, edge ∈ row ↔ OnRow data path edge := mem_orderedRow_iff hEnds path
  have hNodup : row.Nodup := orderedRow_nodup hEnds path
  have hSurv : ∀ edge ∈ row, ¬ IsDangling data edge :=
    fun edge hedge ↦ ((hMem edge).mp hedge).survives
  have hChain : row.IsChain fun first second ↦ (∃ meet : data.SourceVertex,
      Incident data first meet ∧ Incident data second meet ∧
        nonDanglingValency data meet = 2) ∧
      (first.1.1 : target.edges) ≠ second.1.1 := by
    refine (isChain_ne_of_nodup hNodup (orderedRow_chain hEnds path)).imp_of_mem_imp ?_
    intro a b ha hb hab
    obtain ⟨⟨meet, hAMeet, hBMeet, hValency⟩, hNe⟩ := hab
    exact ⟨⟨meet, hAMeet, hBMeet, hValency⟩,
      target_ne_of_row hNoGlue hTame hValency ((hMem a).mp ha) hAMeet
        ((hMem b).mp hb) hBMeet hNe⟩
  obtain ⟨hIncidentStart, hValencyStart⟩ := startEdge_isPathEnd hEnds path
  have hWalk : IsWalkFrom (startVertex hEnds path).1.1
      (row.map fun edge ↦ (edge.1.1 : target.edges)) := by
    refine isWalkFrom_of_isChain row (startVertex hEnds path) hNodup hSurv hChain
      (fun head hhead ↦ ?_) (Or.inl hValencyStart)
    have hheadEq : head = (startEdge hEnds path).1 := by
      have h' := hhead
      rw [orderedRow_head? hEnds path] at h'
      simpa using h'.symm
    rw [hheadEq]
    exact hIncidentStart
  have hTargets := nodup_of_isWalkFrom_of_genusZero hConn hGenus hWalk
  intro first second hFirst hSecond hTargetEq
  exact List.inj_on_of_nodup_map hTargets ((hMem first).mpr hFirst)
    ((hMem second).mpr hSecond) hTargetEq

/-! ## 6. The consequences for the count, on a general row -/

/-- **The simple column**, with the target-side residue discharged. -/
theorem occurrences_eq_singleton_of_genusZero (hConn : graph_connected target)
    (hGenus : genus target = 0) (hNoGlue : DanglingEdgeNoGlue data)
    (hEnds : HasPathEnds data) {path : StablePath data}
    (hTame : RowRamificationAtMostOne data path) {place : target.edges}
    {edge : data.SourceEdge} (hEdge : OnRow data path edge) (hTarget : edge.1.1 = place) :
    LocalCases.StableSourceMatrix.occurrences data path place = {edge} :=
  occurrences_eq_singleton_of_rowTargetInjective
    (rowTargetInjective_of_genusZero hConn hGenus hNoGlue hEnds hTame) hEdge hTarget

/-- **`k ∣ d₀`** on the rectangular incoming matrix, with the target-side
residue discharged. -/
theorem dvd_incomingRowDenominator_of_genusZero (hConn : graph_connected target)
    (hGenus : genus target = 0) (hNoGlue : DanglingEdgeNoGlue data)
    (hEnds : HasPathEnds data) {path : StablePath data}
    (hTame : RowRamificationAtMostOne data path)
    {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    data.sourceEdgeIndex edge ∣ TrivalentWeight.incomingRowDenominator data path :=
  dvd_incomingRowDenominator_of_rowTargetInjective
    (rowTargetInjective_of_genusZero hConn hGenus hNoGlue hEnds hTame) hEdge

/-- **The sharp incoming denominator `d₀ = k`**, now with `RowUnramified` as the
only row hypothesis: `RowRamificationAtMostOne` follows from it, and the
target-side residue is discharged by genus zero. -/
theorem incomingRowDenominator_eq_of_rowUnramified_of_genusZero
    (hConn : graph_connected target) (hGenus : genus target = 0)
    (hNoGlue : DanglingEdgeNoGlue data) (hEnds : HasPathEnds data)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge)
    (hUnram : RowUnramified data path) :
    TrivalentWeight.incomingRowDenominator data path = data.sourceEdgeIndex edge :=
  incomingRowDenominator_eq_of_rowUnramified_of_rowTargetInjective hNoGlue hEnds hEdge
    hUnram (rowTargetInjective_of_genusZero hConn hGenus hNoGlue hEnds
      hUnram.rowRamificationAtMostOne)

/-- **`Count.EdgeDenominator`'s trichotomy, unconditional over a connected
genus-zero target.**  `Count.RowWalk.rowDenominator_trichotomy_of_simpleTarget`
with its last hypothesis discharged. -/
theorem rowDenominator_trichotomy_of_genusZero {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (fd : LocalCases.FullDimensionalSource.FullDimensionalSourcePresentation data coordinate)
    (hConn : graph_connected target) (hGenus : genus target = 0)
    (sourceRow : coordinate) :
    (EdgeDenominator.PassesAboveLeaf fd.labelling sourceRow ∧
        rowDenominator fd.labelling.presentation sourceRow = 1) ∨
      (¬ EdgeDenominator.PassesAboveLeaf fd.labelling sourceRow ∧ ∃ index : ℕ, 0 < index ∧
        EdgeDenominator.RowIndexConstant fd.labelling sourceRow index ∧
        rowDenominator fd.labelling.presentation sourceRow ∣ index) ∨
      (¬ EdgeDenominator.PassesAboveLeaf fd.labelling sourceRow ∧ ∃ index : ℕ, 0 < index ∧
        EdgeDenominator.RowIndexTwoValued fd.labelling sourceRow index ∧
        (∃ edge ∈ EdgeDenominator.rowEdges fd.labelling sourceRow,
          data.sourceEdgeIndex edge = index) ∧
        (∃ edge ∈ EdgeDenominator.rowEdges fd.labelling sourceRow,
          data.sourceEdgeIndex edge = index + 1) ∧
        rowDenominator fd.labelling.presentation sourceRow ∣
          index * (index + 1)) :=
  rowDenominator_trichotomy_of_simpleTarget fd (simpleTarget_of_genusZero hConn hGenus) sourceRow

end DraismaVargas.Count.RowGeodesic

namespace DraismaVargas.Count.RowGeodesic

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Count.TargetGeodesic
open DraismaVargas.Count.RowWalk
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W2R1Target
open DraismaVargas.LocalCases.SecondEquation
open DraismaVargas.LocalCases.W2M1kCommonBalance
open DraismaVargas.LocalCases.W2M1kSourceCandidates

/-! ## 7. The wall: `e₂` and `e₃` lie on different rows

At a `{w2-r2}` wall block the surviving valency is three, so the stable row of
`e₂` **ends** at the wall.  If `e₃` were on it, the row would leave the wall
along `t₂` and come back along `t₃`: a closed non-backtracking walk of the
target, which a connected genus-zero target does not carry. -/

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem third_ne_second : profile.third.1 ≠ profile.second.1 := by
  intro hEq
  refine profile.labels_ne ?_
  refine (star.edge_injective ?_).symm
  rw [← profile.second_target, ← profile.third_target, hEq]

/-- **The row-distinctness residue, discharged.**  `Count.IncomingSimpleColumn`'s
`secondRow profile ≠ thirdRow profile` over a connected genus-zero target. -/
theorem secondRow_ne_thirdRow_of_genusZero (hConn : graph_connected target)
    (hGenus : genus target = 0) (hNoGlue : DanglingEdgeNoGlue data)
    (hTame : RowRamificationAtMostOne data (secondRow profile)) :
    secondRow profile ≠ thirdRow profile := by
  classical
  intro hEq
  have hValency : nonDanglingValency data
      (WallBlock.sourceVertex data wall block) = 3 := profile.valency
  have hEnd : IsPathEnd data profile.second.1 (WallBlock.sourceVertex data wall block) :=
    ⟨profile.second.2, by rw [hValency]; norm_num⟩
  have hHead : (traverse data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block)).head? = some profile.second.1 :=
    traverse_head?_eq_some data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block) (by simp)
  have hOnRow : ∀ edge ∈ traverse data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block), OnRow data (secondRow profile) edge := by
    intro edge hedge
    exact traverse_stablePath data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block) profile.second_survives edge hedge
  have hNodup : (traverse data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block)).Nodup :=
    (traverse_nodup_notMem data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block)).1
  have hSurv : ∀ edge ∈ traverse data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block), ¬ IsDangling data edge :=
    fun edge hedge ↦ (hOnRow edge hedge).survives
  have hChain : (traverse data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block)).IsChain
      fun first second ↦ (∃ meet : data.SourceVertex,
        Incident data first meet ∧ Incident data second meet ∧
          nonDanglingValency data meet = 2) ∧
        (first.1.1 : target.edges) ≠ second.1.1 := by
    refine (isChain_ne_of_nodup hNodup (traverse_chain data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block))).imp_of_mem_imp ?_
    intro a b ha hb hab
    obtain ⟨⟨meet, hAMeet, hBMeet, hMeetValency⟩, hNe⟩ := hab
    exact ⟨⟨meet, hAMeet, hBMeet, hMeetValency⟩,
      target_ne_of_row hNoGlue hTame hMeetValency (hOnRow a ha) hAMeet
        (hOnRow b hb) hBMeet hNe⟩
  have hWalk : IsWalkFrom (WallBlock.sourceVertex data wall block).1.1
      ((traverse data ∅ profile.second.1
        (WallBlock.sourceVertex data wall block)).map fun edge ↦
          (edge.1.1 : target.edges)) := by
    refine isWalkFrom_of_isChain _ _ hNodup hSurv hChain (fun first hfirst ↦ ?_)
      (Or.inl (by rw [hValency]; norm_num))
    have hfirstEq : first = profile.second.1 := by
      rw [hHead] at hfirst
      have h' := hfirst
      simp at h'
      exact h'.symm
    rw [hfirstEq]
    exact profile.second.2
  have hMem : profile.third.1 ∈ traverse data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block) :=
    mem_traverse_of_stablePath_eq data hEnd
      ⟨profile.third.1, profile.third_survives⟩ hEq.symm
  have hMemTail : profile.third.1 ∈ (traverse data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block)).tail := by
    revert hHead hMem
    cases hrow : traverse data ∅ profile.second.1
      (WallBlock.sourceVertex data wall block) with
    | nil => intro _ hMem; exact absurd hMem (by simp)
    | cons head rest =>
        intro hHead hMem
        have hheadEq : head = profile.second.1 := by simpa using hHead
        rcases List.mem_cons.mp hMem with h | h
        · exact absurd (h.trans hheadEq) third_ne_second
        · exact h
  refine not_isEnd_of_mem_tail_of_genusZero hConn hGenus hWalk ?_
    (isEnd_of_incident profile.third.2)
  rw [← List.map_tail]
  exact List.mem_map_of_mem hMemTail

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- **`prop-signed-mult` (1) for `{w2-r2-nd3-M-1k}` with the row-distinctness
residue discharged.**  Only the upper halves (the first residue, `RowUnramified`)
and the row's ramification bound remain. -/
theorem sum_signedMult_canonical_eq_zero_of_genusZero
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hTame : RowRamificationAtMostOne data (secondRow profile))
    (hIndex2 : ∀ edge ∈ TrivalentWeight.incomingRowEdges data (secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k)
    (hIndex3 : ∀ edge ∈ TrivalentWeight.incomingRowEdges data (thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k) :
    ∑ position : Fin 3, signedMult
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).labelling
          ((W2M1kLimitColumns.limitColumns input shape hConnected
            hGenus).canonicalInitialLabelling input) position).presentation = 0 :=
  IncomingSimpleColumn.sum_signedMult_canonical_eq_zero_of_rows_ne profile input shape
    hConnected hGenus
    (secondRow_ne_thirdRow_of_genusZero hConnected hGenus input.dangling_no_glue hTame)
    hIndex2 hIndex3

/-- The same with `RowUnramified` in place of the ramification bound, which is
the shape the users of this balance carry. -/
theorem sum_signedMult_canonical_eq_zero_of_rowUnramified
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hUnram : RowUnramified data (secondRow profile))
    (hIndex2 : ∀ edge ∈ TrivalentWeight.incomingRowEdges data (secondRow profile),
      data.sourceEdgeIndex edge ∣ shape.k)
    (hIndex3 : ∀ edge ∈ TrivalentWeight.incomingRowEdges data (thirdRow profile),
      data.sourceEdgeIndex edge ∣ shape.k) :
    ∑ position : Fin 3, signedMult
        ((W2M1kLimitColumns.limitColumns input shape hConnected hGenus).labelling
          ((W2M1kLimitColumns.limitColumns input shape hConnected
            hGenus).canonicalInitialLabelling input) position).presentation = 0 :=
  sum_signedMult_canonical_eq_zero_of_genusZero input shape hConnected hGenus
    hUnram.rowRamificationAtMostOne hIndex2 hIndex3

/-! ## 8. Non-vacuity: the caterpillar of loops -/

/-- `Count.RowWalk.simpleTarget_catTree`, which that module proves by hand for
`T^CL_g`, is a special case. -/
example (m : ℕ) : SimpleTarget (Infrastructure.CaterpillarTree.catTree m) :=
  simpleTarget_of_genusZero (Infrastructure.CaterpillarTree.catTree_connected m)
    (Infrastructure.CaterpillarTree.catTree_genus m)

end DraismaVargas.Count.RowGeodesic
