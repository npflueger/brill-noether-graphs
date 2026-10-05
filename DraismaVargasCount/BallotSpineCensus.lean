module

public import DraismaVargasCount.BallotStemCensus

@[expose] public section

/-!
# The spine census of the ballot caterpillar, at a general slope sequence

The third and last layer of the pruning census behind the full-dimensional
presentation of the ballot caterpillar datum.  `BallotFullDimensional` proves
the leaf layer for every slope sequence and
`DraismaVargasCount.BallotStemCensus` the stem layer; this module proves the
**spine** layer and reads the `mainSurvives` obligation of
`Count.BallotFullDimensional.ballotPresentationOfRowData` off the three
together.  `BallotValency` discharges the other obligations, giving the
presentation at every slope sequence, from which the ballot family of the base
count over the caterpillar of loops is built (step 1 of
`DraismaVargasCount/Assembly.lean`).

## Why the statement, and not merely the proof, changes with `s`

At the zig-zag every spine edge carries a block of two sheets, so
`LocalCases.CaterpillarSpine.spineOccurrence_isDangling_iff` can name the
surviving partner by the single index `pairIndex`.  At a general `s` the spine
edge `h_i` carries the block `SpineMem s i` of `s_i` sheets, so the surviving
occurrence over `h_i` is *one block of size `s_i`* and the dangling ones are
the `m + 2 - s_i` singletons.  The census below is stated in that form.

## What is proved

* §1 -- **survival of the spine block, for every slope sequence**
  (`bSpineMain_survives`).  Each side of a spine edge reaches a lollipop loop
  without crossing the edge, through the reachability machinery of
  `DraismaVargasCount.BallotStemCensus` §3.
* §2 -- **the two boundary danglings** (`bFirstSpine_dangles`,
  `bLastSpine_dangles`).  At the two ends of the spine the block is `{0, 1}`
  respectively `{0, m+1}` for every `s`, and a singleton there sits on a
  divalent source vertex whose other occurrence is a dangling leaf occurrence.
* §3 -- **junction propagation** (`bSpine_propagate_right`,
  `bSpine_propagate_left`).  At a junction where the sheet is a singleton the
  source vertex has exactly three incident occurrences, one of which is the
  already-dangling stem occurrence; so danglingness passes along the spine.
* §4 -- **the exact spine-fibre census, for every slope sequence**
  (`bSpineOccurrence_isDangling_iff`): over the spine edge `h_i` the occurrence
  on sheet `σ` dangles exactly when `σ ∉ SpineMem s i`.  The induction is fed
  by `Count.BallotPruning.not_spineMem_dichotomy`: a label absent from a spine
  block is absent on a whole initial or a whole final stretch of the spine,
  because the block interval of a label is convex.
* §5 -- **the `mainSurvives` obligation of the presentation, for every slope
  sequence** (`ballot_mainSurvives`): the spine-sheet occurrence over *every*
  target occurrence survives pruning.  This is the first of the five
  obligations of `BallotFullDimensional.ballotPresentationOfRowData`.

## Scope

* **The other four obligations are not proved in this file.**
  `RowsInFibres`, `FibresInRows`, `trivalent` and `pathEnds` are read off in
  `Count.BallotValency`; the three censuses are their inputs.
* Consequently **no `FullDimensionalSourcePresentation` is produced in this
  file**; `Count.BallotValency.ballotFullDim` is the one for a general `s`, and
  `Count.BallotFullDimensional.zigFullDim` the one for the zig-zag.
* **`FullDimensionalSourcePresentation` is not `BallotFamily`.**  No
  `FibreMember`, no `catCore`, no `GeometricFibre`, no `openOddCount` occurs
  below.  `Count.CaterpillarBallot.BallotFamily` is inhabited, at every `m`
  and every positive request, by `BallotCoreIdentification.ballotFamily`, but
  not constructed here.
* **No genericity hypothesis is used or supplied.**  The count of Vargas,
  Part II (arXiv:2609.09109), `prop-divisors-on-chain`, carries pairwise
  distinct edge lengths; that hypothesis serves the uniqueness half of the
  ballot classification, and no statement below mentions a length.
* Nothing here counts anything, mod 2 or otherwise.
-/

namespace DraismaVargas.Count.BallotSpineCensus

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingSideStructure
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.LocalCases.CaterpillarSpine
open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.BallotFullDimensional
open DraismaVargas.Count.BallotPruning

variable {m : ℕ}

/-! ## 1.  The spine block survives, for every slope sequence -/

/-- The parent of a spine edge is the junction two steps back (the root, at the
first spine edge). -/
theorem bSpineParent_val {i : Fin (6 * m + 3)} (hSpine : i.val % 3 = 1) :
    (catParent m i).val = i.val - 2 := by
  show parentIndex (i.val + 1) = i.val - 2
  rw [parentIndex]
  split_ifs <;> omega

/-- **The junction side of a spine edge reaches a loop**, through target
vertices of index smaller than the spine edge's own. -/
theorem bSpineLeft_reaches_loop (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hSpine : i.val % 3 = 1)
    (P : (ballotDatum m s).SourceVertex → Prop)
    (hP : ∀ w : (catTree m).V, w.val < i.val → P (bCore m s w)) :
    ∃ leaf : Fin (6 * m + 3), IsLeafEdge m leaf ∧
      ReachP (ballotDatum m s).sourceGraph P (bCore m s (catParent m i))
        (bCore m s (catParent m leaf)) := by
  have hi := i.isLt
  have hcp := bSpineParent_val hSpine
  rcases Nat.lt_or_ge i.val 4 with hsmall | hbig
  · have hone : i.val = 1 := by omega
    refine ⟨⟨0, by omega⟩, Or.inl rfl, ?_⟩
    have heq : catParent m (⟨0, by omega⟩ : Fin (6 * m + 3)) = catParent m i := by
      apply Fin.ext
      show parentIndex (0 + 1) = (catParent m i).val
      rw [hcp, parentIndex]
      split_ifs <;> omega
    rw [heq]
    exact reachP_refl (G := (ballotDatum m s).sourceGraph) P _
  · exact bJunction_reaches_prevLoop s (catParent m i) (by rw [hcp]; omega) P
      (fun w hw => hP w (by rw [hcp] at hw; omega))

/-- **The far side of a spine edge reaches a loop**, through target vertices of
index larger than the spine edge's child. -/
theorem bSpineRight_reaches_loop (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hSpine : i.val % 3 = 1)
    (P : (ballotDatum m s).SourceVertex → Prop)
    (hP : ∀ w : (catTree m).V, i.val + 1 < w.val → P (bCore m s w)) :
    ∃ leaf : Fin (6 * m + 3), IsLeafEdge m leaf ∧
      ReachP (ballotDatum m s).sourceGraph P
        (bCore m s (i.succ : (catTree m).V)) (bCore m s (catParent m leaf)) :=
  bVertex_reaches_nextLoop s (i.succ : (catTree m).V)
    (show (i.val + 1) % 3 = 2 by omega) P hP

/-- **The spine block of every spine edge survives**, for every slope
sequence. -/
theorem bSpineMain_survives (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hSpine : i.val % 3 = 1) :
    ¬ IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) 0) := by
  have hi := i.isLt
  have hcp := bSpineParent_val hSpine
  have hEnds : (ballotDatum m s).sourceEnds
        ((ballotDatum m s).sourceEdge (occ m i) 0)
      = (bCore m s (catParent m i), bCore m s (i.succ : (catTree m).V)) :=
    sourceEnds_sourceEdge (ballotDatum m s) (occ m i) 0
  obtain ⟨leftLeaf, hLeftLeaf, hLeftReach⟩ :=
    bSpineLeft_reaches_loop s hSpine
      (fun vertex => vertex ≠ bCore m s (i.succ : (catTree m).V))
      (fun w hw => bCore_ne s (show w.val ≠ i.val + 1 by omega))
  obtain ⟨rightLeaf, hRightLeaf, hRightReach⟩ :=
    bSpineRight_reaches_loop s hSpine
      (fun vertex => vertex ≠ bCore m s (catParent m i))
      (fun w hw => bCore_ne s (show w.val ≠ (catParent m i).val by rw [hcp]; omega))
  exact not_isDangling_of_active_reaches (ballotDatum m s) _ hEnds
    (bNonDanglingValency_loopBase_ne_zero s hLeftLeaf)
    (bNonDanglingValency_loopBase_ne_zero s hRightLeaf) hLeftReach hRightReach


/-! ## 2.  Incidence and distinctness helpers -/

/-- An occurrence meets the source vertex above its parent endpoint. -/
theorem bIncident_of_parent (s : Slopes (2 * (m + 1))) (j : Fin (6 * m + 3))
    (v : (catTree m).V) (hv : parentIndex (j.val + 1) = v.val) (σ : Fin (m + 2)) :
    Incident (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m j) σ)
      ((ballotDatum m s).sourceEndpoint v σ) := by
  unfold Incident
  rw [sourceEnds_sourceEdge]
  refine Or.inl ?_
  have hEq : (catParent m j : (catTree m).V) = v := Fin.ext hv
  rw [show ((occ m j : (catTree m).edges) : (catTree m).V × (catTree m).V).1
    = catParent m j from rfl, hEq]

/-- An occurrence meets the source vertex above its child endpoint. -/
theorem bIncident_of_child (s : Slopes (2 * (m + 1))) (j : Fin (6 * m + 3))
    (v : (catTree m).V) (hv : j.val + 1 = v.val) (σ : Fin (m + 2)) :
    Incident (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m j) σ)
      ((ballotDatum m s).sourceEndpoint v σ) := by
  unfold Incident
  rw [sourceEnds_sourceEdge]
  refine Or.inr ?_
  have hEq : (j.succ : (catTree m).V) = v := Fin.ext hv
  rw [show ((occ m j : (catTree m).edges) : (catTree m).V × (catTree m).V).2
    = (j.succ : (catTree m).V) from rfl, hEq]

/-- Occurrences over distinct target occurrences are distinct. -/
theorem bOcc_ne (s : Slopes (2 * (m + 1))) {j k : Fin (6 * m + 3)}
    (h : j.val ≠ k.val) (σ τ : Fin (m + 2)) :
    (ballotDatum m s).sourceEdge (occ m j) σ
      ≠ (ballotDatum m s).sourceEdge (occ m k) τ := by
  intro hEq
  have hTarget := congrArg
    (fun e : (ballotDatum m s).SourceEdge => e.1.1) hEq
  exact h (congrArg Fin.val (occ_injective m hTarget))

/-! ## 3.  The blocks at the two ends of the spine

At the first lollipop no label has been introduced, so the block is `{0, 1}`
for every slope sequence; past the last spine edge the counter has stopped at
`m + 1` and the slope is `2`, so the block is `{0, m+1}`. -/

theorem bCum_last (s : Slopes (2 * (m + 1))) : s.cum (2 * m + 1) = m + 1 := by
  have h := Slopes.cum_last s (m := m) rfl
  rwa [show 2 * (m + 1) - 1 = 2 * m + 1 from by omega] at h

theorem bCum_ge (s : Slopes (2 * (m + 1))) :
    ∀ i : ℕ, 2 * m + 1 ≤ i → s.cum i = m + 1 := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = 2 * m + 1 + d := ⟨i - (2 * m + 1), by omega⟩
  clear hi
  induction d with
  | zero => simpa using bCum_last s
  | succ d ih =>
      rw [show 2 * m + 1 + (d + 1) = 2 * m + 1 + d + 1 from by omega,
        Slopes.cum_of_ge s (show 2 * (m + 1) - 1 ≤ 2 * m + 1 + d from by omega)]
      exact ih

/-- **The spine block past the last spine edge is `{0, m+1}`**, for every
slope sequence. -/
theorem bSpineMem_ge (s : Slopes (2 * (m + 1))) (i : ℕ) (hi : 2 * m + 1 ≤ i)
    (k : ℕ) : s.SpineMem i k ↔ (k = 0 ∨ k = m + 1) := by
  have hc := bCum_ge s i hi
  have hs : s.slope i = 2 := Slopes.slope_of_ge s (by omega)
  unfold Slopes.SpineMem
  rw [hc, hs]
  omega

/-- The block at the root `u_1` is `{0, 1}`, for every slope sequence. -/
theorem bRoot_not_vertPred (s : Slopes (2 * (m + 1))) {σ : Fin (m + 2)}
    (h0 : σ.val ≠ 0) (h1 : σ.val ≠ 1) : ¬ VertPred m s 0 σ.val := by
  rw [vertPred_pair s (show (0 : ℕ) % 3 ≠ 2 by norm_num)]
  unfold Slopes.PairMem
  rw [show lolli 0 = 1 from by unfold lolli; norm_num, Slopes.cum_one]
  rintro (h | h)
  · exact h0 h
  · exact h1 h

/-- The block at the last `u`-vertex is `{0, m+1}`, for every slope
sequence. -/
theorem bLastStem_not_vertPred (s : Slopes (2 * (m + 1))) {σ : Fin (m + 2)}
    (h0 : σ.val ≠ 0) (hm : σ.val ≠ m + 1) :
    ¬ VertPred m s (6 * m + 2) σ.val := by
  rw [vertPred_junction s (show (6 * m + 2) % 3 = 2 by omega)]
  unfold Slopes.VertMem
  rw [show lolli (6 * m + 2) = 2 * m + 2 from by unfold lolli; omega]
  rintro (h | h)
  · rcases (bSpineMem_ge s (2 * m + 2 - 1) (by omega) σ.val).mp h with h | h
    · exact h0 h
    · exact hm h
  · rcases (bSpineMem_ge s (2 * m + 2) (by omega) σ.val).mp h with h | h
    · exact h0 h
    · exact hm h

/-! ## 4.  The two boundary danglings -/

/-- **A singleton over the first spine edge dangles**, for every slope
sequence: at the root it sits on a divalent source vertex whose other
occurrence is a dangling leaf occurrence. -/
theorem bFirstSpine_dangles (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hi : i.val = 1) {σ : Fin (m + 2)} (h0 : σ.val ≠ 0) (h1 : σ.val ≠ 1) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ) := by
  have hnot : ¬ VertPred m s (⟨0, by omega⟩ : (catTree m).V).val σ.val :=
    bRoot_not_vertPred s h0 h1
  have hCard : Fintype.card (IncidentSourceEdge (ballotDatum m s)
      ((ballotDatum m s).sourceEndpoint (⟨0, by omega⟩ : (catTree m).V) σ)) = 2 := by
    rw [bCard_incident_of_not s (⟨0, by omega⟩ : (catTree m).V) hnot]
    refine card_incidentEdges_two m (⟨0, by omega⟩ : (catTree m).V) ?_
      (incidentIndices_root m (⟨0, by omega⟩ : (catTree m).V) rfl)
    intro h
    have hval : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  refine isDangling_of_incident_of_vertex_degree_eq_two (ballotDatum m s)
    (first := (ballotDatum m s).sourceEdge (occ m ⟨0, by omega⟩) σ)
    (second := (ballotDatum m s).sourceEdge (occ m i) σ)
    (vertex := (ballotDatum m s).sourceEndpoint (⟨0, by omega⟩ : (catTree m).V) σ)
    (bOcc_ne s (show (0 : ℕ) ≠ i.val by omega) σ σ)
    (bIncident_of_parent s _ _ (by show parentIndex (0 + 1) = 0
                                   rw [parentIndex]; split_ifs <;> omega) σ)
    (bIncident_of_parent s i _ (by show parentIndex (i.val + 1) = 0
                                   rw [parentIndex]; split_ifs <;> omega) σ)
    ?_ ?_
  · rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hCard]
    norm_num
  · refine (bLeafOccurrence_isDangling_iff s (Or.inl rfl) σ).mpr ⟨h0, ?_⟩
    show σ.val ≠ s.cum (lolli (0 + 1))
    rw [show lolli (0 + 1) = 1 from by unfold lolli; norm_num, Slopes.cum_one]
    exact h1

/-- **A singleton over the last spine edge dangles**, for every slope
sequence. -/
theorem bLastSpine_dangles (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hi : i.val = 6 * m + 1) {σ : Fin (m + 2)}
    (h0 : σ.val ≠ 0) (hm : σ.val ≠ m + 1) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ) := by
  have hnot : ¬ VertPred m s (⟨6 * m + 2, by omega⟩ : (catTree m).V).val σ.val :=
    bLastStem_not_vertPred s h0 hm
  have hCard : Fintype.card (IncidentSourceEdge (ballotDatum m s)
      ((ballotDatum m s).sourceEndpoint
        (⟨6 * m + 2, by omega⟩ : (catTree m).V) σ)) = 2 := by
    rw [bCard_incident_of_not s (⟨6 * m + 2, by omega⟩ : (catTree m).V) hnot]
    refine card_incidentEdges_two m (⟨6 * m + 2, by omega⟩ : (catTree m).V) ?_
      (incidentIndices_lastStem m (⟨6 * m + 2, by omega⟩ : (catTree m).V) rfl)
    intro h
    have hval : 6 * m + 1 = 6 * m + 2 := congrArg Fin.val h
    omega
  refine isDangling_of_incident_of_vertex_degree_eq_two (ballotDatum m s)
    (first := (ballotDatum m s).sourceEdge (occ m ⟨6 * m + 2, by omega⟩) σ)
    (second := (ballotDatum m s).sourceEdge (occ m i) σ)
    (vertex := (ballotDatum m s).sourceEndpoint
      (⟨6 * m + 2, by omega⟩ : (catTree m).V) σ)
    (bOcc_ne s (show 6 * m + 2 ≠ i.val by omega) σ σ)
    (bIncident_of_parent s _ _ (by show parentIndex (6 * m + 2 + 1) = 6 * m + 2
                                   rw [parentIndex]; split_ifs <;> omega) σ)
    (bIncident_of_child s i _ (by show i.val + 1 = 6 * m + 2
                                  omega) σ)
    ?_ ?_
  · rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge, hCard]
    norm_num
  · refine (bLeafOccurrence_isDangling_iff s (Or.inr rfl) σ).mpr ⟨h0, ?_⟩
    show σ.val ≠ s.cum (lolli (6 * m + 2 + 1))
    rw [show lolli (6 * m + 2 + 1) = 2 * m + 2 from by unfold lolli; omega,
      bCum_ge s (2 * m + 2) (by omega)]
    exact hm


/-! ## 5.  Junction propagation -/

/-- At a junction where the sheet is a singleton, exactly three source
occurrences meet. -/
theorem bJunction_card (s : Slopes (2 * (m + 1))) (v : (catTree m).V)
    (hmod : v.val % 3 = 2) (hhi : v.val + 1 ≤ 6 * m) {σ : Fin (m + 2)}
    (hσ : ¬ VertPred m s v.val σ.val) :
    Fintype.card (IncidentSourceEdge (ballotDatum m s)
      ((ballotDatum m s).sourceEndpoint v σ)) = 3 := by
  have hlt := v.isLt
  rw [bCard_incident_of_not s v hσ]
  refine card_incidentEdges_three m v ?_ ?_ ?_
    (incidentIndices_junction m v hmod hhi)
  · intro h
    have hval : v.val - 1 = v.val := congrArg Fin.val h
    omega
  · intro h
    have hval : v.val - 1 = v.val + 2 := congrArg Fin.val h
    omega
  · intro h
    have hval : v.val = v.val + 2 := congrArg Fin.val h
    omega

/-- The stem at a junction where the sheet is a singleton dangles: the bridge
pair lies inside the spine-vertex block. -/
theorem bJunctionStem_dangles (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hSpine : i.val % 3 = 1) (hhi : i.val + 3 < 6 * m + 3) {σ : Fin (m + 2)}
    (hσ : ¬ VertPred m s (i.val + 1) σ.val) :
    IsDangling (ballotDatum m s)
      ((ballotDatum m s).sourceEdge (occ m ⟨i.val + 1, by omega⟩) σ) := by
  refine (bStemOccurrence_isDangling_iff s
    (show IsStemEdge m (⟨i.val + 1, by omega⟩ : Fin (6 * m + 3)) from
      ⟨show (i.val + 1) % 3 = 2 by omega, show i.val + 1 ≠ 6 * m + 2 by omega⟩)
    σ).mpr ?_
  intro hPair
  rw [vertPred_junction s (show (i.val + 1) % 3 = 2 by omega)] at hσ
  exact hσ (Slopes.vertMem_of_pairMem s hPair)

/-- **Danglingness propagates forward across a junction** where the sheet is a
singleton: the third incident occurrence is the already-dangling stem. -/
theorem bSpine_propagate_right (s : Slopes (2 * (m + 1))) {i j : Fin (6 * m + 3)}
    (hSpine : i.val % 3 = 1) (hj : j.val = i.val + 3) {σ : Fin (m + 2)}
    (hσ : ¬ VertPred m s (i.val + 1) σ.val)
    (hFrom : IsDangling (ballotDatum m s)
      ((ballotDatum m s).sourceEdge (occ m i) σ)) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m j) σ) := by
  have hjlt := j.isLt
  have hhi : i.val + 3 < 6 * m + 3 := by omega
  exact isDangling_of_card_three_of_two_dangling (ballotDatum m s)
    (ballotDatum_connected m s)
    ((ballotDatum m s).sourceEndpoint (i.succ : (catTree m).V) σ)
    ((ballotDatum m s).sourceEdge (occ m j) σ)
    ((ballotDatum m s).sourceEdge (occ m i) σ)
    ((ballotDatum m s).sourceEdge (occ m ⟨i.val + 1, by omega⟩) σ)
    (bIncident_of_parent s j _
      (by show parentIndex (j.val + 1) = i.val + 1
          rw [hj, parentIndex]; split_ifs <;> omega) σ)
    (bIncident_of_child s i _ (show i.val + 1 = i.val + 1 from rfl) σ)
    (bIncident_of_parent s _ _
      (by show parentIndex (i.val + 1 + 1) = i.val + 1
          rw [parentIndex]; split_ifs <;> omega) σ)
    (bOcc_ne s (show j.val ≠ i.val by omega) σ σ)
    (bOcc_ne s (show j.val ≠ i.val + 1 by omega) σ σ)
    (bOcc_ne s (show i.val ≠ i.val + 1 by omega) σ σ)
    (bJunction_card s (i.succ : (catTree m).V)
      (show (i.val + 1) % 3 = 2 by omega)
      (show i.val + 1 + 1 ≤ 6 * m by omega) hσ)
    hFrom (bJunctionStem_dangles s hSpine hhi hσ)

/-- **Danglingness propagates backward across a junction.** -/
theorem bSpine_propagate_left (s : Slopes (2 * (m + 1))) {i j : Fin (6 * m + 3)}
    (hSpine : i.val % 3 = 1) (hj : j.val = i.val + 3) {σ : Fin (m + 2)}
    (hσ : ¬ VertPred m s (i.val + 1) σ.val)
    (hFrom : IsDangling (ballotDatum m s)
      ((ballotDatum m s).sourceEdge (occ m j) σ)) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ) := by
  have hjlt := j.isLt
  have hhi : i.val + 3 < 6 * m + 3 := by omega
  exact isDangling_of_card_three_of_two_dangling (ballotDatum m s)
    (ballotDatum_connected m s)
    ((ballotDatum m s).sourceEndpoint (i.succ : (catTree m).V) σ)
    ((ballotDatum m s).sourceEdge (occ m i) σ)
    ((ballotDatum m s).sourceEdge (occ m j) σ)
    ((ballotDatum m s).sourceEdge (occ m ⟨i.val + 1, by omega⟩) σ)
    (bIncident_of_child s i _ (show i.val + 1 = i.val + 1 from rfl) σ)
    (bIncident_of_parent s j _
      (by show parentIndex (j.val + 1) = i.val + 1
          rw [hj, parentIndex]; split_ifs <;> omega) σ)
    (bIncident_of_parent s _ _
      (by show parentIndex (i.val + 1 + 1) = i.val + 1
          rw [parentIndex]; split_ifs <;> omega) σ)
    (bOcc_ne s (show i.val ≠ j.val by omega) σ σ)
    (bOcc_ne s (show i.val ≠ i.val + 1 by omega) σ σ)
    (bOcc_ne s (show j.val ≠ i.val + 1 by omega) σ σ)
    (bJunction_card s (i.succ : (catTree m).V)
      (show (i.val + 1) % 3 = 2 by omega)
      (show i.val + 1 + 1 ≤ 6 * m by omega) hσ)
    hFrom (bJunctionStem_dangles s hSpine hhi hσ)

/-! ## 6.  The two inductions along the spine -/

/-- The junction between the spine edges `h_{q+1}` and `h_{q+2}` carries the
sheet as a singleton exactly when neither block contains it. -/
theorem bJunction_not_vertPred (s : Slopes (2 * (m + 1))) (q : ℕ)
    {σ : Fin (m + 2)} (h1 : ¬ s.SpineMem (q + 1) σ.val)
    (h2 : ¬ s.SpineMem (q + 2) σ.val) :
    ¬ VertPred m s (3 * q + 2) σ.val := by
  rw [vertPred_junction s (show (3 * q + 2) % 3 = 2 by omega)]
  unfold Slopes.VertMem
  rw [show lolli (3 * q + 2) = q + 2 from by unfold lolli; omega]
  rintro (h | h)
  · exact h1 (by rw [show q + 2 - 1 = q + 1 from by omega] at h; exact h)
  · exact h2 h

/-- **Rightward propagation from the root**: where the label is absent from
every block up to `h_{q+1}`, the occurrence over `h_{q+1}` dangles. -/
theorem bSpine_dangles_prefix (s : Slopes (2 * (m + 1))) {σ : Fin (m + 2)}
    (h0 : σ.val ≠ 0) :
    ∀ (q : ℕ) (hq : 3 * q + 1 < 6 * m + 3),
      (∀ n : ℕ, n ≤ q + 1 → ¬ s.SpineMem n σ.val) →
      IsDangling (ballotDatum m s)
        ((ballotDatum m s).sourceEdge (occ m ⟨3 * q + 1, hq⟩) σ) := by
  intro q
  induction q with
  | zero =>
      intro hq hall
      refine bFirstSpine_dangles s (show (3 * 0 + 1 : ℕ) = 1 by omega) h0 ?_
      intro h
      refine hall 1 (by omega) ?_
      rw [Slopes.spineMem_one_iff_pairMem_one]
      exact Or.inr (by rw [h, Slopes.cum_one])
  | succ q ih =>
      intro hq hall
      have hqlt : 3 * q + 1 < 6 * m + 3 := by omega
      exact bSpine_propagate_right s (i := ⟨3 * q + 1, hqlt⟩)
        (j := ⟨3 * (q + 1) + 1, hq⟩)
        (show (3 * q + 1) % 3 = 1 by omega)
        (show 3 * (q + 1) + 1 = 3 * q + 1 + 3 by omega)
        (bJunction_not_vertPred s q (hall (q + 1) (by omega)) (hall (q + 2) (by omega)))
        (ih hqlt (fun n hn => hall n (by omega)))

/-- **Leftward propagation from the last spine edge**: where the label is
absent from every block from `h_{q+1}` on, the occurrence over `h_{q+1}`
dangles. -/
theorem bSpine_dangles_suffix (s : Slopes (2 * (m + 1))) {σ : Fin (m + 2)}
    (h0 : σ.val ≠ 0) :
    ∀ (d q : ℕ), q + d = 2 * m →
      (∀ n : ℕ, q + 1 ≤ n → ¬ s.SpineMem n σ.val) →
      ∀ (hq : 3 * q + 1 < 6 * m + 3),
      IsDangling (ballotDatum m s)
        ((ballotDatum m s).sourceEdge (occ m ⟨3 * q + 1, hq⟩) σ) := by
  intro d
  induction d with
  | zero =>
      intro q hqd hall hq
      refine bLastSpine_dangles s (show (3 * q + 1 : ℕ) = 6 * m + 1 by omega) h0 ?_
      intro h
      exact hall (2 * m + 1) (by omega)
        ((bSpineMem_ge s (2 * m + 1) (by omega) σ.val).mpr (Or.inr h))
  | succ d ih =>
      intro q hqd hall hq
      have hq' : 3 * (q + 1) + 1 < 6 * m + 3 := by omega
      exact bSpine_propagate_left s (i := ⟨3 * q + 1, hq⟩)
        (j := ⟨3 * (q + 1) + 1, hq'⟩)
        (show (3 * q + 1) % 3 = 1 by omega)
        (show 3 * (q + 1) + 1 = 3 * q + 1 + 3 by omega)
        (bJunction_not_vertPred s q (hall (q + 1) (by omega)) (hall (q + 2) (by omega)))
        (ih (q + 1) (by omega) (fun n hn => hall n (by omega)) hq')

/-! ## 7.  The exact spine-fibre census -/

/-- **Every singleton sheet over a spine edge dangles**, for every slope
sequence.  The block interval of a label is convex, so a label absent from the
block over `h_i` is absent on a whole initial or a whole final stretch of the
spine, and the corresponding boundary induction applies. -/
theorem bSpineOccurrence_dangles (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hSpine : i.val % 3 = 1) {σ : Fin (m + 2)}
    (hσ : ¬ s.SpineMem ((i.val + 2) / 3) σ.val) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ) := by
  have hi := i.isLt
  have h0 : σ.val ≠ 0 := fun h => hσ (h ▸ Slopes.spineMem_zero s _)
  obtain ⟨q, hq⟩ : ∃ q, i.val = 3 * q + 1 := ⟨(i.val - 1) / 3, by omega⟩
  have hiq : i = (⟨3 * q + 1, by omega⟩ : Fin (6 * m + 3)) :=
    Fin.ext (show i.val = 3 * q + 1 by omega)
  rw [show (i.val + 2) / 3 = q + 1 from by omega] at hσ
  rcases not_spineMem_dichotomy s h0 hσ with hleft | hright
  · rw [hiq]
    exact bSpine_dangles_prefix s h0 q (by omega) hleft
  · rw [hiq]
    exact bSpine_dangles_suffix s h0 (2 * m - q) q (by omega) hright (by omega)

/-- **The exact spine-fibre occurrence census, for every slope sequence.**
Over the spine edge `h_i` the occurrence on sheet `σ` dangles exactly when `σ`
is outside the block `SpineMem s i` of `s_i` sheets; the block itself is a
single surviving source occurrence.  This is
`LocalCases.CaterpillarSpine.spineOccurrence_isDangling_iff` with the zig-zag's
single partner sheet replaced by the general block. -/
theorem bSpineOccurrence_isDangling_iff (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hSpine : i.val % 3 = 1) (σ : Fin (m + 2)) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ)
      ↔ ¬ s.SpineMem ((i.val + 2) / 3) σ.val := by
  constructor
  · intro hDangling hMem
    refine bSpineMain_survives s hSpine ?_
    rwa [bOcc_eq_main s i (by rw [edgePred_spine s hSpine]; exact hMem)] at hDangling
  · exact fun hσ => bSpineOccurrence_dangles s hSpine hσ

/-! ## 8.  The `mainSurvives` obligation, for every slope sequence -/

/-- **The spine-sheet occurrence over every target occurrence survives**, for
every slope sequence.  This is the first of the five obligations of
`BallotFullDimensional.ballotPresentationOfRowData`, at a general `s`: leaf
edges are `BallotFullDimensional.ballot_mainSurvives_leaf`, stems are
`Count.BallotPruning.bStemMain_survives`, spine edges are
`bSpineMain_survives`. -/
theorem ballot_mainSurvives (s : Slopes (2 * (m + 1)))
    (occurrence : (catTree m).edges) :
    ¬ IsDangling (ballotDatum m s) (bMain m s occurrence) := by
  obtain ⟨i, rfl⟩ := occ_surj m occurrence
  show ¬ IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) 0)
  by_cases hleaf : IsLeafEdge m i
  · exact ballot_mainSurvives_leaf s hleaf
  · by_cases hspine : i.val % 3 = 1
    · exact bSpineMain_survives s hspine
    · unfold IsLeafEdge at hleaf
      exact bStemMain_survives s ⟨by omega, by omega⟩


/-! ## 9.  Non-vacuity: the census really depends on the sequence

At genus six the five slope sequences include `Slopes.six = [2,3,4,3,2]`, whose
middle spine edge carries a block of **four** sheets -- the whole fibre, at
degree `d = m + 2 = 4`.  So over that edge *nothing* dangles, a shape that does
not occur at the zig-zag, where every spine block has two sheets and `m` of the
`m + 2` occurrences dangle over every spine edge. -/

/-- The middle spine block of `Slopes.six` is the whole sheet set. -/
theorem six_spineMem_three : ∀ k : Fin 4, Slopes.six.SpineMem 3 k.val := by decide

/-- Genus six, degree four: no occurrence over the middle spine edge `h_3` of
the rise-then-fall sequence dangles. -/
example {i : Fin (6 * 2 + 3)} (hi : i.val = 7) (σ : Fin (2 + 2)) :
    ¬ IsDangling (ballotDatum 2 Slopes.six)
      ((ballotDatum 2 Slopes.six).sourceEdge (occ 2 i) σ) := by
  rw [bSpineOccurrence_isDangling_iff Slopes.six (show i.val % 3 = 1 by omega) σ,
    not_not, show (i.val + 2) / 3 = 3 from by omega]
  exact six_spineMem_three σ

/-- The spine-sheet occurrence survives over every target occurrence, for every
one of the five genus-six slope sequences. -/
example (s : Slopes 6) (occurrence : (catTree 2).edges) :
    ¬ IsDangling (ballotDatum 2 s) (bMain 2 s occurrence) :=
  ballot_mainSurvives s occurrence

end DraismaVargas.Count.BallotSpineCensus
