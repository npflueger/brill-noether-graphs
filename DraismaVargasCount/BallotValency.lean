import DraismaVargasCount.BallotSpineCensus

/-!
# The pruned ballot source: valencies, stable rows and the full-dimensional presentation

This module shows that the ballot gluing datum `ballotDatum m s` carries a
full-dimensional source presentation, for every slope sequence.  `BallotStemCensus`
and `BallotSpineCensus` prove the stem and spine fibre censuses at a general slope
sequence, and `BallotFullDimensional.bLeafOccurrence_isDangling_iff` the leaf one.
This module reads all three back at source vertices and proves the remaining four
obligations of `BallotFullDimensional.ballotPresentationOfRowData`.

## What is proved

* §1 -- **one census for all three layers.**  `bSurvives m s e k` is the set of
  sheets over the target occurrence `e` whose source occurrence survives: the
  spine block `SpineMem s i` over a spine edge, the bridge pair
  `PairMem s (lolli (e+1))` over a stem *and* over a leaf edge.
  `bOccurrence_isDangling_iff` is the resulting uniform census.
* §2 -- **survivors are glued to the spine sheet.**  A surviving sheet over an
  occurrence lies in the block at either of its endpoints
  (`vertPred_of_bSurvives`); this is the refinement receipt of the datum for
  spine and stem occurrences, and the bridge-pair computation at both ends of a
  leaf edge for the leaf ones.
* §3 -- **singleton source vertices are inert**: surviving valency zero
  (`bNonDanglingValency_other_eq_zero`), and every source vertex is either a
  spine-sheet vertex `bCore m s v` or such a singleton.
* §4 -- **the exact surviving star at a spine-sheet vertex**
  (`bNonDanglingIncident_core_eq_visible`, `bNonDanglingValency_core_eq_sum`):
  a leaf occurrence contributes its two loop flags, every other incident
  occurrence contributes one.  The counts are the same for every `s`, although
  the blocks are not: a block of `s_i` sheets is still one source occurrence.
* §5 -- **trivalence, for every slope sequence** (`ballot_trivalent`).
* §6 -- **the surviving-valency-two vertices are exactly the leaf folds**, hence
  `RowsInFibres` (`ballot_rowsInFibres`).
* §7 -- **`FibresInRows`** (`ballot_fibresInRows`) and **`HasPathEnds`**
  (`ballot_pathEnds`).
* §8 -- **the presentation at every slope sequence**: `ballotFullDim m s` is an actual
  `FullDimensionalSourcePresentation (ballotDatum m s) (Fin (6m+3))` for every
  `m` and every `s : Slopes (2 * (m + 1))`.

## What is NOT proved here (every hypothesis, explicitly)

* **`FullDimensionalSourcePresentation` is not `BallotFamily`.**  No
  `FibreMember`, no `catCore`, no `GeometricFibre`, no `openOddCount` occurs
  below.  `Count.CaterpillarBallot.BallotFamily` is inhabited elsewhere, at
  every `m` and every positive request, by
  `BallotCoreIdentification.ballotFamily`.  `ballotFullDim` is the
  presentation, not a member.
* **No semantic seed.**  The entry point of the semantic march is
  `LocalCases.CaterpillarSeed.uniformInitialState`, stated for
  `caterpillarDatum m`; nothing here transports it along the family.
* **No uniqueness and no count.**  That every full-dimensional datum over the
  caterpillar of loops is one of these is not proved, nor stated; nothing here
  counts anything, mod 2 or otherwise.
* **No genericity hypothesis is used or supplied.**  The count of Vargas, Part II
  (arXiv:2609.09109, `prop-divisors-on-chain`) assumes pairwise distinct edge
  lengths; that concerns the classification of the fibre, and no statement below
  mentions a length.  The length matrix below is the combinatorial one attached
  to the labelling.
-/

namespace DraismaVargas.Count.BallotValency

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.BallotFullDimensional
open DraismaVargas.Count.BallotPruning
open DraismaVargas.Count.BallotSpineCensus

variable {m : ℕ}

/-! ## 1.  One census for all three layers -/

/-- The sheets over the target occurrence `e` whose source occurrence survives
pruning: the spine block over a spine edge, the bridge pair over a stem and
over a leaf edge.  Over a stem `lolli (e + 1) = lolli e`, so the single formula
covers both. -/
def bSurvives (m : ℕ) (s : Slopes (2 * (m + 1))) (e k : ℕ) : Prop :=
  if e % 3 = 1 then s.SpineMem ((e + 2) / 3) k else s.PairMem (lolli (e + 1)) k

theorem bSurvives_spine (s : Slopes (2 * (m + 1))) {e : ℕ} (h : e % 3 = 1) (k : ℕ) :
    bSurvives m s e k ↔ s.SpineMem ((e + 2) / 3) k := by
  unfold bSurvives; rw [if_pos h]

theorem bSurvives_of_not_spine (s : Slopes (2 * (m + 1))) {e : ℕ} (h : e % 3 ≠ 1)
    (k : ℕ) : bSurvives m s e k ↔ s.PairMem (lolli (e + 1)) k := by
  unfold bSurvives; rw [if_neg h]

theorem bSurvives_zero (s : Slopes (2 * (m + 1))) (e : ℕ) : bSurvives m s e 0 := by
  unfold bSurvives
  split_ifs
  · exact Slopes.spineMem_zero s _
  · exact Slopes.pairMem_zero s _

/-- **The exact occurrence census of the ballot source, for every slope
sequence and over every target occurrence.**  Leaf edges are
`BallotFullDimensional.bLeafOccurrence_isDangling_iff`, stems are
`Count.BallotPruning.bStemOccurrence_isDangling_iff`, spine edges are
`Count.BallotSpineCensus.bSpineOccurrence_isDangling_iff`. -/
theorem bOccurrence_isDangling_iff (s : Slopes (2 * (m + 1)))
    (i : Fin (6 * m + 3)) (σ : Fin (m + 2)) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ)
      ↔ ¬ bSurvives m s i.val σ.val := by
  have hi := i.isLt
  by_cases hspine : i.val % 3 = 1
  · rw [bSurvives_spine s hspine, bSpineOccurrence_isDangling_iff s hspine]
  · rw [bSurvives_of_not_spine s hspine]
    by_cases hleaf : IsLeafEdge m i
    · rw [bLeafOccurrence_isDangling_iff s hleaf]
      unfold Slopes.PairMem
      constructor
      · rintro ⟨h0, hc⟩ (h | h)
        · exact h0 h
        · exact hc h
      · intro h
        exact ⟨fun h0 => h (Or.inl h0), fun hc => h (Or.inr hc)⟩
    · unfold IsLeafEdge at hleaf
      have hstem : IsStemEdge m i := ⟨by omega, by omega⟩
      rw [bStemOccurrence_isDangling_iff s hstem,
        show lolli (i.val + 1) = lolli i.val from by unfold lolli; omega]

/-! ## 2.  A surviving sheet lies in the block at either endpoint -/

/-- **Every surviving sheet over an occurrence lies in the block at each of its
endpoints.**  For spine and stem occurrences this is the refinement receipt of
the datum; for a leaf occurrence the surviving set is the bridge pair of the
lollipop, which is the block at both of its ends. -/
theorem vertPred_of_bSurvives (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    {v : (catTree m).V}
    (hv : parentIndex (i.val + 1) = v.val ∨ i.val + 1 = v.val)
    {k : ℕ} (h : bSurvives m s i.val k) : VertPred m s v.val k := by
  have hi := i.isLt
  by_cases hspine : i.val % 3 = 1
  · rw [bSurvives_spine s hspine] at h
    have hE : EdgePred m s i.val k := (edgePred_spine s hspine k).mpr h
    rcases hv with hv | hv
    · rw [← hv]; exact edgePred_parent s (by omega) k hE
    · rw [← hv]; exact edgePred_child s (by omega) k hE
  · rw [bSurvives_of_not_spine s hspine] at h
    by_cases hleaf : IsLeafEdge m i
    · rcases hv with hv | hv
      · rw [← hv]
        have hlolli := lolli_parentIndex_leaf hleaf
        by_cases hj : parentIndex (i.val + 1) % 3 = 2
        · rw [vertPred_junction s hj, hlolli]
          exact Slopes.vertMem_of_pairMem s h
        · rw [vertPred_pair s hj, hlolli]
          exact h
      · rw [← hv, vertPred_pair s (show (i.val + 1) % 3 ≠ 2 by
          unfold IsLeafEdge at hleaf; omega)]
        exact h
    · unfold IsLeafEdge at hleaf
      have hstem : IsStemEdge m i := ⟨by omega, by omega⟩
      have hE : EdgePred m s i.val k := by
        rw [edgePred_stem s hstem.1 hstem.2,
          show (i.val + 4) / 3 = lolli (i.val + 1) from by unfold lolli; omega]
        exact h
      rcases hv with hv | hv
      · rw [← hv]; exact edgePred_parent s (by omega) k hE
      · rw [← hv]; exact edgePred_child s (by omega) k hE

/-! ## 3.  Singleton source vertices are inert -/

/-- Over a target occurrence incident to a target vertex, a sheet outside the
block at that vertex gives a dangling occurrence. -/
theorem bDangling_of_incident_other (s : Slopes (2 * (m + 1)))
    {v : (catTree m).V} {σ : Fin (m + 2)} (hσ : ¬ VertPred m s v.val σ.val)
    (i : Fin (6 * m + 3)) (hIncident : occ m i ∈ GluingDatum.incidentEdges v) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ) := by
  rw [bOccurrence_isDangling_iff]
  intro hSur
  exact hσ (vertPred_of_bSurvives s
    ((mem_incidentIndices m v i).mp ((mem_incidentEdges_occ m v i).mp hIncident))
    hSur)

/-- **A source vertex on a singleton sheet has surviving valency zero.** -/
theorem bNonDanglingValency_other_eq_zero (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) {σ : Fin (m + 2)} (hσ : ¬ VertPred m s v.val σ.val) :
    nonDanglingValency (ballotDatum m s)
      ((ballotDatum m s).sourceEndpoint v σ) = 0 := by
  classical
  unfold nonDanglingValency
  rw [Finset.card_eq_zero]
  ext edge
  constructor
  · intro hEdge
    have hFilter := (Finset.mem_filter.mp hEdge).2
    have hEdgeEq := CaterpillarValency.sourceEdge_eq_of_incident_sourceEndpoint_other
      (ballotDatum m s) v σ (bVertexBlock_of_not s v hσ) edge hFilter.2
    obtain ⟨i, hi⟩ := occ_surj m edge.1.1
    have hTargetIncident :=
      (incident_iff_target_mem_and_rel (ballotDatum m s) edge
        ((ballotDatum m s).sourceEndpoint v σ)).mp hFilter.2
    have hTargetIncident' : edge.1.1 ∈ GluingDatum.incidentEdges v := by
      simpa only [GluingDatum.sourceEndpoint] using hTargetIncident.1
    exfalso
    refine hFilter.1 ?_
    rw [hEdgeEq, hi]
    exact bDangling_of_incident_other s hσ i (by simpa only [hi] using hTargetIncident')
  · intro hEmpty
    simp at hEmpty

/-- **Every source vertex is a spine-sheet vertex or a singleton.** -/
theorem bSourceVertex_eq_core_or_other (s : Slopes (2 * (m + 1)))
    (vertex : (ballotDatum m s).SourceVertex) :
    vertex = bCore m s vertex.1.1 ∨
      ¬ VertPred m s vertex.1.1.val vertex.1.2.val := by
  by_cases h : VertPred m s vertex.1.1.val vertex.1.2.val
  · refine Or.inl ?_
    have hrepr : ((ballotDatum m s).vertexPartition vertex.1.1).repr vertex.1.2
        = 0 := catStar_repr_of_mem _ h
    have hzero : vertex.1.2 = 0 := by
      have hidem := vertex.2
      rw [hrepr] at hidem
      exact hidem.symm
    apply Subtype.ext
    apply Prod.ext
    · rfl
    show vertex.1.2 = ((ballotDatum m s).vertexPartition vertex.1.1).repr 0
    rw [show ((ballotDatum m s).vertexPartition vertex.1.1).repr (0 : Fin (m + 2))
      = 0 from catStar_repr_of_mem _ (vertPred_zero s _)]
    exact hzero
  · exact Or.inr h


/-! ## 4.  The exact surviving star at a spine-sheet vertex -/

/-- Both ends of a leaf edge belong to its lollipop, so they name the same
counter sheet. -/
theorem bCumSheet_eq_of_leaf_incident (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) {v : (catTree m).V}
    (hv : parentIndex (i.val + 1) = v.val ∨ i.val + 1 = v.val) :
    cumSheet m s v.val = cumSheet m s (i.val + 1) := by
  apply Fin.ext
  rw [cumSheet_val, cumSheet_val]
  rcases hv with hv | hv
  · rw [← hv, lolli_parentIndex_leaf hLeaf]
  · rw [← hv]

/-- The spine-sheet occurrence over an incident target occurrence meets the
spine-sheet vertex. -/
theorem bMain_incident_core (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    {v : (catTree m).V} (hIncident : occ m i ∈ GluingDatum.incidentEdges v) :
    Incident (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) 0)
      (bCore m s v) :=
  incident_sourceEdge_sourceEndpoint (ballotDatum m s) v (occ m i) hIncident 0

/-- The counter-sheet flag of a loop also meets the spine-sheet vertex, at
either end of its leaf edge. -/
theorem bLoopSecond_incident_core (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) {v : (catTree m).V}
    (hIncident : occ m i ∈ GluingDatum.incidentEdges v) :
    Incident (ballotDatum m s) (bLoopSecond m s i) (bCore m s v) := by
  have hv := (mem_incidentIndices m v i).mp ((mem_incidentEdges_occ m v i).mp hIncident)
  have hEq : (ballotDatum m s).sourceEndpoint v (cumSheet m s (i.val + 1))
      = bCore m s v := by
    rw [← bCumSheet_eq_of_leaf_incident s hLeaf hv]
    exact sourceEndpoint_cumSheet s v
  rw [← hEq]
  exact incident_sourceEdge_sourceEndpoint (ballotDatum m s) v (occ m i) hIncident _

/-- Away from a leaf edge, a surviving sheet is one of the sheets of the
occurrence's own block. -/
theorem edgePred_of_bSurvives_of_not_leaf (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hleaf : ¬ IsLeafEdge m i) {k : ℕ}
    (h : bSurvives m s i.val k) : EdgePred m s i.val k := by
  have hi := i.isLt
  by_cases hspine : i.val % 3 = 1
  · rw [bSurvives_spine s hspine] at h
    exact (edgePred_spine s hspine k).mpr h
  · unfold IsLeafEdge at hleaf
    have hstem : IsStemEdge m i := ⟨by omega, by omega⟩
    rw [bSurvives_of_not_spine s hspine] at h
    rw [edgePred_stem s hstem.1 hstem.2,
      show (i.val + 4) / 3 = lolli (i.val + 1) from by unfold lolli; omega]
    exact h

/-- **A surviving occurrence is visibly a loop flag or a spine-sheet
occurrence.** -/
theorem bSurviving_classification (s : Slopes (2 * (m + 1)))
    (edge : (ballotDatum m s).SourceEdge)
    (hSurvives : ¬ IsDangling (ballotDatum m s) edge) :
    ∃ i : Fin (6 * m + 3), edge.1.1 = occ m i ∧
      ((IsLeafEdge m i ∧ (edge = (ballotDatum m s).sourceEdge (occ m i) 0 ∨
          edge = bLoopSecond m s i)) ∨
        (¬ IsLeafEdge m i ∧ edge = (ballotDatum m s).sourceEdge (occ m i) 0)) := by
  obtain ⟨i, hi⟩ := occ_surj m edge.1.1
  have hEdge : edge = (ballotDatum m s).sourceEdge (occ m i) edge.1.2 := by
    calc edge = (ballotDatum m s).sourceEdge edge.1.1 edge.1.2 :=
          (GluingDatum.sourceEdge_self (ballotDatum m s) edge).symm
      _ = (ballotDatum m s).sourceEdge (occ m i) edge.1.2 := by rw [hi]
  have hSur : bSurvives m s i.val edge.1.2.val := by
    by_contra h
    exact hSurvives (hEdge ▸ (bOccurrence_isDangling_iff s i edge.1.2).mpr h)
  refine ⟨i, hi, ?_⟩
  by_cases hleaf : IsLeafEdge m i
  · refine Or.inl ⟨hleaf, ?_⟩
    rw [bSurvives_of_not_spine s (show i.val % 3 ≠ 1 by
      unfold IsLeafEdge at hleaf; omega)] at hSur
    rcases hSur with h0 | hc
    · exact Or.inl (by rw [hEdge]; exact congrArg _ (Fin.ext h0))
    · refine Or.inr ?_
      rw [hEdge]
      exact congrArg _ (Fin.ext (by rw [cumSheet_val]; exact hc))
  · refine Or.inr ⟨hleaf, ?_⟩
    rw [hEdge]
    exact bOcc_eq_main s i (edgePred_of_bSurvives_of_not_leaf s hleaf hSur)

/-- The complete visible surviving fibre over one target occurrence: two loop
flags over a leaf edge, one spine-sheet occurrence otherwise. -/
noncomputable def bVisible (m : ℕ) (s : Slopes (2 * (m + 1)))
    (i : Fin (6 * m + 3)) : Finset ((ballotDatum m s).SourceEdge) :=
  if IsLeafEdge m i then
    {(ballotDatum m s).sourceEdge (occ m i) 0, bLoopSecond m s i}
  else {(ballotDatum m s).sourceEdge (occ m i) 0}

theorem bVisible_target (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    {edge : (ballotDatum m s).SourceEdge} (hEdge : edge ∈ bVisible m s i) :
    edge.1.1 = occ m i := by
  classical
  by_cases hleaf : IsLeafEdge m i
  · rw [bVisible, if_pos hleaf] at hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl <;> rfl
  · rw [bVisible, if_neg hleaf, Finset.mem_singleton] at hEdge
    rw [hEdge]
    rfl

theorem card_bVisible (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    (bVisible m s i).card = if IsLeafEdge m i then 2 else 1 := by
  classical
  by_cases hleaf : IsLeafEdge m i
  · rw [bVisible, if_pos hleaf, if_pos hleaf]
    exact Finset.card_pair (bLoopFirst_ne_bLoopSecond s hleaf)
  · rw [bVisible, if_neg hleaf, if_neg hleaf, Finset.card_singleton]

theorem bVisible_pairwiseDisjoint (s : Slopes (2 * (m + 1)))
    (indices : Finset (Fin (6 * m + 3))) :
    Set.PairwiseDisjoint (indices : Set (Fin (6 * m + 3))) (bVisible m s) := by
  classical
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro edge hiEdge hjEdge
  exact hij (occ_injective m ((bVisible_target s hiEdge).symm.trans
    (bVisible_target s hjEdge)))

/-- **The surviving star at a spine-sheet vertex is exactly the union of the
visible occurrences over its incident target occurrences.** -/
theorem bNonDanglingIncident_core_eq_visible (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) :
    nonDanglingIncident (ballotDatum m s) (bCore m s v) =
      (incidentIndices m v).biUnion (bVisible m s) := by
  classical
  ext edge
  constructor
  · intro hEdge
    have hData := (mem_nonDanglingIncident _ _ _).mp hEdge
    obtain ⟨i, hiTarget, hiClass⟩ := bSurviving_classification s edge hData.1
    have hTarget := (incident_iff_target_mem_and_rel (ballotDatum m s) edge
      (bCore m s v)).mp hData.2
    have hiMem : occ m i ∈ GluingDatum.incidentEdges v := by
      have hraw := hTarget.1
      rw [hiTarget] at hraw
      exact hraw
    refine Finset.mem_biUnion.mpr ⟨i, (mem_incidentEdges_occ m v i).mp hiMem, ?_⟩
    rcases hiClass with ⟨hLeaf, hLoop⟩ | ⟨hNotLeaf, hMain⟩
    · rw [bVisible, if_pos hLeaf]
      rcases hLoop with h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [bVisible, if_neg hNotLeaf, Finset.mem_singleton]
      exact hMain
  · intro hEdge
    obtain ⟨i, hiIncident, hiVisible⟩ := Finset.mem_biUnion.mp hEdge
    have hIncident : occ m i ∈ GluingDatum.incidentEdges v :=
      (mem_incidentEdges_occ m v i).mpr hiIncident
    by_cases hLeaf : IsLeafEdge m i
    · rw [bVisible, if_pos hLeaf] at hiVisible
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiVisible
      rcases hiVisible with rfl | rfl
      · exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨bLoopFirst_survives s hLeaf, bMain_incident_core s hIncident⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨bLoopSecond_survives s hLeaf, bLoopSecond_incident_core s hLeaf hIncident⟩
    · rw [bVisible, if_neg hLeaf, Finset.mem_singleton] at hiVisible
      subst edge
      exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨ballot_mainSurvives s (occ m i), bMain_incident_core s hIncident⟩

/-- **Numerical form of the star census**, identical for every slope sequence:
a target leaf occurrence contributes its two loop flags, every other incident
target occurrence contributes one surviving occurrence.  A spine block of `s_i`
sheets is still a single source occurrence, which is why the count does not see
the sequence. -/
theorem bNonDanglingValency_core_eq_sum (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) :
    nonDanglingValency (ballotDatum m s) (bCore m s v) =
      ∑ i ∈ incidentIndices m v, if IsLeafEdge m i then 2 else 1 := by
  classical
  rw [← card_nonDanglingIncident, bNonDanglingIncident_core_eq_visible,
    Finset.card_biUnion (bVisible_pairwiseDisjoint s (incidentIndices m v))]
  exact Finset.sum_congr rfl fun i _ => card_bVisible s i

/-! ## 5.  Trivalence -/

theorem bNonDanglingValency_core_root (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) (hv : v.val = 0) :
    nonDanglingValency (ballotDatum m s) (bCore m s v) = 3 := by
  rw [bNonDanglingValency_core_eq_sum, incidentIndices_root m v hv]
  simp [IsLeafEdge]

theorem bNonDanglingValency_core_leaf (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) (hv : v.val % 3 = 1) :
    nonDanglingValency (ballotDatum m s) (bCore m s v) = 2 := by
  rw [bNonDanglingValency_core_eq_sum, incidentIndices_leaf m v hv]
  have hLeaf : IsLeafEdge m
      (⟨v.val - 1, by have := v.isLt; omega⟩ : Fin (6 * m + 3)) :=
    Or.inl (show (v.val - 1) % 3 = 0 by omega)
  simp [hLeaf]

theorem bNonDanglingValency_core_lastLeaf (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) (hv : v.val = 6 * m + 3) :
    nonDanglingValency (ballotDatum m s) (bCore m s v) = 2 := by
  rw [bNonDanglingValency_core_eq_sum, incidentIndices_lastLeaf m v hv]
  have hLeaf : IsLeafEdge m (⟨6 * m + 2, by omega⟩ : Fin (6 * m + 3)) := Or.inr rfl
  simp [hLeaf]

theorem bNonDanglingValency_core_stem (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) (hmod : v.val % 3 = 0) (hlo : 3 ≤ v.val)
    (hhi : v.val ≤ 6 * m) :
    nonDanglingValency (ballotDatum m s) (bCore m s v) = 3 := by
  rw [bNonDanglingValency_core_eq_sum, incidentIndices_stem m v hmod hlo hhi]
  have hStemNotLeaf : ¬ IsLeafEdge m (⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)) := by
    rintro (h | h)
    · exact absurd (show (v.val - 1) % 3 = 0 from h) (by omega)
    · exact absurd (show v.val - 1 = 6 * m + 2 from h) (by omega)
  have hLeaf : IsLeafEdge m (⟨v.val, by omega⟩ : Fin (6 * m + 3)) := Or.inl hmod
  have hNe : (⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)) ≠ ⟨v.val, by omega⟩ := by
    intro h
    have hval : v.val - 1 = v.val := congrArg Fin.val h
    omega
  simp [hStemNotLeaf, hLeaf, hNe]

theorem bNonDanglingValency_core_junction (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) (hmod : v.val % 3 = 2) (hhi : v.val + 1 ≤ 6 * m) :
    nonDanglingValency (ballotDatum m s) (bCore m s v) = 3 := by
  have hlt := v.isLt
  rw [bNonDanglingValency_core_eq_sum, incidentIndices_junction m v hmod hhi]
  have hLeftNotLeaf : ¬ IsLeafEdge m (⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)) := by
    rintro (h | h)
    · exact absurd (show (v.val - 1) % 3 = 0 from h) (by omega)
    · exact absurd (show v.val - 1 = 6 * m + 2 from h) (by omega)
  have hStemNotLeaf : ¬ IsLeafEdge m (⟨v.val, by omega⟩ : Fin (6 * m + 3)) := by
    rintro (h | h)
    · exact absurd (show v.val % 3 = 0 from h) (by omega)
    · exact absurd (show v.val = 6 * m + 2 from h) (by omega)
  have hRightNotLeaf : ¬ IsLeafEdge m (⟨v.val + 2, by omega⟩ : Fin (6 * m + 3)) := by
    rintro (h | h)
    · exact absurd (show (v.val + 2) % 3 = 0 from h) (by omega)
    · exact absurd (show v.val + 2 = 6 * m + 2 from h) (by omega)
  have hLS : (⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)) ≠ ⟨v.val, by omega⟩ := by
    intro h
    have hval : v.val - 1 = v.val := congrArg Fin.val h
    omega
  have hLR : (⟨v.val - 1, by omega⟩ : Fin (6 * m + 3)) ≠ ⟨v.val + 2, by omega⟩ := by
    intro h
    have hval : v.val - 1 = v.val + 2 := congrArg Fin.val h
    omega
  have hSR : (⟨v.val, by omega⟩ : Fin (6 * m + 3)) ≠ ⟨v.val + 2, by omega⟩ := by
    intro h
    have hval : v.val = v.val + 2 := congrArg Fin.val h
    omega
  simp [hLeftNotLeaf, hStemNotLeaf, hRightNotLeaf, hLS, hLR, hSR]

theorem bNonDanglingValency_core_lastStem (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) (hv : v.val = 6 * m + 2) :
    nonDanglingValency (ballotDatum m s) (bCore m s v) = 3 := by
  rw [bNonDanglingValency_core_eq_sum, incidentIndices_lastStem m v hv]
  have hSpineNotLeaf : ¬ IsLeafEdge m (⟨6 * m + 1, by omega⟩ : Fin (6 * m + 3)) := by
    rintro (h | h)
    · exact absurd (show (6 * m + 1) % 3 = 0 from h) (by omega)
    · exact absurd (show 6 * m + 1 = 6 * m + 2 from h) (by omega)
  have hLeaf : IsLeafEdge m (⟨6 * m + 2, by omega⟩ : Fin (6 * m + 3)) := Or.inr rfl
  have hNe : (⟨6 * m + 1, by omega⟩ : Fin (6 * m + 3)) ≠ ⟨6 * m + 2, by omega⟩ := by
    intro h
    have hval : 6 * m + 1 = 6 * m + 2 := congrArg Fin.val h
    omega
  simp [hSpineNotLeaf, hLeaf, hNe]

/-- **The pruned ballot source is trivalent, for every slope sequence.**  This
is the `trivalent` obligation of the presentation. -/
theorem ballot_trivalent (s : Slopes (2 * (m + 1)))
    (x : (ballotDatum m s).SourceVertex) :
    nonDanglingValency (ballotDatum m s) x ≤ 3 := by
  rcases bSourceVertex_eq_core_or_other s x with hCore | hOther
  · rw [hCore]
    rcases vertexClass m x.1.1 with hRoot | hLeaf | hStem | hLastLeaf |
        hJunction | hLastStem
    · rw [bNonDanglingValency_core_root s x.1.1 hRoot]
    · rw [bNonDanglingValency_core_leaf s x.1.1 hLeaf]; omega
    · rw [bNonDanglingValency_core_stem s x.1.1 hStem.1 hStem.2.1 hStem.2.2]
    · rw [bNonDanglingValency_core_lastLeaf s x.1.1 hLastLeaf]; omega
    · rw [bNonDanglingValency_core_junction s x.1.1 hJunction.1 hJunction.2]
    · rw [bNonDanglingValency_core_lastStem s x.1.1 hLastStem]
  · have hSelf := (ballotDatum m s).sourceEndpoint_self x
    rw [← hSelf, bNonDanglingValency_other_eq_zero s x.1.1 hOther]
    omega


/-! ## 6.  The surviving-valency-two vertices are exactly the leaf folds -/

/-- **A surviving-valency-two source vertex is a leaf fold**, for every slope
sequence: every other class has surviving valency `0` or `3`. -/
theorem bEq_fold_of_nonDanglingValency_eq_two (s : Slopes (2 * (m + 1)))
    (x : (ballotDatum m s).SourceVertex)
    (hx : nonDanglingValency (ballotDatum m s) x = 2) :
    ∃ i : Fin (6 * m + 3), IsLeafEdge m i ∧
      x = bCore m s (i.succ : (catTree m).V) := by
  rcases bSourceVertex_eq_core_or_other s x with hCore | hOther
  · rw [hCore] at hx ⊢
    have hlt := x.1.1.isLt
    rcases vertexClass m x.1.1 with hRoot | hLeaf | hStem | hLastLeaf |
        hJunction | hLastStem
    · rw [bNonDanglingValency_core_root s x.1.1 hRoot] at hx; omega
    · exact ⟨⟨x.1.1.val - 1, by omega⟩,
        Or.inl (show (x.1.1.val - 1) % 3 = 0 by omega),
        congrArg (bCore m s)
          (Fin.ext (show x.1.1.val = x.1.1.val - 1 + 1 by omega))⟩
    · rw [bNonDanglingValency_core_stem s x.1.1 hStem.1 hStem.2.1 hStem.2.2] at hx
      omega
    · exact ⟨⟨6 * m + 2, by omega⟩, Or.inr rfl,
        congrArg (bCore m s)
          (Fin.ext (show x.1.1.val = 6 * m + 2 + 1 by omega))⟩
    · rw [bNonDanglingValency_core_junction s x.1.1 hJunction.1 hJunction.2] at hx
      omega
    · rw [bNonDanglingValency_core_lastStem s x.1.1 hLastStem] at hx; omega
  · have hSelf := (ballotDatum m s).sourceEndpoint_self x
    rw [← hSelf, bNonDanglingValency_other_eq_zero s x.1.1 hOther] at hx
    omega

/-- A surviving occurrence at a leaf fold lies over that leaf edge: the fold's
target vertex is a target leaf. -/
theorem bTarget_eq_occ_of_incident_fold (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i)
    (edge : (ballotDatum m s).SourceEdge)
    (hIncident : Incident (ballotDatum m s) edge
      (bCore m s (i.succ : (catTree m).V))) :
    edge.1.1 = occ m i := by
  have hi := i.isLt
  have hTarget := (incident_iff_target_mem_and_rel (ballotDatum m s) edge
    (bCore m s (i.succ : (catTree m).V))).mp hIncident
  obtain ⟨j, hj⟩ := occ_surj m edge.1.1
  have hj' := j.isLt
  rw [hj]
  refine congrArg (occ m) (Fin.ext ?_)
  have hjMem : j ∈ incidentIndices m (i.succ : (catTree m).V) := by
    refine (mem_incidentEdges_occ m (i.succ : (catTree m).V) j).mp ?_
    have hraw := hTarget.1
    rw [hj] at hraw
    exact hraw
  rcases hLeaf with hMod | hLast
  · rw [incidentIndices_leaf m (i.succ : (catTree m).V)
      (show (i.val + 1) % 3 = 1 by omega), Finset.mem_singleton] at hjMem
    have hVal : j.val = i.val + 1 - 1 := congrArg Fin.val hjMem
    omega
  · rw [incidentIndices_lastLeaf m (i.succ : (catTree m).V)
      (show i.val + 1 = 6 * m + 3 by omega), Finset.mem_singleton] at hjMem
    have hVal : j.val = 6 * m + 2 := congrArg Fin.val hjMem
    omega

/-- **Stable paths never cross a target fibre**, for every slope sequence.
This is the `RowsInFibres` obligation of the presentation. -/
theorem ballot_rowsInFibres (s : Slopes (2 * (m + 1))) :
    RowsInFibres (ballotDatum m s) := by
  intro first second h
  obtain ⟨-, vertex, hFirst, hSecond, hValency⟩ := h
  obtain ⟨i, hLeaf, hVertex⟩ :=
    bEq_fold_of_nonDanglingValency_eq_two s vertex hValency
  rw [hVertex] at hFirst hSecond
  exact (bTarget_eq_occ_of_incident_fold s hLeaf first.1 hFirst).trans
    (bTarget_eq_occ_of_incident_fold s hLeaf second.1 hSecond).symm

/-! ## 7.  Fibres lie in rows, and every row has an end -/

theorem bLeafOcc_incident_fold (m : ℕ) (i : Fin (6 * m + 3)) :
    occ m i ∈ GluingDatum.incidentEdges (i.succ : (catTree m).V) :=
  (mem_incidentEdges_occ m (i.succ : (catTree m).V) i).mpr
    ((mem_incidentIndices m _ i).mpr (Or.inr rfl))

/-- The two flags of a ballot loop are consecutive at its fold, for every slope
sequence: the fold has surviving valency two. -/
theorem bLoopFlags_consecutive (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    Consecutive (ballotDatum m s)
      ⟨(ballotDatum m s).sourceEdge (occ m i) 0, bLoopFirst_survives s hLeaf⟩
      ⟨bLoopSecond m s i, bLoopSecond_survives s hLeaf⟩ := by
  have hi := i.isLt
  refine ⟨?_, bCore m s (i.succ : (catTree m).V),
    bMain_incident_core s (bLeafOcc_incident_fold m i),
    bLoopSecond_incident_core s hLeaf (bLeafOcc_incident_fold m i), ?_⟩
  · intro hEq
    exact bLoopFirst_ne_bLoopSecond s hLeaf (congrArg Subtype.val hEq)
  · rcases hLeaf with hMod | hLast
    · exact bNonDanglingValency_core_leaf s (i.succ : (catTree m).V)
        (show (i.val + 1) % 3 = 1 by omega)
    · exact bNonDanglingValency_core_lastLeaf s (i.succ : (catTree m).V)
        (show i.val + 1 = 6 * m + 3 by omega)

/-- The spine-sheet occurrence over a target occurrence, as a surviving
occurrence. -/
noncomputable def bMainND (m : ℕ) (s : Slopes (2 * (m + 1)))
    (i : Fin (6 * m + 3)) : NonDanglingEdge (ballotDatum m s) :=
  ⟨(ballotDatum m s).sourceEdge (occ m i) 0, ballot_mainSurvives s (occ m i)⟩

/-- **Every surviving occurrence in one target fibre lies on the spine-sheet
occurrence's stable row.**  Over a leaf edge the two flags are consecutive at
the fold; over a stem or a spine edge the whole block is literally one
occurrence. -/
theorem bSourceEdge_stablePath_eq_main (s : Slopes (2 * (m + 1)))
    (i : Fin (6 * m + 3)) (σ : Fin (m + 2))
    (hSurvives : ¬ IsDangling (ballotDatum m s)
      ((ballotDatum m s).sourceEdge (occ m i) σ)) :
    NonDanglingEdge.stablePath (data := ballotDatum m s)
        ⟨(ballotDatum m s).sourceEdge (occ m i) σ, hSurvives⟩
      = (bMainND m s i).stablePath := by
  have hSur : bSurvives m s i.val σ.val := by
    by_contra h
    exact hSurvives ((bOccurrence_isDangling_iff s i σ).mpr h)
  by_cases hs0 : σ.val = 0
  · have hσ : σ = 0 := Fin.ext hs0
    subst hσ
    rfl
  · by_cases hleaf : IsLeafEdge m i
    · rw [bSurvives_of_not_spine s (show i.val % 3 ≠ 1 by
        unfold IsLeafEdge at hleaf; omega)] at hSur
      have hcum : σ.val = s.cum (lolli (i.val + 1)) := by
        rcases hSur with h | h
        · exact absurd h hs0
        · exact h
      have hσ : σ = cumSheet m s (i.val + 1) :=
        Fin.ext (by rw [cumSheet_val]; exact hcum)
      subst hσ
      exact (stablePath_eq_of_consecutive (bLoopFlags_consecutive s hleaf)).symm
    · exact congrArg (NonDanglingEdge.stablePath (data := ballotDatum m s))
        (show (⟨_, hSurvives⟩ : NonDanglingEdge (ballotDatum m s)) = bMainND m s i
          from Subtype.ext
            (bOcc_eq_main s i (edgePred_of_bSurvives_of_not_leaf s hleaf hSur)))

theorem bEdge_stablePath_eq_main (s : Slopes (2 * (m + 1)))
    (edge : NonDanglingEdge (ballotDatum m s)) :
    edge.stablePath = (bMainND m s ((catEdgeEquiv m).symm edge.1.1.1)).stablePath := by
  have hi : occ m ((catEdgeEquiv m).symm edge.1.1.1) = edge.1.1.1 :=
    (catEdgeEquiv m).apply_symm_apply _
  have hEq : (ballotDatum m s).sourceEdge
      (occ m ((catEdgeEquiv m).symm edge.1.1.1)) edge.1.1.2 = edge.1 := by
    rw [hi]
    exact GluingDatum.sourceEdge_self _ _
  have hs : ¬ IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge
      (occ m ((catEdgeEquiv m).symm edge.1.1.1)) edge.1.1.2) := hEq.symm ▸ edge.2
  exact (congrArg (NonDanglingEdge.stablePath (data := ballotDatum m s))
      (show (⟨_, hs⟩ : NonDanglingEdge (ballotDatum m s)) = edge from
        Subtype.ext hEq)).symm.trans
    (bSourceEdge_stablePath_eq_main s _ edge.1.1.2 hs)

/-- **Target fibres do not split between stable paths**, for every slope
sequence.  This is the `FibresInRows` obligation of the presentation. -/
theorem ballot_fibresInRows (s : Slopes (2 * (m + 1))) :
    FibresInRows (ballotDatum m s) := by
  intro first second h
  rw [bEdge_stablePath_eq_main s first, bEdge_stablePath_eq_main s second, h]

/-- The parent endpoint of a spine-sheet occurrence is never a leaf fold, so it
is a path end. -/
theorem bMain_left_isPathEnd (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    IsPathEnd (ballotDatum m s) (bMainND m s i).1 (bCore m s (catParent m i)) := by
  refine ⟨bMain_incident_core s
    ((mem_incidentEdges_occ m (catParent m i) i).mpr
      ((mem_incidentIndices m _ i).mpr (Or.inl rfl))), ?_⟩
  intro hValency
  obtain ⟨j, hLeaf, hVertex⟩ :=
    bEq_fold_of_nonDanglingValency_eq_two s _ hValency
  have hTarget : (catParent m i).val = j.val + 1 :=
    congrArg (fun vertex : (ballotDatum m s).SourceVertex => vertex.1.1.val) hVertex
  have hi := i.isLt
  have hj := j.isLt
  unfold IsLeafEdge at hLeaf
  rw [catParent_val, parentIndex] at hTarget
  split_ifs at hTarget <;> omega

/-- **Every stable row reaches a branch**, for every slope sequence.  This is
the `pathEnds` obligation of the presentation. -/
theorem ballot_pathEnds (s : Slopes (2 * (m + 1))) :
    HasPathEnds (ballotDatum m s) := fun edge =>
  ⟨bMainND m s ((catEdgeEquiv m).symm edge.1.1.1),
    bCore m s (catParent m ((catEdgeEquiv m).symm edge.1.1.1)),
    (bEdge_stablePath_eq_main s edge).symm, bMain_left_isPathEnd s _⟩

/-! ## 8.  The full-dimensional presentation at every slope sequence -/

/-- **The ballot-parametrized caterpillar datum carries a full-dimensional
source presentation over `Fin (3g - 3)`, for every even genus `g = 2m + 2` and
every slope sequence.**  The five obligations of
`BallotFullDimensional.ballotPresentationOfRowData` are proved: leaf, stem
and spine censuses give `mainSurvives`, the star census gives `trivalent`, the
fold classification gives `RowsInFibres` and `pathEnds`, and the fibre-to-row
argument gives `FibresInRows`. -/
noncomputable def ballotFullDim (m : ℕ) (s : Slopes (2 * (m + 1))) :
    FullDimensionalSourcePresentation (ballotDatum m s) (Fin (6 * m + 3)) :=
  ballotPresentationOfRowData m s (ballot_mainSurvives s) (ballot_rowsInFibres s)
    (ballot_fibresInRows s) (ballot_trivalent s) (ballot_pathEnds s)


/-- **The honest stable length-matrix labelling of the ballot datum**, over the
coordinate type `Fin (3g - 3)`, for every slope sequence. -/
noncomputable def ballotLabelling (m : ℕ) (s : Slopes (2 * (m + 1))) :
    StableLengthMatrixLabelling (ballotDatum m s) (Fin (6 * m + 3)) :=
  rowLabelling (catEdgeEquiv m) (ballot_rowsInFibres s) (ballot_fibresInRows s)
    (fun occurrence => ⟨bMain m s occurrence, ballot_mainSurvives s occurrence⟩)
    (fun _ => rfl)

/-- **The diagonal index pattern of the ballot datum**, for every slope
sequence. -/
theorem ballotDiagonalPattern (m : ℕ) (s : Slopes (2 * (m + 1))) :
    SeedDeterminant.DiagonalPattern (ballotLabelling m s).presentation :=
  rowDiagonalPattern (catEdgeEquiv m) (ballot_rowsInFibres s)
    (ballot_fibresInRows s) _ _

/-- **The length matrix of the ballot datum is nonsingular**, for every slope
sequence. -/
theorem ballotDet_pos (m : ℕ) (s : Slopes (2 * (m + 1))) :
    0 < (GluingDatum.LengthMatrixPresentation.matrix
      (ballotLabelling m s).presentation).det :=
  (ballotDiagonalPattern m s).det_pos

theorem ballotDet_ne_zero (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (ballotLabelling m s).presentation).det ≠ 0 :=
  (ballotDiagonalPattern m s).det_ne_zero

@[simp] theorem ballotFullDim_labelling (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (ballotFullDim m s).labelling = ballotLabelling m s := rfl

/-- Non-vacuity: at genus six every one of the five slope sequences carries a
full-dimensional presentation over the fifteen coordinates `3g - 3`. -/
noncomputable example (s : Slopes 6) :
    FullDimensionalSourcePresentation (ballotDatum 2 s) (Fin (6 * 2 + 3)) :=
  ballotFullDim 2 s

/-- Consistency with the caterpillar datum: the zig-zag member of the
family is `caterpillarDatum m`. -/
noncomputable example (m : ℕ) :
    FullDimensionalSourcePresentation (caterpillarDatum m) (Fin (6 * m + 3)) := by
  rw [← ballotDatum_zig m]
  exact ballotFullDim m (zig m)

end DraismaVargas.Count.BallotValency
