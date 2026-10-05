module

public import DraismaVargasCount.BallotFullDimensional

@[expose] public section

/-!
# The stem census of the ballot caterpillar, at a general slope sequence

The second layer of the pruning census behind the full-dimensional presentation of the ballot
caterpillar datum.  `Count.BallotFullDimensional.ballotPresentationOfRowData` reduces that
presentation, at a general slope sequence `s`, to five named obligations, all of which factor
through three exact fibre censuses.  The **leaf** layer is
`Count.BallotFullDimensional.bLeafOccurrence_isDangling_iff`, for every `s`.  This module
proves the **stem** layer for every `s`, together with the two pieces of reachability
machinery that the spine layer also needs.

## What is proved

* §1 -- **the interval structure of the spine blocks.**  `SpineMem s i k` is
  `k = 0 ∨ (cum i + 2 ≤ k + slope i ∧ k ≤ cum i)`; the first conjunct cuts out
  a down-set of spine indices (`spineLow_anti`) and the second an up-set
  (`Slopes.cum_mono`), so for a fixed nonzero label the set of spine edges
  carrying it is an interval.  `not_spineMem_dichotomy` is the form the spine
  induction consumes: where a label is *absent*, it is absent on a whole
  initial or a whole final stretch of the spine.  Nothing geometric is used.
* §2 -- **singleton incidence.**  Above a sheet outside the block at a target
  vertex, the source vertex has exactly as many incident source occurrences as
  the target vertex has incident target occurrences
  (`bCard_incident_of_not`).  This is
  `LocalCases.CaterpillarSpine.card_incidentSourceEdge_sourceEndpoint_other`
  with the zig-zag's `pairPart` replaced by the general star partition.
* §3 -- **loop anchors and confined reachability.**  `bCore m s v` is the
  spine-sheet source vertex over `v`.  `bJunction_reaches_prevLoop` and
  `bVertex_reaches_nextLoop` walk from a junction to the nearest lollipop loop
  behind it, respectively ahead of it, through target vertices of strictly
  smaller, respectively strictly larger, index; both are stated against an
  arbitrary confinement predicate, so the spine layer can reuse them verbatim.
  `bNonDanglingValency_loopBase_ne_zero` is the positive-genus anchor, and it
  rests on the leaf census.
* §4 -- **the exact stem-fibre census, for every slope sequence**:
  `bStemOccurrence_isDangling_iff`.  Over a target stem the bridge pair
  `{0, cum i}` -- a single block, hence a single source occurrence -- survives
  pruning, and every other singleton sheet occurrence dangles.  This is
  `LocalCases.CaterpillarPruning.stemOccurrence_isDangling_iff` with the
  zig-zag's partner sheet `pairIndex` replaced by the general counter
  `cum s (lolli ·)`.

## What is not proved here

* **The spine layer is not here.**  `bSpineOccurrence_isDangling_iff` -- the
  statement that over the spine edge `h_i` the surviving occurrence is the one
  block `SpineMem s i` of `s_i` sheets and the `m + 2 - s_i` singletons dangle
  -- is `Count.BallotSpineCensus`, which consumes §1, §2 and §3 of this file.
* **None of the five obligations of the presentation is discharged here.**
  `mainSurvives`, `RowsInFibres`, `FibresInRows`, `trivalent` and `pathEnds` are not
  proved below for a general `s`, and nothing here claims them.  They are discharged
  downstream, in `Count.BallotSpineCensus` (`mainSurvives`) and
  `Count.BallotValency` (the other four, and the presentation itself).
* **`FullDimensionalSourcePresentation` is not `BallotFamily`.**  No
  `FibreMember`, no `catCore`, no `GeometricFibre`, no `openOddCount` occurs
  below.  `Count.CaterpillarBallot.BallotFamily` is inhabited elsewhere, at
  every `m` and every positive request, by
  `BallotCoreIdentification.ballotFamily`, but not constructed here.
* **No genericity hypothesis is used or supplied.**  Part II's count carries
  pairwise distinct edge lengths on the metric caterpillar; that hypothesis
  belongs to the uniqueness half and no statement below mentions a length.
* Nothing here counts anything, mod 2 or otherwise.
-/

namespace DraismaVargas.Count.BallotPruning

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingSideStructure
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.BallotFullDimensional

/-! ## 1.  The spine blocks of a slope sequence form an interval

`SpineMem s i k` for `k ≠ 0` is the conjunction of a *lower* condition
`cum i + 2 ≤ k + slope i` and an *upper* condition `k ≤ cum i`.  The counter
`cum` is monotone, so the upper condition holds on a final stretch.  The
quantity `cum i - slope i` is also monotone -- an up-step raises both by one, a
down-step raises it by one, a flat step leaves it alone -- so the lower
condition holds on an initial stretch. -/

section Interval

variable {g : ℕ}

/-- One step of the lower condition, backwards. -/
theorem spineLow_step (s : Slopes g) {k i : ℕ}
    (h : s.cum (i + 1) + 2 ≤ k + s.slope (i + 1)) :
    s.cum i + 2 ≤ k + s.slope i := by
  have hc := Slopes.cum_succ s i
  rcases Slopes.slope_trichotomy s i with hup | hdown | hflat
  · rw [ite_eq_left hup] at hc; omega
  · rw [ite_eq_right (show ¬ (s.slope (i + 1) = s.slope i + 1) by omega)] at hc; omega
  · rw [ite_eq_right (show ¬ (s.slope (i + 1) = s.slope i + 1) by omega)] at hc; omega

/-- **The lower condition of `SpineMem` is a down-set in the spine index.** -/
theorem spineLow_anti (s : Slopes g) {k : ℕ} :
    ∀ (n i : ℕ), s.cum (i + n) + 2 ≤ k + s.slope (i + n) →
      s.cum i + 2 ≤ k + s.slope i := by
  intro n
  induction n with
  | zero => intro i h; simpa using h
  | succ n ih =>
      intro i h
      refine ih i (spineLow_step s ?_)
      rw [show i + n + 1 = i + (n + 1) by omega]
      exact h

/-- A nonzero label present on some spine edge satisfies the lower condition
at every earlier spine edge. -/
theorem spineLow_of_spineMem (s : Slopes g) {k i j : ℕ} (hk : k ≠ 0)
    (hij : i ≤ j) (h : s.SpineMem j k) : s.cum i + 2 ≤ k + s.slope i := by
  obtain ⟨n, rfl⟩ : ∃ n, j = i + n := ⟨j - i, by omega⟩
  refine spineLow_anti s n i ?_
  rcases h with h0 | ⟨h1, -⟩
  · exact absurd h0 hk
  · exact h1

/-- **Where a nonzero label is absent from a spine block, it is absent on a
whole initial stretch or on a whole final stretch of the spine.**  This is the
combinatorial input of the spine induction: the block interval of a label is
convex, so the complement is the union of a prefix and a suffix. -/
theorem not_spineMem_dichotomy (s : Slopes g) {k i : ℕ} (hk : k ≠ 0)
    (h : ¬ s.SpineMem i k) :
    (∀ j, j ≤ i → ¬ s.SpineMem j k) ∨ (∀ j, i ≤ j → ¬ s.SpineMem j k) := by
  by_cases hhigh : k ≤ s.cum i
  · refine Or.inr (fun j hij hmem => ?_)
    exact h (Or.inr ⟨spineLow_of_spineMem s hk hij hmem, hhigh⟩)
  · refine Or.inl (fun j hji hmem => ?_)
    have h1 := Slopes.spineMem_le s hmem
    have h2 := Slopes.cum_mono s hji
    omega

end Interval

/-! ## 2.  Singleton incidence above the ballot datum -/

section Singleton

variable {m : ℕ}

/-- Above a sheet outside the block at a target vertex, the vertex block is a
singleton. -/
theorem bVertexBlock_of_not (s : Slopes (2 * (m + 1))) (v : (catTree m).V)
    {σ : Fin (m + 2)} (hσ : ¬ VertPred m s v.val σ.val) :
    ((ballotDatum m s).vertexPartition v).block σ = {σ} := by
  rw [ballotDatum_vertexPart_val]
  exact SheetPartition.sheetStar_block_of_not (VertPred m s v.val)
    (vertPred_zero s v.val) hσ

/-- **Above a singleton sheet, source incidence counts target incidence.** -/
theorem bCard_incident_of_not (s : Slopes (2 * (m + 1))) (v : (catTree m).V)
    {σ : Fin (m + 2)} (hσ : ¬ VertPred m s v.val σ.val) :
    Fintype.card (IncidentSourceEdge (ballotDatum m s)
        ((ballotDatum m s).sourceEndpoint v σ))
      = (GluingDatum.incidentEdges v).card := by
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  have hrepr : ((ballotDatum m s).sourceEndpoint v σ).1.2 = σ := by
    show (catStar m (VertPred m s v.val)).repr σ = σ
    exact catStar_repr_of_not (VertPred m s v.val) hσ
  have htgt : ((ballotDatum m s).sourceEndpoint v σ).1.1 = v := rfl
  rw [htgt, hrepr]
  calc (∑ edge ∈ GluingDatum.incidentEdges v,
          ((ballotDatum m s).edgePartition edge).blockCountWithin
            ((ballotDatum m s).vertexPartition v) σ)
      = ∑ _edge ∈ GluingDatum.incidentEdges v, 1 :=
        Finset.sum_congr rfl fun edge _ =>
          SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _
            (bVertexBlock_of_not s v hσ)
    _ = (GluingDatum.incidentEdges v).card := by simp

end Singleton


/-! ## 3.  Loop anchors and confined reachability

The spine sheet `0` lies in every block, so it lifts the whole target tree to a
spanning subgraph of the source.  Walking along it from a junction reaches the
`u`-vertex of the lollipop behind or ahead, and that vertex carries the two
parallel flags of the leaf census -- the positive-genus anchor. -/

section Anchors

variable {m : ℕ}

/-- The spine-sheet source vertex above a target vertex. -/
def bCore (m : ℕ) (s : Slopes (2 * (m + 1))) (v : (catTree m).V) :
    (ballotDatum m s).SourceVertex :=
  (ballotDatum m s).sourceEndpoint v 0

@[simp] theorem bCore_target (s : Slopes (2 * (m + 1))) (v : (catTree m).V) :
    (bCore m s v).1.1 = v := rfl

theorem bCore_ne (s : Slopes (2 * (m + 1))) {v w : (catTree m).V}
    (h : v.val ≠ w.val) : bCore m s v ≠ bCore m s w := fun hEq =>
  h (congrArg (fun x : (ballotDatum m s).SourceVertex => x.1.1.val) hEq)

/-- Every target occurrence has its spine-sheet lift. -/
theorem bCoreStep_pos (s : Slopes (2 * (m + 1))) (k : Fin (6 * m + 3)) :
    0 < num_edges (ballotDatum m s).sourceGraph
      (bCore m s (catParent m k)) (bCore m s k.succ) := by
  have hOne := TreeFamily.num_edges_rootedTree_eq_one
    (6 * m + 3) (catParent m) (catParent_le m) k
  have hTarget : 0 < num_edges (catTree m) (catParent m k) k.succ := by
    change 0 < num_edges
      (TreeFamily.rootedTree (6 * m + 3) (catParent m) (catParent_le m))
        (catParent m k) k.succ
    rw [hOne]
    norm_num
  exact num_edges_sourceEndpoint_pos (ballotDatum m s) 0
    (catParent m k) k.succ hTarget

/-- The spine-sheet lift of a named target step. -/
theorem bCoreStep_of (s : Slopes (2 * (m + 1))) {a b : (catTree m).V}
    (k : Fin (6 * m + 3)) (ha : (catParent m k).val = a.val)
    (hb : k.val + 1 = b.val) :
    0 < num_edges (ballotDatum m s).sourceGraph (bCore m s a) (bCore m s b) := by
  have h1 : catParent m k = a := Fin.ext ha
  have h2 : (k.succ : (catTree m).V) = b := Fin.ext hb
  rw [← h1, ← h2]
  exact bCoreStep_pos s k

/-- **From a junction the loop behind it is reachable**, through target
vertices of strictly smaller index. -/
theorem bJunction_reaches_prevLoop (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) (hv : v.val % 3 = 2)
    (P : (ballotDatum m s).SourceVertex → Prop)
    (hP : ∀ w : (catTree m).V, w.val < v.val → P (bCore m s w)) :
    ∃ leaf : Fin (6 * m + 3), IsLeafEdge m leaf ∧
      ReachP (ballotDatum m s).sourceGraph P (bCore m s v)
        (bCore m s (catParent m leaf)) := by
  have hlt := v.isLt
  have hPn : ∀ (x : ℕ) (hx : x < 6 * m + 4), x < v.val →
      P (bCore m s ⟨x, hx⟩) := fun x hx h => hP ⟨x, hx⟩ h
  rcases Nat.lt_or_ge v.val 5 with hsmall | hbig
  · -- the junction `p_2`: one step back to the root `u_1`
    have hv2 : v.val = 2 := by omega
    refine ⟨⟨0, by omega⟩, Or.inl rfl, ?_⟩
    have hbase : catParent m (⟨0, by omega⟩ : Fin (6 * m + 3))
        = (⟨0, by omega⟩ : (catTree m).V) := by
      apply Fin.ext
      show parentIndex (0 + 1) = 0
      rw [parentIndex]
      split_ifs <;> omega
    rw [hbase]
    refine reachP_tail (reachP_refl (G := (ballotDatum m s).sourceGraph) P _) ?_
      (hPn 0 (by omega) (by omega))
    refine num_edges_pos_rev (bCoreStep_of s ⟨1, by omega⟩ ?_ ?_)
    · show parentIndex (1 + 1) = 0
      rw [parentIndex]
      split_ifs <;> omega
    · show 1 + 1 = v.val
      omega
  · -- an interior junction: back along the spine, then out along the stem
    refine ⟨⟨v.val - 2, by omega⟩, Or.inl (show (v.val - 2) % 3 = 0 by omega), ?_⟩
    have hbase : catParent m (⟨v.val - 2, by omega⟩ : Fin (6 * m + 3))
        = (⟨v.val - 2, by omega⟩ : (catTree m).V) := by
      apply Fin.ext
      show parentIndex (v.val - 2 + 1) = v.val - 2
      rw [parentIndex]
      split_ifs <;> omega
    rw [hbase]
    have hFirst : ReachP (ballotDatum m s).sourceGraph P (bCore m s v)
        (bCore m s ⟨v.val - 3, by omega⟩) := by
      refine reachP_tail (reachP_refl (G := (ballotDatum m s).sourceGraph) P _) ?_
        (hPn (v.val - 3) (by omega) (by omega))
      refine num_edges_pos_rev (bCoreStep_of s ⟨v.val - 1, by omega⟩ ?_ ?_)
      · show parentIndex (v.val - 1 + 1) = v.val - 3
        rw [parentIndex]
        split_ifs <;> omega
      · show v.val - 1 + 1 = v.val
        omega
    refine reachP_tail hFirst ?_ (hPn (v.val - 2) (by omega) (by omega))
    refine bCoreStep_of s ⟨v.val - 3, by omega⟩ ?_ ?_
    · show parentIndex (v.val - 3 + 1) = v.val - 3
      rw [parentIndex]
      split_ifs <;> omega
    · show v.val - 3 + 1 = v.val - 2
      omega

/-- **From a junction the loop ahead of it is reachable**, through target
vertices of strictly larger index.  At the last `u`-vertex there is nothing to
walk: it already carries the last loop. -/
theorem bVertex_reaches_nextLoop (s : Slopes (2 * (m + 1)))
    (v : (catTree m).V) (hv : v.val % 3 = 2)
    (P : (ballotDatum m s).SourceVertex → Prop)
    (hP : ∀ w : (catTree m).V, v.val < w.val → P (bCore m s w)) :
    ∃ leaf : Fin (6 * m + 3), IsLeafEdge m leaf ∧
      ReachP (ballotDatum m s).sourceGraph P (bCore m s v)
        (bCore m s (catParent m leaf)) := by
  have hlt := v.isLt
  have hPn : ∀ (x : ℕ) (hx : x < 6 * m + 4), v.val < x →
      P (bCore m s ⟨x, hx⟩) := fun x hx h => hP ⟨x, hx⟩ h
  by_cases hlast : v.val = 6 * m + 2
  · refine ⟨⟨6 * m + 2, by omega⟩, Or.inr rfl, ?_⟩
    have hbase : catParent m (⟨6 * m + 2, by omega⟩ : Fin (6 * m + 3)) = v := by
      apply Fin.ext
      show parentIndex (6 * m + 2 + 1) = v.val
      rw [parentIndex]
      split_ifs <;> omega
    rw [hbase]
    exact reachP_refl (G := (ballotDatum m s).sourceGraph) P _
  · refine ⟨⟨v.val + 1, by omega⟩, Or.inl (show (v.val + 1) % 3 = 0 by omega), ?_⟩
    have hbase : catParent m (⟨v.val + 1, by omega⟩ : Fin (6 * m + 3))
        = (⟨v.val + 1, by omega⟩ : (catTree m).V) := by
      apply Fin.ext
      show parentIndex (v.val + 1 + 1) = v.val + 1
      rw [parentIndex]
      split_ifs <;> omega
    rw [hbase]
    refine reachP_tail (reachP_refl (G := (ballotDatum m s).sourceGraph) P _) ?_
      (hPn (v.val + 1) (by omega) (by omega))
    refine bCoreStep_of s ⟨v.val, by omega⟩ ?_ ?_
    · show parentIndex (v.val + 1) = v.val
      rw [parentIndex]
      split_ifs <;> omega
    · show v.val + 1 = v.val + 1
      rfl

/-- The spine-sheet flag of a loop meets its attachment vertex. -/
theorem bLoopFirst_incident_base (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    Incident (ballotDatum m s) (bLoopFirst m s i) (bCore m s (catParent m i)) := by
  unfold Incident bLoopFirst bCore
  rw [sourceEnds_sourceEdge]
  exact Or.inl rfl

/-- **The attachment vertex of every ballot loop is active**, for every slope
sequence.  This is the leaf census used as the positive-genus anchor. -/
theorem bNonDanglingValency_loopBase_ne_zero (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) :
    nonDanglingValency (ballotDatum m s) (bCore m s (catParent m i)) ≠ 0 := by
  intro hZero
  have hMem : bLoopFirst m s i ∈
      nonDanglingIncident (ballotDatum m s) (bCore m s (catParent m i)) :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨bLoopFirst_survives s hLeaf, bLoopFirst_incident_base s i⟩
  have hPos := Finset.card_pos.mpr ⟨_, hMem⟩
  rw [card_nonDanglingIncident, hZero] at hPos
  omega

end Anchors


/-! ## 4.  The exact stem-fibre census

Over a target stem the occurrence partition is the star of the bridge pair
`PairMem s i = {0, cum i}`, so the pair is a *single* source occurrence and the
other `m` sheets are singletons.  The pair survives (§3 anchors on both sides);
each singleton dangles, because the `u`-end of the stem carries only the stem
and its leaf occurrence, and the latter dangles by the leaf census. -/

section Stem

variable {m : ℕ}

/-- The representative of a sheet of the distinguished block. -/
theorem catStar_repr_of_mem (P : ℕ → Prop) [DecidablePred P] {σ : Fin (m + 2)}
    (hσ : P σ.val) : (catStar m P).repr σ = 0 :=
  SheetPartition.sheetStar_repr_of_mem P hσ

/-- The `u`-vertex of a stem, the stem itself and the stem's leaf edge all
belong to one lollipop. -/
theorem lolli_stem_succ {i : ℕ} (h : i % 3 = 2) :
    lolli (i + 1) = lolli i ∧ lolli (i + 1 + 1) = lolli i := by
  unfold lolli
  omega

/-- Sheets of the bridge pair name one and the same source occurrence over the
stem. -/
theorem bOcc_eq_main (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3))
    {σ : Fin (m + 2)} (h : EdgePred m s i.val σ.val) :
    (ballotDatum m s).sourceEdge (occ m i) σ
      = (ballotDatum m s).sourceEdge (occ m i) 0 := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  show ((ballotDatum m s).edgePartition (occ m i)).repr σ
      = ((ballotDatum m s).edgePartition (occ m i)).repr 0
  rw [ballotDatum_edgePart_occ, catStar_repr_of_mem _ h,
    catStar_repr_of_mem _ (edgePred_zero s i.val)]

/-- Above a stem's `u`-end, a sheet outside the bridge pair is a singleton. -/
theorem bStemTip_not_vertPred (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) {σ : Fin (m + 2)}
    (hσ : ¬ s.PairMem (lolli i.val) σ.val) :
    ¬ VertPred m s (i.val + 1) σ.val := by
  rw [vertPred_pair s (show (i.val + 1) % 3 ≠ 2 by have := hStem.1; omega),
    (lolli_stem_succ hStem.1).1]
  exact hσ

/-- The `u`-end of a stem meets exactly the stem and the stem's leaf edge. -/
theorem incidentIndices_stemTip (m : ℕ) (v : (catTree m).V) {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) (hv : v.val = i.val + 1) :
    incidentIndices m v = {i, stemLeafIndex m i hStem} := by
  have hi := i.isLt
  have hmod := hStem.1
  have hlast := hStem.2
  ext j
  have hj := j.isLt
  simp only [mem_incidentIndices, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, parentIndex_eq_iff, stemLeafIndex_val, hv]
  omega

/-- Away from the bridge pair, the source vertex above a stem's `u`-end meets
exactly the stem and its leaf occurrence. -/
theorem bStemTip_card (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) {σ : Fin (m + 2)}
    (hσ : ¬ s.PairMem (lolli i.val) σ.val) :
    Fintype.card (IncidentSourceEdge (ballotDatum m s)
      ((ballotDatum m s).sourceEndpoint (i.succ : (catTree m).V) σ)) = 2 := by
  have hi := i.isLt
  have hmod := hStem.1
  have hlast := hStem.2
  have hnot : ¬ VertPred m s (i.succ : (catTree m).V).val σ.val :=
    bStemTip_not_vertPred s hStem hσ
  rw [bCard_incident_of_not s (i.succ : (catTree m).V) hnot]
  have hab : i ≠ stemLeafIndex m i hStem := by
    intro h
    have hval : i.val = i.val + 1 := congrArg Fin.val h
    omega
  exact card_incidentEdges_two m (i.succ : (catTree m).V) hab
    (incidentIndices_stemTip m (i.succ : (catTree m).V) hStem rfl)

/-- **Every singleton sheet over a stem dangles**, for every slope sequence. -/
theorem bStem_dangles_of_not (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) {σ : Fin (m + 2)}
    (hσ : ¬ s.PairMem (lolli i.val) σ.val) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ) := by
  have hi := i.isLt
  have hmod := hStem.1
  have hParent : catParent m (stemLeafIndex m i hStem) = (i.succ : (catTree m).V) := by
    apply Fin.ext
    show parentIndex (i.val + 1 + 1) = i.val + 1
    rw [parentIndex]
    split_ifs <;> omega
  refine isDangling_of_incident_of_vertex_degree_eq_two (ballotDatum m s)
    (first := (ballotDatum m s).sourceEdge (occ m (stemLeafIndex m i hStem)) σ)
    (second := (ballotDatum m s).sourceEdge (occ m i) σ)
    (vertex := (ballotDatum m s).sourceEndpoint (i.succ : (catTree m).V) σ)
    ?_ ?_ ?_ ?_ ?_
  · intro hEq
    have hTarget := congrArg
      (fun edge : (ballotDatum m s).SourceEdge => edge.1.1) hEq
    have hIndex := occ_injective m hTarget
    have hval : i.val + 1 = i.val := congrArg Fin.val hIndex
    omega
  · show Incident (ballotDatum m s) _ _
    unfold Incident
    rw [sourceEnds_sourceEdge]
    exact Or.inl (by
      rw [show ((occ m (stemLeafIndex m i hStem) : (catTree m).edges) :
        (catTree m).V × (catTree m).V).1 = catParent m (stemLeafIndex m i hStem)
          from rfl, hParent])
  · show Incident (ballotDatum m s) _ _
    unfold Incident
    rw [sourceEnds_sourceEdge]
    exact Or.inr rfl
  · rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge,
      bStemTip_card s hStem hσ]
    norm_num
  · refine (bLeafOccurrence_isDangling_iff s (stemLeafIndex_isLeaf hStem) σ).mpr ?_
    simp only [stemLeafIndex_val]
    rw [(lolli_stem_succ hmod).2]
    unfold Slopes.PairMem at hσ
    exact ⟨fun h => hσ (Or.inl h), fun h => hσ (Or.inr h)⟩

/-- **The bridge pair of every stem survives**, for every slope sequence: the
tip side is the attachment vertex of its own lollipop loop, and the junction
side reaches the loop of the lollipop behind it. -/
theorem bStemMain_survives (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) :
    ¬ IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) 0) := by
  have hi := i.isLt
  have hmod := hStem.1
  have hEnds : (ballotDatum m s).sourceEnds
        ((ballotDatum m s).sourceEdge (occ m i) 0)
      = (bCore m s (catParent m i), bCore m s (i.succ : (catTree m).V)) :=
    sourceEnds_sourceEdge (ballotDatum m s) (occ m i) 0
  have hJunctionVal : (catParent m i).val = i.val := by
    show parentIndex (i.val + 1) = i.val
    rw [parentIndex]
    split_ifs <;> omega
  have hTipParent : catParent m (stemLeafIndex m i hStem)
      = (i.succ : (catTree m).V) := by
    apply Fin.ext
    show parentIndex (i.val + 1 + 1) = i.val + 1
    rw [parentIndex]
    split_ifs <;> omega
  obtain ⟨leftLeaf, hLeftLeaf, hLeftReach⟩ :=
    bJunction_reaches_prevLoop s (catParent m i) (by rw [hJunctionVal]; omega)
      (fun vertex => vertex ≠ bCore m s (i.succ : (catTree m).V))
      (fun w hw => bCore_ne s (by
        rw [hJunctionVal] at hw
        show w.val ≠ (i.succ : (catTree m).V).val
        show w.val ≠ i.val + 1
        omega))
  refine not_isDangling_of_active_reaches (ballotDatum m s) _ hEnds
    (firstAnchor := bCore m s (catParent m leftLeaf))
    (secondAnchor := bCore m s (catParent m (stemLeafIndex m i hStem)))
    (bNonDanglingValency_loopBase_ne_zero s hLeftLeaf)
    (bNonDanglingValency_loopBase_ne_zero s (stemLeafIndex_isLeaf hStem))
    hLeftReach ?_
  rw [hTipParent]
  exact reachP_refl (G := (ballotDatum m s).sourceGraph) _ _

/-- **The exact stem-fibre occurrence census, for every slope sequence.**  The
bridge pair `{0, cum s i}` -- one block, hence one source occurrence -- is the
unique surviving stem occurrence; every other singleton sheet occurrence
dangles.  This is `LocalCases.CaterpillarPruning.stemOccurrence_isDangling_iff`
with the zig-zag's partner sheet `pairIndex` replaced by the general counter
`cum s (lolli ·)`. -/
theorem bStemOccurrence_isDangling_iff (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hStem : IsStemEdge m i) (σ : Fin (m + 2)) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ)
      ↔ ¬ s.PairMem (lolli i.val) σ.val := by
  constructor
  · intro hDangling hMem
    refine bStemMain_survives s hStem ?_
    rwa [bOcc_eq_main s i (by
      rw [edgePred_stem s hStem.1 hStem.2]
      exact hMem)] at hDangling
  · exact fun hσ => bStem_dangles_of_not s hStem hσ

/-- The census in the explicit two-label form: over a stem, the occurrence on
sheet `σ` dangles exactly when `σ` is neither the spine sheet nor the newest
label of the lollipop. -/
theorem bStemOccurrence_isDangling_iff' (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hStem : IsStemEdge m i) (σ : Fin (m + 2)) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ)
      ↔ (σ.val ≠ 0 ∧ σ.val ≠ s.cum (lolli i.val)) := by
  rw [bStemOccurrence_isDangling_iff s hStem σ]
  unfold Slopes.PairMem
  constructor
  · exact fun h => ⟨fun h0 => h (Or.inl h0), fun hc => h (Or.inr hc)⟩
  · rintro ⟨h0, hc⟩ (h | h)
    · exact h0 h
    · exact hc h

end Stem

end DraismaVargas.Count.BallotPruning
