module

public import DraismaVargasMarkedCount.MarkedCount.RegrowStable
public import DraismaVargas.LocalCases.StableSourceMatrix

@[expose] public section

/-!
# Regrowth, part 5: the length matrix of the regrown datum

The natural length matrix
`StableSourceMatrix.matrix` of `regrowDatum β`, at the rows of `stablePathEquiv` and the columns
of `occEquiv`, is block diagonal:

* a marked row of `D` over an old edge: the entry of the natural marked matrix of `D`
  (`matrix_inl_oldE`, in the form `markedEntry`);
* the bridge row of mark `j` over `t_b j`: `1/2` (the bridge has index two);
* the loop row of mark `j` over `t_l j`: `2` (two edges of index one);
* zero everywhere else.
-/

namespace DraismaVargas.Count.MarkedCount.Regrow

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource

variable {T : CFGraph.{0}} {d k : ℕ} {D : GluingDatum T d} (β : Branching D k)

/-! ## 1.  Matrix entries as sums over surviving edges -/

open Classical in
/-- A sum over the surviving occurrences of a row above a target edge, as a sum over all
surviving edges. -/
theorem sum_filter_nonDangling {S : CFGraph} (E : GluingDatum S d)
    (q : NonDanglingEdge E → Prop) (t : S.edges) (g : E.SourceEdge → ℚ) :
    ∑ e ∈ Finset.univ.filter (fun e : E.SourceEdge ↦
        (∃ h : ¬ IsDangling E e, q ⟨e, h⟩) ∧ e.1.1 = t), g e =
      ∑ e : NonDanglingEdge E, if q e ∧ e.1.1.1 = t then g e.1 else 0 := by
  rw [Finset.sum_filter, ← Fintype.sum_subtype_add_sum_subtype (fun e ↦ ¬ IsDangling E e)]
  have h0 : ∑ e : {e : E.SourceEdge // ¬ ¬ IsDangling E e},
      (if (∃ h : ¬ IsDangling E e.1, q ⟨e.1, h⟩) ∧ e.1.1.1 = t then g e.1 else 0) = 0 :=
    Finset.sum_eq_zero fun e _ ↦ ite_eq_right fun ⟨⟨h, _⟩, _⟩ ↦ e.2 h
  rw [h0, add_zero]
  refine Fintype.sum_congr _ _ fun e ↦ ?_
  have hiff : ((∃ h : ¬ IsDangling E e.1, q ⟨e.1, h⟩) ∧ e.1.1.1 = t) ↔ (q e ∧ e.1.1.1 = t) :=
    ⟨fun ⟨⟨_, hq⟩, ht⟩ ↦ ⟨hq, ht⟩, fun ⟨hq, ht⟩ ↦ ⟨⟨e.2, hq⟩, ht⟩⟩
  exact if_congr hiff rfl rfl

open Classical in
theorem matrix_eq_sum {S : CFGraph} (E : GluingDatum S d) (path : StablePath E) (t : S.edges) :
    StableSourceMatrix.matrix E path t =
      ∑ e : NonDanglingEdge E,
        if e.stablePath = path ∧ e.1.1.1 = t then (1 : ℚ) / E.sourceEdgeIndex e.1 else 0 := by
  unfold StableSourceMatrix.matrix StableSourceMatrix.occurrences
  exact sum_filter_nonDangling E (fun e ↦ e.stablePath = path) t _

open Classical in
/-- **The natural marked matrix entry of `D`**, as a sum over surviving edges. -/
def markedEntry (P : MarkedStablePath D (marks β)) (t : T.edges) : ℚ :=
  ∑ F : NonDanglingEdge D,
    if markedRow (marks β) F = P ∧ F.1.1.1 = t then (1 : ℚ) / D.sourceEdgeIndex F.1 else 0

/-! ## 2.  Indices -/

theorem sourceEdgeIndex_oldSE (F : D.SourceEdge) :
    (regrowDatum β).sourceEdgeIndex (oldSE β F) = D.sourceEdgeIndex F := by
  unfold GluingDatum.sourceEdgeIndex
  simp only [oldSE, ep_oldE]

theorem blockCard_pair_left {a b : Fin d} (hab : a ≠ b) :
    (GenusSixExistence.Tripod.Gluing.SheetOps.pair a b).blockCard a = 2 := by
  classical
  unfold SheetPartition.blockCard
  have : (GenusSixExistence.Tripod.Gluing.SheetOps.pair a b).block a = {a, b} := by
    ext i
    rw [SheetPartition.mem_block_iff, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.Rel]
    have h := (pair_rel_left_iff hab i)
    unfold SheetPartition.Rel at h
    rw [eq_comm, h]
  rw [this, Finset.card_pair hab]

theorem sourceEdgeIndex_ebSE (j : Fin k) : (regrowDatum β).sourceEdgeIndex (ebSE β j) = 2 := by
  unfold ebSE bridgeSE
  rw [GluingDatum.sourceEdgeIndex_sourceEdge, ep_bridgeE]
  exact blockCard_pair_left (β.a_ne j)

theorem sourceEdgeIndex_leafSE (j : Fin k) (i : Fin d) :
    (regrowDatum β).sourceEdgeIndex (leafSE β j i) = 1 := by
  unfold leafSE
  rw [GluingDatum.sourceEdgeIndex_sourceEdge, ep_leafE]
  classical
  unfold SheetPartition.blockCard
  rw [Finset.card_eq_one]
  exact ⟨i, by ext i'; simp [SheetPartition.discrete, eq_comm]⟩

/-! ## 3.  The entries -/

variable (hD : D.Connected) (hMark : ∀ j, nonDanglingValency D (β.mark j) ≠ 0)

include hD hMark

open Classical in
/-- An entry of the natural matrix of the regrowth, by rows: summed over the four kinds of
surviving edge. -/
theorem matrix_tagPath (tag : MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k))
    (t : (regrowTarget T β.x).edges) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark tag) t =
      (∑ F : NonDanglingEdge D,
          if Sum.inl (markedRow (marks β) F) = tag ∧ oldE β.x F.1.1.1 = t
            then (1 : ℚ) / D.sourceEdgeIndex F.1 else 0) +
        (∑ j, if Sum.inr (Sum.inl j) = tag ∧ bridgeE β.x j = t then (1 : ℚ) / 2 else 0) +
        (∑ j, if Sum.inr (Sum.inr j) = tag ∧ leafE β.x j = t then (1 : ℚ) else 0) +
        (∑ j, if Sum.inr (Sum.inr j) = tag ∧ leafE β.x j = t then (1 : ℚ) else 0) := by
  rw [matrix_eq_sum, sum_nonDanglingEdge β hD hMark]
  simp only [stablePath_eq_tagPath_iff, rowTag_oldND, rowTag_ebND, rowTag_e₁ND, rowTag_e₂ND]
  congr 1
  congr 1
  congr 1
  · refine Fintype.sum_congr _ _ fun F ↦ ?_
    simp only [oldND, oldSE_target, sourceEdgeIndex_oldSE]
  · refine Fintype.sum_congr _ _ fun j ↦ ?_
    simp only [ebND, ebSE, bridgeSE_target]
    rw [← ebSE, sourceEdgeIndex_ebSE]
    norm_num
  · refine Fintype.sum_congr _ _ fun j ↦ ?_
    simp only [e₁ND, e₁SE, leafSE_target, sourceEdgeIndex_leafSE]
    norm_num
  · refine Fintype.sum_congr _ _ fun j ↦ ?_
    simp only [e₂ND, e₂SE, leafSE_target, sourceEdgeIndex_leafSE]
    norm_num

theorem matrix_inl_oldE (P : MarkedStablePath D (marks β)) (t : T.edges) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inl P)) (oldE β.x t) =
      markedEntry β P t := by
  classical
  rw [matrix_tagPath]
  simp [markedEntry]

theorem matrix_inl_bridgeE (P : MarkedStablePath D (marks β)) (j : Fin k) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inl P)) (bridgeE β.x j) =
      0 := by
  classical
  rw [matrix_tagPath]
  simp

theorem matrix_inl_leafE (P : MarkedStablePath D (marks β)) (j : Fin k) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inl P)) (leafE β.x j) =
      0 := by
  classical
  rw [matrix_tagPath]
  simp

theorem matrix_bridge_oldE (j : Fin k) (t : T.edges) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inr (.inl j)))
      (oldE β.x t) = 0 := by
  classical
  rw [matrix_tagPath]
  simp

theorem matrix_bridge_bridgeE (j j' : Fin k) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inr (.inl j)))
      (bridgeE β.x j') = if j = j' then 1 / 2 else 0 := by
  classical
  rw [matrix_tagPath]
  simp only [reduceCtorEq, false_and, ite_false, Finset.sum_const_zero, zero_add, add_zero,
    Sum.inr.injEq, Sum.inl.injEq, bridgeE_inj, leafE_ne_bridgeE, and_false]
  rw [Finset.sum_eq_single j]
  · by_cases h : j = j' <;> simp [h]
  · intro i _ hi; simp [hi]
  · simp

theorem matrix_bridge_leafE (j j' : Fin k) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inr (.inl j)))
      (leafE β.x j') = 0 := by
  classical
  rw [matrix_tagPath]
  simp

theorem matrix_loop_oldE (j : Fin k) (t : T.edges) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inr (.inr j)))
      (oldE β.x t) = 0 := by
  classical
  rw [matrix_tagPath]
  simp

theorem matrix_loop_bridgeE (j j' : Fin k) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inr (.inr j)))
      (bridgeE β.x j') = 0 := by
  classical
  rw [matrix_tagPath]
  simp

theorem matrix_loop_leafE (j j' : Fin k) :
    StableSourceMatrix.matrix (regrowDatum β) (tagPath β hD hMark (.inr (.inr j)))
      (leafE β.x j') = if j = j' then 2 else 0 := by
  classical
  rw [matrix_tagPath]
  simp only [reduceCtorEq, false_and, ite_false, Finset.sum_const_zero, zero_add,
    Sum.inr.injEq, leafE_inj, bridgeE_ne_leafE, and_false]
  have hsum : (∑ x : Fin k, if x = j ∧ x = j' then (1 : ℚ) else 0) = if j = j' then 1 else 0 := by
    rw [Finset.sum_eq_single j]
    · by_cases h : j = j' <;> simp [h]
    · intro i _ hi; simp [hi]
    · simp
  rw [hsum]
  split_ifs <;> norm_num

end

end DraismaVargas.Count.MarkedCount.Regrow
