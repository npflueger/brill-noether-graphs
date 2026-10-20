module

public import DraismaVargasMarkedCount.MarkedCountGeneral.Caterpillar
public import DraismaVargasMarkedCount.MarkedCountGeneral.RigidTail
public import DraismaVargasMarkedCount.MarkedCountGeneral.Ballot
public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame
public import DraismaVargasCount.SegmentWalls

@[expose] public section

/-!
# The two-point ramified count, module 5: the rigidity of a caterpillar tail

Let `φ` be a full-dimensional frame over a cubic core `H` (an unmarked `Frame`: change-minimal,
the object of the integer count) and `C` a caterpillar tail of genus `c + 1` in `H` at `w`
(`CaterpillarAt`). Then the tail is **private and rigid**:

1. (`exists_loneRow_bridge`, `index_bridgeEdge`) every lollipop bridge `b_i` is a single surviving
   edge of index `2`, the only survivor over its target edge, as in the lollipop lemma of the
   ramification-one count (module `MarkedCount.RestrictLollipop`); so is the
   terminal path edge `h_{c+1}` (the bridge of the terminal lollipop, `slope_last`, `s_a = 2`);
2. (`exists_loneRow_path`) every path edge `h_{i+1}` is a single surviving edge `e_{i+1}` of index
   `s_{i+1}`, the only survivor over its target edge `t_{i+1}`;
3. (`exists_slopeSeq`) the slopes form a slope sequence: `s_a = 2`, `s_i ≥ 1`, `s_{i+1} - s_i = ±1`;
4. (`spine_local`) the image `x_i` of `B_i` is trivalent, `B_i` is the only surviving vertex over
   it, `r(B_i) = 0` and `m(B_i) = max(s_i, s_{i+1})`;
5. (`tail_block`) the tail rows of `A_φ` are supported on private columns, one each, with the
   diagonal entries `1/s_i`, `1/2` on the bridges and `2` on the loops.

The step of the downward induction that is new compared with the ramification-one count is the
trivalent case of (r0-nd2), excluded by **the three-column relation**
`col(t') - col(t'') = col(t_i)` (`three_column_false`, stated for any full-dimensional
presentation).

Everything here is used only inside the restriction (module `Restriction`); the headline
reaches these facts through `restrictTailed` and its property lemmas.

## Structure

All eight statements rest on the standard axioms. The work is in the helper modules
`RigidLoop` (the ramification-one lollipop package at any core loop), `RigidStep` (the step of the
downward induction at a spine vertex, generic), `RigidSpine` (the caterpillar's incidences in a
cubic core, and the downward induction `TailAt.lonePath`) and `RigidTail` (the tail columns). The
four cases (r2-nd2), (r1-nd2), (r0-nd2) of the step are all excluded by one generic lemma of the
ramification-one count, `RestrictBridge.nonDanglingValency_ne_two_of_unique` (an end of the only
survivor over a target edge is never interior to a stable row); its trivalent case is the
three-column relation, which is how `three_column_false` is proved.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  The three-column relation -/

section ThreeColumn

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The three-column relation** (the step of the downward induction, case (r0-nd2) with
`y` trivalent). Let `y` be a trivalent target vertex with edges `t, t', t''`; let `E` be the only
survivor over `t`, ending at a vertex `C` over `y` of surviving valency two whose other survivor
`E'` lies over `t'` with the same index; and let every other surviving vertex over `y` have
surviving valency two, with one survivor over `t'` and one over `t''` of equal index. Then
`col(t') - col(t'') = col(t)` in the length matrix, so it is singular: impossible.

*Why.* A survivor over `t'` or `t''` has exactly one end over `y`, a surviving vertex. At a vertex
`X ≠ C` the two survivors lie in one row (they are consecutive) with equal entries, so they cancel
in `col(t') - col(t'')`; at `C` only `E'` remains, in the row of `E` (consecutive at `C`), with
entry `1/s`, which is `col(t)` (`E` alone over `t`). Then `det_eq_zero_of_columns`
(module `MarkedCount.RestrictBridge`), with `LeafFibre.matrix_eq_sum_fibre`. -/
theorem three_column_false (fd : FullDimensionalSourcePresentation data coordinate)
    {y : target.V} {t t' t'' : target.edges}
    (hy : (GluingDatum.incidentEdges y).card = 3) (ht : t ∈ GluingDatum.incidentEdges y)
    (ht' : t' ∈ GluingDatum.incidentEdges y) (ht'' : t'' ∈ GluingDatum.incidentEdges y)
    (htt' : t ≠ t') (htt'' : t ≠ t'') (ht't'' : t' ≠ t'')
    {E : data.SourceEdge} (hE : ¬ IsDangling data E) (hEt : E.1.1 = t)
    (hUnique : ∀ F, ¬ IsDangling data F → F.1.1 = t → F = E)
    {Cv : data.SourceVertex} (hCy : Cv.1.1 = y) (hEC : Incident data E Cv)
    (hCval : nonDanglingValency data Cv = 2)
    {E' : data.SourceEdge} (hE' : ¬ IsDangling data E') (hE't : E'.1.1 = t')
    (hE'C : Incident data E' Cv) (hIndex : data.sourceEdgeIndex E' = data.sourceEdgeIndex E)
    (hOther : ∀ X : data.SourceVertex, X.1.1 = y → X ≠ Cv → nonDanglingValency data X ≠ 0 →
      nonDanglingValency data X = 2 ∧ ∃ F' F'' : data.SourceEdge,
        ¬ IsDangling data F' ∧ ¬ IsDangling data F'' ∧ F'.1.1 = t' ∧ F''.1.1 = t'' ∧
        Incident data F' X ∧ Incident data F'' X ∧
        data.sourceEdgeIndex F' = data.sourceEdgeIndex F'') :
    False := by
  -- Part I's column dependence (`nonDanglingValency_ne_two_of_unique`) excludes any
  -- surviving valency-two end of a lone survivor; its trivalent case is exactly this relation,
  -- so the description of the other blocks over `y` is not needed.
  have _ := And.intro hy (And.intro ht (And.intro ht' (And.intro ht'' (And.intro htt'
    (And.intro htt'' (And.intro ht't'' (And.intro hCy (And.intro hE' (And.intro hE't
      (And.intro hE'C (And.intro hIndex hOther)))))))))))
  exact MarkedCount.Lollipops.nonDanglingValency_ne_two_of_unique fd hE (fun F hF hFt ↦
    hUnique F hF (hFt.trans hEt)) hEC hCval

end ThreeColumn

/-! ## 2.  The tail of a frame -/

variable {N P degree : ℕ} {H : Core N P} {w : Fin N} {c : ℕ}

/-- **A lone row**: `E` is the only survivor of the stable path `row`, and the only survivor over
its target edge. -/
def IsLoneRow {target : CFGraph.{0}} (data : GluingDatum target degree) (E : NonDanglingEdge data)
    (row : StablePath data) : Prop :=
  (∀ F : NonDanglingEdge data, F.stablePath = row ↔ F = E) ∧
    ∀ F : data.SourceEdge, ¬ IsDangling data F → F.1.1 = E.1.1.1 → F = E.1

/-- The stable path of the tail slot `s`. -/
def tailRow (C : CaterpillarAt H w c) (f : Frame H degree) (s : CatSlot c) : StablePath f.data :=
  f.ident.row.symm (C.slot s)

/-- The source vertex `B_{i+1}` over the spine vertex. -/
noncomputable def spineSource (C : CaterpillarAt H w c) (f : Frame H degree) (i : Fin c) :
    f.data.SourceVertex :=
  (f.ident.vertex.symm (C.vertex (CatVertex.spine i))).1

/-- **Rigidity (2), and (1) for `h_{c+1}`**: every path row is a single lone edge. *Proof.*
Downward induction on `i` (base `i = c`: the ramification-one lollipop lemma at the terminal
lollipop, through the public lollipop package and `RestrictBridge.farEnd_eq_markV`'s argument; step:
the far end `C` of `e_i` has surviving valency `≥ 3` (then `C = B_{i-1}`) or `2`, and the four cases
(r2-nd2), (r1-nd2), (r0-nd2) divalent, (r0-nd2) trivalent are excluded by uniqueness over `t_i`, by
`RestrictBridge.nonDanglingValency_ne_two_of_unique`, by the equality of the two columns at a
divalent target vertex of change `0`, and by `three_column_false`). -/
theorem exists_loneRow_path (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree)
    (i : Fin (c + 1)) : ∃ E : NonDanglingEdge f.data, IsLoneRow f.data E (tailRow C f (.inl i)) :=
  ⟨TailAt.pathE C (f.member 0) hH i, TailAt.lone_pathE C (f.member 0) hH i⟩

/-- **Rigidity (1)**: every lollipop bridge row is a single lone edge (the ramification-one
lollipop lemma at each lollipop, `RestrictBridge.farEnd_eq_markV`). -/
theorem exists_loneRow_bridge (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree)
    (i : Fin c) :
    ∃ E : NonDanglingEdge f.data, IsLoneRow f.data E (tailRow C f (.inr (.inl i))) := by
  refine ⟨TailAt.bridgeAt C (f.member 0) i.castSucc, ?_⟩
  have h := TailAt.lone_bridgeAt C (f.member 0) hH i.castSucc
  rwa [CatSlot.bulbBridge_castSucc] at h

/-- The path edge `e_{i+1}`. -/
noncomputable def pathEdge (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree)
    (i : Fin (c + 1)) : NonDanglingEdge f.data :=
  (exists_loneRow_path hH C f i).choose

/-- The slope `s_{i+1}`: the index of `e_{i+1}`. -/
noncomputable def slope (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree)
    (i : Fin (c + 1)) : ℕ :=
  f.data.sourceEdgeIndex (pathEdge hH C f i).1

/-- The chosen path edge is the lone survivor of module `RigidSpine`. -/
theorem pathEdge_eq (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree)
    (i : Fin (c + 1)) : pathEdge hH C f i = TailAt.pathE C (f.member 0) hH i :=
  (TailAt.lone_pathE C (f.member 0) hH i).unique (exists_loneRow_path hH C f i).choose_spec

theorem slope_eq (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree)
    (i : Fin (c + 1)) :
    slope hH C f i = (f.member 0).data.sourceEdgeIndex (TailAt.pathE C (f.member 0) hH i).1 := by
  unfold slope; rw [pathEdge_eq]; rfl

/-- **Rigidity (1)**: the bridges have index `2`. -/
theorem index_bridgeEdge (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree)
    (i : Fin c) :
    f.data.sourceEdgeIndex (exists_loneRow_bridge hH C f i).choose.1 = 2 := by
  have h := TailAt.lone_bridgeAt C (f.member 0) hH i.castSucc
  rw [CatSlot.bulbBridge_castSucc] at h
  rw [h.unique (exists_loneRow_bridge hH C f i).choose_spec]
  exact TailAt.bridgeAt_index C (f.member 0) i.castSucc

/-- **`s_a = 2`**: the terminal path edge is the bridge of the terminal lollipop (the
ramification-one lollipop package at `B_c`, which is trivalent in `H(φ)` by the core
identification). -/
theorem slope_last (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree) :
    slope hH C f (Fin.last c) = 2 := by
  rw [slope_eq, TailAt.pathE_last]
  exact TailAt.bridgeAt_index C (f.member 0) (Fin.last c)

/-- **The index relation at `B_{i+1}`** (`(I_i)`, `r(B) = 0`): `2 + s_{i+2} + s_{i+1} = 2 m(B) + 1`,
with both slopes at most `m(B)`. -/
theorem spine_index (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree) (i : Fin c) :
    2 + slope hH C f i.succ + slope hH C f i.castSucc =
        2 * markIndex f.data (spineSource C f i) + 1 ∧
      slope hH C f i.succ ≤ markIndex f.data (spineSource C f i) ∧
      slope hH C f i.castSucc ≤ markIndex f.data (spineSource C f i) := by
  set M := f.member 0
  have hHyp := TailAt.spineHyp C M hH i
  have hIdx := SpineStep.spineStep_index M.fullDim hHyp
  rw [TailAt.third_spineHyp, TailAt.bridgeAt_index] at hIdx
  rw [slope_eq, slope_eq]
  refine ⟨hIdx, ?_, ?_⟩
  · exact StableLocalProperties.sourceEdgeIndex_le_blockCard M.data _
      ⟨_, TailAt.pathE_incident_spine_upper C M hH i⟩
  · exact StableLocalProperties.sourceEdgeIndex_le_blockCard M.data _
      ⟨_, TailAt.pathE_incident_spine_lower C M hH i⟩

/-- **Rigidity (3)**: the slopes are a slope sequence, with `J` ascents. *Proof.* (I_i)
gives `s_i + s_{i+1} = 2m(B_i) - 1` and harmonicity `m(B_i) ≥ max(s_i, s_{i+1})`, so
`|s_{i+1} - s_i| = 1`; `s_i ≥ 1` is an index; `s_a = 2` is `slope_last`; then `J` is the number of
ascents and the values are `≤ a + 1`. -/
theorem exists_slopeSeq (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree) :
    ∃ (J : ℕ) (s : SlopeSeq (c + 1) J), 2 * J ≤ c + 1 ∧ ∀ i, s.1 i = slope hH C f i := by
  set s := slope hH C f with hs
  have hstep : ∀ i : Fin c, s i.succ = s i.castSucc + 1 ∨ s i.castSucc = s i.succ + 1 := by
    intro i
    have := spine_index hH C f i
    simp only [← hs] at this
    omega
  have hpos : ∀ i, 1 ≤ s i := fun i ↦ StableLocalProperties.sourceEdgeIndex_pos _ _
  have hlast : s (Fin.last c) = 2 := slope_last hH C f
  -- descending to `2` in unit steps: `s_i + i ≤ c + 2`, with the parity of `c`
  have hpar : ∀ i : Fin (c + 1), s i + i.val ≤ c + 2 ∧ (s i + i.val) % 2 = c % 2 := by
    suffices H' : ∀ m (i : Fin (c + 1)), c - i.val = m →
        s i + i.val ≤ c + 2 ∧ (s i + i.val) % 2 = c % 2 from fun i ↦ H' _ i rfl
    intro m
    induction m with
    | zero =>
      intro i hi
      obtain rfl : i = Fin.last c := Fin.ext (by have := i.isLt; simp; omega)
      rw [hlast]; simp; omega
    | succ m ih =>
      intro i hi
      have hlt : i.val < c := by omega
      obtain ⟨i', rfl⟩ : ∃ i' : Fin c, i'.castSucc = i := ⟨⟨i.val, hlt⟩, rfl⟩
      have h' := ih i'.succ (by simp at hi ⊢; omega)
      simp only [Fin.val_succ] at h'
      simp only [Fin.val_castSucc]
      rcases hstep i' with h | h <;> omega
  have h0 := hpar 0
  simp only [Fin.val_zero, add_zero] at h0
  have h01 := hpos 0
  refine ⟨(c + 2 - s 0) / 2, ⟨s, ⟨hpos, fun i hi ↦ ?_, fun i i' hi ↦ ?_, fun i hi ↦ ?_⟩⟩,
    by omega, fun i ↦ rfl⟩
  · obtain rfl : i = Fin.last c := Fin.ext (by simp; omega)
    exact hlast
  · have hlt : i.val < c := by have := i'.isLt; omega
    obtain ⟨j, rfl⟩ : ∃ j : Fin c, j.castSucc = i := ⟨⟨i.val, hlt⟩, rfl⟩
    obtain rfl : i' = j.succ := Fin.ext (by simp at hi ⊢; omega)
    rcases hstep j with h | h
    · exact Or.inl h
    · exact Or.inr h
  · obtain rfl : i = 0 := Fin.ext hi
    omega

/-- **Rigidity (4), the spine vertices**: `x_i` is trivalent, `B_i` is the only surviving
vertex over it, `r(B_i) = 0`, `m(B_i) = max(s_i, s_{i+1})`. -/
theorem spine_local (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree) (i : Fin c) :
    (GluingDatum.incidentEdges (spineSource C f i).1.1).card = 3 ∧
      (∀ X : f.data.SourceVertex, X.1.1 = (spineSource C f i).1.1 →
        nonDanglingValency f.data X ≠ 0 → X = spineSource C f i) ∧
      MarkedCount.markRamification f.data (spineSource C f i) = 0 ∧
      markIndex f.data (spineSource C f i) =
        max (slope hH C f i.castSucc) (slope hH C f i.succ) := by
  set M := f.member 0
  have hHyp := TailAt.spineHyp C M hH i
  have hIdx := spine_index hH C f i
  refine ⟨SpineStep.spineStep_trivalent M.fullDim hHyp,
    fun X hX hNd ↦ SpineStep.spineStep_unique_vertex M.fullDim hHyp hX hNd,
    SpineStep.spineStep_localRamification M.fullDim hHyp, ?_⟩
  omega

/-- **Rigidity (5), the tail block**: every tail row has a single nonzero entry, in a private
column (a target edge of `T_tail` carrying no other row): `1/s_{i+1}` on `h_{i+1}` (`1/2` on
`h_{c+1}`, as `s_a = 2`), `1/2` on a bridge, `2` on a loop. So `A_φ = A_{ψ;u} ⊕ diag(...)` after
reordering, the block decomposition used by the restriction (module `Restriction`). -/
theorem tail_block (hH : H.Cubic) (C : CaterpillarAt H w c) (f : Frame H degree) :
    ∃ col : CatSlot c → f.target.edges, Function.Injective col ∧
      (∀ (s : CatSlot c) (e : f.target.edges), (∀ s', col s' ≠ e) →
        f.matrix (f.fullDim.labelling.row (tailRow C f s)) (f.fullDim.labelling.targetEdge.symm e) =
          0) ∧
      ∀ (s : CatSlot c) (row : Fin P),
        f.matrix row (f.fullDim.labelling.targetEdge.symm (col s)) =
          if row = f.fullDim.labelling.row (tailRow C f s) then
            (match s with
              | .inl i => 1 / (slope hH C f i : ℚ)
              | .inr (.inl _) => 1 / 2
              | .inr (.inr _) => 2)
          else 0 := by
  classical
  set M := f.member 0
  refine ⟨TailAt.tcol C M hH, TailAt.tcol_injective C M hH, fun s e he ↦ ?_, fun s row ↦ ?_⟩
  · -- a tail row meets no column but its own
    unfold Frame.matrix
    rw [LeafFibre.matrix_eq_sum_fibre]
    refine Finset.sum_eq_zero fun F hF ↦ ?_
    obtain ⟨⟨hFS, hFR⟩, hFT⟩ := (LeafFibre.mem_rowFibre _ _ _ _).mp hF
    have hRow : NonDanglingEdge.stablePath (⟨F, hFS⟩ : NonDanglingEdge M.data) =
        TailAt.row C M s := f.fullDim.labelling.row.injective hFR
    exact absurd ((TailAt.over_tcol_of_onRow C M hH s hRow).symm.trans hFT) (he s)
  · unfold Frame.matrix
    rcases s with i | i | i
    · have h := MarkedCount.Lollipops.matrix_column_of_unique M.fullDim
        (TailAt.pathE C M hH i).2 (fun F hF hT ↦ (TailAt.lone_pathE C M hH i).2 F hF hT) row
      have hS := (TailAt.lone_pathE C M hH i).stablePath
      refine h.trans (if_congr ?_ ?_ rfl)
      · exact Iff.of_eq (congrArg (fun r ↦ row = f.fullDim.labelling.row r) hS)
      · show _ = 1 / (slope hH C f i : ℚ)
        rw [slope_eq]
    · have h := MarkedCount.Lollipops.matrix_column_of_unique M.fullDim
        (TailAt.bridgeAt C M i.castSucc).2
        (fun F hF hT ↦ LoopAt.eq_bridgeE M (C.isLoop i.castSucc) hF hT) row
      have hR := TailAt.bridgeAt_stablePath C M hH i.castSucc
      rw [CatSlot.bulbBridge_castSucc] at hR
      refine h.trans (if_congr ?_ ?_ rfl)
      · exact Iff.of_eq (congrArg (fun r ↦ row = f.fullDim.labelling.row r) hR)
      · show _ = (1 / 2 : ℚ)
        rw [TailAt.bridgeAt_index]
        norm_num
    · have h := LeafFibre.matrix_leafEdge_column M.fullDim (LoopAt.vC_isLeaf M (C.isLoop i)) row
      refine h.trans (if_congr ?_ rfl rfl)
      exact Iff.of_eq (congrArg (fun r ↦ row = r)
        (LollipopLeafRow.leafRow_loopLeaf M (C.isLoop i)))

end DraismaVargas.Count.MarkedCountGeneral
