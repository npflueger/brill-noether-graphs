module

public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrRestrictRegrow

@[expose] public section

/-!
# The inverse laws, part 7: the tail chains of a frame

For the decomposition theorem: the blocks `P_i^φ` of a member over the tail form an add/drop
chain (by the rigidity of the tail, every path edge is a single edge whose index is its slope, and
the block at a spine vertex is the larger of the two path blocks there). For a member `M` over the
tailed core, the restriction locates the tails of `M` (module `RestrictTailShape`); here the blocks
of `M.data` over tail `j` are read as a `TailChain` (`chain`):

* `P i`, the block of the lone path edge over `h_{i+1}` (size the slope `s_{i+1}`);
* `Q i`, the block of the lollipop bridge `b_{i+1}` (size two);
* the names: the sheets of the spine vertices, the bulbs and the core vertices of the leaves.

Proved here: `chain_valid` (as in the regrowth, the spine block is `P_i ∪ P_{i+1}`, the larger of
the two, by `TailRestrict.spine_relation`; a sheet entering at an ascent is the shed sheet of the
ascent, so a sheet never re-enters, by `TailRestrict.shedSheet_injective`), and the partitions of
`M.data` over the tail, one block and singletons (`vp_xSpine`, `vp_xBulb`, `vp_xLeaf`,
`ep_path`, `ep_bridge`, `ep_loop`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace FrameChain

noncomputable section

open DraismaVargas.Infrastructure CatSlot
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.MarkedCountGeneral.CatRegrow (TailChain blockPart blockPart_repr)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Generic facts on partitions -/

section Generic

variable {d : ℕ}

/-- **One block and singletons**: a partition whose blocks away from `a` are singletons is the
block partition of the block of `a`, named by its representative. -/
theorem eq_blockPart (P : SheetPartition d) (a : Fin d)
    (h : ∀ q, q ∉ P.block a → P.blockCard q = 1) : P = blockPart (P.block a) (P.repr a) := by
  refine SheetPartition.ext_repr _ _ (funext fun q ↦ ?_)
  rw [blockPart_repr]
  split_ifs with hq
  · exact ((SheetPartition.mem_block_iff _ _ _).mp hq).symm
  · have h1 := P.block_eq_singleton_of_blockCard_eq_one q (h q hq)
    have h2 : P.repr q ∈ P.block q := (SheetPartition.mem_block_iff _ _ _).mpr (P.rel_repr_right q)
    rw [h1] at h2
    exact Finset.mem_singleton.mp h2

/-- **A discrete partition** is the block partition of the empty block. -/
theorem eq_blockPart_empty (P : SheetPartition d) (b : Fin d) (h : ∀ q, P.blockCard q = 1) :
    P = blockPart ∅ b := by
  refine SheetPartition.ext_repr _ _ (funext fun q ↦ ?_)
  rw [blockPart_repr, ite_eq_right (Finset.notMem_empty q)]
  have h1 := P.block_eq_singleton_of_blockCard_eq_one q (h q)
  have h2 : P.repr q ∈ P.block q := (SheetPartition.mem_block_iff _ _ _).mpr (P.rel_repr_right q)
  rw [h1] at h2
  exact Finset.mem_singleton.mp h2

variable {target : CFGraph.{0}} {data : GluingDatum target d}

/-- The block of an incident source edge lies in the block of the vertex. -/
theorem block_sub_of_incident {E : data.SourceEdge} {X : data.SourceVertex} (h : Incident data E X) :
    (data.edgePartition E.1.1).block E.1.2 ⊆ (data.vertexPartition X.1.1).block X.1.2 := by
  obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel data _ _).mp h
  have hRef := StableLocalProperties.refines_of_mem_incidentEdges data hMem
  intro q hq
  rw [SheetPartition.mem_block_iff] at hq ⊢
  exact hRel.trans (hRef.rel hq)

/-- The sheet of a source edge is in its block. -/
theorem self_mem_edgeBlock (E : data.SourceEdge) : E.1.2 ∈ (data.edgePartition E.1.1).block E.1.2 :=
  SheetPartition.self_mem_block _ _

/-- A discrete version of the intermediate value theorem: a sheet outside `P a` and inside
`P b`, `a ≤ b`, enters at some step between. -/
theorem exists_entry {α : Type*} {c : ℕ} (P : Fin (c + 1) → Finset α) {q : α}
    {a b : Fin (c + 1)} (hab : a ≤ b) (ha : q ∉ P a) (hb : q ∈ P b) :
    ∃ i : Fin c, a ≤ i.castSucc ∧ i.succ ≤ b ∧ q ∉ P i.castSucc ∧ q ∈ P i.succ := by
  classical
  have hEx : ∃ m, ∃ hm : m < c + 1, a.val ≤ m ∧ q ∈ P ⟨m, hm⟩ := ⟨b.val, b.2, hab, hb⟩
  obtain ⟨hlt, hle, hmem⟩ := Nat.find_spec hEx
  have hne : Nat.find hEx ≠ a.val := by
    intro h
    apply ha
    have : (⟨Nat.find hEx, hlt⟩ : Fin (c + 1)) = a := Fin.ext h
    rw [← this]; exact hmem
  have hpos : 0 < Nat.find hEx := by omega
  have hmin := Nat.find_min' hEx ⟨b.2, hab, hb⟩
  refine ⟨⟨Nat.find hEx - 1, by omega⟩, ?_, ?_, ?_, ?_⟩
  · rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega
  · rw [Fin.le_def]; simp only [Fin.val_succ]; omega
  · intro h'
    exact Nat.find_min hEx (show Nat.find hEx - 1 < Nat.find hEx by omega) ⟨by omega, by omega, h'⟩
  · have : (⟨Nat.find hEx - 1, by omega⟩ : Fin c).succ = ⟨Nat.find hEx, hlt⟩ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [this]; exact hmem

end Generic

/-! ## 2.  The blocks of one tail -/

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree)

/-- The sheet of the lone path edge over `h_{i+1}`. -/
abbrev pathSheet (j : Fin k) (i : Fin (c j + 1)) : Fin degree :=
  (TailAt.pathE (TailRestrict.cat T j) M (T.cubic hc) i).1.1.2

/-- The sheet of the lollipop bridge `b_{i+1}`. -/
abbrev bridgeSheet (j : Fin k) (i : Fin (c j)) : Fin degree :=
  (TailAt.bridgeAt (TailRestrict.cat T j) M i.castSucc).1.1.2

/-- The sheet of the bulb `A_{i+1}`. -/
abbrev bulbSheet (j : Fin k) (i : Fin (c j + 1)) : Fin degree :=
  (TailAt.vSource M ((TailRestrict.cat T j).vertex (Sum.inr i))).1.2

/-- The sheet of the core vertex over the leaf of the bulb `A_{i+1}`. -/
abbrev tipSheet (j : Fin k) (i : Fin (c j + 1)) : Fin degree :=
  (LeafFibre.coreVertex M.fullDim (LoopAt.vC_isLeaf M ((TailRestrict.cat T j).isLoop i))).1.2

/-- The sheet of the spine vertex `B_{i+1}`. -/
abbrev spineSheet (j : Fin k) (i : Fin (c j)) : Fin degree :=
  (TailAt.spineV (TailRestrict.cat T j) M i).1.2

/-- **`P_{i+1}`**: the block of the lone path edge. -/
def P (j : Fin k) (i : Fin (c j + 1)) : Finset (Fin degree) :=
  (M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inl i))).block (pathSheet T hc M j i)

/-- **`Q_{i+1}`**: the block of the lollipop bridge. -/
def Q (j : Fin k) (i : Fin (c j)) : Finset (Fin degree) :=
  (M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inr (Sum.inl i)))).block
    (bridgeSheet T M j i)

/-- The names of the blocks at the tail vertices. -/
def vA (j : Fin k) : CatRegrow.TailV (c j) → Fin degree
  | Sum.inl (Sum.inl i) => spineSheet T M j i
  | Sum.inl (Sum.inr i) => bulbSheet T M j i
  | Sum.inr i => tipSheet T M j i

/-- The names of the blocks over the tail slots. -/
def eA (j : Fin k) : CatSlot (c j) → Fin degree
  | Sum.inl i => pathSheet T hc M j i
  | Sum.inr (Sum.inl i) => bridgeSheet T M j i
  | Sum.inr (Sum.inr i) => bulbSheet T M j i

/-- **The tail chain of `M` at mark `j`.** -/
def chain (j : Fin k) : TailChain degree (c j) where
  P := P T hc M j
  Q := Q T hc M j
  vA := vA T M j
  eA := eA T hc M j

theorem card_P (j : Fin k) (i : Fin (c j + 1)) :
    (P T hc M j i).card = TailRestrict.sPath T hc M j i := rfl

theorem card_Q (j : Fin k) (i : Fin (c j)) : (Q T hc M j i).card = 2 :=
  TailAt.bridgeAt_index (TailRestrict.cat T j) M i.castSucc

theorem P_castSucc_sub (j : Fin k) (i : Fin (c j)) :
    P T hc M j i.castSucc ⊆ TailRestrict.sBlock T M j i :=
  TailRestrict.pBlock_subset_sBlock T hc M j i

theorem P_succ_sub (j : Fin k) (i : Fin (c j)) :
    P T hc M j i.succ ⊆ TailRestrict.sBlock T M j i :=
  block_sub_of_incident (TailAt.pathE_incident_spine_upper (TailRestrict.cat T j) M (T.cubic hc) i)

theorem Q_sub (j : Fin k) (i : Fin (c j)) : Q T hc M j i ⊆ TailRestrict.sBlock T M j i := by
  have h := TailAt.bridgeAt_incident_tail (TailRestrict.cat T j) M (T.cubic hc) i.castSucc
  rw [bulbBridge_castSucc, (TailRestrict.cat T j).tail_bridge] at h
  exact block_sub_of_incident h

/-- **The step at a spine vertex**: the spine block is the larger of the two path blocks, which
contains the smaller, one size apart. -/
theorem spine_step (j : Fin k) (i : Fin (c j)) :
    (P T hc M j i.succ = TailRestrict.sBlock T M j i ∧ P T hc M j i.castSucc ⊆ P T hc M j i.succ ∧
        (P T hc M j i.succ).card = (P T hc M j i.castSucc).card + 1) ∨
      (P T hc M j i.castSucc = TailRestrict.sBlock T M j i ∧
        P T hc M j i.succ ⊆ P T hc M j i.castSucc ∧
        (P T hc M j i.castSucc).card = (P T hc M j i.succ).card + 1) := by
  have hR := TailRestrict.spine_relation T hc M j i
  have hS := TailRestrict.card_sBlock T M j i
  rw [← card_P, ← card_P] at hR
  rcases Nat.lt_or_ge (P T hc M j i.succ).card (TailRestrict.mSpine T M j i) with hlt | hge
  · right
    have hEq : P T hc M j i.castSucc = TailRestrict.sBlock T M j i :=
      Finset.eq_of_subset_of_card_le (P_castSucc_sub T hc M j i) (by omega)
    exact ⟨hEq, hEq ▸ P_succ_sub T hc M j i, by omega⟩
  · left
    have hEq : P T hc M j i.succ = TailRestrict.sBlock T M j i :=
      Finset.eq_of_subset_of_card_le (P_succ_sub T hc M j i) (by omega)
    exact ⟨hEq, hEq ▸ P_castSucc_sub T hc M j i, by omega⟩

theorem sBlock_eq_S (j : Fin k) (i : Fin (c j)) :
    TailRestrict.sBlock T M j i = (chain T hc M j).S i := by
  change _ = P T hc M j i.castSucc ∪ P T hc M j i.succ
  rcases spine_step T hc M j i with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · rw [Finset.union_eq_right.mpr h2, h1]
  · rw [Finset.union_eq_left.mpr h2, h1]

theorem P_succ_eq_of_isAscent {j : Fin k} {i : Fin (c j)} (h : TailRestrict.IsAscent T hc M j i) :
    P T hc M j i.succ = TailRestrict.sBlock T M j i := by
  have hA : TailRestrict.mSpine T M j i = (P T hc M j i.castSucc).card + 1 := h
  rcases spine_step T hc M j i with ⟨h1, -, -⟩ | ⟨h1, -, -⟩
  · exact h1
  · have := TailRestrict.card_sBlock T M j i
    rw [← h1] at this
    omega

/-- The bridge into bulb `i`: the lollipop bridge, or the last path edge. -/
theorem R_eq_bridgeAt (j : Fin k) (i : Fin (c j + 1)) :
    (chain T hc M j).R i =
      (M.data.edgePartition (TailAt.bridgeAt (TailRestrict.cat T j) M i).1.1.1).block
        (TailAt.bridgeAt (TailRestrict.cat T j) M i).1.1.2 := by
  induction i using Fin.lastCases with
  | last =>
    rw [TailChain.R_last]
    change P T hc M j (Fin.last (c j)) = _
    unfold P
    rw [← TailAt.pathE_last (TailRestrict.cat T j) M (T.cubic hc)]
    rfl
  | cast i => rw [TailChain.R_castSucc]; rfl

/-- **The block into bulb `i` is the block of the bulb.** -/
theorem R_eq_bulb (j : Fin k) (i : Fin (c j + 1)) :
    (chain T hc M j).R i =
      (M.data.vertexPartition (TailRestrict.xBulb T M j i)).block (bulbSheet T M j i) := by
  rw [R_eq_bridgeAt]
  have hℓ := (TailRestrict.cat T j).isLoop i
  have h1 := LoopAt.block_tb_eq_block_uP M hℓ
  have hInc := TailAt.bridgeAt_incident_head (TailRestrict.cat T j) M i
  obtain ⟨-, hRel⟩ := (incident_iff_target_mem_and_rel M.data _ _).mp hInc
  refine h1.trans ?_
  change (M.data.vertexPartition (TailRestrict.xBulb T M j i)).block
    (TailAt.bridgeAt (TailRestrict.cat T j) M i).1.1.2 = _
  rw [TailRestrict.xBulb_eq]
  exact (SheetPartition.block_eq_of_rel _ hRel).symm

/-! ## 3.  The partitions over the tail -/

theorem blockCard_vertex_of_ne {v : M.target.V} {X : M.data.SourceVertex} (hX : X.1.1 = v)
    (hNd : ∀ Y : M.data.SourceVertex, Y.1.1 = v → nonDanglingValency M.data Y ≠ 0 → Y = X)
    (q : Fin degree) (hq : q ∉ (M.data.vertexPartition v).block X.1.2) :
    (M.data.vertexPartition v).blockCard q = 1 := by
  subst hX
  set Y := M.data.sourceEndpoint X.1.1 q
  have hY : Y ≠ X := by
    intro h
    apply hq
    rw [SheetPartition.mem_block_iff]
    have h2 : (M.data.vertexPartition X.1.1).repr q = X.1.2 := congrArg (fun Z ↦ Z.1.2) h
    rw [SheetPartition.rel_iff, ← h2, SheetPartition.repr_idem]
  have h0 : nonDanglingValency M.data Y = 0 := by
    by_contra h0
    exact hY (hNd Y rfl h0)
  have h1 := LoopAt.blockCard_eq_one_of_nonDanglingValency_zero M h0
  change (M.data.vertexPartition X.1.1).blockCard ((M.data.vertexPartition X.1.1).repr q) = 1 at h1
  rwa [SheetPartition.blockCard_congr _ ((M.data.vertexPartition X.1.1).rel_repr_left q)] at h1

theorem blockCard_edge_of_ne {e : M.target.edges} {E : M.data.SourceEdge} (hE : E.1.1 = e)
    (hNd : ∀ F : M.data.SourceEdge, F.1.1 = e → ¬ IsDangling M.data F → F = E)
    (q : Fin degree) (hq : q ∉ (M.data.edgePartition e).block E.1.2) :
    (M.data.edgePartition e).blockCard q = 1 := by
  subst hE
  set F := M.data.sourceEdge E.1.1 q
  have hF : F ≠ E := by
    intro h
    apply hq
    rw [SheetPartition.mem_block_iff]
    have h2 : (M.data.edgePartition E.1.1).repr q = E.1.2 := congrArg (fun Z ↦ Z.1.2) h
    rw [SheetPartition.rel_iff, ← h2, SheetPartition.repr_idem]
  have hD : IsDangling M.data F := by
    by_contra hD
    exact hF (hNd F rfl hD)
  have h1 := M.fullDim.danglingEdgeNoGlue F hD
  change (M.data.edgePartition E.1.1).blockCard ((M.data.edgePartition E.1.1).repr q) = 1 at h1
  rwa [SheetPartition.blockCard_congr _ ((M.data.edgePartition E.1.1).rel_repr_left q)] at h1

/-- **The partition at a spine image**: the spine block and singletons. -/
theorem vp_xSpine (j : Fin k) (i : Fin (c j)) :
    M.data.vertexPartition (TailRestrict.xSpine T M j i) =
      blockPart ((chain T hc M j).S i) (spineSheet T M j i) := by
  rw [← sBlock_eq_S]
  have h := eq_blockPart (M.data.vertexPartition (TailRestrict.xSpine T M j i)) (spineSheet T M j i)
    (blockCard_vertex_of_ne T M (X := TailAt.spineV (TailRestrict.cat T j) M i) rfl
      fun Y hY h0 ↦ TailRestrict.eq_spineV_of_over T hc M hY h0)
  have hr : (M.data.vertexPartition (TailRestrict.xSpine T M j i)).repr (spineSheet T M j i) =
      spineSheet T M j i := (TailAt.spineV (TailRestrict.cat T j) M i).2
  rw [hr] at h
  exact h

/-- **The partition at a bulb image**: the bridge block and singletons. -/
theorem vp_xBulb (j : Fin k) (i : Fin (c j + 1)) :
    M.data.vertexPartition (TailRestrict.xBulb T M j i) =
      blockPart ((chain T hc M j).R i) (bulbSheet T M j i) := by
  rw [R_eq_bulb]
  have hX := (TailRestrict.xBulb_eq T M j i).symm
  have h := eq_blockPart (M.data.vertexPartition (TailRestrict.xBulb T M j i)) (bulbSheet T M j i)
    (blockCard_vertex_of_ne T M hX fun Y hY h0 ↦ TailRestrict.eq_bulbV_of_over T M hY h0)
  have hr : (M.data.vertexPartition (TailRestrict.xBulb T M j i)).repr (bulbSheet T M j i) =
      bulbSheet T M j i := by
    rw [TailRestrict.xBulb_eq]
    exact (TailAt.vSource M ((TailRestrict.cat T j).vertex (Sum.inr i))).2
  rw [hr] at h
  exact h

theorem card_R (j : Fin k) (i : Fin (c j + 1)) : ((chain T hc M j).R i).card = 2 := by
  rw [R_eq_bridgeAt]
  exact TailAt.bridgeAt_index (TailRestrict.cat T j) M i

/-- **The block at a leaf is the block of its bulb.** -/
theorem block_tip (j : Fin k) (i : Fin (c j + 1)) :
    (M.data.vertexPartition (TailRestrict.xLeaf T M j i)).block (tipSheet T M j i) =
      (chain T hc M j).R i := by
  have hℓ := (TailRestrict.cat T j).isLoop i
  have hLeaf := LoopAt.vC_isLeaf M hℓ
  have hRef := LoopAt.refines_vC_uP M hℓ
  have hCard : ((M.data.vertexPartition (TailRestrict.xLeaf T M j i)).block
      (tipSheet T M j i)).card = 2 := LeafFibre.blockCard_coreBlock M.fullDim hLeaf
  have hSub : (M.data.vertexPartition (TailRestrict.xLeaf T M j i)).block (tipSheet T M j i) ⊆
      (M.data.vertexPartition (TailRestrict.xBulb T M j i)).block (tipSheet T M j i) := by
    intro q hq
    rw [SheetPartition.mem_block_iff] at hq ⊢
    exact hRef.rel hq
  have hR := vp_xBulb T hc M j i
  have hAnch : CatRegrow.Anchored ((chain T hc M j).R i) (bulbSheet T M j i) := by
    right; rw [R_eq_bulb]; exact SheetPartition.self_mem_block _ _
  by_cases ht : tipSheet T M j i ∈ (chain T hc M j).R i
  · rw [hR, CatRegrow.blockPart_block_of_mem hAnch ht] at hSub
    exact Finset.eq_of_subset_of_card_le hSub (by rw [hCard, card_R])
  · rw [hR, CatRegrow.blockPart_block_of_not_mem hAnch ht] at hSub
    have := Finset.card_le_card hSub
    rw [hCard, Finset.card_singleton] at this
    omega

/-- **The partition at a leaf image**: the bridge block and singletons. -/
theorem vp_xLeaf (j : Fin k) (i : Fin (c j + 1)) :
    M.data.vertexPartition (TailRestrict.xLeaf T M j i) =
      blockPart ((chain T hc M j).R i) (tipSheet T M j i) := by
  have hℓ := (TailRestrict.cat T j).isLoop i
  have hLeaf := LoopAt.vC_isLeaf M hℓ
  rw [← block_tip]
  set Pv := M.data.vertexPartition (TailRestrict.xLeaf T M j i)
  have h := eq_blockPart Pv (tipSheet T M j i) fun q hq ↦ by
    have hNe : (⟨Pv.repr q, Pv.repr_idem q⟩ : Pv.Blocks) ≠ LeafFibre.coreBlock M.fullDim hLeaf := by
      intro hb
      apply hq
      have h1 : Pv.repr q = tipSheet T M j i := congrArg Subtype.val hb
      have h2 : Pv.repr (tipSheet T M j i) = tipSheet T M j i :=
        (LeafFibre.coreVertex M.fullDim hLeaf).2
      rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff, h2, h1]
    have h1 := (LeafFibre.other_block_data M.fullDim hLeaf hNe).2.1
    change Pv.blockCard (Pv.repr q) = 1 at h1
    rwa [SheetPartition.blockCard_congr _ (Pv.rel_repr_left q)] at h1
  rw [show Pv.repr (tipSheet T M j i) = tipSheet T M j i from
    (LeafFibre.coreVertex M.fullDim hLeaf).2] at h
  exact h

/-- **The partition over a path edge**: its block and singletons. -/
theorem ep_path (j : Fin k) (i : Fin (c j + 1)) :
    M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inl i)) =
      blockPart (P T hc M j i) (pathSheet T hc M j i) := by
  have h := eq_blockPart (M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inl i)))
    (pathSheet T hc M j i)
    (blockCard_edge_of_ne T M (E := (TailAt.pathE (TailRestrict.cat T j) M (T.cubic hc) i).1) rfl
      fun F hF hD ↦ TailAt.eq_pathE_of_over (TailRestrict.cat T j) M (T.cubic hc) i hD hF)
  have hr : (M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inl i))).repr
      (pathSheet T hc M j i) = pathSheet T hc M j i :=
    (TailAt.pathE (TailRestrict.cat T j) M (T.cubic hc) i).1.2
  rw [hr] at h
  exact h

/-- **The partition over a bridge**: its block and singletons. -/
theorem ep_bridge (j : Fin k) (i : Fin (c j)) :
    M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inr (Sum.inl i))) =
      blockPart (Q T hc M j i) (bridgeSheet T M j i) := by
  have h := eq_blockPart (M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inr (Sum.inl i))))
    (bridgeSheet T M j i)
    (blockCard_edge_of_ne T M (E := (TailAt.bridgeAt (TailRestrict.cat T j) M i.castSucc).1) rfl
      fun F hF hD ↦ TailAt.eq_bridgeAt_of_over (TailRestrict.cat T j) M (T.cubic hc) i hD hF)
  have hr : (M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inr (Sum.inl i)))).repr
      (bridgeSheet T M j i) = bridgeSheet T M j i :=
    (TailAt.bridgeAt (TailRestrict.cat T j) M i.castSucc).1.2
  rw [hr] at h
  exact h

/-- **The partition over a leaf edge** is discrete. -/
theorem ep_loop (j : Fin k) (i : Fin (c j + 1)) :
    M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inr (Sum.inr i))) =
      blockPart ∅ (bulbSheet T M j i) := by
  have hℓ := (TailRestrict.cat T j).isLoop i
  have hLeaf := LoopAt.vC_isLeaf M hℓ
  refine eq_blockPart_empty _ _ fun q ↦ ?_
  set Pe := M.data.edgePartition (TailRestrict.tEdge T hc M j (Sum.inr (Sum.inr i)))
  have h1 := LeafFibre.sourceEdgeIndex_eq_one_above_leaf M.fullDim hLeaf
    (edge := ⟨(TailRestrict.tEdge T hc M j (Sum.inr (Sum.inr i)), Pe.repr q), Pe.repr_idem q⟩) rfl
  change Pe.blockCard (Pe.repr q) = 1 at h1
  rwa [SheetPartition.blockCard_congr _ (Pe.rel_repr_left q)] at h1

/-! ## 4.  Validity -/

/-- The first path block lies in the block of the mark. -/
theorem P_zero_sub (j : Fin k) :
    P T hc M j 0 ⊆ (M.data.vertexPartition (TailRestrict.uSource T M j).1.1).block
      (TailRestrict.uSource T M j).1.2 :=
  block_sub_of_incident (TailRestrict.uSource_incident_pathE T hc M j)

/-- **A sheet of `P_1` is not lone**: it shares the block of the mark, a kept survivor. -/
theorem not_isLone_of_mem_P_zero {j : Fin k} {q : Fin degree} (hq : q ∈ P T hc M j 0) :
    ¬ Sheets.IsLone (TailRestrict.rData T hc M) q := by
  intro hL
  have hRel := (SheetPartition.mem_block_iff _ _ _).mp (P_zero_sub T hc M j hq)
  have hEq : (TailRestrict.uSource T M j).1.2 = q :=
    hL (vRestrict (TailRestrict.uSource T M j).1.1 (TailRestrict.xMark_mem_Keep T hc M j)) _
      ((SheetPartition.rel_iff _ _ _).mpr hRel.symm)
  refine TailRestrict.not_isLone_of_survivor T hc M (TailRestrict.xMark_mem_Keep T hc M j)
    (by rw [TailRestrict.nonDanglingValency_uSource]; omega) ?_
  rw [hEq]; exact hL

/-- **A sheet entering the chain is the shed sheet of an ascent.** -/
theorem shed_of_enters {j : Fin k} {i : Fin (c j)} {q : Fin degree} (h1 : q ∈ P T hc M j i.succ)
    (h2 : q ∉ P T hc M j i.castSucc) :
    ∃ h, q = TailRestrict.shedSheet T hc M j i h :=
  TailRestrict.eq_shed_of_mem T hc M (P_succ_sub T hc M j i h1) h2

/-- **A sheet of the chain outside `P_1` is lone**, shed at an ascent below. -/
theorem shed_of_not_mem_zero {j : Fin k} {i : Fin (c j + 1)} {q : Fin degree}
    (hq : q ∈ P T hc M j i) (h0 : q ∉ P T hc M j 0) :
    ∃ (i' : Fin (c j)) (h : TailRestrict.IsAscent T hc M j i'),
      q = TailRestrict.shedSheet T hc M j i' h := by
  obtain ⟨i', -, -, hn, hm⟩ := exists_entry (P T hc M j) (Fin.zero_le i) h0 hq
  obtain ⟨h, rfl⟩ := shed_of_enters T hc M hm hn
  exact ⟨i', h, rfl⟩

theorem isLone_of_not_mem_zero {j : Fin k} {i : Fin (c j + 1)} {q : Fin degree}
    (hq : q ∈ P T hc M j i) (h0 : q ∉ P T hc M j 0) :
    Sheets.IsLone (TailRestrict.rData T hc M) q := by
  obtain ⟨i', h, rfl⟩ := shed_of_not_mem_zero T hc M hq h0
  exact TailRestrict.isLone_shedSheet T hc M j i' h

/-- **Convexity**: a sheet leaving the chain never returns (it would be shed twice). -/
theorem convex (j : Fin k) (q : Fin degree) (i₁ i₂ i₃ : Fin (c j + 1)) (h12 : i₁ ≤ i₂)
    (h23 : i₂ ≤ i₃) (h1 : q ∈ P T hc M j i₁) (h3 : q ∈ P T hc M j i₃) : q ∈ P T hc M j i₂ := by
  by_contra h2
  obtain ⟨a, ha, -, han, ham⟩ := exists_entry (P T hc M j) h23 h2 h3
  obtain ⟨ha', hqa⟩ := shed_of_enters T hc M ham han
  by_cases h0 : q ∈ P T hc M j 0
  · exact not_isLone_of_mem_P_zero T hc M h0 (hqa ▸ TailRestrict.isLone_shedSheet T hc M j a ha')
  · obtain ⟨b, -, hb, hbn, hbm⟩ := exists_entry (P T hc M j) (Fin.zero_le i₁) h0 h1
    obtain ⟨hb', hqb⟩ := shed_of_enters T hc M hbm hbn
    have hEq := TailRestrict.shedSheet_injective T hc M hb' ha' (hqb.symm.trans hqa)
    have hba : b = a := eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
    subst hba
    rw [Fin.le_def] at ha hb h12
    simp only [Fin.val_castSucc, Fin.val_succ] at ha hb
    omega

theorem vA_mem (j : Fin k) (w : CatRegrow.TailV (c j)) :
    (chain T hc M j).vA w ∈ (chain T hc M j).vB w := by
  rcases w with (i | i) | i
  · change spineSheet T M j i ∈ (chain T hc M j).S i
    rw [← sBlock_eq_S]
    exact SheetPartition.self_mem_block _ _
  · change bulbSheet T M j i ∈ (chain T hc M j).R i
    rw [R_eq_bulb]
    exact SheetPartition.self_mem_block _ _
  · change tipSheet T M j i ∈ (chain T hc M j).R i
    rw [← block_tip]
    exact SheetPartition.self_mem_block _ _

theorem eA_anchored (j : Fin k) (t : CatSlot (c j)) :
    CatRegrow.Anchored ((chain T hc M j).eB t) ((chain T hc M j).eA t) := by
  rcases t with i | i | i
  · exact Or.inr (SheetPartition.self_mem_block _ _)
  · exact Or.inr (SheetPartition.self_mem_block _ _)
  · exact Or.inl rfl

/-- **The tail chains of a frame are valid** (the rigidity of the tail). -/
theorem chain_valid (j : Fin k) : (chain T hc M j).Valid where
  card_P_last := TailRestrict.sPath_last T hc M j
  card_Q := card_Q T hc M j
  P_nonempty _ := ⟨_, SheetPartition.self_mem_block _ _⟩
  step i := (spine_step T hc M j i).imp (fun h ↦ ⟨h.2.1, h.2.2⟩) (fun h ↦ ⟨h.2.1, h.2.2⟩)
  Q_sub i := by rw [← sBlock_eq_S]; exact Q_sub T hc M j i
  vA_mem := vA_mem T hc M j
  eA_anchored := eA_anchored T hc M j
  convex := convex T hc M j

/-! ## 5.  The frame as a branching over its restriction -/

variable (m : ℕ) (hm : m + TailRestrict.nShed T hc M = degree)

theorem P_zero_old {j : Fin k} {q : Fin degree} (hq : q ∈ P T hc M j 0) :
    ∃ a, (TailRestrict.split T hc M m hm).symm (.inl a) = q := by
  rcases Sheets.sheet_cases (TailRestrict.split T hc M m hm) q with h | ⟨n, rfl⟩
  · exact h
  · exact absurd (TailRestrict.isLone_split T hc M m hm n) (not_isLone_of_mem_P_zero T hc M hq)

/-- **The frame, as a caterpillar branching over its restriction**: the sheets split into the
kept and the lone ones, the marks of the restriction, and its own tail chains. -/
def branching : CatRegrow.CatBranching (TailRestrict.dat T hc M m hm)
    (Fin (TailRestrict.nShed T hc M)) degree c where
  e := (TailRestrict.split T hc M m hm).symm
  mark := TailRestrict.markSrc T hc M m hm
  chain := chain T hc M
  valid := chain_valid T hc M
  P0_sub j q hq := by
    obtain ⟨a, rfl⟩ := P_zero_old T hc M m hm hq
    refine ⟨a, rfl, ?_⟩
    rw [Sheets.restrictSheets_vertex_rel_iff]
    have hC := congrArg Subtype.val (TailRestrict.cSV_markSrc T hc M m hm j)
    have h1 : vIncl (TailRestrict.markSrc T hc M m hm j).1.1 = (TailRestrict.uSource T M j).1.1 :=
      congrArg Prod.fst hC
    have h2 : (TailRestrict.split T hc M m hm).symm (.inl (TailRestrict.markSrc T hc M m hm j).1.2) =
        (TailRestrict.uSource T M j).1.2 := congrArg Prod.snd hC
    change (M.data.vertexPartition (vIncl (TailRestrict.markSrc T hc M m hm j).1.1)).Rel _ _
    rw [h1, h2]
    exact (SheetPartition.mem_block_iff _ _ _).mp (P_zero_sub T hc M j hq)
  fresh j i q hq h0 := by
    have hL := isLone_of_not_mem_zero T hc M hq h0
    rw [← TailRestrict.isNew_split_iff T hc M m hm, Sheets.isNew_iff] at hL
    obtain ⟨n, rfl⟩ := hL
    exact ⟨n, rfl⟩
  fresh_disjoint j j' i i' q hq hq' h0 := by
    obtain ⟨a, ha, rfl⟩ := shed_of_not_mem_zero T hc M hq h0
    have h0' : TailRestrict.shedSheet T hc M j a ha ∉ P T hc M j' 0 := fun h ↦
      not_isLone_of_mem_P_zero T hc M h (TailRestrict.isLone_shedSheet T hc M j a ha)
    obtain ⟨b, hb, hbq⟩ := shed_of_not_mem_zero T hc M hq' h0'
    exact (Sigma.mk.inj_iff.mp (TailRestrict.shedSheet_injective T hc M ha hb hbq)).1
  new_used n := by
    obtain ⟨j, i, h, hτ⟩ := TailRestrict.exists_ascent_of_isLone T hc M
      (TailRestrict.isLone_split T hc M m hm n)
    refine ⟨j, i.succ, ?_⟩
    change (TailRestrict.split T hc M m hm).symm (.inr n) ∈ P T hc M j i.succ
    rw [← hτ, P_succ_eq_of_isAscent T hc M h]
    exact TailRestrict.shed_mem_sBlock T hc M j i h

end

end FrameChain

end DraismaVargas.Count.MarkedCountGeneral
