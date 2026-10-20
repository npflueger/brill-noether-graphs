module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailShape

@[expose] public section

/-!
# Restriction over the tails: the restricted target, and the block counts over the tails

For a member `M` over the tailed core:

* the retraction of the target onto the kept vertices (each tail to the image of its mark), and
  the restricted target `T'` is a tree (`rTarget_connected`, `rTarget_genus`) with `p` edges
  (`card_rTarget_edges`);
* the block counts over the tails (the Euler characteristic count behind the number of shed
  sheets): over the tail at mark `j`, the source edges minus the source vertices number
  `c j + 1 + A j`, where `A j = Σᵢ (m(B_{i+1}) - s_{i+1})` is the number of ascents (`blockExcess`);
* hence the genus of the target restriction `D₀ = Restrict.restrictDatum M.data Keep _`
  (`genus_rData`): `g(D₀) = g(M) - Σⱼ (c j + 1 + A j)`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree)

/-! ## 1.  The ends of the tail edges lie in their own tail -/

/-- A vertex of the tail at `j`, or the image of its mark. -/
def InTail (j : Fin k) (v : M.target.V) : Prop := v = xMark T M j ∨ ∃ t, tailVertex T M ⟨j, t⟩ = v

theorem inTail_xSpine (j : Fin k) (i : Fin (c j)) : InTail T M j (xSpine T M j i) :=
  Or.inr ⟨Sum.inl i, rfl⟩

theorem inTail_xBulb (j : Fin k) (i : Fin (c j + 1)) : InTail T M j (xBulb T M j i) :=
  Or.inr ⟨Sum.inr (Sum.inl i), rfl⟩

theorem inTail_xLeaf (j : Fin k) (i : Fin (c j + 1)) : InTail T M j (xLeaf T M j i) :=
  Or.inr ⟨Sum.inr (Sum.inr i), rfl⟩

theorem inTail_lowerX (j : Fin k) (i : Fin (c j + 1)) : InTail T M j (lowerX T M j i) := by
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · rw [lowerX_zero]; exact Or.inl rfl
  · rw [lowerX_succ]; exact inTail_xSpine T M j i'

theorem inTail_upperX (j : Fin k) (i : Fin (c j + 1)) : InTail T M j (upperX T M j i) := by
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i
  · rw [upperX_last]; exact inTail_xBulb T M j _
  · rw [upperX_castSucc]; exact inTail_xSpine T M j i'

include hc in
/-- **The ends of a tail edge are in its tail.** -/
theorem inTail_of_mem_tEdge (j : Fin k) (s : CatSlot (c j)) {v : M.target.V}
    (hv : tEdge T hc M j s ∈ GluingDatum.incidentEdges v) : InTail T M j v := by
  rcases s with i | i | i
  · rcases eq_of_mem_incidentEdges T M (path_mem_lowerX T hc M j i) (path_mem_upperX T hc M j i)
      (lowerX_ne_upperX T hc M j i) hv with rfl | rfl
    · exact inTail_lowerX T M j i
    · exact inTail_upperX T M j i
  · have hS : tEdge T hc M j (Sum.inr (Sum.inl i)) ∈ GluingDatum.incidentEdges (xSpine T M j i) := by
      rw [incidentEdges_xSpine T hc M]; simp
    have hB : tEdge T hc M j (Sum.inr (Sum.inl i)) ∈
        GluingDatum.incidentEdges (xBulb T M j i.castSucc) := by
      rw [incidentEdges_xBulb T hc M, bulbBridge_castSucc]; simp
    rcases eq_of_mem_incidentEdges T M hS hB (xSpine_ne_xBulb T hc M _ _ _ _) hv with rfl | rfl
    · exact inTail_xSpine T M j i
    · exact inTail_xBulb T M j _
  · have hB : tEdge T hc M j (Sum.inr (Sum.inr i)) ∈ GluingDatum.incidentEdges (xBulb T M j i) := by
      rw [incidentEdges_xBulb T hc M]; simp
    have hL : tEdge T hc M j (Sum.inr (Sum.inr i)) ∈ GluingDatum.incidentEdges (xLeaf T M j i) := by
      rw [incidentEdges_xLeaf T hc M]; simp
    rcases eq_of_mem_incidentEdges T M hB hL (xBulb_ne_xLeaf T M _ _ _ _) hv with rfl | rfl
    · exact inTail_xBulb T M j i
    · exact inTail_xLeaf T M j i

/-! ## 2.  The retraction, and the restricted target -/

theorem exists_tailVertex_of_notMem {v : M.target.V} (hv : v ∉ Keep T M) :
    ∃ q, tailVertex T M q = v := by
  rw [mem_Keep] at hv
  push Not at hv
  exact hv

/-- The tail containing a deleted vertex. -/
def tailOf {v : M.target.V} (hv : v ∉ Keep T M) : Fin k :=
  (exists_tailVertex_of_notMem T M hv).choose.1

include hc in
theorem tailOf_tailVertex (j : Fin k) (t : TailV (c j)) :
    tailOf T M (tailVertex_notMem_Keep T M ⟨j, t⟩) = j := by
  have h := (exists_tailVertex_of_notMem T M (tailVertex_notMem_Keep T M ⟨j, t⟩)).choose_spec
  have := tailVertex_injective T hc M h
  unfold tailOf
  rw [this]

/-- **The retraction** of the target onto `T'`: each tail to the image of its mark. -/
def retract (v : M.target.V) : (restrictTarget (Keep T M) (Keep_nonempty T hc M)).V :=
  if h : v ∈ Keep T M then vRestrict v h
  else vRestrict (xMark T M (tailOf T M h)) (xMark_mem_Keep T hc M _)

theorem retract_of_mem {v : M.target.V} (h : v ∈ Keep T M) :
    retract T hc M v = vRestrict v h := by
  simp only [retract, h, ↓reduceDIte]

theorem retract_inTail {j : Fin k} {v : M.target.V} (h : InTail T M j v) :
    retract T hc M v = vRestrict (xMark T M j) (xMark_mem_Keep T hc M j) := by
  rcases h with rfl | ⟨t, rfl⟩
  · exact retract_of_mem T hc M _
  · simp only [retract, tailVertex_notMem_Keep T M ⟨j, t⟩, ↓reduceDIte]
    congr 2
    exact tailOf_tailVertex T hc M j t

theorem retract_edge (e : M.target.edges) (he : ¬ KeptEdge (Keep T M) e) :
    retract T hc M (e : M.target.V × M.target.V).1 = retract T hc M (e : M.target.V × M.target.V).2 := by
  obtain ⟨j, s, rfl⟩ := (not_keptEdge_iff T hc M e).mp he
  rw [retract_inTail T hc M (inTail_of_mem_tEdge T hc M j s
      ((mem_incidentEdges_iff_end T M).mpr (Or.inl rfl))),
    retract_inTail T hc M (inTail_of_mem_tEdge T hc M j s
      ((mem_incidentEdges_iff_end T M).mpr (Or.inr rfl)))]

/-- The restricted target `T'`. -/
abbrev rTarget : CFGraph.{0} := restrictTarget (Keep T M) (Keep_nonempty T hc M)

/-- The target restriction of the datum (the ramification-one `Restrict.restrictDatum`). -/
abbrev rData : GluingDatum (rTarget T hc M) degree :=
  restrictDatum M.data (Keep T M) (Keep_nonempty T hc M)

theorem rTarget_connected : graph_connected (rTarget T hc M) :=
  graph_connected_restrictTarget M.fullDim.targetConnected (retract T hc M)
    (fun _ h ↦ retract_of_mem T hc M h) (retract_edge T hc M)

/-! ### Counts -/

theorem card_tailV : Fintype.card (Σ j, TailV (c j)) = ∑ j, (3 * c j + 2) := by
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

theorem card_catSlot : Fintype.card (Σ j, CatSlot (c j)) = ∑ j, (3 * c j + 2) := by
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

theorem Keep_compl : (Keep T M)ᶜ = Finset.univ.image (tailVertex T M) := by
  rw [Keep, compl_compl]

include hc in
theorem card_Keep_compl : ((Keep T M)ᶜ).card = ∑ j, (3 * c j + 2) := by
  rw [Keep_compl, Finset.card_image_of_injective _ (tailVertex_injective T hc M), Finset.card_univ,
    card_tailV]

theorem notKept_eq :
    (Finset.univ.filter fun e : M.target.edges ↦ ¬ KeptEdge (Keep T M) e) =
      Finset.univ.image (tailEdge T hc M) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [not_keptEdge_iff T hc M]
  constructor
  · rintro ⟨j, s, rfl⟩; exact ⟨⟨j, s⟩, rfl⟩
  · rintro ⟨⟨j, s⟩, rfl⟩; exact ⟨j, s, rfl⟩

include hc in
theorem card_notKept :
    (Finset.univ.filter fun e : M.target.edges ↦ ¬ KeptEdge (Keep T M) e).card =
      ∑ j, (3 * c j + 2) := by
  rw [notKept_eq T hc M, Finset.card_image_of_injective _ (tailEdge_injective T hc M),
    Finset.card_univ, card_catSlot]

theorem card_edges_target : Multiset.card M.target.edges = p + ∑ j, (3 * c j + 2) := by
  rw [← Multiset.card_coe M.target.edges, ← Fintype.card_congr M.fullDim.labelling.targetEdge,
    Fintype.card_fin, T.card_slots]

theorem card_rTarget_edges : Multiset.card (rTarget T hc M).edges = p := by
  rw [card_edges_restrictTarget]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset M.target.edges))
    (fun e ↦ KeptEdge (Keep T M) e)
  rw [card_notKept T hc M, Finset.card_univ, Multiset.card_coe, card_edges_target] at h
  omega

theorem rTarget_genus : genus (rTarget T hc M) = 0 := by
  classical
  have hT := M.fullDim.targetGenus
  unfold genus at hT ⊢
  rw [card_rTarget_edges, card_restrictTarget_V]
  rw [card_edges_target T M] at hT
  have hV := Finset.card_add_card_compl (Keep T M)
  rw [card_Keep_compl T hc M] at hV
  generalize ∑ j, (3 * c j + 2) = S at hT hV
  push_cast at hT ⊢
  omega

/-! ## 3.  Block counts -/

/-- One block of size `m`, the others singletons: `#blocks + m = d + 1`. -/
theorem card_blocks_of_single {d : ℕ} (P : SheetPartition d) (hd : 0 < d) (b₀ : P.Blocks)
    (h1 : ∀ b : P.Blocks, b ≠ b₀ → P.blockCard b.1 = 1) :
    Fintype.card P.Blocks + P.blockCard b₀.1 = d + 1 := by
  classical
  have hSum := SheetPartition.sum_blockCard_blocks_eq_degree P hd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀),
    Finset.sum_congr rfl fun b hb ↦ by rw [h1 b (Finset.mem_erase.mp hb).1]] at hSum
  simp only [Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ b₀), Finset.card_univ] at hSum
  have hPos : 0 < Fintype.card P.Blocks := Fintype.card_pos_iff.mpr ⟨b₀⟩
  push_cast [Nat.cast_sub hPos] at hSum
  omega

/-- The block size of the spine vertex `B_{i+1}`. -/
def mSpine (j : Fin k) (i : Fin (c j)) : ℕ :=
  (M.data.vertexPartition (TailAt.spineV (cat T j) M i).1.1).blockCard
    (TailAt.spineV (cat T j) M i).1.2

/-- The slope `s_{i+1}` of the tail at `j`: the index of its lone path edge. -/
def sPath (j : Fin k) (i : Fin (c j + 1)) : ℕ :=
  M.data.sourceEdgeIndex (TailAt.pathE (cat T j) M (T.cubic hc) i).1

include hc in
theorem card_blocks_xSpine (j : Fin k) (i : Fin (c j)) :
    Fintype.card (M.data.vertexPartition (xSpine T M j i)).Blocks + mSpine T M j i =
      degree + 1 := by
  set B := TailAt.spineV (cat T j) M i
  refine card_blocks_of_single _ M.data.degree_pos ⟨B.1.2, B.2⟩ fun b hb ↦ ?_
  refine (PendantFibre.degree_one_of_nonDanglingValency_zero M.fullDim
    ⟨(xSpine T M j i, b.1), b.2⟩ ?_).1
  by_contra hNd
  have := eq_spineV_of_over T hc M (X := ⟨(xSpine T M j i, b.1), b.2⟩) rfl hNd
  apply hb
  exact Subtype.ext (congrArg (fun X : M.data.SourceVertex ↦ X.1.2) this)

theorem card_blocks_path (j : Fin k) (i : Fin (c j + 1)) :
    Fintype.card (M.data.edgePartition (tEdge T hc M j (Sum.inl i))).Blocks + sPath T hc M j i =
      degree + 1 := by
  set E := (TailAt.pathE (cat T j) M (T.cubic hc) i).1
  refine card_blocks_of_single _ M.data.degree_pos ⟨E.1.2, E.2⟩ fun b hb ↦ ?_
  set F : M.data.SourceEdge := ⟨(tEdge T hc M j (Sum.inl i), b.1), b.2⟩
  have hD : IsDangling M.data F := by
    by_contra hS
    apply hb
    have := TailAt.eq_pathE_of_over (cat T j) M (T.cubic hc) i hS rfl
    exact Subtype.ext (congrArg (fun G : M.data.SourceEdge ↦ G.1.2) this)
  exact M.fullDim.danglingEdgeNoGlue F hD

theorem card_blocks_bridge (j : Fin k) (i : Fin (c j)) :
    Fintype.card (M.data.edgePartition (tEdge T hc M j (Sum.inr (Sum.inl i)))).Blocks + 1 =
      degree :=
  LoopAt.card_blocks_tb M ((cat T j).isLoop i.castSucc)

theorem card_blocks_loop (j : Fin k) (i : Fin (c j + 1)) :
    Fintype.card (M.data.edgePartition (tEdge T hc M j (Sum.inr (Sum.inr i)))).Blocks = degree :=
  LoopAt.card_blocks_tl M ((cat T j).isLoop i)

theorem card_blocks_xBulb (j : Fin k) (i : Fin (c j + 1)) :
    Fintype.card (M.data.vertexPartition (xBulb T M j i)).Blocks + 1 = degree :=
  LoopAt.card_blocks_uP M ((cat T j).isLoop i)

theorem card_blocks_xLeaf (j : Fin k) (i : Fin (c j + 1)) :
    Fintype.card (M.data.vertexPartition (xLeaf T M j i)).Blocks + 1 = degree :=
  LoopAt.card_blocks_vC M ((cat T j).isLoop i)

/-- **The block excess of a tail**, `Σᵢ (m(B_{i+1}) - s_{i+1})`: the number of ascents. -/
def blockExcess (j : Fin k) : ℤ := ∑ i : Fin (c j), ((mSpine T M j i : ℤ) - sPath T hc M j i.castSucc)

theorem sPath_last (j : Fin k) : sPath T hc M j (Fin.last (c j)) = 2 := by
  unfold sPath
  rw [TailAt.pathE_last]
  exact TailAt.bridgeAt_index (cat T j) M (Fin.last (c j))

/-- **Edges minus vertices over one tail**: `c j + 1 + (block excess)`. -/
theorem tail_euler (j : Fin k) :
    (∑ s : CatSlot (c j), (Fintype.card (M.data.edgePartition (tEdge T hc M j s)).Blocks : ℤ)) -
        ∑ t : TailV (c j), (Fintype.card (M.data.vertexPartition (tailVertex T M ⟨j, t⟩)).Blocks : ℤ) =
      c j + 1 + blockExcess T hc M j := by
  have hd := M.data.degree_pos
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hP : (∑ i : Fin (c j + 1),
      (Fintype.card (M.data.edgePartition (tEdge T hc M j (Sum.inl i))).Blocks : ℤ)) =
      ∑ i : Fin (c j + 1), ((degree : ℤ) + 1 - sPath T hc M j i) :=
    Finset.sum_congr rfl fun i _ ↦ by have := card_blocks_path T hc M j i; omega
  have hB : (∑ i : Fin (c j),
      (Fintype.card (M.data.edgePartition (tEdge T hc M j (Sum.inr (Sum.inl i)))).Blocks : ℤ)) =
      ∑ _i : Fin (c j), ((degree : ℤ) - 1) :=
    Finset.sum_congr rfl fun i _ ↦ by have := card_blocks_bridge T hc M j i; omega
  have hL : (∑ i : Fin (c j + 1),
      (Fintype.card (M.data.edgePartition (tEdge T hc M j (Sum.inr (Sum.inr i)))).Blocks : ℤ)) =
      ∑ _i : Fin (c j + 1), (degree : ℤ) :=
    Finset.sum_congr rfl fun i _ ↦ by have := card_blocks_loop T hc M j i; omega
  have hS : (∑ i : Fin (c j),
      (Fintype.card (M.data.vertexPartition (tailVertex T M ⟨j, Sum.inl i⟩)).Blocks : ℤ)) =
      ∑ i : Fin (c j), ((degree : ℤ) + 1 - mSpine T M j i) :=
    Finset.sum_congr rfl fun i _ ↦ by
      have := card_blocks_xSpine T hc M j i
      show (Fintype.card (M.data.vertexPartition (xSpine T M j i)).Blocks : ℤ) = _
      omega
  have hU : (∑ i : Fin (c j + 1),
      (Fintype.card (M.data.vertexPartition (tailVertex T M ⟨j, Sum.inr (Sum.inl i)⟩)).Blocks : ℤ)) =
      ∑ _i : Fin (c j + 1), ((degree : ℤ) - 1) :=
    Finset.sum_congr rfl fun i _ ↦ by
      have := card_blocks_xBulb T M j i
      show (Fintype.card (M.data.vertexPartition (xBulb T M j i)).Blocks : ℤ) = _
      omega
  have hV : (∑ i : Fin (c j + 1),
      (Fintype.card (M.data.vertexPartition (tailVertex T M ⟨j, Sum.inr (Sum.inr i)⟩)).Blocks : ℤ)) =
      ∑ _i : Fin (c j + 1), ((degree : ℤ) - 1) :=
    Finset.sum_congr rfl fun i _ ↦ by
      have := card_blocks_xLeaf T M j i
      show (Fintype.card (M.data.vertexPartition (xLeaf T M j i)).Blocks : ℤ) = _
      omega
  rw [hP, hB, hL, hS, hU, hV]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun i ↦ (sPath T hc M j i : ℤ)), sPath_last T hc M j]
  unfold blockExcess
  rw [Finset.sum_sub_distrib]
  push_cast
  ring

/-- **The genus of the target restriction** (the count behind the number of shed sheets). -/
theorem genus_rData :
    genus (rData T hc M).sourceGraph =
      genus M.data.sourceGraph - ∑ j, ((c j + 1 : ℤ) + blockExcess T hc M j) := by
  classical
  rw [genus_sourceGraph, genus_sourceGraph]
  have hV : Fintype.card (rData T hc M).SourceVertex +
      ∑ v ∈ (Keep T M)ᶜ, Fintype.card (M.data.vertexPartition v).Blocks =
      Fintype.card M.data.SourceVertex :=
    card_sourceVertex_restrict_add M.data (Keep T M) (Keep_nonempty T hc M)
  have hE : Fintype.card (rData T hc M).SourceEdge +
      ∑ e ∈ Finset.univ.filter (fun e ↦ ¬ KeptEdge (Keep T M) e),
        Fintype.card (M.data.edgePartition e).Blocks = Fintype.card M.data.SourceEdge :=
    card_sourceEdge_restrict_add M.data (Keep T M) (Keep_nonempty T hc M)
  rw [Keep_compl, Finset.sum_image fun a _ b _ h ↦ tailVertex_injective T hc M h,
    Fintype.sum_sigma] at hV
  rw [notKept_eq T hc M, Finset.sum_image fun a _ b _ h ↦ tailEdge_injective T hc M h,
    Fintype.sum_sigma] at hE
  have hEuler := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ tail_euler T hc M j
  rw [Finset.sum_sub_distrib] at hEuler
  simp only [tailEdge] at hE
  have hE' : (Fintype.card (rData T hc M).SourceEdge : ℤ) +
      ∑ j, ∑ s : CatSlot (c j), (Fintype.card (M.data.edgePartition (tEdge T hc M j s)).Blocks : ℤ) =
      Fintype.card M.data.SourceEdge := by exact_mod_cast hE
  have hV' : (Fintype.card (rData T hc M).SourceVertex : ℤ) +
      ∑ j, ∑ t : TailV (c j),
        (Fintype.card (M.data.vertexPartition (tailVertex T M ⟨j, t⟩)).Blocks : ℤ) =
      Fintype.card M.data.SourceVertex := by exact_mod_cast hV
  linarith

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
