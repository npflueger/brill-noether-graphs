module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowDatum

@[expose] public section

/-!
# Regrowth, part 5: the dangling dictionary

The new sheets of the regrowth are dangling (the splitting of the restriction into a core
component and index-one copies of `T'`, read backwards). Which source edges of
`regrowDatum β` dangle:

* an old edge (of an old sheet over `T`) dangles iff it dangles in `ψ` (`isDangling_psiSE_iff`);
* the block edges over the path and bridge slots, and the two loop edges of every branch, survive
  (`Survives`, by the public witness lemma `Gluing.not_isDangling_of_witness`);
* every other edge dangles: the singleton edges over the tail (a sheet that is a singleton over a
  region of the target attached at one vertex dangles there, `isDangling_of_region`), and every
  edge of a new sheet over `T` (a new sheet is a singleton everywhere below the spine vertex where
  it enters its chain: it is one of the index-one copies `D_r` of `T'` that the restriction splits
  off).

The generic tool is `isDangling_of_region`: over a tree target, the edges of a sheet that is a
singleton at every vertex of a region `Reg`, attached to the rest of the target only at one vertex
`m`, dangle. Its proof is the public tree lemma `Gluing.tCount_add_le` applied to the surviving
edges of that sheet over the region (at a singleton vertex they are the surviving edges of the
source vertex, and a connected datum has no source vertex of surviving valency one).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases.W4StableSource
open GenusSixExistence.Tripod.Gluing (tCount tCount_add_le wCount not_isDangling_of_witness
  nonDanglingValency_eq_wCount wCount_congr)

/-! ## 1.  Singleton sheets over a region dangle -/

section Region

variable {S : CFGraph} {d : ℕ} (E : GluingDatum S d)

theorem tCount_eq_zero (X : S.edges → Prop) (v : S.V)
    (h : ∀ ε ∈ GluingDatum.incidentEdges v, ¬ X ε) : tCount X v = 0 := by
  rw [GenusSixExistence.Tripod.Gluing.tCount_eq_sum]
  exact Finset.sum_eq_zero fun ε _ ↦ ite_eq_right fun h' ↦ h ε h'.2 h'.1

theorem one_le_tCount {X : S.edges → Prop} {v : S.V} {ε : S.edges} (hX : X ε)
    (hε : ε ∈ GluingDatum.incidentEdges v) : 1 ≤ tCount X v := by
  classical
  rw [GenusSixExistence.Tripod.Gluing.tCount_eq_sum]
  calc 1 = (if X ε ∧ ε ∈ GluingDatum.incidentEdges v then 1 else 0) := by rw [ite_eq_left ⟨hX, hε⟩]
    _ ≤ _ := Finset.single_le_sum (f := fun ε ↦ if X ε ∧ ε ∈ GluingDatum.incidentEdges v then 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ ε)

/-- At a singleton source vertex, the incident source edges are the edges of its sheet over the
incident target edges. -/
theorem incident_sourceEndpoint_singleton {u : S.V} {q : Fin d}
    (hSing : ∀ q', (E.vertexPartition u).Rel q q' → q' = q) (F : E.SourceEdge)
    (hF : Incident E F (E.sourceEndpoint u q)) :
    F = E.sourceEdge F.1.1 q ∧ F.1.1 ∈ GluingDatum.incidentEdges u := by
  have hEnds := hF
  unfold Incident GluingDatum.sourceEnds at hEnds
  have key : ∀ v : S.V, E.sourceEndpoint v F.1.2 = E.sourceEndpoint u q → v = u ∧ F.1.2 = q := by
    intro v hv
    obtain ⟨hvu, hrel⟩ := (E.sourceEndpoint_eq_iff v F.1.2 (E.sourceEndpoint u q)).mp hv
    change v = u at hvu
    subst hvu
    refine ⟨rfl, hSing _ ?_⟩
    exact (hrel.trans ((E.vertexPartition v).rel_repr_left q)).symm
  rcases hEnds with h | h
  · obtain ⟨hu, hq⟩ := key _ h
    refine ⟨?_, ?_⟩
    · rw [← hq]; exact (GluingDatum.sourceEdge_self E F).symm
    · unfold GluingDatum.incidentEdges
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hu⟩
  · obtain ⟨hu, hq⟩ := key _ h
    refine ⟨?_, ?_⟩
    · rw [← hq]; exact (GluingDatum.sourceEdge_self E F).symm
    · unfold GluingDatum.incidentEdges
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hu⟩

theorem incident_sourceEdge_sourceEndpoint {u : S.V} {ε : S.edges}
    (hε : ε ∈ GluingDatum.incidentEdges u) (q : Fin d) :
    Incident E (E.sourceEdge ε q) (E.sourceEndpoint u q) := by
  unfold GluingDatum.incidentEdges at hε
  rcases (Finset.mem_filter.mp hε).2 with h | h
  · left
    rw [GenusSixExistence.Tripod.Gluing.sourceEnds_sourceEdge_fst, h]
  · right
    rw [GenusSixExistence.Tripod.Gluing.sourceEnds_sourceEdge_snd, h]

/-- At a singleton source vertex, the surviving valency counts the target edges over which the
sheet's edge survives. -/
theorem nonDanglingValency_singleton {u : S.V} {q : Fin d}
    (hSing : ∀ q', (E.vertexPartition u).Rel q q' → q' = q) (X : S.edges → Prop)
    (hX : ∀ ε ∈ GluingDatum.incidentEdges u, X ε ↔ ¬ IsDangling E (E.sourceEdge ε q)) :
    tCount X u = nonDanglingValency E (E.sourceEndpoint u q) := by
  classical
  unfold tCount nonDanglingValency
  refine Finset.card_bij (fun ε _ ↦ E.sourceEdge ε q) ?_ ?_ ?_
  · intro ε hε
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hε ⊢
    exact ⟨(hX ε hε.2).mp hε.1, incident_sourceEdge_sourceEndpoint E hε.2 q⟩
  · intro ε _ ε' _ h
    exact congrArg (fun F : E.SourceEdge ↦ F.1.1) h
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    obtain ⟨hF1, hF2⟩ := incident_sourceEndpoint_singleton E hSing F hF.2
    refine ⟨F.1.1, ?_, hF1.symm⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(hX _ hF2).mpr ?_, hF2⟩
    rw [← hF1]
    exact hF.1

/-- **A sheet that is a singleton over a region of a tree attached at one vertex dangles over the
region.** `Reg` is a set of target vertices, closed under the target edges except through the
attaching vertex `m`; the sheet `q` is a singleton at every vertex of `Reg`. -/
theorem isDangling_of_region (hE : E.Connected) (hS : graph_connected S) (hg : genus S = 0)
    (q : Fin d) (Reg : S.V → Prop) (m : S.V)
    (hClosed : ∀ ε : S.edges, (Reg (ε : S.V × S.V).1 ∨ Reg (ε : S.V × S.V).2) →
      (Reg (ε : S.V × S.V).1 ∨ (ε : S.V × S.V).1 = m) ∧
        (Reg (ε : S.V × S.V).2 ∨ (ε : S.V × S.V).2 = m))
    (hSing : ∀ v, Reg v → ∀ q', (E.vertexPartition v).Rel q q' → q' = q)
    (ε : S.edges) (hε : Reg (ε : S.V × S.V).1 ∨ Reg (ε : S.V × S.V).2) :
    IsDangling E (E.sourceEdge ε q) := by
  classical
  by_contra hnd
  let X : S.edges → Prop := fun ε ↦
    (Reg (ε : S.V × S.V).1 ∨ Reg (ε : S.V × S.V).2) ∧ ¬ IsDangling E (E.sourceEdge ε q)
  have hX : ∀ u ∉ ({m} : Finset S.V), tCount X u ≠ 1 := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    by_cases hReg : Reg u
    · rw [nonDanglingValency_singleton E (hSing u hReg) X fun ε' hε' ↦ ?_]
      · exact DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one E hE _
      · unfold GluingDatum.incidentEdges at hε'
        have hinc := (Finset.mem_filter.mp hε').2
        constructor
        · exact fun h ↦ h.2
        · intro h
          refine ⟨?_, h⟩
          rcases hinc with h' | h'
          · exact Or.inl (h' ▸ hReg)
          · exact Or.inr (h' ▸ hReg)
    · have h0 : tCount X u = 0 := by
        refine tCount_eq_zero X u fun ε' hinc hX' ↦ ?_
        unfold GluingDatum.incidentEdges at hinc
        have hinc' := (Finset.mem_filter.mp hinc).2
        have hc := hClosed ε' hX'.1
        rcases hinc' with h' | h'
        · rcases hc.1 with h'' | h''
          · exact hReg (h' ▸ h'')
          · exact hu (h'.symm.trans h'')
        · rcases hc.2 with h'' | h''
          · exact hReg (h' ▸ h'')
          · exact hu (h'.symm.trans h'')
      omega
  have hXε : X ε := ⟨hε, hnd⟩
  have hpos : ∀ v, ((ε : S.V × S.V).1 = v ∨ (ε : S.V × S.V).2 = v) → 1 ≤ tCount X v := by
    intro v hv
    refine one_le_tCount hXε ?_
    unfold GluingDatum.incidentEdges
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  have h1 := tCount_add_le hS hg {m} X hX (ε : S.V × S.V).1
  have h2 := tCount_add_le hS hg {m} X hX (ε : S.V × S.V).2
  rw [Finset.card_singleton] at h1 h2
  have hp1 := hpos _ (Or.inl rfl)
  have hp2 := hpos _ (Or.inr rfl)
  by_cases hm1 : (ε : S.V × S.V).1 = m
  · rw [ite_eq_left (Finset.mem_singleton.mpr hm1)] at h1
    omega
  · have := hX _ (fun h ↦ hm1 (Finset.mem_singleton.mp h))
    rw [ite_eq_right (fun h ↦ hm1 (Finset.mem_singleton.mp h))] at h1
    omega

end Region

/-! ## 2.  Levels along a tail -/

section Level

variable {c : ℕ}

/-- **The level of a tail vertex**: `i` for the spine vertex `x_{i+1}` and for the branch at
`A_{i+1}`. A path slot `path i` climbs from level `i - 1` (or `x`) to level `i`; every other slot
stays on its level. -/
def level : TailV c → ℕ
  | Sum.inl (Sum.inl i) => i
  | Sum.inl (Sum.inr i) => i
  | Sum.inr i => i

@[simp] theorem level_spine (i : Fin c) : level (spine i) = i := rfl
@[simp] theorem level_bulb (i : Fin (c + 1)) : level (c := c) (bulb i) = i := rfl
@[simp] theorem level_tip (i : Fin (c + 1)) : level (c := c) (tip i) = i := rfl

theorem level_lHead_path (i : Fin (c + 1)) : level (lHead (path i)) = i := by
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem level_lHead_bridge (i : Fin c) : level (lHead (bridge i)) = i := by simp
theorem level_lHead_loop (i : Fin (c + 1)) : level (lHead (loop i)) = i := by simp

end Level

theorem TailChain.Valid.exists_P_of_mem_vB {d c : ℕ} {ch : TailChain d c} (h : ch.Valid)
    {w : TailV c} {q : Fin d} (hq : q ∈ ch.vB w) :
    ∃ i : Fin (c + 1), q ∈ ch.P i ∧ level w ≤ i.val ∧ i.val ≤ level w + 1 := by
  rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [TailChain.vB_spine, TailChain.S, Finset.mem_union] at hq
    rcases hq with hq | hq
    · exact ⟨i.castSucc, hq, by simp, by simp⟩
    · exact ⟨i.succ, hq, by simp, by simp⟩
  · rw [TailChain.vB_bulb] at hq
    induction i using Fin.lastCases with
    | last => rw [TailChain.R_last] at hq; exact ⟨Fin.last c, hq, by simp, by simp⟩
    | cast i =>
      have := h.R_sub_S i hq
      rw [TailChain.S, Finset.mem_union] at this
      rcases this with hq | hq
      · exact ⟨i.castSucc, hq, by simp, by simp⟩
      · exact ⟨i.succ, hq, by simp, by simp⟩
  · rw [TailChain.vB_tip] at hq
    induction i using Fin.lastCases with
    | last => rw [TailChain.R_last] at hq; exact ⟨Fin.last c, hq, by simp, by simp⟩
    | cast i =>
      have := h.R_sub_S i hq
      rw [TailChain.S, Finset.mem_union] at this
      rcases this with hq | hq
      · exact ⟨i.castSucc, hq, by simp, by simp⟩
      · exact ⟨i.succ, hq, by simp, by simp⟩

/-! ## 3.  The regions of the regrown target -/

section Regions

variable {T : CFGraph.{0}} {k : ℕ} (c : Fin k → ℕ) (x : Fin k → T.V)

/-- **The part of tail `j` at level at least `L`.** -/
def Up (j : Fin k) (L : ℕ) (v : (catTarget c T x).V) : Prop :=
  ∃ w : TailV (c j), v = tailV c x ⟨j, w⟩ ∧ L ≤ level w

theorem not_up_oldV (j : Fin k) (L : ℕ) (v : T.V) : ¬ Up c x j L (oldV c x v) := by
  rintro ⟨w, h, -⟩; exact oldV_ne_tailV c x _ _ h

theorem up_tailV_iff (j : Fin k) (L : ℕ) (w : TailV (c j)) :
    Up c x j L (tailV c x ⟨j, w⟩) ↔ L ≤ level w := by
  constructor
  · rintro ⟨w', h, hl⟩
    rw [tailV_mk_inj] at h
    rw [h]; exact hl
  · intro h; exact ⟨w, rfl, h⟩

theorem not_up_tailV_of_ne {j j' : Fin k} (hj : j' ≠ j) (L : ℕ) (w : TailV (c j')) :
    ¬ Up c x j L (tailV c x ⟨j', w⟩) := by
  rintro ⟨w', h, -⟩
  rw [tailV_inj] at h
  exact hj (congrArg Sigma.fst h)

/-- **Every target edge stays on one side of a level, except the path slot climbing to it.** -/
theorem up_cases (j : Fin k) (L : ℕ) (ε : (catTarget c T x).edges) :
    (Up c x j L (ε : (catTarget c T x).V × (catTarget c T x).V).1 ↔
      Up c x j L (ε : (catTarget c T x).V × (catTarget c T x).V).2) ∨
      ∃ L' : Fin (c j + 1), L'.val = L ∧ ε = tailE c x ⟨j, path L'⟩ := by
  rcases edge_cases c x ε with ⟨f, rfl⟩ | ⟨⟨j', s⟩, rfl⟩
  · left
    rw [oldE_ends]
    exact iff_of_false (not_up_oldV c x j L _) (not_up_oldV c x j L _)
  · rw [tailE_ends]
    by_cases hj : j' = j
    · subst hj
      rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · by_cases hi : i.val = L
        · exact Or.inr ⟨i, hi, rfl⟩
        · left
          simp only [headEnd, up_tailV_iff, level_lHead_path]
          rw [tailEnd_eq_attach]
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · rw [lTail_path_zero, attach_none]
            simp only [Fin.val_zero] at hi ⊢
            exact iff_of_false (not_up_oldV c x _ L _) (by omega)
          · rw [lTail_path_succ, attach_some, up_tailV_iff, level_spine]
            simp only [Fin.val_succ] at hi ⊢
            omega
      · left
        simp only [headEnd, up_tailV_iff, level_lHead_bridge]
        rw [tailEnd_eq_attach, lTail_bridge, attach_some, up_tailV_iff, level_spine]
      · left
        simp only [headEnd, up_tailV_iff, level_lHead_loop]
        rw [tailEnd_eq_attach, lTail_loop, attach_some, up_tailV_iff, level_bulb]
    · left
      refine iff_of_false ?_ (not_up_tailV_of_ne c x hj L _)
      rw [tailEnd_eq_attach]
      cases lTail s with
      | none => exact not_up_oldV c x j L _
      | some w => exact not_up_tailV_of_ne c x hj L w

theorem tailEnd_path_not_up (j : Fin k) (L' : Fin (c j + 1)) :
    ¬ Up c x j L'.val (tailEnd c x ⟨j, path L'⟩) := by
  rw [tailEnd_eq_attach]
  rcases Fin.eq_zero_or_eq_succ L' with rfl | ⟨i', rfl⟩
  · rw [lTail_path_zero, attach_none]; exact not_up_oldV c x j _ _
  · rw [lTail_path_succ, attach_some, up_tailV_iff, level_spine]; simp

theorem headEnd_path_up (j : Fin k) (L' : Fin (c j + 1)) :
    Up c x j L'.val (headEnd c x ⟨j, path L'⟩) := by
  simp only [headEnd, up_tailV_iff, level_lHead_path, le_refl]

end Regions

/-! ## 4.  The dangling edges of the regrowth -/

namespace CatBranching

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c)

/-- A target edge at a tail vertex is one of its incident slots. -/
theorem eq_tailE_of_incident {ε : (catTarget c T β.x).edges} {j : Fin k} {w : TailV (c j)}
    (h : (ε : (catTarget c T β.x).V × (catTarget c T β.x).V).1 = tailV c β.x ⟨j, w⟩ ∨
      (ε : (catTarget c T β.x).V × (catTarget c T β.x).V).2 = tailV c β.x ⟨j, w⟩) :
    ∃ s ∈ incSlots w, ε = tailE c β.x ⟨j, s⟩ := by
  have hmem : ε ∈ GluingDatum.incidentEdges (tailV c β.x ⟨j, w⟩) := by
    unfold GluingDatum.incidentEdges
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  rw [incidentEdges_tailV, Finset.mem_map] at hmem
  obtain ⟨s, hs, rfl⟩ := hmem
  exact ⟨s, hs, rfl⟩

/-- A singleton at a tail vertex. -/
theorem rel_tailV_of_not_mem {w : TV c} {q : Fin d} (hq : q ∉ β.vB w) (q' : Fin d)
    (h : (β.regrowDatum.vertexPartition (tailV c β.x w)).Rel q q') : q' = q :=
  ((blockPart_rel_iff_of_not_mem (β.vA_anchored w) hq q').mp h).symm

variable (hψ : ψ.Connected) (hT : graph_connected T) (hT0 : genus T = 0)

include hψ hT hT0

/-- **A loop edge outside the branch block dangles**: its tip is a singleton. -/
theorem isDangling_loop {j : Fin k} {i : Fin (c j + 1)} {q : Fin d}
    (hq : q ∉ (β.chain j).R i) : IsDangling β.regrowDatum (β.tailSE ⟨j, loop i⟩ q) := by
  refine isDangling_of_region β.regrowDatum (β.connected_regrowDatum hψ hT)
    (catTarget_connected c β.x hT) ((genus_catTarget c β.x).trans hT0) q
    (fun v ↦ v = tailV c β.x ⟨j, tip i⟩) (tailV c β.x ⟨j, bulb i⟩) ?_ ?_ _ ?_
  · intro ε hε
    obtain ⟨s, hs, rfl⟩ := β.eq_tailE_of_incident hε
    rw [incSlots_tip, Finset.mem_singleton] at hs
    subst hs
    rw [tailE_ends]
    simp [tailEnd_eq_attach, headEnd]
  · rintro v rfl q' h
    exact β.rel_tailV_of_not_mem (w := ⟨j, tip i⟩) hq q' h
  · rw [tailE_ends]
    exact Or.inr rfl

/-- **A bridge edge outside the branch block dangles**: past it, the branch is singletons. -/
theorem isDangling_inBridge {j : Fin k} {i : Fin (c j + 1)} {q : Fin d}
    (hq : q ∉ (β.chain j).R i) : IsDangling β.regrowDatum (β.tailSE ⟨j, inBridge i⟩ q) := by
  refine isDangling_of_region β.regrowDatum (β.connected_regrowDatum hψ hT)
    (catTarget_connected c β.x hT) ((genus_catTarget c β.x).trans hT0) q
    (fun v ↦ v = tailV c β.x ⟨j, bulb i⟩ ∨ v = tailV c β.x ⟨j, tip i⟩)
    (tailEnd c β.x ⟨j, inBridge i⟩) ?_ ?_ _ ?_
  · intro ε hε
    have hε' : ∃ s, (s ∈ incSlots (bulb i) ∨ s ∈ incSlots (tip i)) ∧
        ε = tailE c β.x ⟨j, s⟩ := by
      rcases hε with (h | h) | (h | h)
      · obtain ⟨s, hs, h⟩ := β.eq_tailE_of_incident (Or.inl h); exact ⟨s, Or.inl hs, h⟩
      · obtain ⟨s, hs, h⟩ := β.eq_tailE_of_incident (Or.inl h); exact ⟨s, Or.inr hs, h⟩
      · obtain ⟨s, hs, h⟩ := β.eq_tailE_of_incident (Or.inr h); exact ⟨s, Or.inl hs, h⟩
      · obtain ⟨s, hs, h⟩ := β.eq_tailE_of_incident (Or.inr h); exact ⟨s, Or.inr hs, h⟩
    obtain ⟨s, hs, rfl⟩ := hε'
    rw [incSlots_bulb, incSlots_tip] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self_right] at hs
    rw [tailE_ends]
    rcases hs with rfl | rfl
    · simp [headEnd]
    · simp [tailEnd_eq_attach, headEnd]
  · rintro v (rfl | rfl) q' h
    · exact β.rel_tailV_of_not_mem (w := ⟨j, bulb i⟩) hq q' h
    · exact β.rel_tailV_of_not_mem (w := ⟨j, tip i⟩) hq q' h
  · rw [tailE_ends]
    exact Or.inr (Or.inl (by simp [headEnd]))

/-- **A sheet absent from the chain from level `L` on dangles above level `L`.** -/
theorem isDangling_up {j : Fin k} (L : Fin (c j + 1)) {q : Fin d}
    (hq : ∀ i, L ≤ i → q ∉ (β.chain j).P i) (ε : (catTarget c T β.x).edges)
    (hε : Up c β.x j L.val (ε : (catTarget c T β.x).V × (catTarget c T β.x).V).1 ∨
      Up c β.x j L.val (ε : (catTarget c T β.x).V × (catTarget c T β.x).V).2) :
    IsDangling β.regrowDatum (β.regrowDatum.sourceEdge ε q) := by
  refine isDangling_of_region β.regrowDatum (β.connected_regrowDatum hψ hT)
    (catTarget_connected c β.x hT) ((genus_catTarget c β.x).trans hT0) q
    (Up c β.x j L.val) (tailEnd c β.x ⟨j, path L⟩) ?_ ?_ ε hε
  · intro ε' hε'
    rcases up_cases c β.x j L.val ε' with hiff | ⟨L', hL', rfl⟩
    · rcases hε' with h | h
      · exact ⟨Or.inl h, Or.inl (hiff.mp h)⟩
      · exact ⟨Or.inl (hiff.mpr h), Or.inl h⟩
    · obtain rfl : L' = L := Fin.ext hL'
      rw [tailE_ends]
      exact ⟨Or.inr rfl, Or.inl (headEnd_path_up c β.x j L')⟩
  · rintro v ⟨w, rfl, hw⟩ q' h
    refine β.rel_tailV_of_not_mem (w := ⟨j, w⟩) (fun hmem ↦ ?_) q' h
    obtain ⟨i, hi, hlo, -⟩ := (β.valid j).exists_P_of_mem_vB (w := w) hmem
    exact hq i (Fin.le_def.mpr (by omega)) hi

/-- **A sheet absent from everything below level `L + 1` dangles below level `L`**: it is a
singleton over `T`, over the other tails and below `x_{L+1}`. -/
theorem isDangling_down {j : Fin k} (L : Fin (c j)) {q : Fin d}
    (hq : ∀ i : Fin (c j + 1), i.val ≤ L.val → q ∉ (β.chain j).P i)
    (hold : ∀ v q', (liftPart β.e (ψ.vertexPartition v)).Rel q q' → q' = q)
    (hother : ∀ j', j' ≠ j → ∀ w, q ∉ β.vB ⟨j', w⟩) (ε : (catTarget c T β.x).edges)
    (hε : ¬ Up c β.x j L.val (ε : (catTarget c T β.x).V × (catTarget c T β.x).V).1 ∨
      ¬ Up c β.x j L.val (ε : (catTarget c T β.x).V × (catTarget c T β.x).V).2) :
    IsDangling β.regrowDatum (β.regrowDatum.sourceEdge ε q) := by
  refine isDangling_of_region β.regrowDatum (β.connected_regrowDatum hψ hT)
    (catTarget_connected c β.x hT) ((genus_catTarget c β.x).trans hT0) q
    (fun v ↦ ¬ Up c β.x j L.val v) (tailV c β.x ⟨j, spine L⟩) ?_ ?_ ε hε
  · intro ε' hε'
    rcases up_cases c β.x j L.val ε' with hiff | ⟨L', hL', rfl⟩
    · rcases hε' with h | h
      · exact ⟨Or.inl h, Or.inl (fun h' ↦ h (hiff.mpr h'))⟩
      · exact ⟨Or.inl (fun h' ↦ h (hiff.mp h')), Or.inl h⟩
    · obtain rfl : L' = L.castSucc := Fin.ext hL'
      rw [tailE_ends]
      refine ⟨Or.inl (tailEnd_path_not_up c β.x j _), Or.inr ?_⟩
      simp [headEnd]
  · intro v hv q' h
    rcases vertex_cases c β.x v with ⟨u, rfl⟩ | ⟨⟨j', w⟩, rfl⟩
    · exact hold u q' h
    · by_cases hj : j' = j
      · subst hj
        refine β.rel_tailV_of_not_mem (w := ⟨j', w⟩) (fun hmem ↦ ?_) q' h
        obtain ⟨i, hi, -, hhi⟩ := (β.valid j').exists_P_of_mem_vB (w := w) hmem
        rw [up_tailV_iff, not_le] at hv
        exact hq i (by omega) hi
      · exact β.rel_tailV_of_not_mem (w := ⟨j', w⟩) (hother j' hj w) q' h

omit hψ hT hT0 in
/-- **A new sheet enters one chain, at some spine vertex**, and is absent below it and from the
other tails. -/
theorem new_late (n : N) : ∃ j, ∃ L : Fin (c j),
    (∀ i : Fin (c j + 1), i.val ≤ L.val → new β.e n ∉ (β.chain j).P i) ∧
      new β.e n ∈ (β.chain j).P L.succ ∧ ∀ j', j' ≠ j → ∀ w, new β.e n ∉ β.vB ⟨j', w⟩ := by
  classical
  obtain ⟨j, i, hi⟩ := β.new_used n
  have hEx : ∃ m, ∃ h : m < c j + 1, new β.e n ∈ (β.chain j).P ⟨m, h⟩ := ⟨i.val, i.2, hi⟩
  obtain ⟨hlt, hmem⟩ := Nat.find_spec hEx
  have hnot0 : new β.e n ∉ (β.chain j).P 0 := fun h ↦ by
    obtain ⟨i', h', -⟩ := β.P0_sub j _ h
    exact new_ne_old _ _ h'
  have hpos : Nat.find hEx ≠ 0 := by
    intro h0
    apply hnot0
    have : (⟨Nat.find hEx, hlt⟩ : Fin (c j + 1)) = 0 := Fin.ext (by simpa using h0)
    rw [← this]; exact hmem
  refine ⟨j, ⟨Nat.find hEx - 1, by omega⟩, fun i' hi' hmem' ↦ ?_, ?_, fun j' hj' w hw ↦ ?_⟩
  · have := Nat.find_min' hEx ⟨i'.2, hmem'⟩
    simp only at hi'
    omega
  · have : (⟨Nat.find hEx - 1, by omega⟩ : Fin (c j)).succ = ⟨Nat.find hEx, hlt⟩ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [this]; exact hmem
  · obtain ⟨i', hi', -⟩ := (β.valid j').exists_P_of_mem_vB (w := w) hw
    have hnot0' : new β.e n ∉ (β.chain j').P 0 := fun h ↦ by
      obtain ⟨i'', h', -⟩ := β.P0_sub j' _ h
      exact new_ne_old _ _ h'
    exact hj' (β.fresh_disjoint j' j i' i _ hi' hi hnot0')

/-- **An edge of a new sheet over `T` dangles.** -/
theorem isDangling_newSE (ε : T.edges) (n : N) : IsDangling β.regrowDatum (β.newSE ε n) := by
  obtain ⟨j, L, h1, -, h2⟩ := β.new_late n
  have hE : β.newSE ε n = β.regrowDatum.sourceEdge (oldE c β.x ε) (new β.e n) := by
    apply Subtype.ext
    change (oldE c β.x ε, new β.e n) =
      (oldE c β.x ε, (β.regrowDatum.edgePartition (oldE c β.x ε)).repr (new β.e n))
    rw [ep_oldE, liftPart_repr_new]
  rw [hE]
  refine β.isDangling_down hψ hT hT0 L h1 (fun v q' h ↦ (liftPart_rel_new_iff _ n q').mp h) h2 _ ?_
  left
  rw [oldE_ends]
  exact not_up_oldV c β.x j _ _

/-- **A path edge outside its block dangles.** -/
theorem isDangling_path {j : Fin k} {i : Fin (c j + 1)} {q : Fin d}
    (hq : q ∉ (β.chain j).P i) : IsDangling β.regrowDatum (β.tailSE ⟨j, path i⟩ q) := by
  by_cases hAbove : ∃ i', i < i' ∧ q ∈ (β.chain j).P i'
  · obtain ⟨i'', hi'', hq''⟩ := hAbove
    have hnot0 : q ∉ (β.chain j).P 0 := fun h0 ↦
      hq ((β.valid j).convex q 0 i i'' (Fin.zero_le _) hi''.le h0 hq'')
    obtain ⟨n, rfl⟩ := β.fresh j i'' q hq'' hnot0
    obtain ⟨j₂, L, h1, h3, h2⟩ := β.new_late n
    have hj : j₂ = j := by
      by_contra hne
      exact h2 j (Ne.symm hne) (lHead (path i'')) ((β.valid j).eB_sub_vB_head (path i'') hq'')
    subst hj
    have hiL : i.val ≤ L.val := by
      by_contra hlt
      push Not at hlt
      exact hq ((β.valid j₂).convex _ L.succ i i'' (Fin.le_def.mpr (by simp; omega)) hi''.le h3
        hq'')
    refine β.isDangling_down hψ hT hT0 L h1 (fun v q' h ↦ (liftPart_rel_new_iff _ n q').mp h) h2 _
      ?_
    left
    rw [tailE_ends, tailEnd_eq_attach]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rw [lTail_path_zero, attach_none]; exact not_up_oldV c β.x j₂ _ _
    · rw [lTail_path_succ, attach_some, up_tailV_iff, level_spine]
      simp at hiL; omega
  · push Not at hAbove
    refine β.isDangling_up hψ hT hT0 i (fun i' hi' hq' ↦ ?_) _ ?_
    · rcases hi'.lt_or_eq with hlt | rfl
      · exact hAbove i' hlt hq'
      · exact hq hq'
    · rw [tailE_ends]
      exact Or.inr (headEnd_path_up c β.x j i)

/-- **A tail edge outside its surviving sheets dangles.** -/
theorem isDangling_tailSE {t : TE c} {q : Fin d} (hq : q ∉ β.rowSet t) :
    IsDangling β.regrowDatum (β.tailSE t q) := by
  obtain ⟨j, s⟩ := t
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact β.isDangling_path hψ hT hT0 hq
  · have h := β.isDangling_inBridge hψ hT hT0 (j := j) (i := i.castSucc) (q := q)
      (by rw [TailChain.R_castSucc]; exact hq)
    rwa [inBridge_castSucc] at h
  · exact β.isDangling_loop hψ hT hT0 hq

end CatBranching

end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
