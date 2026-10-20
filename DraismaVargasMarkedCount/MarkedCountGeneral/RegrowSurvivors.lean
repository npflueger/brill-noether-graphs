module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowDangling

@[expose] public section

/-!
# Regrowth, part 6: the surviving edges and the surviving valencies

The surviving edges of `regrowDatum β` (`Survives`) are

* the surviving edges of `ψ`, on the old sheets;
* over each path and bridge slot its block edge (`e_i`, of index `s_i`; a bridge of index two);
* over each leaf edge the two loop edges of its branch.

Distinct surviving edges over a tail slot are indexed by `rowIdx` (one sheet for a block edge, the
two sheets of the branch for the loop edges), so that the surviving edges are
`NonDanglingEdge ψ ⊕ Σ t, rowIdx t` (`survOfSum_bijective`).

Proved here: no source vertex has exactly one surviving incident edge (`wCount_survives_ne_one`),
hence by the public witness lemma the survivors survive; the old edges keep their status
(`isDangling_psiSE_iff`); so **the surviving edges are exactly `Survives`** (`not_isDangling_iff`).
The surviving valencies: `ψ`'s plus one at every mark, three at a spine block and at a bulb, two at
a tip, zero at every singleton (`nonDanglingValency_*`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases.W4StableSource
open GenusSixExistence.Tripod.Gluing (wCount not_isDangling_of_witness
  nonDanglingValency_eq_wCount wCount_congr wCount_le_of_imp)

namespace TailChain

variable {d c : ℕ} (ch : TailChain d c)

/-- **The sheets indexing the distinct surviving edges over a slot**: the name of the block over a
path or bridge slot, the two sheets of the branch over a leaf edge. -/
def rowIdx : CatSlot c → Finset (Fin d)
  | Sum.inl i => {ch.eA (Sum.inl i)}
  | Sum.inr (Sum.inl i) => {ch.eA (Sum.inr (Sum.inl i))}
  | Sum.inr (Sum.inr i) => ch.R i

theorem rowIdx_of_not_loop {s : CatSlot c} (hs : ∀ i, s ≠ loop i) : ch.rowIdx s = {ch.eA s} := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rfl
  · rfl
  · exact absurd rfl (hs i)

@[simp] theorem rowIdx_loop (i : Fin (c + 1)) : ch.rowIdx (loop i) = ch.R i := rfl

variable {ch}

theorem Valid.rowIdx_sub_rowSet (h : ch.Valid) (s : CatSlot c) : ch.rowIdx s ⊆ ch.rowSet s := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · intro q hq
    rw [rowIdx_of_not_loop _ (fun _ ↦ path_ne_loop _ _), Finset.mem_singleton] at hq
    subst hq
    exact h.eA_mem (fun _ ↦ path_ne_loop _ _)
  · intro q hq
    rw [rowIdx_of_not_loop _ (fun _ ↦ bridge_ne_loop _ _), Finset.mem_singleton] at hq
    subst hq
    exact h.eA_mem (fun _ ↦ bridge_ne_loop _ _)
  · exact fun q hq ↦ hq

theorem Valid.card_rowIdx (h : ch.Valid) (s : CatSlot c) :
    (ch.rowIdx s).card = if ∃ i, s = loop i then 2 else 1 := by
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [rowIdx_of_not_loop _ (fun _ ↦ path_ne_loop _ _), Finset.card_singleton,
      ite_eq_right (by simp)]
  · rw [rowIdx_of_not_loop _ (fun _ ↦ bridge_ne_loop _ _), Finset.card_singleton,
      ite_eq_right (by simp)]
  · rw [rowIdx_loop, h.card_R, ite_eq_left ⟨i, rfl⟩]

end TailChain

namespace CatBranching

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c)

/-- The indices of the surviving edges over a tail slot. -/
def rowIdx (t : TE c) : Finset (Fin d) := (β.chain t.1).rowIdx t.2

theorem rowIdx_sub_rowSet (t : TE c) : β.rowIdx t ⊆ β.rowSet t :=
  (β.valid t.1).rowIdx_sub_rowSet t.2

/-! ## 1.  Survivors and their ends -/

/-- **The surviving edges of the regrowth.** -/
def Survives (E : β.regrowDatum.SourceEdge) : Prop :=
  (∃ F : ψ.SourceEdge, ¬ IsDangling ψ F ∧ E = β.psiSE F) ∨
    ∃ t q, q ∈ β.rowSet t ∧ E = β.tailSE t q

theorem rowSet_sub_vB_head (t : TE c) : β.rowSet t ⊆ β.vB ⟨t.1, lHead t.2⟩ :=
  (β.valid t.1).rowSet_sub_vB_head t.2

theorem rowSet_sub_vB_tail {t : TE c} {w : TailV (c t.1)} (h : lTail t.2 = some w) :
    β.rowSet t ⊆ β.vB ⟨t.1, w⟩ := by
  obtain ⟨j, s⟩ := t
  rcases slot_cases s with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact β.eB_sub_vB_tail (t := ⟨j, path i⟩) h
  · exact β.eB_sub_vB_tail (t := ⟨j, bridge i⟩) h
  · rw [lTail_loop, Option.some_inj] at h
    subst h
    exact fun q hq ↦ hq

/-- The tail end of a surviving tail edge: the mark, or a block vertex. -/
def tailBlock (t : TE c) : β.regrowDatum.SourceVertex :=
  Option.elim (lTail t.2) (β.psiSV (β.mark t.1)) fun w ↦ β.blockSV ⟨t.1, w⟩

theorem sourceEndpoint_tailEnd_of_rowSet {t : TE c} {q : Fin d} (hq : q ∈ β.rowSet t) :
    β.regrowDatum.sourceEndpoint (tailEnd c β.x t) q = β.tailBlock t := by
  obtain ⟨j, s⟩ := t
  unfold tailBlock
  rw [tailEnd_eq_attach]
  cases h : lTail s with
  | none =>
    rw [lTail_eq_none_iff] at h
    subst h
    exact β.sourceEndpoint_x_of_mem hq
  | some w =>
    exact β.tailSV_of_mem (β.rowSet_sub_vB_tail (t := ⟨j, s⟩) h hq)

theorem incident_tailSE_of_rowSet {t : TE c} {q : Fin d} (hq : q ∈ β.rowSet t)
    (X : β.regrowDatum.SourceVertex) :
    Incident β.regrowDatum (β.tailSE t q) X ↔ X = β.tailBlock t ∨ X = β.blockSV ⟨t.1, lHead t.2⟩ := by
  rw [incident_tailSE_iff, β.sourceEndpoint_tailEnd_of_rowSet hq,
    β.tailSV_of_mem (β.rowSet_sub_vB_head t hq)]

theorem tailBlock_eq_psiSV_iff (t : TE c) (Y : ψ.SourceVertex) :
    β.tailBlock t = β.psiSV Y ↔ t.2 = path 0 ∧ β.mark t.1 = Y := by
  unfold tailBlock
  cases h : lTail t.2 with
  | none =>
    rw [lTail_eq_none_iff] at h
    simp [h]
  | some w =>
    have : t.2 ≠ path 0 := fun h' ↦ by rw [h', lTail_path_zero] at h; cases h
    simp [this, blockSV]

theorem tailBlock_eq_blockSV_iff (t : TE c) (w : TV c) :
    β.tailBlock t = β.blockSV w ↔ tailEnd c β.x t = tailV c β.x w := by
  unfold tailBlock
  rw [tailEnd_eq_attach]
  cases lTail t.2 with
  | none =>
    simp only [Option.elim_none, attach_none]
    exact iff_of_false (β.psiSV_ne_tailSV _ _ _) (oldV_ne_tailV c β.x _ _)
  | some w' =>
    simp only [Option.elim_some, attach_some, blockSV_inj, tailV_inj]

/-- A surviving tail edge meets a block vertex exactly where its slot meets the tail vertex. -/
theorem incident_tailSE_blockSV {t : TE c} {q : Fin d} (hq : q ∈ β.rowSet t) (w : TV c) :
    Incident β.regrowDatum (β.tailSE t q) (β.blockSV w) ↔
      (tailEnd c β.x t = tailV c β.x w ∨ headEnd c β.x t = tailV c β.x w) := by
  rw [β.incident_tailSE_of_rowSet hq, eq_comm, β.tailBlock_eq_blockSV_iff, blockSV_inj, headEnd,
    tailV_inj, eq_comm (a := w)]

theorem tailBlock_ne_newSV (t : TE c) (v : T.V) (n : N) : β.tailBlock t ≠ β.newSV v n := by
  unfold tailBlock
  cases lTail t.2 with
  | none => exact β.psiSV_ne_newSV _ _ _
  | some w => exact fun h ↦ β.tailSV_ne_newSV v n _ _ h

theorem tailBlock_ne_tailSV {t : TE c} {w : TV c} {q : Fin d} (hq : q ∉ β.vB w) :
    β.tailBlock t ≠ β.tailSV w q := by
  unfold tailBlock
  cases h : lTail t.2 with
  | none => exact β.psiSV_ne_tailSV _ _ _
  | some w' =>
    intro h'
    obtain ⟨rfl, -⟩ := (β.tailSV_eq_blockSV_iff w ⟨t.1, w'⟩ q).mp h'.symm
    exact hq (by
      have := (β.tailSV_eq_blockSV_iff ⟨t.1, w'⟩ ⟨t.1, w'⟩ q).mp h'.symm
      exact this.2)

/-! ## 2.  Survivors as a sum -/

/-- The surviving edges, from their decomposition. -/
def survOfSum : NonDanglingEdge ψ ⊕ (Σ t : TE c, {q // q ∈ β.rowIdx t}) →
    {E : β.regrowDatum.SourceEdge // β.Survives E}
  | .inl F => ⟨β.psiSE F.1, Or.inl ⟨F.1, F.2, rfl⟩⟩
  | .inr ⟨t, q⟩ => ⟨β.tailSE t q.1, Or.inr ⟨t, q.1, β.rowIdx_sub_rowSet t q.2, rfl⟩⟩

theorem tailSE_rowIdx_inj {t : TE c} {q q' : Fin d} (hq : q ∈ β.rowIdx t)
    (hq' : q' ∈ β.rowIdx t) (h : β.tailSE t q = β.tailSE t q') : q = q' := by
  obtain ⟨j, s⟩ := t
  by_cases hs : ∃ i, s = loop i
  · obtain ⟨i, rfl⟩ := hs
    rcases ((β.tailSE_eq_iff _ _ _ _).mp h).2 with h' | ⟨h', -⟩
    · exact h'
    · exact absurd h' (Finset.notMem_empty _)
  · push Not at hs
    change q ∈ (β.chain j).rowIdx s at hq
    change q' ∈ (β.chain j).rowIdx s at hq'
    rw [TailChain.rowIdx_of_not_loop _ hs, Finset.mem_singleton] at hq hq'
    rw [hq, hq']

theorem survOfSum_bijective : Function.Bijective β.survOfSum := by
  constructor
  · rintro (F | ⟨t, q⟩) (F' | ⟨t', q'⟩) h <;> have h' := congrArg Subtype.val h <;>
      simp only [survOfSum, psiSE_inj, psiSE_ne_tailSE, tailSE_ne_psiSE] at h'
    · exact congrArg Sum.inl (Subtype.ext h')
    · obtain ⟨rfl, -⟩ := (β.tailSE_eq_iff _ _ _ _).mp h'
      have := β.tailSE_rowIdx_inj q.2 q'.2 h'
      exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext this)))
  · rintro ⟨E, ⟨F, hF, rfl⟩ | ⟨t, q, hq, rfl⟩⟩
    · exact ⟨.inl ⟨F, hF⟩, rfl⟩
    · obtain ⟨j, s⟩ := t
      by_cases hs : ∃ i, s = loop i
      · obtain ⟨i, rfl⟩ := hs
        exact ⟨.inr ⟨⟨j, loop i⟩, q, hq⟩, rfl⟩
      · push Not at hs
        have hmem : β.eA ⟨j, s⟩ ∈ β.rowIdx ⟨j, s⟩ := by
          change _ ∈ (β.chain j).rowIdx s
          rw [TailChain.rowIdx_of_not_loop _ hs]; exact Finset.mem_singleton_self _
        refine ⟨.inr ⟨⟨j, s⟩, β.eA ⟨j, s⟩, hmem⟩, Subtype.ext ?_⟩
        change β.tailSE ⟨j, s⟩ (β.eA ⟨j, s⟩) = β.tailSE ⟨j, s⟩ q
        have hq' : q ∈ β.eB ⟨j, s⟩ := by
          change q ∈ (β.chain j).rowSet s at hq
          rwa [TailChain.rowSet_of_not_loop _ hs] at hq
        rw [β.tailSE_of_mem hq']
        rfl

open Classical in
/-- **Sums over the surviving edges** (before the dictionary: over `Survives`). -/
theorem sum_survives {M : Type*} [AddCommMonoid M] (f : β.regrowDatum.SourceEdge → M) :
    ∑ E : {E // β.Survives E}, f E.1 =
      ∑ F : NonDanglingEdge ψ, f (β.psiSE F.1) + ∑ t, ∑ q : {q // q ∈ β.rowIdx t}, f (β.tailSE t q.1) := by
  rw [← Fintype.sum_bijective _ β.survOfSum_bijective (fun z ↦ f (β.survOfSum z).1)
    (fun E ↦ f E.1) (fun _ ↦ rfl), Fintype.sum_sum_type, Fintype.sum_sigma]
  rfl

/-- A count of source edges with a property, as a sum over the edges with the property. -/
theorem wCount_eq_sum {S : CFGraph} {d₀ : ℕ} (E : GluingDatum S d₀) (W : E.SourceEdge → Prop)
    [DecidablePred W] (X : E.SourceVertex) :
    wCount E W X = ∑ e : {e // W e}, if Incident E e.1 X then 1 else 0 := by
  unfold wCount
  rw [Finset.card_filter]
  trans ∑ e, if W e then (if Incident E e X then 1 else 0) else 0
  · apply Finset.sum_congr rfl
    intro e _
    by_cases hW : W e <;> by_cases hI : Incident E e X <;> simp [hW, hI]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  exact Finset.sum_subtype _ (fun e ↦ by simp) _

/-- The surviving valency of `ψ`, as a sum. -/
theorem nonDanglingValency_eq_sum {S : CFGraph} {d₀ : ℕ} (E : GluingDatum S d₀)
    (X : E.SourceVertex) :
    nonDanglingValency E X = ∑ F : NonDanglingEdge E, if Incident E F.1 X then 1 else 0 := by
  rw [nonDanglingValency_eq_wCount, wCount_eq_sum]
  rfl

open Classical in
/-- **The count of survivors at a source vertex**, by kinds. -/
theorem wCount_survives (X : β.regrowDatum.SourceVertex) :
    wCount β.regrowDatum β.Survives X =
      (∑ F : NonDanglingEdge ψ, if Incident β.regrowDatum (β.psiSE F.1) X then 1 else 0) +
        ∑ t, ∑ q : {q // q ∈ β.rowIdx t},
          if Incident β.regrowDatum (β.tailSE t q.1) X then 1 else 0 := by
  classical
  rw [wCount_eq_sum, ← Fintype.sum_bijective _ β.survOfSum_bijective
    (fun z ↦ if Incident β.regrowDatum (β.survOfSum z).1 X then 1 else 0)
    (fun E ↦ if Incident β.regrowDatum E.1 X then 1 else 0) (fun _ ↦ rfl),
    Fintype.sum_sum_type, Fintype.sum_sigma]
  rfl

theorem card_rowIdx (t : TE c) :
    (β.rowIdx t).card = if ∃ i, t.2 = loop i then 2 else 1 := (β.valid t.1).card_rowIdx t.2

/-- The number of marks at a source vertex of `ψ`. -/
def markCount (Y : ψ.SourceVertex) : ℕ := (Finset.univ.filter fun j ↦ β.mark j = Y).card

theorem wCount_survives_psiSV (Y : ψ.SourceVertex) :
    wCount β.regrowDatum β.Survives (β.psiSV Y) = nonDanglingValency ψ Y + β.markCount Y := by
  classical
  rw [wCount_survives, nonDanglingValency_eq_sum]
  congr 1
  · exact Fintype.sum_congr _ _ fun F ↦ if_congr (β.incident_psiSE_psiSV _ _) rfl rfl
  · have h : ∀ (t : TE c) (q : {q // q ∈ β.rowIdx t}),
        (if Incident β.regrowDatum (β.tailSE t q.1) (β.psiSV Y) then 1 else 0) =
          if t.2 = path 0 ∧ β.mark t.1 = Y then 1 else 0 := by
      intro t q
      refine if_congr ?_ rfl rfl
      rw [β.incident_tailSE_of_rowSet (β.rowIdx_sub_rowSet t q.2), eq_comm,
        β.tailBlock_eq_psiSV_iff]
      simp [blockSV]
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    rw [Fintype.sum_sigma]
    unfold markCount
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_eq_single (path 0)]
    · by_cases hj : β.mark j = Y
      · simp only [hj, and_true, ite_true, mul_one]
        rw [card_rowIdx, ite_eq_right (by simp)]
      · simp [hj]
    · intro s _ hs; simp [hs]
    · simp

theorem wCount_survives_newSV (v : T.V) (n : N) :
    wCount β.regrowDatum β.Survives (β.newSV v n) = 0 := by
  rw [wCount_survives]
  have h1 : ∀ F : NonDanglingEdge ψ,
      (if Incident β.regrowDatum (β.psiSE F.1) (β.newSV v n) then 1 else 0) = 0 :=
    fun F ↦ ite_eq_right (β.incident_psiSE_newSV _ _ _)
  rw [Fintype.sum_congr _ _ h1]
  have h2 : ∀ (t : TE c) (q : {q // q ∈ β.rowIdx t}),
      (if Incident β.regrowDatum (β.tailSE t q.1) (β.newSV v n) then 1 else 0) = 0 := by
    intro t q
    refine ite_eq_right fun h ↦ ?_
    rcases (β.incident_tailSE_of_rowSet (β.rowIdx_sub_rowSet t q.2) _).mp h with h | h
    · exact β.tailBlock_ne_newSV t v n h.symm
    · exact β.newSV_ne_tailSV _ _ _ _ h
  simp [h2]

theorem wCount_survives_tailSV_of_not_mem {w : TV c} {q₀ : Fin d} (hq₀ : q₀ ∉ β.vB w) :
    wCount β.regrowDatum β.Survives (β.tailSV w q₀) = 0 := by
  rw [wCount_survives]
  have h1 : ∀ F : NonDanglingEdge ψ,
      (if Incident β.regrowDatum (β.psiSE F.1) (β.tailSV w q₀) then 1 else 0) = 0 :=
    fun F ↦ ite_eq_right (β.incident_psiSE_tailSV _ _ _)
  rw [Fintype.sum_congr _ _ h1]
  have h2 : ∀ (t : TE c) (q : {q // q ∈ β.rowIdx t}),
      (if Incident β.regrowDatum (β.tailSE t q.1) (β.tailSV w q₀) then 1 else 0) = 0 := by
    intro t q
    refine ite_eq_right fun h ↦ ?_
    rcases (β.incident_tailSE_of_rowSet (β.rowIdx_sub_rowSet t q.2) _).mp h with h | h
    · exact β.tailBlock_ne_tailSV hq₀ h.symm
    · obtain ⟨rfl, h'⟩ := (β.tailSV_eq_blockSV_iff _ _ _).mp h
      exact hq₀ h'
  simp [h2]

/-- **The count of survivors at a block vertex**: one per path or bridge slot at it, two per leaf
edge. -/
theorem wCount_survives_blockSV (j : Fin k) (w : TailV (c j)) :
    wCount β.regrowDatum β.Survives (β.blockSV ⟨j, w⟩) =
      ∑ s ∈ incSlots w, (β.rowIdx ⟨j, s⟩).card := by
  classical
  rw [wCount_survives]
  have h1 : ∀ F : NonDanglingEdge ψ,
      (if Incident β.regrowDatum (β.psiSE F.1) (β.blockSV ⟨j, w⟩) then 1 else 0) = 0 :=
    fun F ↦ ite_eq_right (β.incident_psiSE_tailSV _ _ _)
  simp only [h1, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · have h2 : ∀ (s : CatSlot (c j)) (q : {q // q ∈ β.rowIdx ⟨j, s⟩}),
        (if Incident β.regrowDatum (β.tailSE ⟨j, s⟩ q.1) (β.blockSV ⟨j, w⟩) then 1 else 0) =
          if s ∈ incSlots w then 1 else 0 := by
      intro s q
      refine if_congr ?_ rfl rfl
      rw [β.incident_tailSE_blockSV (β.rowIdx_sub_rowSet _ q.2), tail_incident_iff]
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun s _ ↦ Finset.sum_eq_zero fun q _ ↦ ite_eq_right fun h ↦ ?_
    have h' := (β.incident_tailSE_blockSV (β.rowIdx_sub_rowSet _ q.2) ⟨j, w⟩).mp h
    exact hj' (tail_incident_mark c β.x h')
  · simp

theorem wCount_survives_spine (j : Fin k) (i : Fin (c j)) :
    wCount β.regrowDatum β.Survives (β.blockSV ⟨j, spine i⟩) = 3 := by
  rw [wCount_survives_blockSV, incSlots_spine]
  have h1 : path i.castSucc ∉ ({path i.succ, bridge i} : Finset (CatSlot (c j))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, path_inj, path_ne_bridge, or_false]
    intro h; have := congrArg Fin.val h; simp at this
  rw [Finset.sum_insert h1, Finset.sum_pair (path_ne_bridge _ _), card_rowIdx, card_rowIdx,
    card_rowIdx]
  simp

theorem wCount_survives_bulb (j : Fin k) (i : Fin (c j + 1)) :
    wCount β.regrowDatum β.Survives (β.blockSV ⟨j, bulb i⟩) = 3 := by
  rw [wCount_survives_blockSV, incSlots_bulb, Finset.sum_pair (inBridge_ne_loop _ _), card_rowIdx,
    card_rowIdx]
  simp [inBridge_ne_loop]

theorem wCount_survives_tip (j : Fin k) (i : Fin (c j + 1)) :
    wCount β.regrowDatum β.Survives (β.blockSV ⟨j, tip i⟩) = 2 := by
  rw [wCount_survives_blockSV, incSlots_tip, Finset.sum_singleton, card_rowIdx]
  simp

/-! ## 3.  The dictionary -/

variable (hψ : ψ.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
  (hMark : ∀ j, nonDanglingValency ψ (β.mark j) ≠ 0)

/-- Every source vertex over a tail vertex is a block vertex or a singleton. -/
theorem tailSV_cases (w : TV c) (q : Fin d) : β.tailSV w q = β.blockSV w ∨ q ∉ β.vB w := by
  by_cases hq : q ∈ β.vB w
  · exact Or.inl (β.tailSV_of_mem hq)
  · exact Or.inr hq

include hψ hMark in
/-- **No source vertex has exactly one surviving edge**: the witness of the dictionary. -/
theorem wCount_survives_ne_one (X : β.regrowDatum.SourceVertex) :
    wCount β.regrowDatum β.Survives X ≠ 1 := by
  rcases β.sourceVertex_cases X with ⟨Y, rfl⟩ | ⟨v, n, rfl⟩ | ⟨⟨j, w⟩, q, rfl⟩
  · rw [wCount_survives_psiSV]
    have hne := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one ψ hψ Y
    by_cases hm : β.markCount Y = 0
    · rw [hm, add_zero]; exact hne
    · obtain ⟨j, hj⟩ : ∃ j, β.mark j = Y := by
        by_contra hno
        push Not at hno
        apply hm
        unfold markCount
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun j _ ↦ hno j
      have := hMark j
      rw [hj] at this
      omega
  · rw [wCount_survives_newSV]; omega
  · rcases β.tailSV_cases ⟨j, w⟩ q with h | h
    · rw [h]
      rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [wCount_survives_spine]; omega
      · rw [wCount_survives_bulb]; omega
      · rw [wCount_survives_tip]; omega
    · rw [β.wCount_survives_tailSV_of_not_mem h]; omega

include hψ hMark in
/-- The survivors survive. -/
theorem not_isDangling_of_survives {E : β.regrowDatum.SourceEdge} (hE : β.Survives E) :
    ¬ IsDangling β.regrowDatum E :=
  not_isDangling_of_witness _ β.Survives (β.wCount_survives_ne_one hψ hMark) hE

include hψ hT hT0 hMark in
/-- **The old edges keep their status.** -/
theorem isDangling_psiSE_iff (F : ψ.SourceEdge) :
    IsDangling β.regrowDatum (β.psiSE F) ↔ IsDangling ψ F := by
  classical
  have hR := β.connected_regrowDatum hψ hT
  constructor
  · intro h
    by_contra hF
    exact β.not_isDangling_of_survives hψ hMark (Or.inl ⟨F, hF, rfl⟩) h
  · intro hF
    by_contra hnd
    refine not_isDangling_of_witness ψ (fun F' ↦ ¬ IsDangling β.regrowDatum (β.psiSE F'))
      (fun Y ↦ ?_) hnd hF
    by_cases hY : ∃ j, β.mark j = Y
    · obtain ⟨j, rfl⟩ := hY
      have hge : nonDanglingValency ψ (β.mark j) ≤
          wCount ψ (fun F' ↦ ¬ IsDangling β.regrowDatum (β.psiSE F')) (β.mark j) := by
        rw [nonDanglingValency_eq_wCount]
        exact wCount_le_of_imp _ _ fun F' _ h ↦
          β.not_isDangling_of_survives hψ hMark (Or.inl ⟨F', h, rfl⟩)
      have h1 := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one ψ hψ
        (β.mark j)
      have h2 := hMark j
      omega
    · push Not at hY
      have heq : wCount ψ (fun F' ↦ ¬ IsDangling β.regrowDatum (β.psiSE F')) Y =
          nonDanglingValency β.regrowDatum (β.psiSV Y) := by
        unfold wCount nonDanglingValency
        refine Finset.card_bij (fun F' _ ↦ β.psiSE F') ?_ ?_ ?_
        · intro F' hF'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF' ⊢
          exact ⟨hF'.1, (β.incident_psiSE_psiSV _ _).mpr hF'.2⟩
        · intro F₁ _ F₂ _ h
          exact β.psiSE_injective h
        · intro E hE
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
          rcases β.sourceEdge_cases E with ⟨F', rfl⟩ | ⟨ε, n, rfl⟩ | ⟨t, q, rfl⟩
          · refine ⟨F', ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hE.1, (β.incident_psiSE_psiSV _ _).mp hE.2⟩
          · exact absurd (β.isDangling_newSE hψ hT hT0 ε n) hE.1
          · by_cases hq : q ∈ β.rowSet t
            · exfalso
              rcases (β.incident_tailSE_of_rowSet hq _).mp hE.2 with h | h
              · obtain ⟨-, h'⟩ := (β.tailBlock_eq_psiSV_iff t Y).mp h.symm
                exact hY t.1 h'
              · exact β.psiSV_ne_tailSV _ _ _ h
            · exact absurd (β.isDangling_tailSE hψ hT hT0 hq) hE.1
      rw [heq]
      exact DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hR _

include hψ hT hT0 hMark in
/-- **The surviving edges of the regrowth are exactly `Survives`.** -/
theorem not_isDangling_iff (E : β.regrowDatum.SourceEdge) :
    ¬ IsDangling β.regrowDatum E ↔ β.Survives E := by
  constructor
  · intro h
    rcases β.sourceEdge_cases E with ⟨F, rfl⟩ | ⟨ε, n, rfl⟩ | ⟨t, q, rfl⟩
    · exact Or.inl ⟨F, fun hF ↦ h ((β.isDangling_psiSE_iff hψ hT hT0 hMark F).mpr hF), rfl⟩
    · exact absurd (β.isDangling_newSE hψ hT hT0 ε n) h
    · by_cases hq : q ∈ β.rowSet t
      · exact Or.inr ⟨t, q, hq, rfl⟩
      · exact absurd (β.isDangling_tailSE hψ hT hT0 hq) h
  · exact β.not_isDangling_of_survives hψ hMark

include hψ hT hT0 hMark in
theorem nonDanglingValency_eq_wCount_survives (X : β.regrowDatum.SourceVertex) :
    nonDanglingValency β.regrowDatum X = wCount β.regrowDatum β.Survives X := by
  rw [nonDanglingValency_eq_wCount]
  exact wCount_congr _ _ fun E _ ↦ β.not_isDangling_iff hψ hT hT0 hMark E

/-! ## 4.  The surviving valencies -/

include hψ hT hT0 hMark

theorem nonDanglingValency_psiSV (Y : ψ.SourceVertex) :
    nonDanglingValency β.regrowDatum (β.psiSV Y) = nonDanglingValency ψ Y + β.markCount Y := by
  rw [β.nonDanglingValency_eq_wCount_survives hψ hT hT0 hMark, wCount_survives_psiSV]

theorem nonDanglingValency_newSV (v : T.V) (n : N) :
    nonDanglingValency β.regrowDatum (β.newSV v n) = 0 := by
  rw [β.nonDanglingValency_eq_wCount_survives hψ hT hT0 hMark, wCount_survives_newSV]

theorem nonDanglingValency_tailSV_of_not_mem {w : TV c} {q : Fin d} (hq : q ∉ β.vB w) :
    nonDanglingValency β.regrowDatum (β.tailSV w q) = 0 := by
  rw [β.nonDanglingValency_eq_wCount_survives hψ hT hT0 hMark,
    wCount_survives_tailSV_of_not_mem _ hq]

theorem nonDanglingValency_spine (j : Fin k) (i : Fin (c j)) :
    nonDanglingValency β.regrowDatum (β.blockSV ⟨j, spine i⟩) = 3 := by
  rw [β.nonDanglingValency_eq_wCount_survives hψ hT hT0 hMark, wCount_survives_spine]

theorem nonDanglingValency_bulb (j : Fin k) (i : Fin (c j + 1)) :
    nonDanglingValency β.regrowDatum (β.blockSV ⟨j, bulb i⟩) = 3 := by
  rw [β.nonDanglingValency_eq_wCount_survives hψ hT hT0 hMark, wCount_survives_bulb]

theorem nonDanglingValency_tip (j : Fin k) (i : Fin (c j + 1)) :
    nonDanglingValency β.regrowDatum (β.blockSV ⟨j, tip i⟩) = 2 := by
  rw [β.nonDanglingValency_eq_wCount_survives hψ hT hT0 hMark, wCount_survives_tip]

end CatBranching

end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
