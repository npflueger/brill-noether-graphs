module

public import DraismaVargasMarkedCount.MarkedCountGeneral.CorrAdjust

@[expose] public section

/-!
# The inverse laws, part 2: every new sheet enters at one ascent

In a caterpillar branching every
new sheet enters exactly one chain at exactly one ascent (`entry_exists`, `entry_unique`), and
every ascent of every chain lets exactly one new sheet in (`entry_surj`, `entry_injective`); this
is the regrowth side of the fact that the index-one trees `D_r` split off by a restriction
correspond bijectively to the ascents of the slope sequence.
So two branchings with the same slopes have their new sheets matched by the ascent at which they
enter (`newMatch`, `entry_newMatch`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV

namespace TailChain

variable {d c : ℕ} (ch : TailChain d c)

/-- An ascent of the chain: the next block is one larger. -/
def IsAscent (i : Fin c) : Prop := (ch.P i.succ).card = (ch.P i.castSucc).card + 1

/-- The sheet `q` enters the chain at the step `i`. -/
def Enters (q : Fin d) (i : Fin c) : Prop := q ∈ ch.P i.succ ∧ q ∉ ch.P i.castSucc

variable {ch}

theorem Valid.isAscent_of_enters (h : ch.Valid) {q : Fin d} {i : Fin c} (hq : ch.Enters q i) :
    ch.IsAscent i := by
  rcases h.step i with ⟨-, hc⟩ | ⟨hsub, -⟩
  · exact hc
  · exact absurd (hsub hq.1) hq.2

theorem Valid.subset_of_isAscent (h : ch.Valid) {i : Fin c} (ha : ch.IsAscent i) :
    ch.P i.castSucc ⊆ ch.P i.succ := by
  rcases h.step i with ⟨hsub, -⟩ | ⟨-, hc⟩
  · exact hsub
  · unfold IsAscent at ha; omega

/-- At an ascent exactly one sheet enters. -/
theorem Valid.exists_enters (h : ch.Valid) {i : Fin c} (ha : ch.IsAscent i) :
    ∃ q, ch.Enters q i := by
  classical
  have hsub := h.subset_of_isAscent ha
  have : (ch.P i.succ \ ch.P i.castSucc).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]; unfold IsAscent at ha; omega
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp this
  have hmem : q ∈ ch.P i.succ \ ch.P i.castSucc := by rw [hq]; exact Finset.mem_singleton_self q
  exact ⟨q, (Finset.mem_sdiff.mp hmem).1, (Finset.mem_sdiff.mp hmem).2⟩

theorem Valid.enters_unique (h : ch.Valid) {i : Fin c} {q q' : Fin d} (hq : ch.Enters q i)
    (hq' : ch.Enters q' i) : q = q' := by
  classical
  have ha := h.isAscent_of_enters hq
  have hsub := h.subset_of_isAscent ha
  have : (ch.P i.succ \ ch.P i.castSucc).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]; unfold IsAscent at ha; omega
  exact Finset.card_le_one.mp this.le q (Finset.mem_sdiff.mpr hq) q' (Finset.mem_sdiff.mpr hq')

/-- A sheet enters a chain at most once (convexity). -/
theorem Valid.enters_index_unique (h : ch.Valid) {q : Fin d} {i i' : Fin c} (hq : ch.Enters q i)
    (hq' : ch.Enters q i') : i = i' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `q ∈ P (i+1)`, `q ∉ P i'` with `i + 1 ≤ i'`, `q ∈ P (i'+1)`
    have := h.convex q i.succ i'.castSucc i'.succ (Fin.le_def.mpr (by simp; omega))
      (Fin.le_def.mpr (by simp)) hq.1 hq'.1
    exact hq'.2 this
  · have := h.convex q i'.succ i.castSucc i.succ (Fin.le_def.mpr (by simp; omega))
      (Fin.le_def.mpr (by simp)) hq'.1 hq.1
    exact hq.2 this

/-- A sheet entering the chain is not in `P_1`. -/
theorem Valid.not_mem_zero_of_enters (h : ch.Valid) {q : Fin d} {i : Fin c} (hq : ch.Enters q i) :
    q ∉ ch.P 0 := fun h0 ↦
  hq.2 (h.convex q 0 i.castSucc i.succ (Fin.zero_le _) (Fin.le_def.mpr (by simp)) h0 hq.1)

/-- A sheet of the chain outside `P_1` entered at some step before. -/
theorem Valid.exists_enters_of_mem (_h : ch.Valid) {q : Fin d} {i : Fin (c + 1)}
    (hq : q ∈ ch.P i) (hq0 : q ∉ ch.P 0) : ∃ i', ch.Enters q i' ∧ i'.val < i.val := by
  classical
  have hEx : ∃ m, ∃ hm : m < c + 1, q ∈ ch.P ⟨m, hm⟩ := ⟨i.val, i.2, hq⟩
  obtain ⟨hlt, hmem⟩ := Nat.find_spec hEx
  have hpos : Nat.find hEx ≠ 0 := by
    intro h0
    apply hq0
    have : (⟨Nat.find hEx, hlt⟩ : Fin (c + 1)) = 0 := Fin.ext (by simpa using h0)
    rw [← this]; exact hmem
  refine ⟨⟨Nat.find hEx - 1, by omega⟩, ⟨?_, ?_⟩, ?_⟩
  · have : (⟨Nat.find hEx - 1, by omega⟩ : Fin c).succ = ⟨Nat.find hEx, hlt⟩ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [this]; exact hmem
  · intro h'
    exact Nat.find_min hEx (show Nat.find hEx - 1 < Nat.find hEx by omega) ⟨by omega, h'⟩
  · have := Nat.find_min' hEx ⟨i.2, hq⟩
    simp only
    omega

end TailChain

namespace CatBranching

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c)

/-- The new sheet `n` enters chain `j` at the step `i`. -/
def EntersAt (n : N) (j : Fin k) (i : Fin (c j)) : Prop := (β.chain j).Enters (new β.e n) i

theorem entry_exists (n : N) : ∃ j i, β.EntersAt n j i := by
  obtain ⟨j, i, hi⟩ := β.new_used n
  have hq0 : new β.e n ∉ (β.chain j).P 0 := fun h ↦ by
    obtain ⟨i', h', -⟩ := β.P0_sub j _ h
    exact new_ne_old _ _ h'
  obtain ⟨i', hi', -⟩ := (β.valid j).exists_enters_of_mem hi hq0
  exact ⟨j, i', hi'⟩

theorem entry_unique {n : N} {j j' : Fin k} {i : Fin (c j)} {i' : Fin (c j')}
    (h : β.EntersAt n j i) (h' : β.EntersAt n j' i') : j = j' ∧ HEq i i' := by
  have hj : j = j' := β.fresh_disjoint j j' i.succ i'.succ _ h.1 h'.1
    ((β.valid j).not_mem_zero_of_enters h)
  subst hj
  exact ⟨rfl, heq_of_eq ((β.valid j).enters_index_unique h h')⟩

/-- **The ascent at which a new sheet enters.** -/
def entry (n : N) : Σ j, Fin (c j) :=
  ⟨(β.entry_exists n).choose, (β.entry_exists n).choose_spec.choose⟩

theorem entersAt_entry (n : N) : β.EntersAt n (β.entry n).1 (β.entry n).2 :=
  (β.entry_exists n).choose_spec.choose_spec

theorem entry_eq {n : N} {j : Fin k} {i : Fin (c j)} (h : β.EntersAt n j i) :
    β.entry n = ⟨j, i⟩ := by
  obtain ⟨hj, hi⟩ := β.entry_unique (β.entersAt_entry n) h
  exact Sigma.ext hj hi

theorem entry_injective : Function.Injective β.entry := by
  intro n n' h
  have h1 := β.entersAt_entry n
  have h2 := β.entersAt_entry n'
  rw [h] at h1
  exact new_injective ((β.valid _).enters_unique h1 h2)

/-- **Every ascent lets one new sheet in.** -/
theorem entry_surj {j : Fin k} {i : Fin (c j)} (ha : (β.chain j).IsAscent i) :
    ∃ n, β.entry n = ⟨j, i⟩ := by
  obtain ⟨q, hq⟩ := (β.valid j).exists_enters ha
  obtain ⟨n, rfl⟩ := β.fresh j i.succ q hq.1 ((β.valid j).not_mem_zero_of_enters hq)
  exact ⟨n, β.entry_eq hq⟩

theorem isAscent_entry (n : N) : (β.chain (β.entry n).1).IsAscent (β.entry n).2 :=
  (β.valid _).isAscent_of_enters (β.entersAt_entry n)

end CatBranching

/-! ## Matching the new sheets of two branchings -/

section Match

variable {T : CFGraph.{0}} {d' d k : ℕ} {N N' : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β₁ : CatBranching ψ N d c) (β₂ : CatBranching ψ N' d c)
  (hcard : ∀ j i, ((β₁.chain j).P i).card = ((β₂.chain j).P i).card)

include hcard in
theorem isAscent_iff (j : Fin k) (i : Fin (c j)) :
    (β₁.chain j).IsAscent i ↔ (β₂.chain j).IsAscent i := by
  unfold TailChain.IsAscent
  rw [hcard, hcard]

/-- The new sheet of `β₂` entering where `n` enters in `β₁`. -/
def matchFun (n : N) : N' :=
  (β₂.entry_surj ((isAscent_iff β₁ β₂ hcard _ _).mp (β₁.isAscent_entry n))).choose

theorem entry_matchFun (n : N) : β₂.entry (matchFun β₁ β₂ hcard n) = β₁.entry n :=
  (β₂.entry_surj ((isAscent_iff β₁ β₂ hcard _ _).mp (β₁.isAscent_entry n))).choose_spec

/-- **The matching of the new sheets** by the ascent at which they enter. -/
def newMatch : N ≃ N' where
  toFun := matchFun β₁ β₂ hcard
  invFun := matchFun β₂ β₁ (fun j i ↦ (hcard j i).symm)
  left_inv n := by
    apply β₁.entry_injective
    rw [entry_matchFun, entry_matchFun]
  right_inv n := by
    apply β₂.entry_injective
    rw [entry_matchFun, entry_matchFun]

theorem entry_newMatch (n : N) : β₂.entry (newMatch β₁ β₂ hcard n) = β₁.entry n :=
  entry_matchFun β₁ β₂ hcard n

end Match


end

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
