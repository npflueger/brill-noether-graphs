module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowChain
public import DraismaVargasMarkedCount.MarkedCountGeneral.Ballot

@[expose] public section

/-!
# Regrowth, part 9: the canonical chain of a slope sequence

The regrowth chooses `P_1 ⊆ S` with `|P_1| = s_1`, and inductively `P_{i+1} := P_i ∪ {n_r}` at
an ascent, `P_{i+1} := P_i` minus one element at a descent. One choice for all slope sequences: line
up the `s_1` chosen sheets of `S` and then the new sheets, `sh 0, sh 1, …, sh (s_1 + J - 1)`, and
take for `P_i` the **window** `sh [lo_i, lo_i + s_i)`: an ascent moves the top of the window up by
one (adding the next new sheet), a descent moves the bottom up by one (dropping the oldest sheet).
With `2 lo_i + s_i = i + s_1` (`two_mul_winLo`) everything is arithmetic.

`windowChain s sh` is this `TailChain`, with `Q_i` the two lowest sheets of `S_i` and every block
named by its lowest sheet; `windowChain_valid` proves `TailChain.Valid` for any `sh` injective on
`[0, s_1 + J)`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.CatRegrow

open CatSlot TailV

/-! ## 1.  Slope sequences -/

section Slopes

variable {c J : ℕ} {s : Fin (c + 1) → ℕ}

theorem slope_step (hs : IsSlopeSeq (c + 1) J s) (i : Fin c) :
    s i.succ = s i.castSucc + 1 ∨ s i.castSucc = s i.succ + 1 :=
  hs.2.2.1 i.castSucc i.succ (by simp)

theorem slope_first (hs : IsSlopeSeq (c + 1) J s) : s 0 + 2 * J = c + 2 :=
  hs.2.2.2 0 rfl

theorem slope_last (hs : IsSlopeSeq (c + 1) J s) : s (Fin.last c) = 2 :=
  hs.2.1 _ (by simp)

/-- The bottom of the window at level `i`. -/
def winLo (s : Fin (c + 1) → ℕ) (i : Fin (c + 1)) : ℕ := (i.val + s 0 - s i) / 2

theorem two_mul_winLo (hs : IsSlopeSeq (c + 1) J s) (i : Fin (c + 1)) :
    2 * winLo s i + s i = i.val + s 0 := by
  suffices H : ∀ (m : ℕ) (hm : m < c + 1), 2 * winLo s ⟨m, hm⟩ + s ⟨m, hm⟩ = m + s 0 from
    H i.val i.2
  intro m
  induction m with
  | zero => intro hm; unfold winLo; simp
  | succ m ih =>
    intro hm
    have h := ih (by omega)
    have hstep := slope_step hs ⟨m, by omega⟩
    have e1 : (⟨m, by omega⟩ : Fin c).succ = ⟨m + 1, hm⟩ := rfl
    have e2 : (⟨m, by omega⟩ : Fin c).castSucc = ⟨m, by omega⟩ := rfl
    rw [e1, e2] at hstep
    unfold winLo at h ⊢
    simp only at h ⊢
    omega

theorem winLo_zero : winLo s 0 = 0 := by unfold winLo; simp

/-- **One step of the window**: at an ascent the bottom stays, at a descent it moves up by one. -/
theorem winLo_succ (hs : IsSlopeSeq (c + 1) J s) (i : Fin c) :
    (s i.succ = s i.castSucc + 1 ∧ winLo s i.succ = winLo s i.castSucc) ∨
      (s i.castSucc = s i.succ + 1 ∧ winLo s i.succ = winLo s i.castSucc + 1) := by
  have h1 := two_mul_winLo hs i.succ
  have h2 := two_mul_winLo hs i.castSucc
  simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
  rcases slope_step hs i with h | h <;> [left; right] <;> refine ⟨h, ?_⟩ <;> omega

theorem winLo_mono (hs : IsSlopeSeq (c + 1) J s) : Monotone (winLo s) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  rcases winLo_succ hs i with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

theorem winHi_mono (hs : IsSlopeSeq (c + 1) J s) : Monotone fun i ↦ winLo s i + s i := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  rcases winLo_succ hs i with ⟨h1, h⟩ | ⟨h1, h⟩ <;> omega

/-- The windows stay inside `[0, s_1 + J)`. -/
theorem winHi_le (hs : IsSlopeSeq (c + 1) J s) (i : Fin (c + 1)) :
    winLo s i + s i ≤ s 0 + J := by
  have h1 := two_mul_winLo hs i
  have h2 := hs.add_le i
  have h3 := slope_first hs
  omega

end Slopes

/-! ## 2.  The window chain -/

section Window

variable {d c J : ℕ} (s : Fin (c + 1) → ℕ) (sh : ℕ → Fin d)

/-- The window `[lo, lo + len)`, through `sh`. -/
def window (lo len : ℕ) : Finset (Fin d) := (Finset.Ico lo (lo + len)).image sh

/-- **The window chain of a slope sequence.** -/
def windowChain : TailChain d c where
  P i := window sh (winLo s i) (s i)
  Q i := window sh (winLo s i.castSucc) 2
  vA w := match w with
    | Sum.inl (Sum.inl i) => sh (winLo s i.castSucc)
    | Sum.inl (Sum.inr i) => sh (winLo s i)
    | Sum.inr i => sh (winLo s i)
  eA t := match t with
    | Sum.inl i => sh (winLo s i)
    | Sum.inr (Sum.inl i) => sh (winLo s i.castSucc)
    | Sum.inr (Sum.inr _) => sh 0

variable {s sh}

theorem mem_window {lo len : ℕ} {q : Fin d} :
    q ∈ window sh lo len ↔ ∃ r, lo ≤ r ∧ r < lo + len ∧ sh r = q := by
  unfold window
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨r, ⟨h1, h2⟩, h3⟩; exact ⟨r, h1, h2, h3⟩
  · rintro ⟨r, h1, h2, h3⟩; exact ⟨r, ⟨h1, h2⟩, h3⟩

theorem sh_mem_window {lo len r : ℕ} (h1 : lo ≤ r) (h2 : r < lo + len) :
    sh r ∈ window sh lo len := mem_window.mpr ⟨r, h1, h2, rfl⟩

variable {M : ℕ} (hInj : Set.InjOn sh (Set.Iio M))

include hInj in
theorem card_window {lo len : ℕ} (h : lo + len ≤ M) : (window sh lo len).card = len := by
  unfold window
  rw [Finset.card_image_of_injOn, Nat.card_Ico]
  · omega
  · intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    exact hInj (show a < M by omega) (show b < M by omega) hab

include hInj in
theorem mem_window_iff {lo len r : ℕ} (h : lo + len ≤ M) (hr : r < M) :
    sh r ∈ window sh lo len ↔ lo ≤ r ∧ r < lo + len := by
  constructor
  · intro hmem
    obtain ⟨r', h1, h2, h3⟩ := mem_window.mp hmem
    have : r' = r := hInj (show r' < M by omega) hr h3
    subst this
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact sh_mem_window h1 h2

theorem window_subset {lo len lo' len' : ℕ} (h1 : lo' ≤ lo) (h2 : lo + len ≤ lo' + len') :
    window sh lo len ⊆ window sh lo' len' := by
  intro q hq
  obtain ⟨r, hr1, hr2, rfl⟩ := mem_window.mp hq
  exact sh_mem_window (by omega) (by omega)

variable (hs : IsSlopeSeq (c + 1) J s) (hM : M = s 0 + J)

include hs hM in
theorem winHi_le_M (i : Fin (c + 1)) : winLo s i + s i ≤ M := hM ▸ winHi_le hs i

include hs hM in
theorem winQ_le_M (i : Fin c) : winLo s i.castSucc + 2 ≤ M := by
  have h := winHi_le_M hs hM i.succ
  have h' := winHi_le_M hs hM i.castSucc
  have hp := hs.1 i.castSucc
  have hp' := hs.1 i.succ
  rcases winLo_succ hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

include hInj hs hM in
/-- **The window chain is a valid tail chain.** -/
theorem windowChain_valid : (windowChain s sh).Valid where
  card_P_last := by
    change (window sh _ _).card = 2
    rw [card_window hInj (winHi_le_M hs hM _), slope_last hs]
  card_Q i := by
    change (window sh _ _).card = 2
    rw [card_window hInj (winQ_le_M hs hM i)]
  P_nonempty i := ⟨_, sh_mem_window (le_refl _) (by have := hs.1 i; omega)⟩
  step i := by
    change (window sh _ _ ⊆ window sh _ _ ∧ (window sh _ _).card = (window sh _ _).card + 1) ∨
      (window sh _ _ ⊆ window sh _ _ ∧ (window sh _ _).card = (window sh _ _).card + 1)
    rw [card_window hInj (winHi_le_M hs hM _), card_window hInj (winHi_le_M hs hM _)]
    rcases winLo_succ hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨window_subset (by omega) (by omega), h1⟩
    · exact Or.inr ⟨window_subset (by omega) (by omega), h1⟩
  Q_sub i := by
    intro q hq
    obtain ⟨r, hr1, hr2, rfl⟩ := mem_window.mp hq
    change sh r ∈ window sh _ _ ∪ window sh _ _
    rw [Finset.mem_union]
    have hp := hs.1 i.castSucc
    have hp' := hs.1 i.succ
    rcases winLo_succ hs i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hr : r < winLo s i.castSucc + s i.castSucc
      · exact Or.inl (sh_mem_window hr1 hr)
      · exact Or.inr (sh_mem_window (by omega) (by omega))
    · exact Or.inl (sh_mem_window hr1 (by omega))
  vA_mem w := by
    rcases TailV.cases w with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · change sh _ ∈ window sh _ _ ∪ window sh _ _
      exact Finset.mem_union_left _ (sh_mem_window (le_refl _) (by have := hs.1 i.castSucc; omega))
    · change sh (winLo s i) ∈ (windowChain s sh).R i
      induction i using Fin.lastCases with
      | last =>
        rw [TailChain.R_last]
        exact sh_mem_window (le_refl _) (by have := hs.1 (Fin.last c); omega)
      | cast i =>
        rw [TailChain.R_castSucc]
        exact sh_mem_window (le_refl _) (by omega)
    · change sh (winLo s i) ∈ (windowChain s sh).R i
      induction i using Fin.lastCases with
      | last =>
        rw [TailChain.R_last]
        exact sh_mem_window (le_refl _) (by have := hs.1 (Fin.last c); omega)
      | cast i =>
        rw [TailChain.R_castSucc]
        exact sh_mem_window (le_refl _) (by omega)
  eA_anchored t := by
    rcases slot_cases t with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact anchored_of_mem (sh_mem_window (le_refl _) (by have := hs.1 i; omega))
    · exact anchored_of_mem (sh_mem_window (le_refl _) (by omega))
    · exact anchored_empty _
  convex q i₁ i₂ i₃ h12 h23 hq1 hq3 := by
    obtain ⟨r, hr1, hr2, rfl⟩ := mem_window.mp hq1
    have hrM : r < M := lt_of_lt_of_le hr2 (winHi_le_M hs hM i₁)
    change sh r ∈ window sh _ _ at hq3 ⊢
    rw [mem_window_iff hInj (winHi_le_M hs hM _) hrM] at hq3 ⊢
    have hlo := winLo_mono hs h23
    have hhi := winHi_mono hs h12
    simp only at hhi
    exact ⟨by omega, by omega⟩

include hInj hs hM in
theorem card_windowChain_P (i : Fin (c + 1)) : ((windowChain s sh).P i).card = s i :=
  card_window hInj (winHi_le_M hs hM i)

theorem windowChain_P_zero : (windowChain s sh).P 0 = window sh 0 (s 0) := by
  change window sh (winLo s 0) (s 0) = _
  rw [winLo_zero]

end Window

end DraismaVargas.Count.MarkedCountGeneral.CatRegrow
