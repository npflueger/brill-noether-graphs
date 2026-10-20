module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowMatrix
public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowWindow
public import DraismaVargasMarkedCount.MarkedCountGeneral.Restriction

@[expose] public section

/-!
# Regrowth, part 10: the branching of a typed frame

The regrowth construction for a typed frame `κ` of type `lowerType c J` in degree `d - shed J`,
with slopes `s`.

* **The sheets** (`sheetEquiv`): `Fin (d - shed J) ⊕ Fin (shed J) ≃ Fin d`, the inverse of the
  decomposition `σ_B : Fin d ≃ Fin (d - shed J) ⊕ Fin (shed J)` of the sheets into old and
  new ones (through `finSumFinEquiv`); the `r`-th new sheet of tail `j` is
  `finSigmaFinEquiv ⟨j, r⟩`.
* **The chain at mark `j`** (`tailSheet`, `branching`): the window chain of `s j`, through the
  line-up of `s_1` sheets of the block `S` of the mark (in the order of `Fin (d - shed J)`; (D4′)
  gives `|S| ≥ s_1`), followed by the new sheets of tail `j`.

Proved here: all fields of `CatRegrow.CatBranching`, and the hypotheses of the regrowth lemmas
(Riemann--Hurwitz at the marks from (D4′), the marks distinct and of surviving valency two).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

namespace CatRegrow

noncomputable section

open DraismaVargas.Infrastructure CatSlot TailV
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}

/-! ## 1.  The sheets -/

/-- The shed sheets fit: `shed J ≤ d` at the headline degree. -/
theorem shed_le (hd : IsTailDegree n p c degree) (J : LowerIndex c) : shed J ≤ degree := by
  unfold IsTailDegree at hd
  unfold shed
  have h : ∀ j, 2 * (J j : ℕ) ≤ c j + 1 := fun j ↦ by have := (J j).2; omega
  have hsum : 2 * ∑ j, (J j : ℕ) ≤ ∑ j, (c j + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ ↦ h j
  omega

/-- **The sheets of the regrowth**: the old ones, then the new ones. -/
def sheetEquiv (hd : IsTailDegree n p c degree) (J : LowerIndex c) :
    Fin (degree - shed J) ⊕ Fin (shed J) ≃ Fin degree :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel (shed_le hd J)))

/-- The new sheet `r` of tail `j`. -/
def newSheet (J : LowerIndex c) (j : Fin k) (r : Fin (J j)) : Fin (shed J) :=
  finSigmaFinEquiv ⟨j, r⟩

theorem newSheet_injective (J : LowerIndex c) {j j' : Fin k} {r : Fin (J j)} {r' : Fin (J j')}
    (h : newSheet J j r = newSheet J j' r') : j = j' := by
  have := finSigmaFinEquiv.injective h
  exact congrArg Sigma.fst this

/-! ## 2.  The line-up at a mark -/

variable (hd : IsTailDegree n p c degree) (J : LowerIndex c)
  (κ : TypedFrame core mark (lowerType c J) (degree - shed J)) (s : SlopeData c J)

/-- The first slope at mark `j`: `s_1 = a_j - 2J_j + 1`. -/
def firstSlope (j : Fin k) : ℕ := (s j).1 0

theorem firstSlope_eq (j : Fin k) : firstSlope J s j = lowerType c J j + 1 := by
  have h := (s j).2.2.2.2 0 rfl
  unfold firstSlope lowerType
  have := (J j).2
  omega

/-- The block of mark `j` in `κ`. -/
def markBlock (j : Fin k) : Finset (Fin (degree - shed J)) :=
  (κ.data.vertexPartition (κ.markSource j).1.1).block (κ.markSource j).1.2

theorem firstSlope_le (j : Fin k) : firstSlope J s j ≤ (markBlock J κ j).card := by
  rw [firstSlope_eq]
  exact (κ.typed j).2

/-- **The line-up of `s_1` sheets of the block of mark `j`.** -/
def lineUp (j : Fin k) (r : Fin (firstSlope J s j)) : Fin (degree - shed J) :=
  ((markBlock J κ j).orderEmbOfFin rfl) (Fin.castLE (firstSlope_le J κ s j) r)

theorem lineUp_injective (j : Fin k) : Function.Injective (lineUp J κ s j) := fun _ _ h ↦
  Fin.castLE_injective _ (((markBlock J κ j).orderEmbOfFin rfl).injective h)

theorem lineUp_mem (j : Fin k) (r : Fin (firstSlope J s j)) : lineUp J κ s j r ∈ markBlock J κ j :=
  Finset.orderEmbOfFin_mem _ _ _

/-- **The sheets of tail `j`, lined up**: `s_1` sheets of the block of the mark, then the new sheets
of the tail. -/
def tailSheet (j : Fin k) (r : ℕ) : Fin degree :=
  if h : r < firstSlope J s j then old (sheetEquiv hd J) (lineUp J κ s j ⟨r, h⟩)
  else if h' : r - firstSlope J s j < J j then
    new (sheetEquiv hd J) (newSheet J j ⟨r - firstSlope J s j, h'⟩)
  else old (sheetEquiv hd J) ⟨0, κ.data.degree_pos⟩

theorem tailSheet_lt {j : Fin k} {r : ℕ} (h : r < firstSlope J s j) :
    tailSheet hd J κ s j r = old (sheetEquiv hd J) (lineUp J κ s j ⟨r, h⟩) := by
  unfold tailSheet; rw [dite_eq_left h]

theorem tailSheet_ge {j : Fin k} {r : ℕ} (h : firstSlope J s j ≤ r)
    (h' : r - firstSlope J s j < J j) :
    tailSheet hd J κ s j r = new (sheetEquiv hd J) (newSheet J j ⟨r - firstSlope J s j, h'⟩) := by
  unfold tailSheet; rw [dite_eq_right (by omega), dite_eq_left h']

theorem tailSheet_injOn (j : Fin k) :
    Set.InjOn (tailSheet hd J κ s j) (Set.Iio (firstSlope J s j + J j)) := by
  intro r hr r' hr' h
  simp only [Set.mem_Iio] at hr hr'
  by_cases h1 : r < firstSlope J s j <;> by_cases h2 : r' < firstSlope J s j
  · rw [tailSheet_lt hd J κ s h1, tailSheet_lt hd J κ s h2, old_inj] at h
    exact congrArg Fin.val (lineUp_injective J κ s j h)
  · rw [tailSheet_lt hd J κ s h1, tailSheet_ge hd J κ s (by omega) (by omega)] at h
    exact absurd h (old_ne_new _ _)
  · rw [tailSheet_ge hd J κ s (by omega) (by omega), tailSheet_lt hd J κ s h2] at h
    exact absurd h (new_ne_old _ _)
  · rw [tailSheet_ge hd J κ s (by omega) (by omega), tailSheet_ge hd J κ s (by omega) (by omega),
      new_inj] at h
    have := finSigmaFinEquiv.injective h
    have h' := congrArg (fun z : (Σ i : Fin k, Fin (J i)) ↦ (z.2 : ℕ)) this
    simp only at h'
    omega

theorem isSlopeSeq (j : Fin k) : IsSlopeSeq (c j + 1) (J j) (s j).1 := (s j).2

theorem firstSlope_add (j : Fin k) : firstSlope J s j + J j = (s j).1 0 + J j := rfl

/-- **The chain at mark `j`**: the window chain of the slopes through the line-up. -/
def chain (j : Fin k) : TailChain degree (c j) := windowChain (s j).1 (tailSheet hd J κ s j)

theorem chain_valid (j : Fin k) : (chain hd J κ s j).Valid :=
  windowChain_valid (tailSheet_injOn hd J κ s j) (isSlopeSeq J s j) rfl

theorem chain_P_bound (j : Fin k) (i : Fin (c j + 1)) :
    winLo (s j).1 i + (s j).1 i ≤ firstSlope J s j + J j :=
  winHi_le_M (isSlopeSeq J s j) rfl i

theorem mem_chain_P {j : Fin k} {i : Fin (c j + 1)} {q : Fin degree} :
    q ∈ (chain hd J κ s j).P i ↔ ∃ r, winLo (s j).1 i ≤ r ∧ r < winLo (s j).1 i + (s j).1 i ∧
      tailSheet hd J κ s j r = q := mem_window

theorem mem_chain_P_zero {j : Fin k} {q : Fin degree} :
    q ∈ (chain hd J κ s j).P 0 ↔ ∃ r, r < firstSlope J s j ∧ tailSheet hd J κ s j r = q := by
  rw [mem_chain_P, winLo_zero]
  simp only [zero_le, true_and, zero_add]
  rfl

/-- The sheets of the chain past `P_1` are the new sheets of the tail. -/
theorem fresh_chain {j : Fin k} {i : Fin (c j + 1)} {q : Fin degree}
    (hq : q ∈ (chain hd J κ s j).P i) (hq0 : q ∉ (chain hd J κ s j).P 0) :
    ∃ r : Fin (J j), q = new (sheetEquiv hd J) (newSheet J j r) := by
  obtain ⟨r, hr1, hr2, rfl⟩ := (mem_chain_P hd J κ s).mp hq
  have hb := chain_P_bound J s j i
  by_cases h : r < firstSlope J s j
  · exact absurd ((mem_chain_P_zero hd J κ s).mpr ⟨r, h, rfl⟩) hq0
  · exact ⟨⟨r - firstSlope J s j, by omega⟩, tailSheet_ge hd J κ s (by omega) (by omega)⟩

/-- **Every new sheet of tail `j` enters the chain**, at the first window reaching it. -/
theorem new_mem_chain (j : Fin k) (r : Fin (J j)) :
    ∃ i, new (sheetEquiv hd J) (newSheet J j r) ∈ (chain hd J κ s j).P i := by
  classical
  have hs := isSlopeSeq J s j
  set R := firstSlope J s j + r.val with hR
  have hEx : ∃ m, ∃ h : m < c j + 1, R < winLo (s j).1 ⟨m, h⟩ + (s j).1 ⟨m, h⟩ := by
    refine ⟨c j, by omega, ?_⟩
    have h1 := two_mul_winLo hs (Fin.last (c j))
    have h2 := slope_last hs
    have h3 := slope_first hs
    have : (⟨c j, by omega⟩ : Fin (c j + 1)) = Fin.last (c j) := rfl
    rw [this]
    simp only [Fin.val_last] at h1
    unfold firstSlope at hR
    have := r.2
    omega
  obtain ⟨hlt, hmem⟩ := Nat.find_spec hEx
  set m := Nat.find hEx with hm
  have hpos : m ≠ 0 := by
    intro h0
    have : (⟨m, hlt⟩ : Fin (c j + 1)) = 0 := Fin.ext h0
    rw [this, winLo_zero, zero_add] at hmem
    unfold firstSlope at hR
    omega
  have hprev : ¬ R < winLo (s j).1 ⟨m - 1, by omega⟩ + (s j).1 ⟨m - 1, by omega⟩ := fun h ↦
    Nat.find_min hEx (show m - 1 < m by omega) ⟨by omega, h⟩
  have hstep := winLo_succ hs ⟨m - 1, by omega⟩
  have e1 : (⟨m - 1, by omega⟩ : Fin (c j)).succ = ⟨m, hlt⟩ := Fin.ext (by simp; omega)
  have e2 : (⟨m - 1, by omega⟩ : Fin (c j)).castSucc = ⟨m - 1, by omega⟩ := rfl
  rw [e1, e2] at hstep
  have hp := hs.1 ⟨m, hlt⟩
  refine ⟨⟨m, hlt⟩, (mem_chain_P hd J κ s).mpr ⟨R, ?_, hmem, ?_⟩⟩
  · rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rw [tailSheet_ge hd J κ s (by omega) (by omega)]
    congr 2
    exact Fin.ext (by simp [hR])

/-! ## 3.  The branching -/

/-- **The caterpillar branching of a typed frame**. -/
def branching : CatBranching κ.data (Fin (shed J)) degree c where
  e := sheetEquiv hd J
  mark := κ.markSource
  chain := chain hd J κ s
  valid := chain_valid hd J κ s
  P0_sub j q hq := by
    obtain ⟨r, hr, rfl⟩ := (mem_chain_P_zero hd J κ s).mp hq
    refine ⟨lineUp J κ s j ⟨r, hr⟩, tailSheet_lt hd J κ s hr, ?_⟩
    exact ((κ.data.vertexPartition _).mem_block_iff _ _).mp (lineUp_mem J κ s j _)
  fresh j i q hq hq0 := by
    obtain ⟨r, rfl⟩ := fresh_chain hd J κ s hq hq0
    exact ⟨_, rfl⟩
  fresh_disjoint j j' i i' q hq hq' hq0 := by
    obtain ⟨r, rfl⟩ := fresh_chain hd J κ s hq hq0
    by_cases h0 : new (sheetEquiv hd J) (newSheet J j r) ∈ (chain hd J κ s j').P 0
    · obtain ⟨r', hr', h⟩ := (mem_chain_P_zero hd J κ s).mp h0
      rw [tailSheet_lt hd J κ s hr'] at h
      exact absurd h (old_ne_new _ _)
    · obtain ⟨r', h⟩ := fresh_chain hd J κ s hq' h0
      rw [new_inj] at h
      exact newSheet_injective J h
  new_used nn := by
    obtain ⟨⟨j, r⟩, rfl⟩ := finSigmaFinEquiv.surjective nn
    obtain ⟨i, hi⟩ := new_mem_chain hd J κ s j r
    exact ⟨j, i, hi⟩

@[simp] theorem branching_mark (j : Fin k) : (branching hd J κ s).mark j = κ.markSource j := rfl
@[simp] theorem branching_x (j : Fin k) : (branching hd J κ s).x j = (κ.markSource j).1.1 := rfl

theorem card_P_zero (j : Fin k) :
    (((branching hd J κ s).chain j).P 0).card = lowerType c J j + 1 := by
  rw [← firstSlope_eq J s j]
  exact card_windowChain_P (tailSheet_injOn hd J κ s j) (isSlopeSeq J s j) rfl 0

/-! ## 4.  The hypotheses of the regrowth lemmas -/

theorem hψ : κ.data.Connected := κ.fullDim.valid.1
theorem hT : graph_connected κ.target := κ.fullDim.targetConnected
theorem hT0 : genus κ.target = 0 := κ.fullDim.targetGenus

theorem hMark (j : Fin k) : nonDanglingValency κ.data ((branching hd J κ s).mark j) ≠ 0 := by
  rw [branching_mark, κ.fullDim.markValency _ (mem_markSet _ j)]; omega

/-- The marks of a typed frame are distinct source vertices. -/
theorem hInj (hc : IsMarkedCubic core mark) : Function.Injective (branching hd J κ s).mark := by
  intro i j h
  apply hc.injective
  rw [← κ.ident.vertex_mark i, ← κ.ident.vertex_mark j]
  congr 1
  exact Subtype.ext h

/-- Riemann--Hurwitz at the marks: (D4′) gives `r_ψ ≥ a' = s_1 - 1`. -/
theorem hRam (j : Fin k) :
    (((branching hd J κ s).chain j).P 0).card - 1 ≤
      markRamification κ.data ((branching hd J κ s).mark j) := by
  rw [card_P_zero, branching_mark]
  have := (κ.typed j).1
  push_cast
  linarith

end

end CatRegrow

end DraismaVargas.Count.MarkedCountGeneral
