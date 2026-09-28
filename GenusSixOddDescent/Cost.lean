import Utilities.Subdivision.EdgeSumDescent
import Utilities.Subdivision.SlotIntervalFiring

/-!
# Slot cost and the odd-scale chip bound

For an effective divisor, `offsetSum` is the sum of interior chip offsets from
one end of each slot, with multiplicity. `cost` measures its distance to `Nℤ`,
and `Delta` is the sum over slots. For signed divisors the definition first
truncates the offset sum with `Int.toNat`; the distance interpretation and
orientation invariance are asserted only for effective divisors.

`NotSelected A` says that every effective representative of `A` costs at least
`N`. At scale three each slot costs zero or one, so `Delta` counts the slots whose
offset sum is not divisible by three (`Delta_three`), the bad-edge count of
`Utilities.Gonality.bnExists_one_four_of_badEdges_le_two`. At larger scales a
weighted sum is necessary.

`Delta_eq_edgeSumCost` identifies this divisor cost with the fine-chip-family
cost of the generic rounding engine, under a unit-presentation hypothesis.
`bnExists_one_four_of_Delta_lt` applies that engine to a cheap representative.

The key odd-scale bound is `Delta D ≤ (N/2) * #chipEdges D`. For odd `N`,
`2*(N/2) < N`, so nonselection forces at least three chip-carrying slots and
leaves at most one core chip in degree four. For even `N` this argument does
not apply; this observation alone is no assertion of failure of descent.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph

/-! ## Arithmetic of `modDist` -/

/-- The per-chip ceiling: the distance to the nearest multiple of `N` is at most
`⌊N/2⌋`.  This is the one inequality of the whole chain that knows the scale;
`2 * (N / 2) < N` exactly when `N` is odd. -/
theorem modDist_le_half {N : ℕ} (hN : 0 < N) (σ : ℕ) : modDist N σ ≤ N / 2 := by
  have h : σ % N < N := Nat.mod_lt _ hN
  unfold modDist
  omega

theorem modDist_zero (N : ℕ) : modDist N 0 = 0 := by
  unfold modDist
  simp

/-- **`modDist` is orientation-free.**  If `σ + τ` is a multiple of `N` then `σ`
and `τ` are at the same distance from `N * ℤ`.  Reversing the orientation of a
unit slot replaces its offset sum `σ_e` by `k * N - σ_e`, where `k` counts
interior chips. For an original slot of length `L` the formula is
`k * (N * L) - σ_e`. Effective divisors have nonnegative sums from both ends,
so this identity makes their `cost` independent of the chosen orientation. -/
theorem modDist_eq_of_add_eq_mul {N : ℕ} (hN : 0 < N) {σ τ k : ℕ}
    (h : σ + τ = k * N) : modDist N τ = modDist N σ := by
  have ha : σ % N < N := Nat.mod_lt _ hN
  have hb : τ % N < N := Nat.mod_lt _ hN
  have hdvd : N ∣ (σ % N + τ % N) := by
    have h1 : (σ + τ) % N = 0 := by rw [h]; exact Nat.mul_mod_left k N
    have h2 : (σ % N + τ % N) % N = 0 := by rwa [← Nat.add_mod]
    exact Nat.dvd_of_mod_eq_zero h2
  obtain ⟨c, hc⟩ := hdvd
  have hclt : c < 2 := by
    by_contra hcon
    have hle : N * 2 ≤ N * c := Nat.mul_le_mul (le_refl N) (by omega)
    omega
  unfold modDist
  interval_cases c <;> omega

/-- The reversal form of `modDist_eq_of_add_eq_mul`. -/
theorem modDist_mul_sub {N : ℕ} (hN : 0 < N) (k : ℕ) {σ : ℕ} (hσ : σ ≤ k * N) :
    modDist N (k * N - σ) = modDist N σ :=
  modDist_eq_of_add_eq_mul (k := k) hN (by omega)

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Chips, offset sums and the cost weight -/

/-- The number of chips of a fine divisor at core vertices, with multiplicity. -/
def coreChipCount (D : CFDiv (spec.scale N hN).graph) : ℤ :=
  ∑ v : Fin n, D ((spec.scale N hN).coreVertex v)

/-- The number of chips of a fine divisor interior to slot `e`, with
multiplicity. -/
def edgeChipCount (D : CFDiv (spec.scale N hN).graph) (e : Fin p) : ℤ :=
  ∑ j : Fin ((spec.scale N hN).length e - 1),
    D ((spec.scale N hN).interiorVertex e j)

/-- The **chip slots** of a fine divisor: those carrying an interior chip. -/
def chipEdges (D : CFDiv (spec.scale N hN).graph) : Finset (Fin p) :=
  Finset.univ.filter fun e => spec.edgeChipCount N hN D e ≠ 0

/-- `σ_e(D)`: the total offset, measured from the **tail** of `e`, of the chips
of `D` interior to slot `e`. Reversal replaces this sum by
`k * (N * spec.length e) - σ_e`, where `k` is the interior chip count.
For unit slots this is `k * N - σ_e`. For effective divisors, nonnegativity
and `modDist_mul_sub` give the orientation independence of cost. -/
def offsetSum (D : CFDiv (spec.scale N hN).graph) (e : Fin p) : ℤ :=
  ∑ j : Fin ((spec.scale N hN).length e - 1),
    ((j.val + 1 : ℕ) : ℤ) * D ((spec.scale N hN).interiorVertex e j)

/-- For an effective divisor, the distance of the slot's offset sum to `Nℤ`.
The definition is total on signed divisors but truncates negative sums to zero;
its distance interpretation requires nonnegativity. At scale three the cost is
zero or one (`cost_three`); at any scale it is at most `⌊N/2⌋`. -/
def cost (D : CFDiv (spec.scale N hN).graph) (e : Fin p) : ℕ :=
  modDist N (spec.offsetSum N hN D e).toNat

/-- **The cost weight `Δ`** of a fine divisor: the total slot cost.  This is the
budget of `EdgeSumDescent.rank_ge_of_edge_sum`, by `Delta_eq_edgeSumCost`. -/
def Delta (D : CFDiv (spec.scale N hN).graph) : ℕ :=
  ∑ e : Fin p, spec.cost N hN D e

/-- **(¬S)** at a general scale: every effective representative of the class of
`A` costs at least `N`.  Its negation, the *selection property* (S) — some
effective representative costs less than `N` — is what the descent consumes. -/
def NotSelected (A : CFDiv (spec.scale N hN).graph) : Prop :=
  ∀ D : CFDiv (spec.scale N hN).graph, effective D →
    linear_equiv (spec.scale N hN).graph A D → N ≤ spec.Delta N hN D

/-! ### `slotPoint` forms of the two slot sums -/

/-- Reindexing a sum over the interior offsets of a slot of a unit presentation
by the offsets `0 < t < N`. -/
theorem sum_interior_eq_sum_Ioo {M : Type*} [AddCommMonoid M] (hunit : spec.IsUnit)
    (e : Fin p) (f : ℕ → M) :
    ∑ j : Fin ((spec.scale N hN).length e - 1), f (j.val + 1)
      = ∑ t ∈ Finset.Ioo 0 N, f t := by
  have hL : (spec.scale N hN).length e = N := spec.length_scale N hN hunit e
  have hIoo : Finset.Ioo 0 N = Finset.Ico 1 N := by
    ext t
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  rw [Fin.sum_univ_eq_sum_range (fun j => f (j + 1)) ((spec.scale N hN).length e - 1),
    hL, hIoo, Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

/-- `edgeChipCount` in `slotPoint` coordinates. -/
theorem edgeChipCount_eq_sum_slotPoint (hunit : spec.IsUnit)
    (D : CFDiv (spec.scale N hN).graph) (e : Fin p) :
    spec.edgeChipCount N hN D e = ∑ t ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN e t) := by
  have h : ∀ j : Fin ((spec.scale N hN).length e - 1),
      D ((spec.scale N hN).interiorVertex e j) = D (spec.slotPoint N hN e (j.val + 1)) :=
    fun j => by rw [spec.interiorVertex_eq_slotPoint N hN hunit e j]
  unfold edgeChipCount
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  exact spec.sum_interior_eq_sum_Ioo N hN hunit e (fun t => D (spec.slotPoint N hN e t))

/-- `offsetSum` in `slotPoint` coordinates. -/
theorem offsetSum_eq_sum_slotPoint (hunit : spec.IsUnit)
    (D : CFDiv (spec.scale N hN).graph) (e : Fin p) :
    spec.offsetSum N hN D e
      = ∑ t ∈ Finset.Ioo 0 N, (t : ℤ) * D (spec.slotPoint N hN e t) := by
  have h : ∀ j : Fin ((spec.scale N hN).length e - 1),
      ((j.val + 1 : ℕ) : ℤ) * D ((spec.scale N hN).interiorVertex e j)
        = ((j.val + 1 : ℕ) : ℤ) * D (spec.slotPoint N hN e (j.val + 1)) :=
    fun j => by rw [spec.interiorVertex_eq_slotPoint N hN hunit e j]
  unfold offsetSum
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  exact spec.sum_interior_eq_sum_Ioo N hN hunit e
    (fun t => (t : ℤ) * D (spec.slotPoint N hN e t))

/-! ## The counting bound: cost at most `⌊N/2⌋` per chip slot -/

theorem offsetSum_nonneg {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    (e : Fin p) : 0 ≤ spec.offsetSum N hN D e :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Int.natCast_nonneg _) (hD _)

theorem edgeChipCount_nonneg {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    (e : Fin p) : 0 ≤ spec.edgeChipCount N hN D e :=
  Finset.sum_nonneg fun _ _ => hD _

/-- The degree of a fine divisor splits into its core chips and its slot
chips. -/
theorem deg_eq_coreChipCount_add_sum (D : CFDiv (spec.scale N hN).graph) :
    deg D = spec.coreChipCount N hN D + ∑ e : Fin p, spec.edgeChipCount N hN D e := by
  show (∑ v : (spec.scale N hN).graph.V, D v) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  rfl

/-- On an effective divisor a chip-free slot is chip-free vertex by vertex. -/
theorem interior_eq_zero_of_edgeChipCount_zero
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) {e : Fin p}
    (he : spec.edgeChipCount N hN D e = 0)
    (j : Fin ((spec.scale N hN).length e - 1)) :
    D ((spec.scale N hN).interiorVertex e j) = 0 := by
  have hnn : ∀ k ∈ (Finset.univ : Finset (Fin ((spec.scale N hN).length e - 1))),
      0 ≤ D ((spec.scale N hN).interiorVertex e k) := fun k _ => hD _
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp he j (Finset.mem_univ j)

theorem edgeChipCount_eq_zero_of_not_mem {D : CFDiv (spec.scale N hN).graph}
    {e : Fin p} (he : e ∉ spec.chipEdges N hN D) :
    spec.edgeChipCount N hN D e = 0 := by
  simpa [chipEdges] using he

/-- **A slot of positive cost is a chip slot.** -/
theorem cost_eq_zero_of_not_mem_chipEdges {D : CFDiv (spec.scale N hN).graph}
    (hD : effective D) {e : Fin p} (he : e ∉ spec.chipEdges N hN D) :
    spec.cost N hN D e = 0 := by
  have hzero : spec.edgeChipCount N hN D e = 0 :=
    spec.edgeChipCount_eq_zero_of_not_mem N hN he
  have hoff : spec.offsetSum N hN D e = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [spec.interior_eq_zero_of_edgeChipCount_zero N hN hD hzero j]; ring
  unfold cost
  rw [hoff]
  simpa using modDist_zero N

theorem cost_le_half (D : CFDiv (spec.scale N hN).graph) (e : Fin p) :
    spec.cost N hN D e ≤ N / 2 :=
  modDist_le_half hN _

/-- **The counting bound.**  The cost weight is at most `⌊N/2⌋` per chip slot. -/
theorem Delta_le_mul_card_chipEdges {D : CFDiv (spec.scale N hN).graph}
    (hD : effective D) :
    spec.Delta N hN D ≤ (N / 2) * (spec.chipEdges N hN D).card := by
  classical
  have h1 : spec.Delta N hN D = ∑ e ∈ spec.chipEdges N hN D, spec.cost N hN D e := by
    unfold Delta
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro e _ he
    exact spec.cost_eq_zero_of_not_mem_chipEdges N hN hD he
  rw [h1]
  calc ∑ e ∈ spec.chipEdges N hN D, spec.cost N hN D e
      ≤ ∑ _e ∈ spec.chipEdges N hN D, N / 2 :=
        Finset.sum_le_sum fun e _ => spec.cost_le_half N hN D e
    _ = (spec.chipEdges N hN D).card * (N / 2) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (N / 2) * (spec.chipEdges N hN D).card := Nat.mul_comm _ _

theorem one_le_edgeChipCount {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    {e : Fin p} (he : e ∈ spec.chipEdges N hN D) :
    1 ≤ spec.edgeChipCount N hN D e := by
  have h0 := spec.edgeChipCount_nonneg N hN hD e
  have hne : spec.edgeChipCount N hN D e ≠ 0 := by simpa [chipEdges] using he
  omega

/-- `#chipEdges ≤ ∑ edgeChipCount`. -/
theorem card_chipEdges_le_sum {D : CFDiv (spec.scale N hN).graph} (hD : effective D) :
    ((spec.chipEdges N hN D).card : ℤ) ≤ ∑ e : Fin p, spec.edgeChipCount N hN D e := by
  classical
  calc ((spec.chipEdges N hN D).card : ℤ) = ∑ _e ∈ spec.chipEdges N hN D, (1 : ℤ) := by
        simp
    _ ≤ ∑ e ∈ spec.chipEdges N hN D, spec.edgeChipCount N hN D e :=
        Finset.sum_le_sum fun e he => spec.one_le_edgeChipCount N hN hD he
    _ = ∑ e : Fin p, spec.edgeChipCount N hN D e :=
        Finset.sum_subset (Finset.subset_univ _)
          fun _e _ he => spec.edgeChipCount_eq_zero_of_not_mem N hN he

/-- **`#core chips + #chip-slots ≤ deg`**. -/
theorem coreChipCount_add_card_chipEdges_le {D : CFDiv (spec.scale N hN).graph}
    (hD : effective D) :
    spec.coreChipCount N hN D + ((spec.chipEdges N hN D).card : ℤ) ≤ deg D := by
  have hle := spec.card_chipEdges_le_sum N hN hD
  rw [spec.deg_eq_coreChipCount_add_sum N hN D]
  omega

/-- **Three chip slots.**  For *odd* `N` the per-slot ceiling `⌊N/2⌋ = (N-1)/2`
satisfies `2 * ⌊N/2⌋ < N`, so two chip slots cannot pay the budget `N`.  This is
the only place the parity of `N` is used, and it is false for even `N`. -/
theorem three_le_card_chipEdges (hodd : Odd N) (h3N : 3 ≤ N)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    (hDelta : N ≤ spec.Delta N hN D) :
    3 ≤ (spec.chipEdges N hN D).card := by
  by_contra hcon
  have hle : (spec.chipEdges N hN D).card ≤ 2 := by omega
  have h1 := spec.Delta_le_mul_card_chipEdges N hN hD
  have h2 : (N / 2) * (spec.chipEdges N hN D).card ≤ (N / 2) * 2 :=
    Nat.mul_le_mul (le_refl (N / 2)) hle
  have hodd' : N % 2 = 1 := Nat.odd_iff.mp hodd
  have hpos : 0 < N / 2 := by omega
  omega

/-- **At most one core chip**, at odd scale: an effective degree-four divisor
paying the full budget carries at most one chip at a core vertex, since it has at
least three chip slots (`three_le_card_chipEdges`). -/
theorem coreChipCount_le_one (hodd : Odd N) (h3N : 3 ≤ N)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) (hdeg : deg D = 4)
    (hDelta : N ≤ spec.Delta N hN D) :
    spec.coreChipCount N hN D ≤ 1 := by
  have hcard := spec.three_le_card_chipEdges N hN hodd h3N hD hDelta
  have hcard' : (3 : ℤ) ≤ ((spec.chipEdges N hN D).card : ℤ) := by exact_mod_cast hcard
  have hcount := spec.coreChipCount_add_card_chipEdges_le N hN hD
  rw [hdeg] at hcount
  omega

/-- `three_le_card_chipEdges` in the form `(¬S)` supplies. -/
theorem three_le_card_chipEdges_of_notSelected (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    (hDA : linear_equiv (spec.scale N hN).graph A D) :
    3 ≤ (spec.chipEdges N hN D).card :=
  spec.three_le_card_chipEdges N hN hodd h3N hD (hNS D hD hDA)

/-- `coreChipCount_le_one` in the form `(¬S)` supplies. -/
theorem coreChipCount_le_one_of_notSelected (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) (hdeg : deg D = 4)
    (hDA : linear_equiv (spec.scale N hN).graph A D) :
    spec.coreChipCount N hN D ≤ 1 :=
  spec.coreChipCount_le_one N hN hodd h3N hD hdeg (hNS D hD hDA)

/-! ## The bridge to `EdgeSumDescent`: `Δ` is the edge-sum cost -/

/-- The contribution of one fine vertex to the offset sum of the unique coarse
step of the slot `e` of a unit presentation. -/
private def unitStepContribution (e : Fin p) (y : (spec.scale N hN).Vertex) : ℕ :=
  Sum.elim (fun _ : spec.Vertex => 0)
    (fun c : spec.Chip N =>
      if c.coarseStep = (⟨e, ⟨0, spec.length_pos e⟩⟩ : spec.Step) then c.offset else 0)
    (spec.roundData N hN y)

/-- On the `N`-fold refinement of a unit presentation the rounding data of an
interior vertex is the chip on the slot's single coarse step at offset
`j + 1` — the offset measured from the tail, matching `offsetSum`. -/
private theorem roundData_interior (hunit : spec.IsUnit) (f : Fin p)
    (k : Fin ((spec.scale N hN).length f - 1)) :
    ∃ c : spec.Chip N,
      spec.roundData N hN ((spec.scale N hN).interiorVertex f k) = Sum.inr c ∧
        c.edge = f ∧ c.step = 0 ∧ c.offset = k.val + 1 := by
  have hlenN : (spec.scale N hN).length f = N := spec.length_scale N hN hunit f
  have hk := k.isLt
  have hk1 : k.val + 1 < N := by omega
  have hmod : (k.val + 1) % N = k.val + 1 := Nat.mod_eq_of_lt hk1
  have hdiv : (k.val + 1) / N = 0 := Nat.div_eq_of_lt hk1
  have hne : (k.val + 1) % N ≠ 0 := by omega
  refine ⟨{ edge := f, step := (k.val + 1) / N,
            step_lt := by rw [hdiv]; exact spec.length_pos f,
            offset := (k.val + 1) % N, offset_pos := by omega, offset_lt := by omega,
            toRight := decide (N < 2 * ((k.val + 1) % N)) }, ?_, rfl, hdiv, hmod⟩
  rw [show (spec.scale N hN).interiorVertex f k
    = (Sum.inr ⟨f, k⟩ : (spec.scale N hN).Vertex) from rfl]
  simp only [roundData]
  rw [dif_neg hne]

private theorem unitStepContribution_core (e : Fin p) (w : Fin n) :
    spec.unitStepContribution N hN e ((spec.scale N hN).coreVertex w) = 0 := rfl

private theorem unitStepContribution_interior (hunit : spec.IsUnit) (e f : Fin p)
    (k : Fin ((spec.scale N hN).length f - 1)) :
    spec.unitStepContribution N hN e ((spec.scale N hN).interiorVertex f k)
      = if f = e then k.val + 1 else 0 := by
  obtain ⟨c, hc, hedge, hstep, hoff⟩ := roundData_interior spec N hN hunit f k
  have hcs : c.coarseStep = (⟨f, ⟨0, spec.length_pos f⟩⟩ : spec.Step) := by
    unfold Chip.coarseStep
    subst hedge
    rw [show (⟨c.step, c.step_lt⟩ : Fin (spec.length c.edge))
      = ⟨0, spec.length_pos c.edge⟩ from Fin.ext hstep]
  show Sum.elim _ _ (spec.roundData N hN _) = _
  rw [hc]
  simp only [Sum.elim_inr]
  rw [hcs, hoff]
  by_cases hfe : f = e
  · subst hfe
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hfe, if_neg (fun hc2 => hfe (congrArg Sigma.fst hc2))]

private theorem contribution_eq (hunit : spec.IsUnit) (e : Fin p)
    (y : (spec.scale N hN).Vertex) :
    ((spec.unitStepContribution N hN e y : ℕ) : ℤ)
      = ∑ j : Fin ((spec.scale N hN).length e - 1),
          ((j.val + 1 : ℕ) : ℤ) *
            (if (spec.scale N hN).interiorVertex e j = y then (1 : ℤ) else 0) := by
  rcases y with w | ⟨f, k⟩
  · rw [show (Sum.inl w : (spec.scale N hN).Vertex)
      = (spec.scale N hN).coreVertex w from rfl,
      unitStepContribution_core spec N hN e w]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [if_neg (by simp [interiorVertex, coreVertex]), mul_zero]
  · rw [show (Sum.inr ⟨f, k⟩ : (spec.scale N hN).Vertex)
      = (spec.scale N hN).interiorVertex f k from rfl,
      unitStepContribution_interior spec N hN hunit e f k]
    by_cases hfe : f = e
    · subst hfe
      rw [if_pos rfl]
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl, mul_one]
      · intro j _ hjk
        have hne : (spec.scale N hN).interiorVertex f j
            ≠ (spec.scale N hN).interiorVertex f k := by
          intro hc
          refine hjk (Fin.ext ?_)
          exact congrArg (fun s : (spec.scale N hN).Interior => s.2.val)
            (Sum.inr.inj hc)
        rw [if_neg hne, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · rw [if_neg hfe]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg (by
        intro hc
        exact hfe (congrArg Sigma.fst (Sum.inr.inj hc)).symm), mul_zero]

/-- The divisor-level offset sum of a family of fine chips is the family-level
`stepOffsetSum` of `EdgeSumDescent.lean`, slot by slot. -/
theorem offsetSum_eq_vertexStepOffsetSum (hunit : spec.IsUnit) {ι : Type*} [Fintype ι]
    (ys : ι → (spec.scale N hN).Vertex) (e : Fin p) :
    ((spec.vertexStepOffsetSum N hN ys
        (⟨e, ⟨0, spec.length_pos e⟩⟩ : spec.Step) : ℕ) : ℤ)
      = spec.offsetSum N hN (∑ i, one_chip (ys i)) e := by
  classical
  have hLHS : spec.vertexStepOffsetSum N hN ys
      (⟨e, ⟨0, spec.length_pos e⟩⟩ : spec.Step)
        = ∑ i : ι, spec.unitStepContribution N hN e (ys i) := by
    have hsub : ∑ i : {i : ι // (spec.roundData N hN (ys i)).isRight = true},
        spec.unitStepContribution N hN e (ys i.1)
          = ∑ i : ι, spec.unitStepContribution N hN e (ys i) := by
      rw [← Finset.sum_subtype (Finset.univ.filter
          fun i : ι => (spec.roundData N hN (ys i)).isRight = true)
        (fun x => by simp) (fun i => spec.unitStepContribution N hN e (ys i))]
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      have hP : ¬ ((spec.roundData N hN (ys i)).isRight = true) := by simpa using hi
      show Sum.elim _ _ (spec.roundData N hN (ys i)) = 0
      cases hcase : spec.roundData N hN (ys i) with
      | inl x => rfl
      | inr c => rw [hcase] at hP; simp at hP
    rw [← hsub]
    show ∑ i ∈ spec.stepChips N (spec.vertexChips N hN ys) _,
      (spec.vertexChips N hN ys i).offset = _
    rw [stepChips, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = Sum.elim _ _ (spec.roundData N hN (ys i.1))
    rw [← Sum.inr_getRight (spec.roundData N hN (ys i.1)) i.2]
    rfl
  have hRHS : spec.offsetSum N hN (∑ i, one_chip (ys i)) e
      = ∑ i : ι, ∑ j : Fin ((spec.scale N hN).length e - 1),
          ((j.val + 1 : ℕ) : ℤ) *
            (if (spec.scale N hN).interiorVertex e j = ys i then (1 : ℤ) else 0) := by
    have h1 : ∀ j : Fin ((spec.scale N hN).length e - 1),
        ((j.val + 1 : ℕ) : ℤ) *
            (∑ i, one_chip (ys i) : CFDiv (spec.scale N hN).graph)
              ((spec.scale N hN).interiorVertex e j)
          = ∑ i : ι, ((j.val + 1 : ℕ) : ℤ) *
              (if (spec.scale N hN).interiorVertex e j = ys i then (1 : ℤ) else 0) := by
      intro j
      rw [Finset.sum_apply, Finset.mul_sum]
      rfl
    show ∑ j : Fin ((spec.scale N hN).length e - 1),
        ((j.val + 1 : ℕ) : ℤ) *
          (∑ i, one_chip (ys i) : CFDiv (spec.scale N hN).graph)
            ((spec.scale N hN).interiorVertex e j) = _
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  rw [hLHS, hRHS, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => contribution_eq spec N hN hunit e (ys i)

/-- **The bridge lemma.**  The cost weight of the divisor carried by a family of
fine chips is the family's `edgeSumCost`, so `(¬S)` and the descent budget are
literally the same number. -/
theorem Delta_eq_edgeSumCost (hunit : spec.IsUnit) {ι : Type*} [Fintype ι]
    (ys : ι → (spec.scale N hN).Vertex) :
    spec.Delta N hN (∑ i, one_chip (ys i)) = spec.edgeSumCost N hN ys := by
  classical
  unfold Delta edgeSumCost
  refine Finset.sum_nbij'
    (fun e : Fin p => (⟨e, ⟨0, spec.length_pos e⟩⟩ : spec.Step))
    (fun st : spec.Step => st.1)
    (fun a _ => Finset.mem_univ _) (fun a _ => Finset.mem_univ _)
    (fun a _ => rfl) ?_ ?_
  · rintro ⟨f, kk⟩ -
    have hlen1 : spec.length f = 1 := hunit f
    have hk : kk.val = 0 := by have := kk.isLt; omega
    have hkk : kk = (⟨0, spec.length_pos f⟩ : Fin (spec.length f)) := Fin.ext hk
    show (⟨f, ⟨0, spec.length_pos f⟩⟩ : spec.Step) = ⟨f, kk⟩
    rw [hkk]
  · intro e _
    show spec.cost N hN (∑ i, one_chip (ys i)) e
      = modDist N (spec.vertexStepOffsetSum N hN ys
          (⟨e, ⟨0, spec.length_pos e⟩⟩ : spec.Step))
    unfold cost
    rw [← spec.offsetSum_eq_vertexStepOffsetSum N hN hunit ys e, Int.toNat_natCast]

/-! ## The descent -/

private theorem embed_zero_aux : spec.embed N hN 0 = 0 := by
  funext y
  unfold embed
  simp

/-- **`w¹₄` from an `N`-fold subdivision of cost less than `N`.**  Four fine
chips spanning a divisor of rank at least one and of total slot cost `< N`
produce a degree-four divisor of rank at least one on the coarse graph.

This is `EdgeSumDescent.rank_ge_of_edge_sum` read through
`Delta_eq_edgeSumCost`; it generalizes the scale-three statement
`Utilities.Gonality.bnExists_one_four_of_badEdges_le_two`. -/
theorem bnExists_one_four_of_Delta_lt (hunit : spec.IsUnit)
    (ys : Fin 4 → (spec.scale N hN).graph.V)
    (hDelta : spec.Delta N hN (∑ i, one_chip (ys i)) < N)
    (hrank : rank (spec.scale N hN).graph (∑ i, one_chip (ys i)) ≥ 1) :
    BNExists spec.graph 1 4 := by
  have hcost : (spec.edgeSumCost N hN ys : ℤ) < (N : ℤ) := by
    rw [← spec.Delta_eq_edgeSumCost N hN hunit ys]
    exact_mod_cast hDelta
  have hrank' : rank (spec.scale N hN).graph
      (spec.embed N hN 0 + ∑ i, one_chip (ys i)) ≥ 1 := by
    rw [spec.embed_zero_aux N hN, zero_add]
    exact hrank
  obtain ⟨D, hDdeg, hDrank, -⟩ := spec.rank_ge_of_edge_sum N hN ys 0 1 hcost hrank'
  refine ⟨D, ?_, hDrank⟩
  rw [hDdeg]
  simp

/-! ## Sanity: the specialization to `N = 3` -/

/-- At `N = 3` the cost of a slot is the indicator that its offset sum is not
divisible by three. -/
theorem cost_three (h3 : 0 < 3) {D : CFDiv (spec.scale 3 h3).graph} (hD : effective D)
    (e : Fin p) :
    spec.cost 3 h3 D e = if spec.offsetSum 3 h3 D e % 3 = 0 then 0 else 1 := by
  have hnn := spec.offsetSum_nonneg 3 h3 hD e
  have hiff : (spec.offsetSum 3 h3 D e).toNat % 3 = 0
      ↔ spec.offsetSum 3 h3 D e % 3 = 0 := by omega
  unfold cost
  rw [modDist_three]
  by_cases h : spec.offsetSum 3 h3 D e % 3 = 0
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

/-- At `N = 3` the cost weight counts the bad slots. -/
theorem Delta_three (h3 : 0 < 3) {D : CFDiv (spec.scale 3 h3).graph}
    (hD : effective D) :
    spec.Delta 3 h3 D
      = (Finset.univ.filter fun e : Fin p => spec.offsetSum 3 h3 D e % 3 ≠ 0).card := by
  classical
  unfold Delta
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [spec.cost_three h3 hD e]
  by_cases h : spec.offsetSum 3 h3 D e % 3 = 0 <;> simp [h]

end Spec

end SubdivisionGraph

end Utilities.Certificate

namespace Utilities.Gonality

open Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-- **`w¹₄` from an `N`-fold regular subdivision of cost less than `N`**, in the
shape `GenusSixOddDescent.descent_odd` consumes: the general-`N` form of
`bnExists_one_four_of_badEdges_le_two`. -/
theorem bnExists_one_four_of_Delta_lt (G : CFGraph) (N : ℕ) (hN : 0 < N)
    (ys : Fin 4 → (regularSubdivision G N hN).V)
    (hDelta : (UnitSubdivisionPresentation.spec G).Delta N hN (∑ i, one_chip (ys i)) < N)
    (hrank : rank (regularSubdivision G N hN) (∑ i, one_chip (ys i)) ≥ 1) :
    BNExists G 1 4 := by
  have hunit : (UnitSubdivisionPresentation.spec G).IsUnit := fun _ => rfl
  have hspec := (UnitSubdivisionPresentation.spec G).bnExists_one_four_of_Delta_lt
    N hN hunit ys hDelta hrank
  exact ((UnitSubdivisionPresentation.laplacianEquiv G).bnExists_iff 1 4).mpr hspec

end Utilities.Gonality
