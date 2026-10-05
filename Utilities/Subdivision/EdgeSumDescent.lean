module

public import Utilities.Subdivision.SquareRootDescent
public import Mathlib.Tactic

@[expose] public section

/-!
# Edge-sum descent: choosing the rounding flags to minimise the step budget

`Utilities/Subdivision/SubdivisionChipDescent.lean` rounds chips on an `N`-fold
refinement to the ends of their coarse steps and charges each step the absolute
value of the *signed* sum `stepCost` of its chips' costs; the descent
`rank_ge_of_rank_scale_ge_cost` needs `∑ step, |stepCost step| < N`.  The
descents of `OddSubdivisionDescent.lean` (nearest rounding) and
`SquareRootDescent.lean` (the `Chip.double` split) fix the flags first and then
bound the resulting cost.  This file does the opposite: it chooses the flags to
minimise the cost, and so gets the sharp budget.

The point is that `Chip.toRight` is a **free per-chip flag**:

  `signedCost c = if c.toRight then N - c.offset else -c.offset`,

so a chip of offset `o` may be charged `-o` *or* `N - o`, and both values are
`≡ -o (mod N)`.  On a coarse step carrying `k` interior chips of offsets
`o₁, …, o_k` (with multiplicity) and total `σ = ∑ oᵢ`, flagging exactly `j` of
them to the right gives `stepCost = N * j - σ`; as `j` runs over `0, …, k` the
achievable step costs are exactly the arithmetic progression
`{-σ + N * j : 0 ≤ j ≤ k}` of step `N`, which straddles `0` because
`0 ≤ σ ≤ k * (N - 1) < k * N` when `k ≥ 1`.  Hence

  `min over flags of |stepCost| = dist(σ, N * ℤ) = min (σ % N) (N - σ % N)`,

and `rightTarget N σ` names a `j` achieving it.  `exists_flags_stepCost` is the
resulting **flag-selection lemma**: an arbitrary family of chips can be
re-flagged, without moving any chip, so that every step is charged exactly
`modDist N σ_step`.  Feeding that into the descent engine gives
`rank_ge_of_edge_sum`, in which the only hypothesis on a family of fine chips is
the *edge sum* condition `∑ step, dist(σ_step, N * ℤ) < N`.

At `N = 3` the distance `dist(σ, 3ℤ)` is `0` or `1`, so the budget reads
"**at most two bad steps**", a step being bad when `3 ∤ σ_step`; on the unit
subdivision presentation of a `CFGraph` the steps are the edges of `G`, and
`bnExists_one_four_of_badEdges_le_two` packages the `r = 1`, `d = 4` case.

The edge-sum descent and its `N = 3` form are used by the genus-six
odd-subdivision descent.
-/

namespace Utilities.Certificate.SubdivisionGraph

open Finset

/-! ## The arithmetic of one step -/

/-- The distance from `σ` to the nearest multiple of `N`, as a natural number;
it is `0` exactly when `N ∣ σ`. -/
def modDist (N σ : ℕ) : ℕ := min (σ % N) (N - σ % N)

/-- The number of chips to flag to the right on a step whose interior chips
have total offset `σ`: the nearest multiple of `N` to `σ` is `N * rightTarget N σ`. -/
def rightTarget (N σ : ℕ) : ℕ := if 2 * (σ % N) ≤ N then σ / N else σ / N + 1

theorem modDist_eq_zero_iff {N σ : ℕ} (hN : 0 < N) : modDist N σ = 0 ↔ σ % N = 0 := by
  have h : σ % N < N := Nat.mod_lt _ hN
  unfold modDist
  omega

/-- **The achieved distance.**  Flagging `rightTarget N σ` chips to the right on
a step of total offset `σ` charges that step exactly `modDist N σ`. -/
theorem abs_mul_rightTarget_sub {N : ℕ} (hN : 0 < N) (σ : ℕ) :
    |(N : ℤ) * (rightTarget N σ : ℤ) - (σ : ℤ)| = (modDist N σ : ℤ) := by
  obtain ⟨q, hq⟩ : ∃ q, σ / N = q := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, σ % N = ρ := ⟨_, rfl⟩
  have hlt : ρ < N := hρ ▸ Nat.mod_lt _ hN
  have hsum : N * q + ρ = σ := by rw [← hq, ← hρ]; exact Nat.div_add_mod σ N
  have hsumZ : (N : ℤ) * (q : ℤ) + (ρ : ℤ) = (σ : ℤ) := by exact_mod_cast hsum
  have hρZ : (ρ : ℤ) ≤ (N : ℤ) := by exact_mod_cast hlt.le
  unfold rightTarget modDist
  rw [hq, hρ]
  split_ifs with hc
  · rw [Nat.min_eq_left (by omega),
      show (N : ℤ) * (q : ℤ) - (σ : ℤ) = -(ρ : ℤ) by linarith,
      abs_neg, abs_of_nonneg (Int.natCast_nonneg ρ)]
  · rw [Nat.min_eq_right (by omega), Nat.cast_sub hlt.le,
      show (N : ℤ) * ((q + 1 : ℕ) : ℤ) - (σ : ℤ) = (N : ℤ) - (ρ : ℤ) by push_cast; linarith]
    exact abs_of_nonneg (by linarith)

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## The offset sum of a coarse step -/

/-- The total interior offset of the chips of a family lying on a coarse step:
`σ_step` in the module docstring. -/
def stepOffsetSum {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (step : spec.Step) : ℕ :=
  ∑ i ∈ spec.stepChips N chips step, (chips i).offset

theorem mem_stepChips_iff {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (step : spec.Step) (i : ι) :
    i ∈ spec.stepChips N chips step ↔ (chips i).coarseStep = step := by
  simp [stepChips]

/-- **The step cost as a function of the flags.**  A step whose chips have total
offset `σ` and `j` of which are flagged to the right is charged `N * j - σ`. -/
theorem stepCost_eq_mul_card_sub {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (step : spec.Step) :
    spec.stepCost N chips step
      = (N : ℤ) * ((((spec.stepChips N chips step).filter
            fun i => (chips i).toRight = true).card : ℕ) : ℤ)
        - (spec.stepOffsetSum N chips step : ℤ) := by
  classical
  have hpt : ∀ i : ι, (chips i).signedCost
      = (if (chips i).toRight then (N : ℤ) else 0) - ((chips i).offset : ℤ) := by
    intro i
    unfold Chip.signedCost
    split_ifs <;> ring
  unfold stepCost stepOffsetSum
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- The offset sum of a step is at most `card * (N - 1)`: every interior chip has
offset at most `N - 1`. -/
private theorem stepOffsetSum_le {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (step : spec.Step) :
    spec.stepOffsetSum N chips step ≤ (spec.stepChips N chips step).card * (N - 1) := by
  unfold stepOffsetSum
  calc ∑ i ∈ spec.stepChips N chips step, (chips i).offset
      ≤ ∑ _i ∈ spec.stepChips N chips step, (N - 1) :=
        Finset.sum_le_sum fun i _ => by have := (chips i).offset_lt; omega
    _ = (spec.stepChips N chips step).card * (N - 1) := by
        rw [Finset.sum_const, smul_eq_mul]

include hN in
/-- The target number of right-flagged chips never exceeds the number of chips on
the step, so it can actually be realised. -/
private theorem rightTarget_le_card {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (step : spec.Step) :
    rightTarget N (spec.stepOffsetSum N chips step)
      ≤ (spec.stepChips N chips step).card := by
  set k := (spec.stepChips N chips step).card with hk
  set σ := spec.stepOffsetSum N chips step with hσ
  have hbound : σ ≤ k * (N - 1) := spec.stepOffsetSum_le N chips step
  have hdm : N * (σ / N) + σ % N = σ := Nat.div_add_mod σ N
  have hmod : σ % N < N := Nat.mod_lt _ hN
  unfold rightTarget
  split_ifs with hc
  · have h1 : N * (σ / N) ≤ σ := Nat.le.intro hdm
    have h2 : k * (N - 1) ≤ N * k := by
      calc k * (N - 1) ≤ k * N := Nat.mul_le_mul_left k (by omega)
        _ = N * k := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left (h1.trans (hbound.trans h2)) hN
  · have hρpos : 0 < σ % N := by omega
    have hmodle : σ % N ≤ σ := Nat.mod_le σ N
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, Nat.zero_mul] at hbound; omega
      · exact h
    have hlt : σ < k * N :=
      hbound.trans_lt ((Nat.mul_lt_mul_left hkpos).mpr (by omega))
    have : σ / N < k := (Nat.div_lt_iff_lt_mul hN).mpr hlt
    omega

/-! ## The flag-selection lemma -/

include hN in
/-- **Flag selection.**  Any family of interior chips can be re-flagged — the
chips themselves, hence the fine divisor they carry, are untouched — so that
every coarse step is charged exactly the distance from its total offset to the
nearest multiple of `N`.

This is the sharp form of the budget of `rank_ge_of_rank_scale_ge_cost`: on each
step the achievable values of `stepCost` are `{-σ + N * j : 0 ≤ j ≤ k}`, and
`rightTarget N σ` picks the `j` nearest to `σ / N`. -/
theorem exists_flags_stepCost {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) :
    ∃ b : ι → Bool, ∀ step : spec.Step,
      |spec.stepCost N (fun i => (chips i).reround (b i)) step|
        = (modDist N (spec.stepOffsetSum N chips step) : ℤ) := by
  classical
  choose T hTsub hTcard using fun step : spec.Step =>
    Finset.exists_subset_card_eq (spec.rightTarget_le_card N hN chips step)
  refine ⟨fun i => decide (i ∈ T ((chips i).coarseStep)), fun step => ?_⟩
  have hsteps : spec.stepChips N
      (fun i => (chips i).reround (decide (i ∈ T ((chips i).coarseStep)))) step
      = spec.stepChips N chips step := by
    ext i
    simp only [mem_stepChips_iff, Chip.reround_coarseStep]
  have hoffsets : spec.stepOffsetSum N
      (fun i => (chips i).reround (decide (i ∈ T ((chips i).coarseStep)))) step
      = spec.stepOffsetSum N chips step := by
    unfold stepOffsetSum
    rw [hsteps]
    simp only [Chip.reround_offset]
  have hfilter : ((spec.stepChips N chips step).filter fun i =>
      ((chips i).reround (decide (i ∈ T ((chips i).coarseStep)))).toRight = true)
      = T step := by
    ext i
    simp only [Finset.mem_filter, Chip.reround_toRight, decide_eq_true_eq]
    constructor
    · rintro ⟨hi, hiT⟩
      rwa [(spec.mem_stepChips_iff N chips step i).mp hi] at hiT
    · intro hiT
      have hi := hTsub step hiT
      exact ⟨hi, by rwa [(spec.mem_stepChips_iff N chips step i).mp hi]⟩
  rw [spec.stepCost_eq_mul_card_sub N _ step, hsteps, hoffsets, hfilter, hTcard]
  exact abs_mul_rightTarget_sub hN _

/-! ## The edge-sum descent -/

/-- The interior chips of an arbitrary family of fine vertices: the fine
vertices that are not images of coarse vertices, read off as `Chip`s. -/
def vertexChips {ι : Type*} (ys : ι → (spec.scale N hN).Vertex) :
    {i : ι // (spec.roundData N hN (ys i)).isRight = true} → spec.Chip N :=
  fun i => (spec.roundData N hN (ys i.1)).getRight i.2

/-- The grid points of an arbitrary family of fine vertices: those that are
images of coarse vertices, read off as coarse vertices. -/
def vertexGrid {ι : Type*} (ys : ι → (spec.scale N hN).Vertex) :
    {i : ι // ¬ ((spec.roundData N hN (ys i)).isRight = true)} → spec.Vertex :=
  fun i => (spec.roundData N hN (ys i.1)).getLeft (Sum.not_isRight.mp i.2)

/-- The total offset `σ_step` of the interior chips of a family of fine vertices
lying on a given coarse step. -/
def vertexStepOffsetSum {ι : Type*} [Fintype ι] (ys : ι → (spec.scale N hN).Vertex)
    (step : spec.Step) : ℕ :=
  spec.stepOffsetSum N (spec.vertexChips N hN ys) step

/-- The **edge sum** of a family of fine vertices: `∑ step, dist(σ_step, N * ℤ)`.
`exists_flags_stepCost` shows this value of the budget
`∑ step, |stepCost step|` of `rank_ge_of_rank_scale_ge_cost` is achievable; it is
in fact the minimum over all flag choices, since every achievable step cost is
`≡ -σ_step (mod N)`, but only achievability is needed and only achievability is
proved here. -/
def edgeSumCost {ι : Type*} [Fintype ι] (ys : ι → (spec.scale N hN).Vertex) : ℕ :=
  ∑ step : spec.Step, modDist N (spec.vertexStepOffsetSum N hN ys step)

/-- **Edge-sum descent, split form.**  The family of fine vertices has already
been separated into grid points (with `lefts` their coarse preimages) and
interior chips (with `chips0` the chips, flags irrelevant). -/
private theorem rank_ge_of_edge_sum_of_split {ι : Type*} [Fintype ι]
    (ys : ι → (spec.scale N hN).Vertex) (D₀ : CFDiv spec.graph) (r : ℤ)
    (P : ι → Prop) [DecidablePred P]
    (chips0 : {i : ι // P i} → spec.Chip N) (lefts : {i : ι // ¬ P i} → spec.Vertex)
    (hchips : ∀ i : {i : ι // P i}, ys i.1 = (chips0 i).fineVertex hN)
    (hlefts : ∀ i : {i : ι // ¬ P i}, ys i.1 = spec.fineOf N hN (lefts i))
    (hcost : (∑ step : spec.Step, (modDist N (spec.stepOffsetSum N chips0 step) : ℤ))
      < (N : ℤ))
    (hrank : rank (spec.scale N hN).graph
      (spec.embed N hN D₀ + ∑ i, one_chip (ys i)) ≥ r) :
    ∃ D : CFDiv spec.graph, deg D = deg D₀ + (Fintype.card ι : ℤ) ∧
      rank spec.graph D ≥ r ∧ (effective D₀ → effective D) := by
  classical
  obtain ⟨b, hb⟩ := spec.exists_flags_stepCost N hN chips0
  set chips : {i : ι // P i} → spec.Chip N := fun i => (chips0 i).reround (b i) with hchipsdef
  have hbudget : (∑ step : spec.Step, |spec.stepCost N chips step|) < (N : ℤ) := by
    rw [Finset.sum_congr rfl fun step _ => hb step]
    exact hcost
  set D₁ : CFDiv spec.graph := D₀ + ∑ i : {i : ι // ¬ P i}, one_chip (lefts i) with hD₁
  have hfineEq : spec.embed N hN D₀ + ∑ i, one_chip (ys i)
      = spec.embed N hN D₁ + spec.fineChips N hN chips := by
    have hE : (∑ i : {i : ι // ¬ P i}, spec.embed N hN (one_chip (lefts i)))
        = ∑ i : {i : ι // ¬ P i}, one_chip (ys i.1) :=
      Finset.sum_congr rfl fun i _ => by rw [spec.embed_one_chip N hN, ← hlefts i]
    have hF : spec.fineChips N hN chips = ∑ i : {i : ι // P i}, one_chip (ys i.1) := by
      unfold fineChips
      exact Finset.sum_congr rfl fun i _ => by
        rw [hchipsdef, Chip.reround_fineVertex, ← hchips i]
    have hsplit := Fintype.sum_subtype_add_sum_subtype P
      (fun i => (one_chip (ys i) : CFDiv (spec.scale N hN).graph))
    rw [hD₁, spec.embed_add N hN, spec.embed_sum N hN, hE, hF, ← hsplit]
    abel
  have hres := spec.rank_ge_of_rank_scale_ge_cost N hN chips D₁ r hbudget
    (by rw [← hfineEq]; exact hrank)
  refine ⟨D₁ + spec.coarseChips N chips, ?_, hres, ?_⟩
  · have hcard : (Fintype.card {i : ι // P i} : ℤ) + (Fintype.card {i : ι // ¬ P i} : ℤ)
        = (Fintype.card ι : ℤ) := by
      have h := Fintype.sum_subtype_add_sum_subtype P (fun _ : ι => (1 : ℤ))
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
      exact h
    have h₁ : deg (∑ i : {i : ι // ¬ P i}, (one_chip (lefts i) : CFDiv spec.graph))
        = (Fintype.card {i : ι // ¬ P i} : ℤ) :=
      deg_sum_one_chip (G := spec.graph) (fun i : {i : ι // ¬ P i} => lefts i)
    have h₂ : deg (spec.coarseChips N chips) = (Fintype.card {i : ι // P i} : ℤ) :=
      deg_sum_one_chip (G := spec.graph)
        (fun i : {i : ι // P i} => (chips i).coarseVertex)
    rw [hD₁, map_add, map_add, h₁, h₂]
    linarith
  · intro hD₀
    have h₁ := effective_sum_one_chip (G := spec.graph) (fun i : {i : ι // ¬ P i} => lefts i)
    have h₂ := effective_sum_one_chip (G := spec.graph)
      (fun i : {i : ι // P i} => (chips i).coarseVertex)
    intro v
    rw [hD₁]
    exact add_nonneg (add_nonneg (hD₀ v) (h₁ v)) (h₂ v)

/-- **Edge-sum descent.**  Let `ys` be an arbitrary family of fine vertices of
the `N`-fold refinement — grid points and interior points alike, with
multiplicity.  If the edge sum `∑ step, dist(σ_step, N * ℤ)` is less than `N`,
then every rank lower bound for `embed D₀ + ∑ ys` on the refinement descends to
a coarse divisor of degree `deg D₀ + #ι`, effective whenever `D₀` is.

Only the *residues* of the interior offsets on each step matter; in particular
arbitrarily many chips may sit on a single step provided their offsets sum to a
multiple of `N`. -/
theorem rank_ge_of_edge_sum {ι : Type*} [Fintype ι]
    (ys : ι → (spec.scale N hN).Vertex) (D₀ : CFDiv spec.graph) (r : ℤ)
    (hcost : (spec.edgeSumCost N hN ys : ℤ) < (N : ℤ))
    (hrank : rank (spec.scale N hN).graph
      (spec.embed N hN D₀ + ∑ i, one_chip (ys i)) ≥ r) :
    ∃ D : CFDiv spec.graph, deg D = deg D₀ + (Fintype.card ι : ℤ) ∧
      rank spec.graph D ≥ r ∧ (effective D₀ → effective D) :=
  spec.rank_ge_of_edge_sum_of_split N hN ys D₀ r
    (fun i => (spec.roundData N hN (ys i)).isRight = true)
    (spec.vertexChips N hN ys) (spec.vertexGrid N hN ys)
    (fun i => spec.eq_fineVertex_of_roundData_eq_inr N hN
      (Sum.eq_right_iff_getRight_eq.mpr ⟨i.2, rfl⟩))
    (fun i => spec.eq_fineOf_of_roundData_eq_inl N hN
      (Sum.eq_left_iff_getLeft_eq.mpr ⟨Sum.not_isRight.mp i.2, rfl⟩))
    (by
      refine lt_of_le_of_lt (le_of_eq ?_) hcost
      unfold edgeSumCost vertexStepOffsetSum
      push_cast
      rfl)
    hrank

/-! ## The case `N = 3`: at most two bad steps -/

/-- A coarse step is **bad** for a family of fine vertices when the total offset
of the interior chips lying on it is not a multiple of `N`. -/
def badSteps {ι : Type*} [Fintype ι] (ys : ι → (spec.scale N hN).Vertex) :
    Finset spec.Step :=
  Finset.univ.filter fun step => spec.vertexStepOffsetSum N hN ys step % N ≠ 0

theorem modDist_three (σ : ℕ) : modDist 3 σ = if σ % 3 = 0 then 0 else 1 := by
  have h : σ % 3 < 3 := Nat.mod_lt _ (by norm_num)
  unfold modDist
  split_ifs with h0 <;> omega

/-- At `N = 3` the distance to `3 * ℤ` is `0` or `1`, so the edge sum simply
counts the bad steps. -/
theorem edgeSumCost_three {ι : Type*} [Fintype ι] (h3 : 0 < 3)
    (ys : ι → (spec.scale 3 h3).Vertex) :
    spec.edgeSumCost 3 h3 ys = (spec.badSteps 3 h3 ys).card := by
  classical
  unfold edgeSumCost badSteps
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun step _ => ?_
  rw [modDist_three]
  by_cases h : spec.vertexStepOffsetSum 3 h3 ys step % 3 = 0 <;> simp [h]

/-- **Edge-sum descent at `N = 3`.**  At most two bad steps suffice: each bad
step is charged exactly `1`, each good step exactly `0`, and `2 < 3`. -/
theorem rank_ge_of_bad_steps_le_two {ι : Type*} [Fintype ι] (h3 : 0 < 3)
    (ys : ι → (spec.scale 3 h3).Vertex) (D₀ : CFDiv spec.graph) (r : ℤ)
    (hbad : (spec.badSteps 3 h3 ys).card ≤ 2)
    (hrank : rank (spec.scale 3 h3).graph
      (spec.embed 3 h3 D₀ + ∑ i, one_chip (ys i)) ≥ r) :
    ∃ D : CFDiv spec.graph, deg D = deg D₀ + (Fintype.card ι : ℤ) ∧
      rank spec.graph D ≥ r ∧ (effective D₀ → effective D) := by
  refine spec.rank_ge_of_edge_sum 3 h3 ys D₀ r ?_ hrank
  rw [spec.edgeSumCost_three h3 ys]
  have : ((spec.badSteps 3 h3 ys).card : ℤ) ≤ 2 := by exact_mod_cast hbad
  push_cast
  omega

end Spec

end Utilities.Certificate.SubdivisionGraph

namespace Utilities.Gonality

open Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-- The **bad edges** of a family of fine chips on the triple regular
subdivision `σ₃ G`.  On the unit subdivision presentation every coarse step is a
single edge occurrence of `G`, so the bad steps of `Spec.badSteps` transport
along `UnitSubdivisionPresentation.stepEquiv` to a set of edges of `G`. -/
noncomputable def badEdges (G : CFGraph) (h3 : 0 < 3) {ι : Type*} [Fintype ι]
    (ys : ι → (regularSubdivision G 3 h3).V) : Finset G.edges :=
  ((UnitSubdivisionPresentation.spec G).badSteps 3 h3 ys).map
    (UnitSubdivisionPresentation.stepEquiv G).toEmbedding

theorem card_badEdges (G : CFGraph) (h3 : 0 < 3) {ι : Type*} [Fintype ι]
    (ys : ι → (regularSubdivision G 3 h3).V) :
    (badEdges G h3 ys).card
      = ((UnitSubdivisionPresentation.spec G).badSteps 3 h3 ys).card :=
  Finset.card_map _

/-- **`w¹₄` from a triple subdivision with at most two bad edges.**  Four fine
chips on `σ₃ G` spanning a divisor of rank at least one, at most two of whose
edges are bad, produce a degree-four divisor of rank at least one on `G` itself.

The divisor `∑ i, one_chip (ys i)` is exactly an effective divisor of degree four
on `σ₃ G` presented by its four chips; an edge is bad when the offsets of the
interior chips on it do not sum to a multiple of three. -/
theorem bnExists_one_four_of_badEdges_le_two (G : CFGraph) (h3 : 0 < 3)
    (ys : Fin 4 → (regularSubdivision G 3 h3).V)
    (hbad : (badEdges G h3 ys).card ≤ 2)
    (hrank : rank (regularSubdivision G 3 h3) (∑ i, one_chip (ys i)) ≥ 1) :
    BNExists G 1 4 := by
  have hbad' : ((UnitSubdivisionPresentation.spec G).badSteps 3 h3 ys).card ≤ 2 := by
    rwa [card_badEdges] at hbad
  have hrank' : rank ((UnitSubdivisionPresentation.spec G).scale 3 h3).graph
      ((UnitSubdivisionPresentation.spec G).embed 3 h3 0
        + ∑ i, (one_chip (ys i) :
            CFDiv ((UnitSubdivisionPresentation.spec G).scale 3 h3).graph)) ≥ 1 := by
    rw [Spec.embed_zero, zero_add]
    exact hrank
  obtain ⟨D, hDdeg, hDrank, -⟩ :=
    (UnitSubdivisionPresentation.spec G).rank_ge_of_bad_steps_le_two h3 ys 0 1 hbad' hrank'
  refine ((UnitSubdivisionPresentation.laplacianEquiv G).bnExists_iff 1 4).mpr ⟨D, ?_, hDrank⟩
  rw [hDdeg]
  simp

end Utilities.Gonality

