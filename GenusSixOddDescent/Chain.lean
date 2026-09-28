import GenusSixOddDescent.Cost
import Utilities.Subdivision.SlotPropagation
import Utilities.Subdivision.CoreCutsAndFlats
import Utilities.Gonality.LegalFiringChain
import Utilities.Foundations.RankDeterminingSet

/-!
# States, reduced representatives and the pivot lemma

A degree-four effective divisor in a nonselected class is either a state
(`TypeI`: one core chip and three interior chips on distinct slots) or a
non-state with no core chip. The non-state alternatives need no finer list.
`IsState` additionally requires that the complement of the three chip slots
be connected; `lemmaQ` proves this from nonselection.

`pivot` uses interval confinement and slot propagation to control legal firing
sets. It yields reducedness and uniqueness of the representative at a state.
These pivot facts do not require oddness or nonselection. The odd hypothesis
enters the degree-four dichotomy through the cost bound in
`GenusSixOddDescent/Cost.lean`.

The main interfaces are `rank_ge_one_iff_core`, `structure_of_notSelected`,
`pivot`, `typeI_qReduced`, `typeI_unique`, `lemmaQ`, `corR_unique_rep` and
`corR_dichotomy`. Statements use an abstract subdivision presentation.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Generic `outdeg_S` helpers

Two small facts about outgoing degrees, local to this module. -/

/-- A vertex of vanishing outdegree has every neighbour in the set. -/
private theorem mem_of_outdeg_zero {G : CFGraph} {S : Finset G.V} {x : G.V}
    (hx : outdeg_S G S x = 0) {y : G.V} (hy : 0 < num_edges G x y) : y ∈ S := by
  by_contra hyS
  have hedge := Gonality.num_edges_le_outdeg_S S x hyS
  have hpos : (0 : ℤ) < (num_edges G x y : ℤ) := by exact_mod_cast hy
  omega

/-- One neighbour inside `T` is a lower bound for the *incoming* degree, which is
what `set_firing` adds outside `T`. -/
private theorem le_outdeg_compl {G : CFGraph} {T : Finset G.V} {x y : G.V}
    (hy : y ∈ T) : (num_edges G x y : ℤ) ≤ outdeg_S G Tᶜ x := by
  unfold outdeg_S
  refine Finset.single_le_sum (f := fun w : G.V => (num_edges G x w : ℤ))
    (fun _ _ => Int.natCast_nonneg _) ?_
  simp [hy]

/-! ## Arithmetic helpers

Two counting facts about finite families of integers. -/

/-- If a finite family of integers is at least one on each of `E.card` members
and sums to `E.card`, every member is exactly one. -/
private theorem eq_one_of_sum_eq_card {ι : Type*} (E : Finset ι) (f : ι → ℤ)
    (hge : ∀ e ∈ E, 1 ≤ f e) (hsum : ∑ e ∈ E, f e = (E.card : ℤ)) :
    ∀ e ∈ E, f e = 1 := by
  intro e he
  by_contra hne
  have hlt : (E.card : ℤ) < ∑ x ∈ E, f x := by
    calc (E.card : ℤ) = ∑ _x ∈ E, (1 : ℤ) := by simp
      _ < ∑ x ∈ E, f x :=
        Finset.sum_lt_sum (fun x hx => hge x hx) ⟨e, he, by have := hge e he; omega⟩
  omega

/-- A nonnegative family summing to one is a single unit chip. -/
private theorem exists_eq_one_of_sum_eq_one {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (f : ι → ℤ) (hnn : ∀ i ∈ E, 0 ≤ f i)
    (hsum : ∑ i ∈ E, f i = 1) :
    ∃ i₀ ∈ E, f i₀ = 1 ∧ ∀ i ∈ E, i ≠ i₀ → f i = 0 := by
  classical
  have hex : ∃ i₀ ∈ E, 0 < f i₀ := by
    by_contra hc
    push Not at hc
    have hle : ∑ i ∈ E, f i ≤ 0 := Finset.sum_nonpos fun i hi => hc i hi
    omega
  obtain ⟨i₀, hi₀, hpos⟩ := hex
  have hsplit := Finset.add_sum_erase E f hi₀
  have hrestnn : 0 ≤ ∑ i ∈ E.erase i₀, f i :=
    Finset.sum_nonneg fun i hi => hnn i (Finset.mem_of_mem_erase hi)
  have hone : f i₀ = 1 := by omega
  have hrest : ∑ i ∈ E.erase i₀, f i = 0 := by omega
  refine ⟨i₀, hi₀, hone, fun i hi hne => ?_⟩
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj => hnn j (Finset.mem_of_mem_erase hj))).mp hrest i
      (Finset.mem_erase.mpr ⟨hne, hi⟩)

/-! ## Reading the slot chip data off `edgeChipCount` -/

/-- A slot of chip count zero is chipless offset by offset. -/
theorem slotPoint_eq_zero_of_edgeChipCount_zero (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) {g : Fin p}
    (hg : spec.edgeChipCount N hN D g = 0) :
    ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0 := by
  rw [spec.edgeChipCount_eq_sum_slotPoint N hN hunit D g] at hg
  exact fun j hj => (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hD _).mp hg j hj

/-- A slot of chip count one carries its single chip at a unique interior
offset. -/
theorem exists_chip_offset (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) {g : Fin p}
    (hg : spec.edgeChipCount N hN D g = 1) :
    ∃ t, 0 < t ∧ t < N ∧ D (spec.slotPoint N hN g t) = 1 ∧
      ∀ k, 0 < k → k < N → k ≠ t → D (spec.slotPoint N hN g k) = 0 := by
  classical
  rw [spec.edgeChipCount_eq_sum_slotPoint N hN hunit D g] at hg
  obtain ⟨t, htmem, ht1, htrest⟩ := exists_eq_one_of_sum_eq_one (Finset.Ioo 0 N)
    (fun j => D (spec.slotPoint N hN g j)) (fun j _ => hD _) hg
  obtain ⟨ht0, htN⟩ := Finset.mem_Ioo.mp htmem
  exact ⟨t, ht0, htN, ht1, fun k hk0 hkN hkt =>
    htrest k (Finset.mem_Ioo.mpr ⟨hk0, hkN⟩) hkt⟩

/-- The one-chip hypothesis of the slot lemmas of
`Utilities/Subdivision/SlotIntervalFiring.lean`, from a chip count of at most
one. -/
theorem sum_interior_le_one_of_edgeChipCount_le_one (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {g : Fin p}
    (hg : spec.edgeChipCount N hN D g ≤ 1) :
    ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1 := by
  rwa [spec.edgeChipCount_eq_sum_slotPoint N hN hunit D g] at hg

/-! ## Rank one is tested at the core vertices -/

/-- **Rank one is tested at the core.**  On a subdivision of a loopless connected
core the core vertices are rank-determining (Luo, via strong separators), so
rank one is decided by the `n` core tests.  `rank_ge_one_of_reaches_coreVertices`
is stated for every scale, so nothing here depends on `N`. -/
theorem rank_ge_one_iff_core (hconn : graph_connected (spec.scale N hN).graph)
    (D : CFDiv (spec.scale N hN).graph) :
    rank (spec.scale N hN).graph D ≥ 1 ↔
      ∀ v : Fin n, winnable (spec.scale N hN).graph
        (D - one_chip ((spec.scale N hN).coreVertex v)) := by
  -- `→` is `Utilities.rank_ge_one_iff_winnable_sub_one_chip` specialised to core
  -- vertices; `←` is `Spec.rank_ge_one_of_reaches_coreVertices (spec.scale N hN)`,
  -- whose looplessness hypothesis is the structure field `core_loopless`.
  constructor
  · intro hrank v
    exact (Utilities.rank_ge_one_iff_winnable_sub_one_chip _ D).mp hrank _
  · intro hcore
    exact (spec.scale N hN).rank_ge_one_of_reaches_coreVertices
      (spec.scale N hN).core_loopless hconn D hcore

/-! ## The two types of representative -/

/-- **The state `D_v`**: exactly one chip at a core vertex, namely `v`, and
exactly one interior chip on each of the three slots of `E`; in formulas,
`D_v = v + Σ_{e ∈ E} ξ_v(e)` with `ξ_v(e)` the chip on the slot `e`.  The
definition does not depend on the scale. -/
def TypeI (D : CFDiv (spec.scale N hN).graph) (v : Fin n) (E : Finset (Fin p)) :
    Prop :=
  effective D ∧ deg D = 4 ∧
    (∀ u : Fin n, D ((spec.scale N hN).coreVertex u) = if u = v then 1 else 0) ∧
    E.card = 3 ∧
    ∀ e : Fin p, spec.edgeChipCount N hN D e = if e ∈ E then 1 else 0

/-- **A state**: a `TypeI` divisor whose chip-slot complement is connected.  By
`lemmaQ` the second clause is automatic under `(¬S)`, but the hub-system layer
needs the two separately. -/
def IsState (D : CFDiv (spec.scale N hN).graph) (v : Fin n) (E : Finset (Fin p)) :
    Prop :=
  spec.TypeI N hN D v E ∧ spec.core.ConnectedOff E

/-- **A non-state**: no chip at any core vertex.  The non-states of a class
include the nodes of hole branches and the intermediate divisors of bridge
chains; their variety grows with `N`, and they are deliberately not
enumerated. -/
def NonState (D : CFDiv (spec.scale N hN).graph) : Prop :=
  ∀ u : Fin n, D ((spec.scale N hN).coreVertex u) = 0

/-! ## The state / non-state dichotomy -/

/-- **The state / non-state dichotomy at odd `N`.**  Under `(¬S)` every
effective degree-four representative is a state at some core vertex or carries
no core chip at all.

The engine is the counting bound `Delta_le_mul_card_chipEdges` of
`GenusSixOddDescent/Cost.lean`: `Δ ≤ ⌊N/2⌋ · #chip-slots` against
`Δ ≥ N` forces `#chip-slots ≥ 3` for odd `N`, and
`#core chips + #chip-slots ≤ deg = 4` then forces at most one core chip.  One
core chip leaves exactly three slots with exactly one chip each — the state; no
core chip is the non-state. -/
theorem structure_of_notSelected (hunit : spec.IsUnit) (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) (hdeg : deg D = 4)
    (hDA : linear_equiv (spec.scale N hN).graph A D) :
    (∃ v E, spec.TypeI N hN D v E) ∨ spec.NonState N hN D := by
  classical
  -- Unit slot lengths play no part in the counting; `hunit` is kept in the
  -- signature because every consumer has it to hand.
  have _ : spec.IsUnit := hunit
  have hcard3 :=
    spec.three_le_card_chipEdges_of_notSelected N hN hodd h3N hNS hD hDA
  have hcard3' : (3 : ℤ) ≤ ((spec.chipEdges N hN D).card : ℤ) := by
    exact_mod_cast hcard3
  have hcore1 :=
    spec.coreChipCount_le_one_of_notSelected N hN hodd h3N hNS hD hdeg hDA
  have hcorenn : 0 ≤ spec.coreChipCount N hN D := Finset.sum_nonneg fun _ _ => hD _
  have hcount := spec.coreChipCount_add_card_chipEdges_le N hN hD
  rw [hdeg] at hcount
  have hsumuniv : ∑ e ∈ spec.chipEdges N hN D, spec.edgeChipCount N hN D e
      = ∑ e : Fin p, spec.edgeChipCount N hN D e :=
    Finset.sum_subset (Finset.subset_univ _)
      fun _e _ he => spec.edgeChipCount_eq_zero_of_not_mem N hN he
  have hsplit := spec.deg_eq_coreChipCount_add_sum N hN D
  rw [hdeg] at hsplit
  by_cases hc : spec.coreChipCount N hN D = 1
  · -- One core chip: exactly three chip slots, one chip each — a state.
    obtain ⟨v, -, hv1, hv0⟩ := exists_eq_one_of_sum_eq_one Finset.univ
      (fun u : Fin n => D ((spec.scale N hN).coreVertex u)) (fun u _ => hD _) hc
    have hm : (spec.chipEdges N hN D).card = 3 := by
      have h : ((spec.chipEdges N hN D).card : ℤ) = 3 := by omega
      exact_mod_cast h
    have heach : ∀ e ∈ spec.chipEdges N hN D, spec.edgeChipCount N hN D e = 1 :=
      eq_one_of_sum_eq_card _ _
        (fun e he => spec.one_le_edgeChipCount N hN hD he)
        (by rw [hsumuniv, hm]; push_cast; omega)
    refine Or.inl ⟨v, spec.chipEdges N hN D, hD, hdeg, ?_, hm, ?_⟩
    · intro u
      by_cases huv : u = v
      · rw [if_pos huv, huv]; exact hv1
      · rw [if_neg huv]; exact hv0 u (Finset.mem_univ u) huv
    · intro e
      by_cases he : e ∈ spec.chipEdges N hN D
      · rw [if_pos he]; exact heach e he
      · rw [if_neg he]; exact spec.edgeChipCount_eq_zero_of_not_mem N hN he
  · -- No core chip at all: a non-state.  Which non-state it is — the part that
    -- grows with `N` — is never needed.
    have hc0 : spec.coreChipCount N hN D = 0 := by omega
    exact Or.inr fun u =>
      (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hD _).mp hc0 u (Finset.mem_univ u)

/-! ## The pivot lemma and reducedness -/

/-- **Propagation out of a core vertex of vanishing outdegree.**  The workhorse
of `pivot`(ii) and `pivot`(iii): if `coreVertex w` lies in the legal set `T` and
absorbs all of its fine neighbours (`outdeg_S T = 0`), and if the offsets
`1, …, t - 1` of the slot `g` at `w` are chipless, then the whole run
`0, …, t` from `w` lies in `T`.

Taking `t = N` on a chipless slot this is `propagate_chipless`, and taking `t`
the offset of the chip it is `propagate_upto_chip`
(`Utilities/Subdivision/SlotPropagation.lean`); the point of restating it is
that the base case here is `outdeg_S T = 0` rather than `D (coreVertex w) = 0`,
which is what the pivot vertex `v` — carrying a chip — needs. -/
private theorem propagate_run (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph}
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T) (g : Fin p) (w : Fin n)
    (hinc : spec.core.tail g = w ∨ spec.core.head g = w)
    (hwT : (spec.scale N hN).coreVertex w ∈ T)
    (hout : outdeg_S (spec.scale N hN).graph T ((spec.scale N hN).coreVertex w) = 0)
    {t : ℕ} (htN : t ≤ N)
    (hzero : ∀ k, 0 < k → k < t → D (spec.sidePoint N hN g w k) = 0) :
    ∀ k, k ≤ t → spec.sidePoint N hN g w k ∈ T := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [spec.sidePoint_zero N hN hunit g hinc]
      exact hwT
  | succ k ih =>
      intro hk
      have hkt : k < t := by omega
      have hkN : k < N := by omega
      have hkT := ih (by omega)
      have hadj := spec.num_edges_sidePoint_succ_pos N hN hunit g w hkN
      rcases Nat.eq_zero_or_pos k with rfl | h0
      · rw [spec.sidePoint_zero N hN hunit g hinc] at hadj
        exact mem_of_outdeg_zero hout hadj
      · exact Gonality.mem_of_apply_le_zero hT hkT (le_of_eq (hzero k h0 hkt)) hadj

/-- **`coreSet_eq_univ_of_closed`.**  A non-empty set of core vertices of a legal
set, each absorbing its own fine neighbourhood, which is closed under crossing
every chipless slot, is all of the core — because `G − E` is connected and every
chip slot lies in `E`.

This is the closure argument of `core_closure`
(`Utilities/Subdivision/SlotPropagation.lean`), with its `D = 0` hypothesis
traded for `outdeg_S T = 0` and driven across the whole core by `ConnectedOff`;
it is the shared engine of `pivot`(ii) and `pivot`(iii). -/
private theorem coreSet_eq_univ_of_closed (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph}
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T)
    {E : Finset (Fin p)} (hconn : spec.core.ConnectedOff E)
    (hfree : ∀ g : Fin p, g ∉ E →
      ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0)
    (hout : ∀ w : Fin n, (spec.scale N hN).coreVertex w ∈ T →
      outdeg_S (spec.scale N hN).graph T ((spec.scale N hN).coreVertex w) = 0)
    (hne : ∃ w₀ : Fin n, (spec.scale N hN).coreVertex w₀ ∈ T) :
    ∀ w : Fin n, (spec.scale N hN).coreVertex w ∈ T := by
  classical
  intro w
  by_contra hw
  obtain ⟨w₀, hw₀⟩ := hne
  have hUmem : ∀ u : Fin n,
      u ∈ (Finset.univ.filter fun u : Fin n => (spec.scale N hN).coreVertex u ∈ T)
        ↔ (spec.scale N hN).coreVertex u ∈ T := by
    intro u; simp
  obtain ⟨g, hgE, hcross⟩ := hconn
    (Finset.univ.filter fun u : Fin n => (spec.scale N hN).coreVertex u ∈ T)
    ⟨w₀, w, (hUmem w₀).mpr hw₀, fun hc => hw ((hUmem w).mp hc)⟩
  -- The crossing slot `g` is outside `E`, hence chipless, so the fire runs its
  -- whole length and both its endpoints are in `T`.
  have hfreeg := hfree g hgE
  have hboth : ∀ z : Fin n, (spec.core.tail g = z ∨ spec.core.head g = z) →
      (spec.scale N hN).coreVertex z ∈ T →
      (spec.scale N hN).coreVertex (spec.core.tail g) ∈ T ∧
        (spec.scale N hN).coreVertex (spec.core.head g) ∈ T := by
    intro z hincz hzT
    have hfar := spec.propagate_run N hN hunit hT g z hincz hzT (hout z hzT)
      (t := N) le_rfl
      (fun k hk0 hkN =>
        spec.sidePoint_apply_eq_zero_of_chipless N hN g z hfreeg hk0 hkN) N le_rfl
    by_cases hc : spec.core.tail g = z
    · rw [spec.sidePoint_last_of_tail N hN hunit g hc] at hfar
      exact ⟨hc ▸ hzT, hfar⟩
    · rw [spec.sidePoint_last_of_ne N hN g hc] at hfar
      exact ⟨hfar, (hincz.resolve_left hc) ▸ hzT⟩
  rcases hcross with ⟨htail, hhead⟩ | ⟨hhead, htail⟩
  · exact hhead ((hUmem _).mpr (hboth _ (Or.inl rfl) ((hUmem _).mp htail)).2)
  · exact htail ((hUmem _).mpr (hboth _ (Or.inr rfl) ((hUmem _).mp hhead)).1)

/-- **Filling one slot.**  If both endpoints of a slot carrying at most one
interior chip lie in the legal set `T` and absorb their fine neighbourhoods,
every point of the slot lies in `T`: propagate from each end up to the chip, and
the two runs meet.  (This is `propagate_both_ends` of
`Utilities/Subdivision/SlotPropagation.lean`, with the `D = 0` hypothesis at the
endpoints traded for `outdeg_S T = 0`.) -/
private theorem fill_slot (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T) (g : Fin p)
    (htailT : (spec.scale N hN).coreVertex (spec.core.tail g) ∈ T)
    (htailOut : outdeg_S (spec.scale N hN).graph T
      ((spec.scale N hN).coreVertex (spec.core.tail g)) = 0)
    (hheadT : (spec.scale N hN).coreVertex (spec.core.head g) ∈ T)
    (hheadOut : outdeg_S (spec.scale N hN).graph T
      ((spec.scale N hN).coreVertex (spec.core.head g)) = 0)
    (hchip : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1)
    {k : ℕ} (hkN : k ≤ N) :
    spec.slotPoint N hN g k ∈ T := by
  classical
  by_cases hfree : ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0
  · -- No chip at all: one run from the tail suffices.
    have h := spec.propagate_run N hN hunit hT g (spec.core.tail g) (Or.inl rfl)
      htailT htailOut (t := N) le_rfl
      (fun j hj0 hjN =>
        spec.sidePoint_apply_eq_zero_of_chipless N hN g _ hfree hj0 hjN) k hkN
    rwa [spec.sidePoint_tail N hN g k] at h
  · -- One chip, at offset `t` from the tail and `N - t` from the head.
    push Not at hfree
    obtain ⟨t, htIoo, htne⟩ := hfree
    obtain ⟨ht0, htN⟩ := Finset.mem_Ioo.mp htIoo
    have hDt : 1 ≤ D (spec.slotPoint N hN g t) := by
      have := hD (spec.slotPoint N hN g t); omega
    by_cases hkt : k ≤ t
    · have hDt' : 1 ≤ D (spec.sidePoint N hN g (spec.core.tail g) t) := by
        rwa [spec.sidePoint_tail N hN g t]
      have h := spec.propagate_run N hN hunit hT g (spec.core.tail g) (Or.inl rfl)
        htailT htailOut (t := t) (le_of_lt htN)
        (fun j hj0 hjt =>
          spec.sidePoint_apply_eq_zero_of_chip N hN hD g _ hchip ht0 htN hDt'
            hj0 (by omega) (by omega)) k hkt
      rwa [spec.sidePoint_tail N hN g k] at h
    · have hDt' : 1 ≤ D (spec.sidePoint N hN g (spec.core.head g) (N - t)) := by
        rw [spec.sidePoint_head N hN g (N - t), show N - (N - t) = t by omega]
        exact hDt
      have h := spec.propagate_run N hN hunit hT g (spec.core.head g) (Or.inr rfl)
        hheadT hheadOut (t := N - t) (by omega)
        (fun j hj0 hjt =>
          spec.sidePoint_apply_eq_zero_of_chip N hN hD g _ hchip (by omega)
            (by omega) hDt' hj0 (by omega) (by omega)) (N - k) (by omega)
      rwa [spec.sidePoint_head N hN g (N - k), show N - (N - k) = k by omega] at h

/-- **The pivot lemma.**  Let `D` be a state at `v` with chip slots `E`, and
suppose `G − E` is connected.  Then every non-empty proper legal firing set `T`
contains the core vertex `v` and satisfies `outdeg_S T v = 1`; firing `T`
therefore removes the chip from `v`.

The proof has three steps.
**(i)** `T` meets the core: otherwise no slot has an endpoint in `T`, and every
slot carries at most one chip, so `slotInterior_disjoint_of_chip_le_one`
empties every slot interior and `T = ∅`.
**(ii)** `v ∈ T`: otherwise every core vertex of `T` is chipless, hence absorbs
its neighbourhood, and `coreSet_eq_univ_of_closed` sweeps the connected `G − E`,
putting `v` in `T` after all.
**(iii)** `outdeg_S T v ≤ D v = 1`, and `= 0` would sweep the core as in (ii)
and then fill every slot (`fill_slot`), making `T = univ`.

`min deg ≥ 3` is nowhere used, and neither is `(¬S)` nor the parity of `N` —
which is what the separation lemma of `GenusSixOddDescent/HubSystem.lean` needs,
since it applies the resulting reducedness (`typeI_qReduced`) to every state of
a hub system. -/
theorem pivot (hunit : spec.IsUnit) {D : CFDiv (spec.scale N hN).graph} {v : Fin n}
    {E : Finset (Fin p)} (hD : spec.TypeI N hN D v E)
    (hconn : spec.core.ConnectedOff E)
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T) (hne : T.Nonempty)
    (hproper : T ≠ Finset.univ) :
    (spec.scale N hN).coreVertex v ∈ T ∧
      outdeg_S (spec.scale N hN).graph T ((spec.scale N hN).coreVertex v) = 1 := by
  classical
  obtain ⟨hDeff, -, hcore, -, hslot⟩ := hD
  -- Every slot carries at most one interior chip, and the slots outside `E`
  -- carry none.
  have hchip : ∀ g : Fin p,
      ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1 := by
    intro g
    refine spec.sum_interior_le_one_of_edgeChipCount_le_one N hN hunit ?_
    rw [hslot g]
    split <;> omega
  have hfree : ∀ g : Fin p, g ∉ E →
      ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0 := by
    intro g hg
    refine spec.slotPoint_eq_zero_of_edgeChipCount_zero N hN hunit hDeff ?_
    rw [hslot g, if_neg hg]
  -- (i) `T` meets the core: otherwise `slotInterior_disjoint_of_chip_le_one`
  -- empties every slot interior.
  have hmeet : ∃ w : Fin n, (spec.scale N hN).coreVertex w ∈ T := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := hne
    rcases x with w | ⟨g, j⟩
    · exact hcon w hx
    · have hxT : (spec.scale N hN).interiorVertex g j ∈ T := hx
      rw [spec.interiorVertex_eq_slotPoint N hN hunit g j] at hxT
      have hj := j.isLt
      have hL := spec.length_scale N hN hunit g
      exact spec.slotInterior_disjoint_of_chip_le_one N hN hunit hDeff hT g
        (hchip g) (hcon _) (hcon _) (Nat.succ_pos _) (by omega) hxT
  -- (ii) `v ∈ T`: otherwise every core vertex of `T` is chipless, absorbs its
  -- neighbourhood, and the fire sweeps the connected `G − E`.
  have hvT : (spec.scale N hN).coreVertex v ∈ T := by
    by_contra hv
    refine hv (spec.coreSet_eq_univ_of_closed N hN hunit hT hconn hfree ?_ hmeet v)
    intro w hw
    have hwv : w ≠ v := by rintro rfl; exact hv hw
    have hlegal := hT _ hw
    rw [hcore w, if_neg hwv] at hlegal
    have hnn := outdeg_S_nonneg (spec.scale N hN).graph T
      ((spec.scale N hN).coreVertex w)
    omega
  refine ⟨hvT, ?_⟩
  -- (iii) `outdeg_S T v ≤ D v = 1`, and `= 0` would make `T` everything.
  have hle : outdeg_S (spec.scale N hN).graph T ((spec.scale N hN).coreVertex v)
      ≤ 1 := by
    have hlegal := hT _ hvT
    rwa [hcore v, if_pos rfl] at hlegal
  have hnn := outdeg_S_nonneg (spec.scale N hN).graph T
    ((spec.scale N hN).coreVertex v)
  by_contra hone
  have hzero : outdeg_S (spec.scale N hN).graph T
      ((spec.scale N hN).coreVertex v) = 0 := by omega
  have hall0 : ∀ w : Fin n, (spec.scale N hN).coreVertex w ∈ T →
      outdeg_S (spec.scale N hN).graph T ((spec.scale N hN).coreVertex w) = 0 := by
    intro w hw
    by_cases hwv : w = v
    · rw [hwv]; exact hzero
    · have hlegal := hT _ hw
      rw [hcore w, if_neg hwv] at hlegal
      have hnn' := outdeg_S_nonneg (spec.scale N hN).graph T
        ((spec.scale N hN).coreVertex w)
      omega
  have hallcore :=
    spec.coreSet_eq_univ_of_closed N hN hunit hT hconn hfree hall0 hmeet
  refine hproper (Finset.eq_univ_iff_forall.mpr fun x => ?_)
  rcases x with w | ⟨g, j⟩
  · exact hallcore w
  · -- Every slot is now filled from its two endpoints (`fill_slot`).
    have hj := j.isLt
    have hL := spec.length_scale N hN hunit g
    have h := spec.fill_slot N hN hunit hDeff hT g (hallcore _)
      (hall0 _ (hallcore _)) (hallcore _) (hall0 _ (hallcore _)) (hchip g)
      (k := j.val + 1) (by omega)
    show (spec.scale N hN).interiorVertex g j ∈ T
    rw [spec.interiorVertex_eq_slotPoint N hN hunit g j]
    exact h

/-- **Reducedness.**  A state whose chip-slot complement is connected is the
`v`-reduced representative of its class. -/
theorem typeI_qReduced (hunit : spec.IsUnit) {D : CFDiv (spec.scale N hN).graph}
    {v : Fin n} {E : Finset (Fin p)} (hD : spec.TypeI N hN D v E)
    (hconn : spec.core.ConnectedOff E) :
    q_reduced (spec.scale N hN).graph ((spec.scale N hN).coreVertex v) D := by
  -- `q_reduced` asks that no non-empty set avoiding `v` be legal; `pivot` says
  -- every non-empty proper legal set contains `v`, and `univ` is not disjoint
  -- from `{v}`.
  refine ⟨fun x _ => hD.1 x, ?_⟩
  intro S hvS hSne hlegal
  have hproper : S ≠ Finset.univ :=
    fun hc => hvS (by rw [hc]; exact Finset.mem_univ _)
  exact hvS (spec.pivot N hN hunit hD hconn hlegal hSne hproper).1

/-- Uniqueness of the state at `v`: two linearly equivalent states at the same
core vertex, both with connected chip-slot complement, are equal. -/
theorem typeI_unique (hunit : spec.IsUnit) {D D' : CFDiv (spec.scale N hN).graph}
    {v : Fin n} {E E' : Finset (Fin p)} (hD : spec.TypeI N hN D v E)
    (hD' : spec.TypeI N hN D' v E') (hconn : spec.core.ConnectedOff E)
    (hconn' : spec.core.ConnectedOff E')
    (hlin : linear_equiv (spec.scale N hN).graph D D') :
    D = D' := by
  -- Both are `coreVertex v`-reduced by `typeI_qReduced`, and the `q`-reduced
  -- representative of a class is unique (`q_reduced_unique`).
  exact q_reduced_unique (spec.scale N hN).graph ((spec.scale N hN).coreVertex v) D D'
    ⟨spec.typeI_qReduced N hN hunit hD hconn,
      spec.typeI_qReduced N hN hunit hD' hconn', hlin⟩

/-! ## Connectivity of the chip-slot complement: `lemmaQ`

The proof burns from one side of a cut and is carried out by hand.  `K` is the
side of the offending cut *not* containing `v`; the burnt set is described in
closed form (below), its legality is a direct `outdeg` computation, and firing
it advances every crossing chip one fine step away from `K`.  The loop is an
induction on the distance the chip of one fixed crossing slot still has to
travel. -/

/-! ### The fine neighbourhood of a core vertex

Two facts about the fine edges at a core vertex.  A unit step of the refinement
has an interior endpoint as soon as `2 ≤ N`, which is all that is needed. -/

/-- A vertex all of whose neighbours lie in `T` has vanishing outdegree. -/
private theorem outdeg_eq_zero_of_nbrs_mem {G : CFGraph} {T : Finset G.V} {x : G.V}
    (h : ∀ y : G.V, 0 < num_edges G x y → y ∈ T) : outdeg_S G T x = 0 := by
  unfold outdeg_S
  refine Finset.sum_eq_zero fun y hy => ?_
  have hyT : y ∉ T := (Finset.mem_sdiff.mp hy).2
  have hz : num_edges G x y = 0 := by
    by_contra hne
    exact hyT (h y (Nat.pos_of_ne_zero hne))
  simp [hz]

/-- **No fine edge joins two core vertices** once `2 ≤ N`: every unit step of a
slot of length `N` has an interior endpoint. -/
private theorem num_edges_core_core (hunit : spec.IsUnit) (h2N : 2 ≤ N)
    (w u : Fin n) :
    num_edges (spec.scale N hN).graph ((spec.scale N hN).coreVertex w)
      ((spec.scale N hN).coreVertex u) = 0 := by
  by_contra hzero
  obtain ⟨⟨g, i⟩, hst⟩ :=
    ((spec.scale N hN).num_edges_pos_iff _ _).mp (Nat.pos_of_ne_zero hzero)
  have hL : (spec.scale N hN).length g = N := spec.length_scale N hN hunit g
  have hi := i.isLt
  obtain ⟨a, ha⟩ : ∃ a : Fin n, (spec.scale N hN).stepLeft g i
      = (spec.scale N hN).coreVertex a := by
    rcases hst with h | h
    · exact ⟨w, congrArg Prod.fst h⟩
    · exact ⟨u, congrArg Prod.fst h⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, (spec.scale N hN).stepRight g i
      = (spec.scale N hN).coreVertex b := by
    rcases hst with h | h
    · exact ⟨u, congrArg Prod.snd h⟩
    · exact ⟨w, congrArg Prod.snd h⟩
  have hi0 : i.val = 0 := by
    by_contra hne
    have hj : i.val - 1 < (spec.scale N hN).length g - 1 := by omega
    have hstep := (spec.scale N hN).stepLeft_after_zero g ⟨i.val - 1, hj⟩
    rw [show (⟨(⟨i.val - 1, hj⟩ : Fin ((spec.scale N hN).length g - 1)).val + 1,
        by omega⟩ : Fin ((spec.scale N hN).length g)) = i from
      Fin.ext (show i.val - 1 + 1 = (i : ℕ) by omega)] at hstep
    rw [hstep] at ha
    simp [coreVertex, interiorVertex] at ha
  have hilast : i.val + 1 = (spec.scale N hN).length g := by
    by_contra hne
    have hj : i.val < (spec.scale N hN).length g - 1 := by omega
    have hstep := (spec.scale N hN).stepRight_before_last g ⟨i.val, hj⟩
    rw [show (⟨(⟨i.val, hj⟩ : Fin ((spec.scale N hN).length g - 1)).val,
        by omega⟩ : Fin ((spec.scale N hN).length g)) = i from Fin.ext rfl] at hstep
    rw [hstep] at hb
    simp [coreVertex, interiorVertex] at hb
  omega

/-- **The fine neighbours of a core vertex** are the offset-one points of the
slots at it. -/
private theorem coreVertex_nbhd (hunit : spec.IsUnit) (h2N : 2 ≤ N) {w : Fin n}
    {y : (spec.scale N hN).graph.V}
    (hy : 0 < num_edges (spec.scale N hN).graph ((spec.scale N hN).coreVertex w) y) :
    ∃ g : Fin p, (spec.core.tail g = w ∨ spec.core.head g = w) ∧
      y = spec.sidePoint N hN g w 1 := by
  rcases y with u | ⟨g, j⟩
  · exfalso
    have hz := spec.num_edges_core_core N hN hunit h2N w u
    have hy' : 0 < num_edges (spec.scale N hN).graph
      ((spec.scale N hN).coreVertex w) ((spec.scale N hN).coreVertex u) := hy
    omega
  · have hj := j.isLt
    have hL := spec.length_scale N hN hunit g
    have hyeq : (Sum.inr ⟨g, j⟩ : (spec.scale N hN).graph.V)
        = spec.slotPoint N hN g (j.val + 1) :=
      spec.interiorVertex_eq_slotPoint N hN hunit g j
    have hy' : 0 < num_edges (spec.scale N hN).graph
        (spec.slotPoint N hN g (j.val + 1)) ((spec.scale N hN).coreVertex w) := by
      rw [num_edges_symmetric, ← hyeq]; exact hy
    rcases (spec.slotPoint_adj_iff N hN hunit g (t := j.val + 1) (by omega)
      (by omega) _).mp hy' with h | h
    · simp only [Nat.add_sub_cancel] at h
      have hj0 : j.val = 0 := by
        by_contra hne
        exact spec.coreVertex_ne_slotPoint N hN hunit w g (t := j.val)
          (by omega) (by omega) h
      rw [hj0, spec.slotPoint_zero N hN g] at h
      have hw : spec.core.tail g = w := by simpa [coreVertex] using h.symm
      refine ⟨g, Or.inl hw, ?_⟩
      rw [spec.sidePoint_of_tail N hN g hw 1, hyeq, hj0]
    · have hjN : j.val + 1 + 1 = N := by
        by_contra hne
        exact spec.coreVertex_ne_slotPoint N hN hunit w g (t := j.val + 1 + 1)
          (by omega) (by omega) h
      rw [hjN, spec.slotPoint_last N hN hunit g] at h
      have hw : spec.core.head g = w := by simpa [coreVertex] using h.symm
      have hne : spec.core.tail g ≠ w := by
        rw [← hw]; exact spec.core_loopless g
      refine ⟨g, Or.inr hw, ?_⟩
      rw [spec.sidePoint_of_ne N hN g hne 1, hyeq, show N - 1 = j.val + 1 by omega]

/-! ### Counting two core chips, and the chip offset from a chosen end -/

/-- Two distinct core chips of an effective divisor. -/
private theorem two_le_coreChipCount {D' : CFDiv (spec.scale N hN).graph}
    (hD' : effective D') {v z : Fin n} (hvz : v ≠ z)
    (h1 : 1 ≤ D' ((spec.scale N hN).coreVertex v))
    (h2 : 1 ≤ D' ((spec.scale N hN).coreVertex z)) :
    2 ≤ spec.coreChipCount N hN D' := by
  classical
  have hle : ∑ w ∈ ({v, z} : Finset (Fin n)), D' ((spec.scale N hN).coreVertex w)
      ≤ ∑ w : Fin n, D' ((spec.scale N hN).coreVertex w) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hD' _
  rw [Finset.sum_pair hvz] at hle
  show 2 ≤ ∑ w : Fin n, D' ((spec.scale N hN).coreVertex w)
  omega

/-- One doubled core chip does as well. -/
private theorem two_le_coreChipCount_double {D' : CFDiv (spec.scale N hN).graph}
    (hD' : effective D') {v : Fin n}
    (h1 : 2 ≤ D' ((spec.scale N hN).coreVertex v)) :
    2 ≤ spec.coreChipCount N hN D' := by
  classical
  have hle : ∑ w ∈ ({v} : Finset (Fin n)), D' ((spec.scale N hN).coreVertex w)
      ≤ ∑ w : Fin n, D' ((spec.scale N hN).coreVertex w) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hD' _
  rw [Finset.sum_singleton] at hle
  show 2 ≤ ∑ w : Fin n, D' ((spec.scale N hN).coreVertex w)
  omega

/-- `exists_chip_offset` read from a chosen endpoint of the slot. -/
theorem exists_chip_offset_side (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) {g : Fin p} (z : Fin n)
    (hg : spec.edgeChipCount N hN D g = 1) :
    ∃ t, 0 < t ∧ t < N ∧ D (spec.sidePoint N hN g z t) = 1 ∧
      ∀ k, 0 < k → k < N → k ≠ t → D (spec.sidePoint N hN g z k) = 0 := by
  obtain ⟨c, hc0, hcN, hc1, hcrest⟩ := spec.exists_chip_offset N hN hunit hD hg
  by_cases hz : spec.core.tail g = z
  · refine ⟨c, hc0, hcN, ?_, ?_⟩
    · rw [spec.sidePoint_of_tail N hN g hz]; exact hc1
    · intro k hk0 hkN hkc
      rw [spec.sidePoint_of_tail N hN g hz]; exact hcrest k hk0 hkN hkc
  · refine ⟨N - c, by omega, by omega, ?_, ?_⟩
    · rw [spec.sidePoint_of_ne N hN g hz, show N - (N - c) = c by omega]; exact hc1
    · intro k hk0 hkN hkc
      rw [spec.sidePoint_of_ne N hN g hz]
      exact hcrest (N - k) (by omega) (by omega) (by omega)

/-- Crossing is a property of the partition, not of the chosen side. -/
private theorem crosses_compl (S : Finset (Fin n)) (g : Fin p) :
    spec.core.Crosses Sᶜ g ↔ spec.core.Crosses S g := by
  classical
  unfold ExplicitPotential.Core.Crosses
  simp only [Finset.mem_compl, not_not]
  tauto

/-! ### One burn-and-fire

`K` is a side of a cut every crossing slot of which carries a chip of the state
`D`, and `v ∉ K`.  The **burnt set** is described in closed form: a core vertex
burns iff it lies in `K`, and the interior point of `g` at offset `j` burns iff
the fire reaches it from one of the two ends, i.e. iff

* `tail g ∈ K` and the offsets `1, …, j - 1` are chipless, or
* `head g ∈ K` and the offsets `j + 1, …, N - 1` are chipless.

Both clauses are available on a chip slot with **both** ends in `K`, which is why
such a slot burns completely, with no separate argument.  Firing the burnt set
advances every crossing chip one fine step away from `K`. -/
private theorem burn_step (hunit : spec.IsUnit) (h2N : 2 ≤ N)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hDtype : spec.TypeI N hN D v E) (K : Finset (Fin n)) (hvK : v ∉ K)
    (hcrossE : ∀ g : Fin p, spec.core.Crosses K g → g ∈ E) :
    ∃ D' : CFDiv (spec.scale N hN).graph,
      linear_equiv (spec.scale N hN).graph D D' ∧ effective D' ∧
        (2 ≤ spec.coreChipCount N hN D' ∨
          (1 ≤ D' ((spec.scale N hN).coreVertex v) ∧
            ∀ (g : Fin p) (z : Fin n) (t : ℕ), spec.core.Crosses K g →
              (spec.core.tail g = z ∨ spec.core.head g = z) → z ∈ K →
              0 < t → t < N → 1 ≤ D (spec.sidePoint N hN g z t) →
              t + 1 < N ∧ 1 ≤ D' (spec.sidePoint N hN g z (t + 1)))) := by
  classical
  obtain ⟨hDeff, hDdeg, hcoreD, -, hslotD⟩ := hDtype
  have hDv : D ((spec.scale N hN).coreVertex v) = 1 := by rw [hcoreD v]; simp
  -- The burnt set.
  obtain ⟨T, hTmem⟩ : ∃ T : Finset (spec.scale N hN).graph.V,
      ∀ x : (spec.scale N hN).graph.V, x ∈ T ↔
        Sum.elim (fun u : Fin n => u ∈ K)
          (fun i : (spec.scale N hN).Interior =>
            (spec.core.tail i.1 ∈ K ∧
                ∀ l, 0 < l → l < i.2.val + 1 → D (spec.slotPoint N hN i.1 l) = 0) ∨
              (spec.core.head i.1 ∈ K ∧
                ∀ l, i.2.val + 1 < l → l < N →
                  D (spec.slotPoint N hN i.1 l) = 0)) x := by
    refine ⟨Finset.univ.filter (fun x =>
      Sum.elim (fun u : Fin n => u ∈ K)
        (fun i : (spec.scale N hN).Interior =>
          (spec.core.tail i.1 ∈ K ∧
              ∀ l, 0 < l → l < i.2.val + 1 → D (spec.slotPoint N hN i.1 l) = 0) ∨
            (spec.core.head i.1 ∈ K ∧
              ∀ l, i.2.val + 1 < l → l < N →
                D (spec.slotPoint N hN i.1 l) = 0)) x), fun x => ?_⟩
    exact ⟨fun hx => (Finset.mem_filter.mp hx).2,
      fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hTcore : ∀ u : Fin n, ((spec.scale N hN).coreVertex u ∈ T ↔ u ∈ K) :=
    fun u => hTmem ((spec.scale N hN).coreVertex u)
  have hTslot : ∀ (g : Fin p) (j : ℕ), 0 < j → j < N →
      (spec.slotPoint N hN g j ∈ T ↔
        ((spec.core.tail g ∈ K ∧
            ∀ l, 0 < l → l < j → D (spec.slotPoint N hN g l) = 0) ∨
          (spec.core.head g ∈ K ∧
            ∀ l, j < l → l < N → D (spec.slotPoint N hN g l) = 0))) := by
    intro g j hj0 hjN
    have hL := spec.length_scale N hN hunit g
    obtain ⟨k, hk⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit g hj0 hjN
    have hklt := k.isLt
    have hkj : j = k.val + 1 := by
      by_contra hne
      exact spec.slotPoint_ne N hN hunit g (le_of_lt hjN) (by omega) hne
        (hk.trans (spec.interiorVertex_eq_slotPoint N hN hunit g k))
    have hred : ((spec.scale N hN).interiorVertex g k ∈ T) ↔
        ((spec.core.tail g ∈ K ∧
            ∀ l, 0 < l → l < k.val + 1 → D (spec.slotPoint N hN g l) = 0) ∨
          (spec.core.head g ∈ K ∧
            ∀ l, k.val + 1 < l → l < N → D (spec.slotPoint N hN g l) = 0)) :=
      hTmem ((spec.scale N hN).interiorVertex g k)
    rw [hk, hred, ← hkj]
  -- The same, read from a chosen endpoint of the slot.
  have hTside : ∀ (g : Fin p) (z : Fin n),
      (spec.core.tail g = z ∨ spec.core.head g = z) → ∀ k, 0 < k → k < N →
      (spec.sidePoint N hN g z k ∈ T ↔
        ((z ∈ K ∧ ∀ l, 0 < l → l < k → D (spec.sidePoint N hN g z l) = 0) ∨
          (spec.core.otherEnd g z ∈ K ∧
            ∀ l, k < l → l < N → D (spec.sidePoint N hN g z l) = 0))) := by
    intro g z hinc k hk0 hkN
    by_cases hc : spec.core.tail g = z
    · have hother : spec.core.otherEnd g z = spec.core.head g := by
        unfold ExplicitPotential.Core.otherEnd; rw [if_pos hc]
      have hside : ∀ l, spec.sidePoint N hN g z l = spec.slotPoint N hN g l :=
        fun l => spec.sidePoint_of_tail N hN g hc l
      rw [hside, hother, hTslot g k hk0 hkN]
      simp only [hside, hc]
    · have hz : spec.core.head g = z := hinc.resolve_left hc
      have hother : spec.core.otherEnd g z = spec.core.tail g := by
        unfold ExplicitPotential.Core.otherEnd; rw [if_neg hc]
      have hside : ∀ l, spec.sidePoint N hN g z l = spec.slotPoint N hN g (N - l) :=
        fun l => spec.sidePoint_of_ne N hN g hc l
      rw [hside, hother, hTslot g (N - k) (by omega) (by omega)]
      simp only [hside]
      rw [hz]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inr ⟨h1, fun l hl1 hl2 => h2 (N - l) (by omega) (by omega)⟩
        · exact Or.inl ⟨h1, fun l hl1 hl2 => h2 (N - l) (by omega) (by omega)⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · refine Or.inr ⟨h1, fun l hl1 hl2 => ?_⟩
          have := h2 (N - l) (by omega) (by omega)
          rwa [show N - (N - l) = l by omega] at this
        · refine Or.inl ⟨h1, fun l hl1 hl2 => ?_⟩
          have := h2 (N - l) (by omega) (by omega)
          rwa [show N - (N - l) = l by omega] at this
  -- A completely chipless slot cannot cross the cut: it lies outside `E`.
  have hnc : ∀ g : Fin p, (∀ l, 0 < l → l < N → D (spec.slotPoint N hN g l) = 0) →
      ¬ spec.core.Crosses K g := by
    intro g hall hcr
    have hone : spec.edgeChipCount N hN D g = 1 := by
      rw [hslotD g, if_pos (hcrossE g hcr)]
    rw [spec.edgeChipCount_eq_sum_slotPoint N hN hunit D g,
      Finset.sum_congr rfl (fun l hl =>
        hall l (Finset.mem_Ioo.mp hl).1 (Finset.mem_Ioo.mp hl).2)] at hone
    simp at hone
  have hotherTail : ∀ g : Fin p,
      spec.core.otherEnd g (spec.core.tail g) = spec.core.head g := by
    intro g; unfold ExplicitPotential.Core.otherEnd; rw [if_pos rfl]
  have hotherHead : ∀ g : Fin p,
      spec.core.otherEnd g (spec.core.head g) = spec.core.tail g := by
    intro g; unfold ExplicitPotential.Core.otherEnd; rw [if_neg (spec.core_loopless g)]
  -- **Legality.**
  have hTlegal : legal_set (spec.scale N hN).graph D T := by
    intro x hx
    rcases x with u | ⟨g, j⟩
    · have huK : u ∈ K := (hTcore u).mp hx
      have huv : u ≠ v := by rintro rfl; exact hvK huK
      show outdeg_S (spec.scale N hN).graph T ((spec.scale N hN).coreVertex u)
        ≤ D ((spec.scale N hN).coreVertex u)
      rw [hcoreD u, if_neg huv]
      refine le_of_eq (outdeg_eq_zero_of_nbrs_mem fun y hy => ?_)
      obtain ⟨g, hinc, rfl⟩ := spec.coreVertex_nbhd N hN hunit h2N hy
      exact (hTside g u hinc 1 (by omega) (by omega)).mpr
        (Or.inl ⟨huK, fun l hl1 hl2 => absurd hl2 (by omega)⟩)
    · have hjlt := j.isLt
      have hL := spec.length_scale N hN hunit g
      have hs0 : 0 < j.val + 1 := by omega
      have hsN : j.val + 1 < N := by omega
      have hxT : spec.slotPoint N hN g (j.val + 1) ∈ T := by
        rw [← spec.interiorVertex_eq_slotPoint N hN hunit g j]; exact hx
      show outdeg_S (spec.scale N hN).graph T
          ((spec.scale N hN).interiorVertex g j)
        ≤ D ((spec.scale N hN).interiorVertex g j)
      rw [spec.interiorVertex_eq_slotPoint N hN hunit g j,
        spec.outdeg_slotPoint N hN hunit T g hs0 hsN]
      set s := j.val + 1 with hsdef
      have hDnn := hDeff (spec.slotPoint N hN g s)
      have hlow0 : spec.slotPoint N hN g 0
          = (spec.scale N hN).coreVertex (spec.core.tail g) := spec.slotPoint_zero N hN g
      have hhighN : spec.slotPoint N hN g N
          = (spec.scale N hN).coreVertex (spec.core.head g) :=
        spec.slotPoint_last N hN hunit g
      rcases (hTslot g s hs0 hsN).mp hxT with ⟨htK, hzero⟩ | ⟨hhK, hzero⟩
      · -- Burnt from the tail: the lower neighbour is burnt too.
        have hlow : spec.slotPoint N hN g (s - 1) ∈ T := by
          rcases Nat.eq_zero_or_pos (s - 1) with h | h
          · rw [h, hlow0]; exact (hTcore _).mpr htK
          · exact (hTslot g (s - 1) h (by omega)).mpr
              (Or.inl ⟨htK, fun l hl1 hl2 => hzero l hl1 (by omega)⟩)
        rw [if_pos hlow]
        by_cases hDs : D (spec.slotPoint N hN g s) = 0
        · have hhigh : spec.slotPoint N hN g (s + 1) ∈ T := by
            rcases Nat.lt_or_ge (s + 1) N with h | h
            · refine (hTslot g (s + 1) (by omega) h).mpr (Or.inl ⟨htK, ?_⟩)
              intro l hl1 hl2
              rcases Nat.lt_or_ge l s with hls | hls
              · exact hzero l hl1 hls
              · rw [show l = s by omega]; exact hDs
            · have hchipless : ∀ l, 0 < l → l < N → D (spec.slotPoint N hN g l) = 0 := by
                intro l hl1 hl2
                rcases Nat.lt_or_ge l s with hls | hls
                · exact hzero l hl1 hls
                · rw [show l = s by omega]; exact hDs
              have hmem := spec.core.otherEnd_mem_of_not_crosses (W := K) (e := g)
                (z := spec.core.tail g) (Or.inl rfl) htK (hnc g hchipless)
              rw [hotherTail g] at hmem
              rw [show s + 1 = N by omega, hhighN]
              exact (hTcore _).mpr hmem
          rw [if_pos hhigh]
          omega
        · have hone : 1 ≤ D (spec.slotPoint N hN g s) := by omega
          split_ifs <;> omega
      · -- Burnt from the head: the upper neighbour is burnt too.
        have hhigh : spec.slotPoint N hN g (s + 1) ∈ T := by
          rcases Nat.lt_or_ge (s + 1) N with h | h
          · exact (hTslot g (s + 1) (by omega) h).mpr
              (Or.inr ⟨hhK, fun l hl1 hl2 => hzero l (by omega) hl2⟩)
          · rw [show s + 1 = N by omega, hhighN]; exact (hTcore _).mpr hhK
        rw [if_pos hhigh]
        by_cases hDs : D (spec.slotPoint N hN g s) = 0
        · have hlow : spec.slotPoint N hN g (s - 1) ∈ T := by
            rcases Nat.eq_zero_or_pos (s - 1) with h | h
            · have hchipless : ∀ l, 0 < l → l < N → D (spec.slotPoint N hN g l) = 0 := by
                intro l hl1 hl2
                rcases Nat.lt_or_ge s l with hls | hls
                · exact hzero l hls hl2
                · rw [show l = s by omega]; exact hDs
              have hmem := spec.core.otherEnd_mem_of_not_crosses (W := K) (e := g)
                (z := spec.core.head g) (Or.inr rfl) hhK (hnc g hchipless)
              rw [hotherHead g] at hmem
              rw [h, hlow0]
              exact (hTcore _).mpr hmem
            · refine (hTslot g (s - 1) h (by omega)).mpr (Or.inr ⟨hhK, ?_⟩)
              intro l hl1 hl2
              rcases Nat.lt_or_ge s l with hls | hls
              · exact hzero l hls hl2
              · rw [show l = s by omega]; exact hDs
          rw [if_pos hlow]
          omega
        · have hone : 1 ≤ D (spec.slotPoint N hN g s) := by omega
          split_ifs <;> omega
  -- **Fire it.**
  refine ⟨set_firing (spec.scale N hN).graph D T,
    Utilities.linear_equiv_set_firing D T,
    Utilities.Gonality.effective_setFiring hDeff hTlegal, ?_⟩
  have hvT : (spec.scale N hN).coreVertex v ∉ T := fun hc => hvK ((hTcore v).mp hc)
  have hvgain : (1 : ℤ) ≤ set_firing (spec.scale N hN).graph D T
      ((spec.scale N hN).coreVertex v) := by
    rw [set_firing_apply_of_not_mem _ _ hvT, hDv]
    have := outdeg_S_nonneg (spec.scale N hN).graph Tᶜ
      ((spec.scale N hN).coreVertex v)
    omega
  -- The chip of a crossing slot sits at a burnt point, and the offsets below it
  -- are chipless, so the run from the `K`-end up to it is burnt.
  have hburnChip : ∀ (g : Fin p) (z : Fin n) (t : ℕ), spec.core.Crosses K g →
      (spec.core.tail g = z ∨ spec.core.head g = z) → z ∈ K → 0 < t → t < N →
      1 ≤ D (spec.sidePoint N hN g z t) →
      (∀ l, 0 < l → l < N → l ≠ t → D (spec.sidePoint N hN g z l) = 0) := by
    intro g z t hcr hinc hzK ht0 htN hDt
    have hone : spec.edgeChipCount N hN D g = 1 := by
      rw [hslotD g, if_pos (hcrossE g hcr)]
    obtain ⟨c, hc0, hcN, hc1, hcrest⟩ :=
      spec.exists_chip_offset_side N hN hunit hDeff z hone
    have hct : c = t := by
      by_contra hne
      have := hcrest t ht0 htN (Ne.symm hne)
      omega
    subst hct
    exact hcrest
  by_cases hland : ∃ (g : Fin p) (z : Fin n), spec.core.Crosses K g ∧
      (spec.core.tail g = z ∨ spec.core.head g = z) ∧ z ∈ K ∧
      1 ≤ D (spec.sidePoint N hN g z (N - 1))
  · -- **A chip lands on a core vertex.**
    left
    obtain ⟨g, z, hcr, hinc, hzK, hDlast⟩ := hland
    set u := spec.core.otherEnd g z with hudef
    have huK : u ∉ K :=
      spec.core.otherEnd_not_mem_of_crosses (e := g) (z := z) hinc hzK hcr
    have huinc : spec.core.tail g = u ∨ spec.core.head g = u :=
      spec.core.incident_otherEnd g z
    have huT : (spec.scale N hN).coreVertex u ∉ T := fun hc => huK ((hTcore u).mp hc)
    -- the chip vertex, read from `u`, is at offset one
    have hswap : spec.sidePoint N hN g u 1 = spec.sidePoint N hN g z (N - 1) := by
      by_cases hc : spec.core.tail g = z
      · have hu : spec.core.head g = u := by rw [hudef, ← hc, hotherTail g]
        have hne : spec.core.tail g ≠ u := by rw [← hu]; exact spec.core_loopless g
        rw [spec.sidePoint_of_ne N hN g hne 1, spec.sidePoint_of_tail N hN g hc]
      · have hz : spec.core.head g = z := hinc.resolve_left hc
        have hu : spec.core.tail g = u := by rw [hudef, ← hz, hotherHead g]
        rw [spec.sidePoint_of_tail N hN g hu 1, spec.sidePoint_of_ne N hN g hc,
          show N - (N - 1) = 1 by omega]
    have hchipT : spec.sidePoint N hN g u 1 ∈ T := by
      rw [hswap]
      refine (hTside g z hinc (N - 1) (by omega) (by omega)).mpr
        (Or.inl ⟨hzK, fun l hl1 hl2 => ?_⟩)
      exact hburnChip g z (N - 1) hcr hinc hzK (by omega) (by omega) hDlast l hl1
        (by omega) (by omega)
    have hedge : 0 < num_edges (spec.scale N hN).graph
        ((spec.scale N hN).coreVertex u) (spec.sidePoint N hN g u 1) := by
      have h := spec.num_edges_sidePoint_succ_pos N hN hunit g u (k := 0) hN
      rwa [spec.sidePoint_zero N hN hunit g huinc] at h
    have hgain : (1 : ℤ) ≤ outdeg_S (spec.scale N hN).graph Tᶜ
        ((spec.scale N hN).coreVertex u) := by
      have h1 := le_outdeg_compl (G := (spec.scale N hN).graph) (T := T)
        (x := (spec.scale N hN).coreVertex u) hchipT
      have h2 : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
        ((spec.scale N hN).coreVertex u) (spec.sidePoint N hN g u 1) : ℤ) := by
        exact_mod_cast hedge
      omega
    have hD'eff := Utilities.Gonality.effective_setFiring hDeff hTlegal
    by_cases huv : u = v
    · refine two_le_coreChipCount_double spec N hN hD'eff (v := v) ?_
      rw [set_firing_apply_of_not_mem _ _ hvT, hDv]
      rw [huv] at hgain
      omega
    · refine two_le_coreChipCount spec N hN hD'eff (v := v) (z := u)
        (Ne.symm huv) hvgain ?_
      rw [set_firing_apply_of_not_mem _ _ huT, hcoreD u, if_neg huv]
      omega
  · -- **No landing: every crossing chip advances one step.**
    right
    push Not at hland
    refine ⟨hvgain, fun g z t hcr hinc hzK ht0 htN hDt => ?_⟩
    have htlast : t ≠ N - 1 := by
      intro hc
      exact absurd (hc ▸ hDt) (by
        have := hland g z hcr hinc hzK
        omega)
    have htN1 : t + 1 < N := by omega
    refine ⟨htN1, ?_⟩
    have hrest := hburnChip g z t hcr hinc hzK ht0 htN hDt
    have hchipT : spec.sidePoint N hN g z t ∈ T :=
      (hTside g z hinc t ht0 htN).mpr
        (Or.inl ⟨hzK, fun l hl1 hl2 => hrest l hl1 (by omega) (by omega)⟩)
    have hnextT : spec.sidePoint N hN g z (t + 1) ∉ T := by
      intro hc
      rcases (hTside g z hinc (t + 1) (by omega) htN1).mp hc with ⟨-, h2⟩ | ⟨h1, -⟩
      · have := h2 t ht0 (by omega); omega
      · exact spec.core.otherEnd_not_mem_of_crosses (e := g) (z := z) hinc hzK hcr h1
    have hedge : 0 < num_edges (spec.scale N hN).graph
        (spec.sidePoint N hN g z (t + 1)) (spec.sidePoint N hN g z t) := by
      rw [num_edges_symmetric]
      exact spec.num_edges_sidePoint_succ_pos N hN hunit g z (by omega)
    have hgain : (1 : ℤ) ≤ outdeg_S (spec.scale N hN).graph Tᶜ
        (spec.sidePoint N hN g z (t + 1)) := by
      have h1 := le_outdeg_compl (G := (spec.scale N hN).graph) (T := T)
        (x := spec.sidePoint N hN g z (t + 1)) hchipT
      have h2 : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
        (spec.sidePoint N hN g z (t + 1)) (spec.sidePoint N hN g z t) : ℤ) := by
        exact_mod_cast hedge
      omega
    rw [set_firing_apply_of_not_mem _ _ hnextT]
    have := hDeff (spec.sidePoint N hN g z (t + 1))
    omega


/-- **The descent behind `lemmaQ`.**  Each burn-and-fire advances the chip of the
fixed crossing slot `e₀` one step away from `K`; after at most `N` of them it
would have to leave the slot, which is impossible, so a landing — two core chips
against `coreChipCount_le_one` of `GenusSixOddDescent/Cost.lean` — must have
happened first.

The induction is on the budget `s` bounding `N -` (the chip's offset from the
`K`-end), and every intermediate `T` is **re-derived by a fresh burn**; the
intermediate divisors are not described explicitly, because
`structure_of_notSelected` recognises each of them as a state at `v` from the
single fact that `v` never loses its chip. -/
private theorem lemmaQ_descend (hunit : spec.IsUnit) (h2N : 2 ≤ N)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (K : Finset (Fin n)) {v : Fin n} (hvK : v ∉ K)
    {e₀ : Fin p} {z₀ : Fin n} (he₀ : spec.core.Crosses K e₀)
    (hz₀inc : spec.core.Incident e₀ z₀) (hz₀K : z₀ ∈ K) :
    ∀ (s : ℕ) (D : CFDiv (spec.scale N hN).graph) (E : Finset (Fin p)),
      linear_equiv (spec.scale N hN).graph A D → spec.TypeI N hN D v E →
      (∀ g : Fin p, spec.core.Crosses K g → g ∈ E) →
      (∀ t, 0 < t → t < N → 1 ≤ D (spec.sidePoint N hN e₀ z₀ t) → N ≤ t + s) →
      False := by
  intro s
  induction s with
  | zero =>
      intro D E hDA hDtype hcrossE hbudget
      obtain ⟨t, ht0, htN, ht1, -⟩ := spec.exists_chip_offset_side N hN hunit
        hDtype.1 z₀ (by rw [hDtype.2.2.2.2 e₀, if_pos (hcrossE e₀ he₀)])
      have := hbudget t ht0 htN (by omega)
      omega
  | succ s ih =>
      intro D E hDA hDtype hcrossE hbudget
      obtain ⟨D', hDD', hD'eff, hcase⟩ :=
        spec.burn_step N hN hunit h2N hDtype K hvK hcrossE
      have hD'A : linear_equiv (spec.scale N hN).graph A D' := hDA.trans hDD'
      have hD'deg : deg D' = 4 := by
        rw [← linear_equiv_preserves_deg _ D D' hDD']
        exact hDtype.2.1
      rcases hcase with hland | ⟨hvchip, hadv⟩
      · -- A chip landed: two core chips, which `(¬S)` forbids.
        have := spec.coreChipCount_le_one_of_notSelected N hN hodd h3N hNS hD'eff
          hD'deg hD'A
        omega
      · -- Every crossing chip advanced one step; `D'` is again a state at `v`.
        obtain ⟨u, E', hI⟩ : ∃ u E', spec.TypeI N hN D' u E' := by
          rcases spec.structure_of_notSelected N hN hunit hodd h3N hNS hD'eff
            hD'deg hD'A with h | hnon
          · exact h
          · exact absurd (hnon v) (by omega)
        have huv : u = v := by
          by_contra hne
          have := hI.2.2.1 v
          rw [if_neg (fun hc : v = u => hne hc.symm)] at this
          omega
        subst huv
        -- The chip of `e₀` has moved one step away from `K`.
        obtain ⟨t₀, ht₀0, ht₀N, ht₀1, -⟩ := spec.exists_chip_offset_side N hN hunit
          hDtype.1 z₀ (by rw [hDtype.2.2.2.2 e₀, if_pos (hcrossE e₀ he₀)])
        obtain ⟨ht₀adv, hD'chip⟩ := hadv e₀ z₀ t₀ he₀ hz₀inc hz₀K ht₀0 ht₀N
          (by omega)
        -- Every slot crossing the cut still carries a chip, so it lies in `E'`.
        have hcrossE' : ∀ g : Fin p, spec.core.Crosses K g → g ∈ E' := by
          intro g hg
          obtain ⟨z, hzinc, hzK, -⟩ :=
            spec.core.exists_nearEnd (spec.core_loopless g) hg
          obtain ⟨t, ht0, htN, ht1, -⟩ := spec.exists_chip_offset_side N hN hunit
            hDtype.1 z (by rw [hDtype.2.2.2.2 g, if_pos (hcrossE g hg)])
          obtain ⟨htadv, hD'g⟩ := hadv g z t hg hzinc hzK ht0 htN (by omega)
          by_contra hgE'
          have hzero : spec.edgeChipCount N hN D' g = 0 := by
            rw [hI.2.2.2.2 g, if_neg hgE']
          have hpt : D' (spec.sidePoint N hN g z (t + 1)) = 0 :=
            spec.sidePoint_apply_eq_zero_of_chipless N hN g z
              (spec.slotPoint_eq_zero_of_edgeChipCount_zero N hN hunit hD'eff hzero)
              (by omega) htadv
          omega
        -- The budget drops by one.
        refine ih D' E' hD'A hI hcrossE' (fun t ht0 htN hDt => ?_)
        obtain ⟨c, hc0, hcN, hc1, hcrest⟩ := spec.exists_chip_offset_side N hN hunit
          hD'eff z₀ (by rw [hI.2.2.2.2 e₀, if_pos (hcrossE' e₀ he₀)])
        have hct : c = t₀ + 1 := by
          by_contra hne
          have := hcrest (t₀ + 1) (by omega) ht₀adv (Ne.symm hne)
          omega
        have htc : t = c := by
          by_contra hne
          have := hcrest t ht0 htN hne
          omega
        have hb := hbudget t₀ ht₀0 ht₀N (by omega)
        omega

/-- **`lemmaQ`: the chip-slot complement of a state is connected.**  Under `(¬S)`,
a representative with a chip at a core vertex automatically has connected
chip-slot complement — so the connectivity hypothesis of `pivot` is free, and by
`typeI_qReduced` the representative *is* the `v`-reduced one.

Suppose a cut `S` of the core is crossed only by slots of `E`, and let `K` be the
side of it *not* containing `v`.  Burn from `K`: the burnt set `T` is the core
vertices of `K`, the interiors of the slots inside `K` (which burn completely,
since a chipless run reaches every offset from one end or the other), and on
each crossing slot the run from the `K`-end **through** the chip.  `T` is legal
(the fronts have `outdeg 1 ≤ D = 1`, everything else `outdeg 0`) and firing it
advances every crossing chip one step away from `K`, keeping the divisor a state
at `v` with the same `E`.  After `N − max_e t_e` firings a crossing chip lands
on a core vertex outside `K`, and `v` still has its own, contradicting
`coreChipCount_le_one` of `GenusSixOddDescent/Cost.lean`. -/
theorem lemmaQ (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D)
    (hDA : linear_equiv (spec.scale N hN).graph A D) {v : Fin n}
    {E : Finset (Fin p)} (hDtype : spec.TypeI N hN D v E) :
    spec.core.ConnectedOff E := by
  classical
  -- Effectivity travels inside `hDtype`; `hD` is kept in the signature because
  -- every consumer has it to hand.
  have _ : effective D := hD
  have h2N : 2 ≤ N := by omega
  intro S hS
  by_contra hcon
  -- Under the assumption every slot crossing the cut is a chip slot.
  have hcrossS : ∀ g : Fin p, spec.core.Crosses S g → g ∈ E := by
    intro g hg
    by_contra hgE
    exact hcon ⟨g, hgE, hg⟩
  -- Burn from whichever side of the cut does **not** contain `v`.
  obtain ⟨K, hvK, hcrossK⟩ : ∃ K : Finset (Fin n), v ∉ K ∧
      ∀ g : Fin p, (spec.core.Crosses K g ↔ spec.core.Crosses S g) := by
    by_cases hv : v ∈ S
    · exact ⟨Sᶜ, by simpa using hv, fun g => spec.crosses_compl S g⟩
    · exact ⟨S, hv, fun _ => Iff.rfl⟩
  have hcrossE : ∀ g : Fin p, spec.core.Crosses K g → g ∈ E :=
    fun g hg => hcrossS g ((hcrossK g).mp hg)
  -- The core is connected, so some slot crosses; fix it and its `K`-endpoint.
  obtain ⟨e₀, he₀raw⟩ := hcore S hS
  have he₀ : spec.core.Crosses K e₀ := (hcrossK e₀).mpr he₀raw
  obtain ⟨z₀, hz₀inc, hz₀K, -⟩ :=
    spec.core.exists_nearEnd (spec.core_loopless e₀) he₀
  exact spec.lemmaQ_descend N hN hunit h2N hodd h3N hNS K hvK he₀ hz₀inc hz₀K
    N D E hDA hDtype hcrossE (fun t _ _ _ => by omega)

/-! ## Unique representatives and the dichotomy at odd `N`

The corollaries `corR_unique_rep` and `corR_dichotomy` combine the dichotomy,
`lemmaQ` and reducedness. -/

/-- Adding one chip at `x` raises the coefficient at `x` by one. -/
private theorem add_one_chip_apply_self {G : CFGraph} (C : CFDiv G) (x : G.V) :
    (C + one_chip x) x = C x + 1 := by
  show C x + one_chip x x = C x + 1
  simp [one_chip]

/-- Adding one chip preserves effectivity. -/
private theorem effective_add_one_chip {G : CFGraph} {C : CFDiv G} (hC : effective C)
    (x : G.V) : effective (C + one_chip x) := by
  intro y
  have h := hC y
  have hval : one_chip x y = if y = x then (1 : ℤ) else 0 := rfl
  show (0 : ℤ) ≤ C y + one_chip x y
  rw [hval]
  split <;> omega

/-- Under `(¬S)` a representative carrying a chip at the core vertex `v` is a
state **at `v`**, with the connectivity of `lemmaQ` for free. -/
private theorem typeI_of_core_chip (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) (hdeg : deg D = 4)
    (hDA : linear_equiv (spec.scale N hN).graph A D) {v : Fin n}
    (hpos : 0 < D ((spec.scale N hN).coreVertex v)) :
    ∃ E, spec.IsState N hN D v E := by
  rcases spec.structure_of_notSelected N hN hunit hodd h3N hNS hD hdeg hDA with
    ⟨u, E, hI⟩ | hnon
  · have hchip := hI.2.2.1 v
    have hvu : v = u := by
      by_contra hne
      rw [if_neg hne] at hchip
      omega
    subst hvu
    exact ⟨E, hI, spec.lemmaQ N hN hunit hcore hodd h3N hNS hD hDA hI⟩
  · exact absurd (hnon v) (by omega)

/-- **Unique representatives.**  Under `(¬S)` and `rank A ≥ 1`, each core
vertex `v` carries a chip in **exactly one** effective representative of the
class, namely the `v`-reduced state `D_v`.  In particular `v ↦ D_v` is
injective. -/
theorem corR_unique_rep (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4) (hrank : rank (spec.scale N hN).graph A ≥ 1) (v : Fin n) :
    ∃! D : CFDiv (spec.scale N hN).graph,
      effective D ∧ linear_equiv (spec.scale N hN).graph A D ∧
        0 < D ((spec.scale N hN).coreVertex v) := by
  -- Existence from `rank A ≥ 1` (which gives `winnable (A - v)`, so some
  -- effective representative carries a chip at `v`); the shape is the
  -- dichotomy, connectivity is `lemmaQ` and uniqueness is `typeI_unique`.
  classical
  obtain ⟨B, hBmem, hBlin⟩ := (Utilities.rank_ge_one_iff_winnable_sub_one_chip
    (spec.scale N hN).graph A).mp hrank ((spec.scale N hN).coreVertex v)
  have hBeff : effective B := hBmem
  obtain ⟨D₀, hDeff, hDlin, hDpos⟩ :
      ∃ D : CFDiv (spec.scale N hN).graph, effective D ∧
        linear_equiv (spec.scale N hN).graph A D ∧
          0 < D ((spec.scale N hN).coreVertex v) := by
    refine ⟨B + one_chip ((spec.scale N hN).coreVertex v),
      effective_add_one_chip hBeff _, ?_, ?_⟩
    · show B + one_chip ((spec.scale N hN).coreVertex v) - A
        ∈ principal_divisors (spec.scale N hN).graph
      have heq : B + one_chip ((spec.scale N hN).coreVertex v) - A
          = B - (A - one_chip ((spec.scale N hN).coreVertex v)) := by abel
      rw [heq]
      exact hBlin
    · rw [add_one_chip_apply_self]
      have := hBeff ((spec.scale N hN).coreVertex v)
      omega
  have hDdeg : deg D₀ = 4 := by
    rw [← linear_equiv_preserves_deg _ A _ hDlin]; exact hdeg
  obtain ⟨EB, hIB, hcB⟩ := spec.typeI_of_core_chip N hN hunit hcore hodd h3N hNS
    hDeff hDdeg hDlin hDpos
  refine ⟨D₀, ⟨hDeff, hDlin, hDpos⟩, ?_⟩
  rintro y ⟨hyeff, hylin, hypos⟩
  have hydeg : deg y = 4 := by
    rw [← linear_equiv_preserves_deg _ A y hylin]; exact hdeg
  obtain ⟨Ey, hIy, hcy⟩ := spec.typeI_of_core_chip N hN hunit hcore hodd h3N hNS
    hyeff hydeg hylin hypos
  exact spec.typeI_unique N hN hunit hIy hIB hcy hcB (hylin.symm.trans hDlin)

/-- **The dichotomy corollary.**  Under `(¬S)` every effective degree-four
representative is a state `D_v` — with the connectivity of `lemmaQ`
automatically available — or a non-state, carrying no core chip at all. -/
theorem corR_dichotomy (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    {D : CFDiv (spec.scale N hN).graph} (hD : effective D) (hdeg : deg D = 4)
    (hDA : linear_equiv (spec.scale N hN).graph A D) :
    (∃ v E, spec.IsState N hN D v E) ∨ spec.NonState N hN D := by
  rcases spec.structure_of_notSelected N hN hunit hodd h3N hNS hD hdeg hDA with
    ⟨v, E, hI⟩ | hnon
  · exact Or.inl ⟨v, E, hI, spec.lemmaQ N hN hunit hcore hodd h3N hNS hD hDA hI⟩
  · exact Or.inr hnon

end Spec

end SubdivisionGraph

end Utilities.Certificate
