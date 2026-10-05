module

public import Utilities.Subdivision.CoreCutsAndFlats
public import Utilities.Subdivision.SlotPropagation
public import Utilities.Subdivision.SlotIntervalFiring
public import Utilities.Gonality.LegalFiringChain

@[expose] public section

/-!
# The multi-firing bridge move at a general scale

A *bridge move* starts from a state with its core chip at `v` and a slot `f` at
`v` that is a bridge of the core with the chip slots of the state deleted.
Firing the side of that bridge containing `v`, together with the parts of slots
already swept, pushes the core chip into `f` and every chip on a slot crossing
the cut one fine step further out, until the crossing chips of largest offset
land on core vertices on the far side.

At a general scale a bridge move is therefore a **chain** of `τ*` firings,
indexed by `k = 0, …, τ* − 1`.  The raw data is bundled in `Spec.BridgeData`:

* a near side `W` with `v ∈ W`;
* a bridge slot `f` at `v` whose far endpoint leaves `W`;
* the crossing chip slots `X`, with `W`-side endpoints `z e` and chip offsets
  `t e ∈ [1, N − 1]` measured from `z e`;
* the cut condition `∂_G(W) ⊆ X ∪ {f}`;
* a rest divisor `R` carrying everything else.

Writing `s := sup_X t` and `τ* := N − s`, the chain is

```
bridgeDiv k = a_k(f) + Σ_{e ∈ X} a_{t e + k}(e) + R
bridgeSet k = core(W) ∪ int(slots inside W)
              ∪ {a_j(f) : 1 ≤ j ≤ k} ∪ {a_j(e) : e ∈ X, 1 ≤ j ≤ t e + k}
```

(the offsets on `f` measured from `v`, those on `e` from `z e`), and the four
theorems are `bridgeSet_legal`, `bridgeSet_step`, `bridgeDiv_linear_equiv` and
`bridgeSet_compl_legal`.  `bridgeDiv 0` is the state itself
(`sidePoint f v 0 = coreVertex v`); `bridgeDiv τ*` is the landing divisor, whose
core chips are counted by `bridgeDiv_tauStar_apply_coreVertex`.

`2 ≤ N` is *derived*, not assumed: `1 ≤ sup_X t` forces `X` to be nonempty and
its offsets to be interior.

Everything is stated at the abstract `Spec`; no concrete subdivided graph is
ever unfolded.  The module imports only `Utilities` (`CoreCutsAndFlats`,
`SlotIntervalFiring`, `SlotPropagation` and `LegalFiringChain`) and no other
module of this library; `GenusSixOddDescent/Moves.lean` adapts a state to the
data `BridgeData`.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Slot geometry at a general scale

Four facts about one slot that `SlotIntervalFiring` and `SlotPropagation` do not
already package, and that the bridge move needs: the arithmetic of the offset
reflection `sideOffset`, the swap of the two endpoints, the identification of the
far endpoint with `otherEnd`, and — the only genuinely new geometry — the
**neighbourhood of a core vertex** at a general scale. -/

/-- The offset **from the tail** of the point at offset `o` from the endpoint `z`
(equivalently, by involutivity, the offset from `z` of the point at tail-offset
`o`).  This is the numerical content of `sidePoint`
(`Utilities/Subdivision/SlotPropagation.lean`). -/
def sideOffset (g : Fin p) (z : Fin n) (o : ℕ) : ℕ :=
  if spec.core.tail g = z then o else N - o

theorem sidePoint_eq_slotPoint (g : Fin p) (z : Fin n) (k : ℕ) :
    spec.sidePoint N hN g z k = spec.slotPoint N hN g (spec.sideOffset N g z k) := by
  unfold sidePoint sideOffset
  split_ifs <;> rfl

theorem sideOffset_sideOffset (g : Fin p) (z : Fin n) {o : ℕ} (ho : o ≤ N) :
    spec.sideOffset N g z (spec.sideOffset N g z o) = o := by
  unfold sideOffset
  split_ifs <;> omega

theorem sideOffset_pos (g : Fin p) (z : Fin n) {o : ℕ} (h0 : 0 < o) (ho : o < N) :
    0 < spec.sideOffset N g z o := by
  unfold sideOffset
  split_ifs <;> omega

theorem sideOffset_lt (g : Fin p) (z : Fin n) {o : ℕ} (h0 : 0 < o) (ho : o < N) :
    spec.sideOffset N g z o < N := by
  unfold sideOffset
  split_ifs <;> omega

theorem sideOffset_le (g : Fin p) (z : Fin n) {o : ℕ} (ho : o ≤ N) :
    spec.sideOffset N g z o ≤ N := by
  unfold sideOffset
  split_ifs <;> omega

/-- Reading an interior point from the other endpoint reflects its offset. -/
theorem sidePoint_swap {g : Fin p} {z z' : Fin n}
    (hz : spec.core.Incident g z) (hz' : spec.core.Incident g z') (hne : z ≠ z')
    {c : ℕ} (hc : c ≤ N) :
    spec.sidePoint N hN g z' c = spec.sidePoint N hN g z (N - c) := by
  by_cases hc1 : spec.core.tail g = z
  · have hne' : spec.core.tail g ≠ z' := fun h => hne (hc1.symm.trans h)
    rw [spec.sidePoint_of_ne N hN g hne', spec.sidePoint_of_tail N hN g hc1]
  · have hhz : spec.core.head g = z := hz.resolve_left hc1
    have hc2 : spec.core.tail g = z' := by
      rcases hz' with h | h
      · exact h
      · exact absurd (hhz.symm.trans h) hne
    rw [spec.sidePoint_of_tail N hN g hc2, spec.sidePoint_of_ne N hN g hc1,
      show N - (N - c) = c by omega]

/-- Offset `N` from `z` is the far endpoint of the slot. -/
theorem sidePoint_last (hunit : spec.IsUnit) (g : Fin p) (z : Fin n) :
    spec.sidePoint N hN g z N
      = (spec.scale N hN).coreVertex (spec.core.otherEnd g z) := by
  by_cases hc : spec.core.tail g = z
  · rw [spec.sidePoint_last_of_tail N hN hunit g hc]
    congr 1
    show spec.core.head g = spec.core.otherEnd g z
    unfold ExplicitPotential.Core.otherEnd
    rw [ite_eq_left hc]
  · rw [spec.sidePoint_last_of_ne N hN g hc]
    congr 1
    show spec.core.tail g = spec.core.otherEnd g z
    unfold ExplicitPotential.Core.otherEnd
    rw [ite_eq_right hc]

/-- A slot has exactly two endpoints: anything incident to `g` other than `a` is
the far endpoint of `g` at `a`. -/
theorem eq_otherEnd_of_incident {g : Fin p} {a b : Fin n}
    (ha : spec.core.Incident g a) (hb : spec.core.Incident g b) (hab : a ≠ b) :
    b = spec.core.otherEnd g a := by
  unfold ExplicitPotential.Core.otherEnd
  by_cases hc : spec.core.tail g = a
  · rw [ite_eq_left hc]
    rcases hb with h | h
    · exact absurd (hc.symm.trans h) hab
    · exact h.symm
  · rw [ite_eq_right hc]
    have hha : spec.core.head g = a := ha.resolve_left hc
    rcases hb with h | h
    · exact h.symm
    · exact absurd (hha.symm.trans h) hab

/-! ### Distinguishing interior points of different slots -/

/-- An interior fine vertex remembers its slot. -/
theorem slot_eq_of_interiorVertex_eq {m q : ℕ} (sp : Spec m q) {e e' : Fin q}
    {j : Fin (sp.length e - 1)} {j' : Fin (sp.length e' - 1)}
    (h : sp.interiorVertex e j = sp.interiorVertex e' j') : e = e' :=
  congrArg Sigma.fst (Sum.inr.inj h)

/-- Interior offsets of distinct slots give distinct fine vertices. -/
theorem slot_eq_of_slotPoint_eq (hunit : spec.IsUnit) {g g' : Fin p} {a b : ℕ}
    (ha0 : 0 < a) (haN : a < N) (hb0 : 0 < b) (hbN : b < N)
    (h : spec.slotPoint N hN g a = spec.slotPoint N hN g' b) : g = g' := by
  obtain ⟨j, hj⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit g ha0 haN
  obtain ⟨j', hj'⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit g' hb0 hbN
  exact slot_eq_of_interiorVertex_eq _ (hj ▸ hj' ▸ h)

/-- A fine point at an interior offset is an `interiorVertex` of the same slot,
at the index one below the offset. -/
theorem slotPoint_eq_interiorVertex (hunit : spec.IsUnit) (g : Fin p) {o : ℕ}
    (h0 : 0 < o) (hoN : o < N) :
    ∃ j : Fin ((spec.scale N hN).length g - 1),
      j.val + 1 = o ∧ spec.slotPoint N hN g o = (spec.scale N hN).interiorVertex g j := by
  have hL := spec.length_scale N hN hunit g
  refine ⟨⟨o - 1, by omega⟩, by simp; omega, ?_⟩
  rw [spec.interiorVertex_eq_slotPoint N hN hunit g ⟨o - 1, by omega⟩]
  congr 1
  show o = o - 1 + 1
  omega

/-! ### The neighbourhood of a core vertex at a general scale

The proof is a case split on whether the unit step carrying the fine edge
starts or ends at the core vertex. -/

/-- **Every fine neighbour of a core vertex is the offset-one point of a slot at
that vertex.** -/
theorem exists_slot_of_coreVertex_adj (hunit : spec.IsUnit) (h2N : 2 ≤ N) (u : Fin n)
    {y : (spec.scale N hN).graph.V}
    (hy : 0 < num_edges (spec.scale N hN).graph ((spec.scale N hN).coreVertex u) y) :
    ∃ g : Fin p, spec.core.Incident g u ∧ y = spec.sidePoint N hN g u 1 := by
  obtain ⟨⟨e, o⟩, hstep⟩ :=
    ((spec.scale N hN).num_edges_pos_iff ((spec.scale N hN).coreVertex u) y).mp hy
  have hL := spec.length_scale N hN hunit e
  rcases hstep with hfwd | hbwd
  · simp only [unitEdge, Prod.mk.injEq] at hfwd
    obtain ⟨hleft, hright⟩ := hfwd
    -- `stepLeft e o = coreVertex u` forces `o = 0` and `tail e = u`.
    have hzero : o.val = 0 := by
      by_contra hne
      rw [stepLeft, dite_eq_right hne] at hleft
      simp [coreVertex, interiorVertex] at hleft
    rw [stepLeft, dite_eq_left hzero] at hleft
    have htail : spec.core.tail e = u := Sum.inl.inj hleft
    refine ⟨e, Or.inl htail, ?_⟩
    have hpos : (spec.scale N hN).stepRightPosition e o = spec.slotPos N hN e 1 := by
      apply Fin.ext
      show o.val + 1 = _
      rw [spec.slotPos_val N hN hunit e (show 1 ≤ N by omega)]
      omega
    rw [spec.sidePoint_of_tail N hN e htail 1, slotPoint_eq_pathVertex, ← hpos,
      (spec.scale N hN).pathVertex_stepRightPosition e o, hright]
  · simp only [unitEdge, Prod.mk.injEq] at hbwd
    obtain ⟨hleft, hright⟩ := hbwd
    have hlast : o.val + 1 = (spec.scale N hN).length e := by
      by_contra hne
      rw [stepRight, dite_eq_right hne] at hright
      simp [coreVertex, interiorVertex] at hright
    rw [stepRight, dite_eq_left hlast] at hright
    have hhead : spec.core.head e = u := Sum.inl.inj hright
    have hne : spec.core.tail e ≠ u := fun hcon =>
      spec.core_loopless e (hcon.trans hhead.symm)
    refine ⟨e, Or.inr hhead, ?_⟩
    have hpos : (spec.scale N hN).stepLeftPosition e o = spec.slotPos N hN e (N - 1) := by
      apply Fin.ext
      show o.val = _
      rw [spec.slotPos_val N hN hunit e (show N - 1 ≤ N by omega)]
      omega
    rw [spec.sidePoint_of_ne N hN e hne 1, slotPoint_eq_pathVertex, ← hpos,
      (spec.scale N hN).pathVertex_stepLeftPosition e o, hleft]

/-- A core vertex is joined to the offset-one point of each slot at it by exactly
one fine edge. -/
theorem num_edges_coreVertex_sidePoint (hunit : spec.IsUnit) (h2N : 2 ≤ N)
    {g : Fin p} {u : Fin n} (hinc : spec.core.Incident g u) :
    num_edges (spec.scale N hN).graph ((spec.scale N hN).coreVertex u)
      (spec.sidePoint N hN g u 1) = 1 := by
  have hpos := spec.num_edges_sidePoint_succ_pos N hN hunit g u (k := 0) hN
  rw [spec.sidePoint_zero N hN hunit g hinc, Nat.zero_add] at hpos
  have hle : num_edges (spec.scale N hN).graph (spec.sidePoint N hN g u 1)
      ((spec.scale N hN).coreVertex u) ≤ 1 := by
    rw [spec.sidePoint_eq_slotPoint N hN g u 1]
    exact spec.num_edges_slotPoint_le_one N hN hunit g
      (spec.sideOffset_pos N g u (by omega) (by omega))
      (spec.sideOffset_lt N g u (by omega) (by omega)) _
  rw [num_edges_symmetric] at hle
  omega

/-- **The outdegree of a core vertex**, as a cardinality.  The caller supplies the
index set `A` of slots at `u` whose offset-one point misses `S`; this keeps the
statement free of any decidability instance for `Incident`. -/
theorem outdeg_coreVertex_eq (hunit : spec.IsUnit) (h2N : 2 ≤ N)
    (S : Finset (spec.scale N hN).graph.V) (u : Fin n) (A : Finset (Fin p))
    (hA : ∀ g : Fin p,
      g ∈ A ↔ (spec.core.Incident g u ∧ spec.sidePoint N hN g u 1 ∉ S)) :
    outdeg_S (spec.scale N hN).graph S ((spec.scale N hN).coreVertex u)
      = (A.card : ℤ) := by
  classical
  -- The offset-one points of the slots of `A` are distinct and lie outside `S`.
  have hinj : ∀ a ∈ A, ∀ b ∈ A,
      spec.sidePoint N hN a u 1 = spec.sidePoint N hN b u 1 → a = b := by
    intro a ha b hb hab
    rw [spec.sidePoint_eq_slotPoint N hN a u 1, spec.sidePoint_eq_slotPoint N hN b u 1] at hab
    exact spec.slot_eq_of_slotPoint_eq N hN hunit
      (spec.sideOffset_pos N a u (by omega) (by omega))
      (spec.sideOffset_lt N a u (by omega) (by omega))
      (spec.sideOffset_pos N b u (by omega) (by omega))
      (spec.sideOffset_lt N b u (by omega) (by omega)) hab
  have hsub : A.image (fun g => spec.sidePoint N hN g u 1)
      ⊆ Finset.univ \ S := by
    intro y hy
    obtain ⟨g, hgA, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ((hA g).mp hgA).2⟩
  -- Outside that image the multiplicity vanishes.
  have hvanish : ∀ y ∈ Finset.univ \ S,
      y ∉ A.image (fun g => spec.sidePoint N hN g u 1) →
        (num_edges (spec.scale N hN).graph ((spec.scale N hN).coreVertex u) y : ℤ) = 0 := by
    intro y hy hynot
    have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
    by_contra hne
    have hpos : 0 < num_edges (spec.scale N hN).graph
        ((spec.scale N hN).coreVertex u) y := by
      rcases Nat.eq_zero_or_pos (num_edges (spec.scale N hN).graph
        ((spec.scale N hN).coreVertex u) y) with h | h
      · exact absurd (by rw [h]; norm_num) hne
      · exact h
    obtain ⟨g, hginc, rfl⟩ := spec.exists_slot_of_coreVertex_adj N hN hunit h2N u hpos
    exact hynot (Finset.mem_image.mpr ⟨g, (hA g).mpr ⟨hginc, hyS⟩, rfl⟩)
  unfold outdeg_S
  rw [← Finset.sum_subset hsub hvanish,
    Finset.sum_image hinj]
  rw [Finset.sum_congr rfl (fun g hg => by
    rw [spec.num_edges_coreVertex_sidePoint N hN hunit h2N ((hA g).mp hg).1])]
  simp

/-! ### Bounding `outdeg_S` from a description of the neighbours

Small local bounds on outgoing degrees, including the "exactly one"
refinement the step lemma needs. -/

private theorem outdeg_eq_zero_of_nbrs_mem {G : CFGraph} {S : Finset G.V} {x : G.V}
    (h : ∀ y : G.V, 0 < num_edges G x y → y ∈ S) : outdeg_S G S x = 0 := by
  unfold outdeg_S
  refine Finset.sum_eq_zero fun y hy => ?_
  have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
  have hz : num_edges G x y = 0 := by
    by_contra hne
    exact hyS (h y (Nat.pos_of_ne_zero hne))
  simp [hz]

private theorem outdeg_le_one_of_nbrs_mem {G : CFGraph} {S : Finset G.V} {x u : G.V}
    (hnbr : ∀ y : G.V, 0 < num_edges G x y → y ≠ u → y ∈ S)
    (hle : num_edges G x u ≤ 1) : outdeg_S G S x ≤ 1 := by
  classical
  have hstep : ∀ y ∈ Finset.univ \ S,
      (num_edges G x y : ℤ) ≤ if y = u then 1 else 0 := by
    intro y hy
    have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
    by_cases hyu : y = u
    · rw [ite_eq_left hyu, hyu]
      exact_mod_cast hle
    · rw [ite_eq_right hyu]
      have hz : num_edges G x y = 0 := by
        by_contra hne
        exact hyS (hnbr y (Nat.pos_of_ne_zero hne) hyu)
      simp [hz]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_ite_eq' (Finset.univ \ S) u (fun _ => (1 : ℤ))]
  split_ifs <;> norm_num

private theorem one_le_outdeg {G : CFGraph} {S : Finset G.V} {x u : G.V} (hu : u ∉ S)
    (h1 : 1 ≤ num_edges G x u) : 1 ≤ outdeg_S G S x := by
  have hle : (num_edges G x u : ℤ) ≤ outdeg_S G S x := by
    unfold outdeg_S
    exact Finset.single_le_sum (f := fun w : G.V => (num_edges G x w : ℤ))
      (fun _ _ => Int.natCast_nonneg _) (by simp [hu])
  have hone : (1 : ℤ) ≤ (num_edges G x u : ℤ) := by exact_mod_cast h1
  omega


/-! ## The raw data of a bridge move -/

/-- **The raw data of a multi-firing bridge move** at scale `N`.  Adapting a
state to this shape (computing `W`, `X`, `z` and `t` from a `TypeI` divisor) is
done by `stateBridgeData` in `GenusSixOddDescent/Moves.lean`; nothing below needs
to know where the data came from. -/
structure BridgeData where
  /-- The near side of the bridge. -/
  W : Finset (Fin n)
  /-- The core vertex the chain starts at. -/
  v : Fin n
  /-- The bridge slot at `v`. -/
  f : Fin p
  /-- The crossing chip slots. -/
  X : Finset (Fin p)
  /-- The `W`-side endpoint of each crossing slot. -/
  z : Fin p → Fin n
  /-- The offset of each crossing chip from its `W`-side endpoint. -/
  t : Fin p → ℕ
  /-- Everything the move does not touch. -/
  R : CFDiv (spec.scale N hN).graph
  /-- `v` lies on the near side. -/
  memW : v ∈ W
  /-- `f` is a slot at `v` … -/
  incF : spec.core.Incident f v
  /-- … whose far endpoint leaves `W`. -/
  farF : spec.core.otherEnd f v ∉ W
  /-- `f` carries no chip of its own, so it is not one of the crossing slots. -/
  notMemF : f ∉ X
  /-- Each crossing slot crosses the cut … -/
  crossX : ∀ e ∈ X, spec.core.Crosses W e
  /-- … at the endpoint `z e` … -/
  incX : ∀ e ∈ X, spec.core.Incident e (z e)
  /-- … which lies in `W`. -/
  memX : ∀ e ∈ X, z e ∈ W
  /-- **The cut condition**: `∂_G(W) ⊆ X ∪ {f}`. -/
  cutSub : ∀ g : Fin p, spec.core.Crosses W g → g ∈ X ∨ g = f
  /-- Each crossing chip is interior to its slot … -/
  onePos : ∀ e ∈ X, 1 ≤ t e
  /-- … on the far side of its `W`-endpoint. -/
  offLt : ∀ e ∈ X, t e ≤ N - 1
  /-- Some crossing slot carries a chip: `s ≥ 1`. -/
  supPos : 1 ≤ X.sup t

namespace BridgeData

variable {n p : ℕ} {spec : Spec n p} {N : ℕ} {hN : 0 < N} (d : spec.BridgeData N hN)

/-- `s = sup_{e ∈ X} t_e`, the largest crossing offset. -/
def sMax : ℕ := d.X.sup d.t

/-- `τ* = N − s`, the number of firings the move takes. -/
def tauStar : ℕ := N - d.sMax

theorem le_sMax {e : Fin p} (he : e ∈ d.X) : d.t e ≤ d.sMax := Finset.le_sup he

theorem sMax_le : d.sMax ≤ N - 1 := Finset.sup_le d.offLt

/-- The move crosses at least one chip slot, so the scale is at least two. -/
theorem two_le_scale (d : spec.BridgeData N hN) : 2 ≤ N := by
  have h := d.supPos
  rw [Finset.le_sup_iff (by norm_num : (0 : ℕ) < 1)] at h
  obtain ⟨e, he, hte⟩ := h
  have := d.offLt e he
  omega

theorem one_le_tauStar : 1 ≤ d.tauStar := by
  have h1 := d.sMax_le
  have h2 := d.two_le_scale
  unfold tauStar
  omega

theorem tauStar_le : d.tauStar ≤ N - 1 := by
  have h1 := d.supPos
  have h2 := d.two_le_scale
  unfold tauStar sMax
  omega

/-- The `f`-front stays interior throughout the chain. -/
theorem lt_scale_of_lt_tauStar {k : ℕ} (hk : k < d.tauStar) : k + 1 ≤ N - 1 := by
  have := d.tauStar_le
  omega

/-- Each crossing front stays interior throughout the chain. -/
theorem offset_add_le {k : ℕ} (hk : k < d.tauStar) {e : Fin p} (he : e ∈ d.X) :
    d.t e + k ≤ N - 1 := by
  have h1 := d.le_sMax he
  have h2 := d.sMax_le
  have h3 := d.two_le_scale
  have h4 : k < N - d.sMax := hk
  omega

theorem one_le_offset_add {k : ℕ} {e : Fin p} (he : e ∈ d.X) : 1 ≤ d.t e + k := by
  have := d.onePos e he
  omega

/-- The bridge slot crosses the cut. -/
theorem crossF : spec.core.Crosses d.W d.f := by
  have hfar := d.farF
  unfold ExplicitPotential.Core.otherEnd at hfar
  by_cases hc : spec.core.tail d.f = d.v
  · rw [ite_eq_left hc] at hfar
    exact Or.inl ⟨by rw [hc]; exact d.memW, hfar⟩
  · rw [ite_eq_right hc] at hfar
    exact Or.inr ⟨by rw [d.incF.resolve_left hc]; exact d.memW, hfar⟩

theorem ne_f_of_mem_X {e : Fin p} (he : e ∈ d.X) : e ≠ d.f := by
  intro h
  exact d.notMemF (h ▸ he)

/-- A crossing slot has exactly one endpoint in `W`. -/
theorem not_both_mem_of_crosses {g : Fin p} (hg : spec.core.Crosses d.W g) :
    ¬ (spec.core.tail g ∈ d.W ∧ spec.core.head g ∈ d.W) := by
  rintro ⟨h1, h2⟩
  rcases hg with ⟨-, h⟩ | ⟨-, h⟩
  · exact h h2
  · exact h h1

/-- On a crossing slot the `W`-endpoint is unique. -/
theorem eq_of_mem_W {g : Fin p} (hg : spec.core.Crosses d.W g) {a b : Fin n}
    (ha : spec.core.Incident g a) (hb : spec.core.Incident g b) (haW : a ∈ d.W)
    (hbW : b ∈ d.W) : a = b := by
  by_contra hne
  exact (spec.core.otherEnd_not_mem_of_crosses ha haW hg)
    (((spec.eq_otherEnd_of_incident ha hb hne) ▸ hbW))

/-! ## The divisor chain and the set chain -/

/-- The `f`-front at step `k`: offset `k` from `v` along the bridge. -/
def frontF (k : ℕ) : (spec.scale N hN).graph.V := spec.sidePoint N hN d.f d.v k

/-- The front of the crossing slot `e` at step `k`. -/
def frontX (e : Fin p) (k : ℕ) : (spec.scale N hN).graph.V :=
  spec.sidePoint N hN e (d.z e) (d.t e + k)

/-- **The divisor chain** `D_k = a_k(f) + Σ_{e ∈ X} a_{t e + k}(e) + R`. -/
def bridgeDiv (k : ℕ) : CFDiv (spec.scale N hN).graph :=
  one_chip (d.frontF k) + (∑ e ∈ d.X, one_chip (d.frontX e k)) + d.R

/-- Membership of the interior of the slot `g` at **tail**-offset `o` in the
`k`-th set of the chain. -/
def OnBridge (k : ℕ) (g : Fin p) (o : ℕ) : Prop :=
  (spec.core.tail g ∈ d.W ∧ spec.core.head g ∈ d.W)
    ∨ (g = d.f ∧ spec.sideOffset N g d.v o ≤ k)
    ∨ (g ∈ d.X ∧ spec.sideOffset N g (d.z g) o ≤ d.t g + k)

instance decidableOnBridge (k : ℕ) (g : Fin p) (o : ℕ) :
    Decidable (d.OnBridge k g o) := by
  unfold OnBridge
  infer_instance

/-- The membership predicate of `bridgeSet k`, as a function on fine vertices. -/
def Member (k : ℕ) : (spec.scale N hN).graph.V → Prop :=
  Sum.elim (fun u : Fin n => u ∈ d.W)
    (fun y : (spec.scale N hN).Interior => d.OnBridge k y.1 (y.2.val + 1))

instance decidableMember (k : ℕ) (x : (spec.scale N hN).graph.V) :
    Decidable (d.Member k x) := by
  rcases x with u | y
  · exact inferInstanceAs (Decidable (u ∈ d.W))
  · exact inferInstanceAs (Decidable (d.OnBridge k y.1 (y.2.val + 1)))

/-- **The set chain**: the core vertices of `W`, the interiors of the slots inside
`W`, the first `k` interior points of `f` from `v`, and the first `t e + k`
interior points of each crossing slot from `z e`. -/
def bridgeSet (k : ℕ) : Finset (spec.scale N hN).graph.V :=
  Finset.univ.filter (d.Member k)

theorem mem_bridgeSet (k : ℕ) (x : (spec.scale N hN).graph.V) :
    x ∈ d.bridgeSet k ↔ d.Member k x := by
  rw [bridgeSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **A core vertex lies in the set exactly when it lies in `W`.** -/
theorem coreVertex_mem_bridgeSet_iff (k : ℕ) (u : Fin n) :
    (spec.scale N hN).coreVertex u ∈ d.bridgeSet k ↔ u ∈ d.W :=
  d.mem_bridgeSet k _

theorem interiorVertex_mem_bridgeSet_iff (k : ℕ) (g : Fin p)
    (j : Fin ((spec.scale N hN).length g - 1)) :
    (spec.scale N hN).interiorVertex g j ∈ d.bridgeSet k ↔ d.OnBridge k g (j.val + 1) :=
  d.mem_bridgeSet k _

theorem slotPoint_mem_bridgeSet_iff (hunit : spec.IsUnit) (k : ℕ) (g : Fin p) {o : ℕ}
    (h0 : 0 < o) (hoN : o < N) :
    spec.slotPoint N hN g o ∈ d.bridgeSet k ↔ d.OnBridge k g o := by
  obtain ⟨j, hj, hjeq⟩ := spec.slotPoint_eq_interiorVertex N hN hunit g h0 hoN
  rw [hjeq, d.interiorVertex_mem_bridgeSet_iff, hj]

/-! ### The four membership rules, one per class of slot -/

/-- A slot with both endpoints in `W` is swallowed whole. -/
theorem mem_bridgeSet_of_inside (hunit : spec.IsUnit) (k : ℕ) {g : Fin p}
    (ht : spec.core.tail g ∈ d.W) (hh : spec.core.head g ∈ d.W) {o : ℕ} (ho : o ≤ N) :
    spec.slotPoint N hN g o ∈ d.bridgeSet k := by
  rcases Nat.eq_zero_or_pos o with rfl | h0
  · rw [spec.slotPoint_zero N hN g]
    exact (d.coreVertex_mem_bridgeSet_iff k _).mpr ht
  · by_cases hoN : o = N
    · rw [hoN, spec.slotPoint_last N hN hunit g]
      exact (d.coreVertex_mem_bridgeSet_iff k _).mpr hh
    · rw [d.slotPoint_mem_bridgeSet_iff hunit k g h0 (by omega)]
      exact Or.inl ⟨ht, hh⟩

/-- A slot with both endpoints outside `W` that is neither the bridge nor a
crossing slot is untouched. -/
theorem not_mem_bridgeSet_of_outside (hunit : spec.IsUnit) (k : ℕ) {g : Fin p}
    (ht : spec.core.tail g ∉ d.W) (hh : spec.core.head g ∉ d.W) (hf : g ≠ d.f)
    (hX : g ∉ d.X) {o : ℕ} (ho : o ≤ N) :
    spec.slotPoint N hN g o ∉ d.bridgeSet k := by
  rcases Nat.eq_zero_or_pos o with rfl | h0
  · rw [spec.slotPoint_zero N hN g]
    exact fun hc => ht ((d.coreVertex_mem_bridgeSet_iff k _).mp hc)
  · by_cases hoN : o = N
    · rw [hoN, spec.slotPoint_last N hN hunit g]
      exact fun hc => hh ((d.coreVertex_mem_bridgeSet_iff k _).mp hc)
    · rw [d.slotPoint_mem_bridgeSet_iff hunit k g h0 (by omega)]
      rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact ht h
      · exact hf h
      · exact hX h

/-- **The bridge is swallowed up to offset `k`.** -/
theorem mem_bridgeSet_frontF_iff (hunit : spec.IsUnit) {k : ℕ} (hkN : k < N) {c : ℕ}
    (hc : c ≤ N) :
    spec.sidePoint N hN d.f d.v c ∈ d.bridgeSet k ↔ c ≤ k := by
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · rw [spec.sidePoint_zero N hN hunit d.f d.incF]
    simpa using (d.coreVertex_mem_bridgeSet_iff k d.v).mpr d.memW
  · by_cases hcN : c = N
    · rw [hcN, spec.sidePoint_last N hN hunit d.f d.v]
      constructor
      · intro hmem
        exact absurd ((d.coreVertex_mem_bridgeSet_iff k _).mp hmem) d.farF
      · intro hle; omega
    · rw [spec.sidePoint_eq_slotPoint N hN d.f d.v c,
        d.slotPoint_mem_bridgeSet_iff hunit k d.f
          (spec.sideOffset_pos N d.f d.v h0 (by omega))
          (spec.sideOffset_lt N d.f d.v h0 (by omega))]
      unfold OnBridge
      rw [spec.sideOffset_sideOffset N d.f d.v hc]
      constructor
      · rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
        · exact absurd h (d.not_both_mem_of_crosses d.crossF)
        · exact h
        · exact absurd h d.notMemF
      · intro h
        exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- **A crossing slot is swallowed up to offset `t e + k`.** -/
theorem mem_bridgeSet_frontX_iff (hunit : spec.IsUnit) {k : ℕ} {e : Fin p}
    (he : e ∈ d.X) (hb : d.t e + k < N) {c : ℕ} (hc : c ≤ N) :
    spec.sidePoint N hN e (d.z e) c ∈ d.bridgeSet k ↔ c ≤ d.t e + k := by
  have hcross := d.crossX e he
  have hinc := d.incX e he
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · rw [spec.sidePoint_zero N hN hunit e hinc]
    simpa using (d.coreVertex_mem_bridgeSet_iff k (d.z e)).mpr (d.memX e he)
  · by_cases hcN : c = N
    · rw [hcN, spec.sidePoint_last N hN hunit e (d.z e)]
      constructor
      · intro hmem
        exact absurd ((d.coreVertex_mem_bridgeSet_iff k _).mp hmem)
          (spec.core.otherEnd_not_mem_of_crosses hinc (d.memX e he) hcross)
      · intro hle; omega
    · rw [spec.sidePoint_eq_slotPoint N hN e (d.z e) c,
        d.slotPoint_mem_bridgeSet_iff hunit k e
          (spec.sideOffset_pos N e (d.z e) h0 (by omega))
          (spec.sideOffset_lt N e (d.z e) h0 (by omega))]
      unfold OnBridge
      rw [spec.sideOffset_sideOffset N e (d.z e) hc]
      constructor
      · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h (d.not_both_mem_of_crosses hcross)
        · exact absurd h (d.ne_f_of_mem_X he)
        · exact h
      · intro h
        exact Or.inr (Or.inr ⟨he, h⟩)

/-! ## The elementary properties of the chain -/

/-- `D_0` is the state itself: its `f`-chip sits on the core vertex `v`. -/
theorem bridgeDiv_zero (hunit : spec.IsUnit) :
    d.bridgeDiv 0 = one_chip ((spec.scale N hN).coreVertex d.v)
      + (∑ e ∈ d.X, one_chip (spec.sidePoint N hN e (d.z e) (d.t e))) + d.R := by
  unfold bridgeDiv frontF frontX
  rw [spec.sidePoint_zero N hN hunit d.f d.incF]
  simp only [Nat.add_zero]

/-- Pointwise reading of the divisor chain. -/
theorem bridgeDiv_apply (k : ℕ) (x : (spec.scale N hN).graph.V) :
    d.bridgeDiv k x
      = one_chip (d.frontF k) x + (∑ e ∈ d.X, one_chip (d.frontX e k) x) + d.R x := by
  simp only [bridgeDiv, Pi.add_apply, Finset.sum_apply]

theorem effective_bridgeDiv (hR : effective d.R) (k : ℕ) : effective (d.bridgeDiv k) := by
  intro x
  have hsum : (0 : ℤ) ≤ ∑ e ∈ d.X, one_chip (d.frontX e k) x :=
    Finset.sum_nonneg fun e _ => by
      unfold one_chip; split_ifs <;> norm_num
  have hchip : (0 : ℤ) ≤ one_chip (d.frontF k) x := by
    unfold one_chip; split_ifs <;> norm_num
  have := hR x
  rw [ge_iff_le, d.bridgeDiv_apply k x]
  omega

theorem deg_bridgeDiv (k : ℕ) : deg (d.bridgeDiv k) = deg d.R + 1 + (d.X.card : ℤ) := by
  have hs : (∑ e ∈ d.X, deg (one_chip (d.frontX e k))) = (d.X.card : ℤ) := by
    rw [Finset.sum_congr rfl (fun e _ => deg_one_chip (d.frontX e k))]
    simp
  unfold bridgeDiv
  rw [map_add, map_add, deg_one_chip, map_sum, hs]
  ring

theorem bridgeSet_mono {k k' : ℕ} (hkk : k ≤ k') : d.bridgeSet k ⊆ d.bridgeSet k' := by
  intro x hx
  rw [d.mem_bridgeSet] at hx ⊢
  rcases x with u | y
  · exact hx
  · rcases hx with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, by omega⟩)

/-! ### Which class a slot belongs to -/

/-- **The four classes of slot**: inside `W`, outside `W`, a crossing chip slot,
or the bridge.  The cut condition is what makes the list exhaustive. -/
theorem slot_cases (g : Fin p) :
    (spec.core.tail g ∈ d.W ∧ spec.core.head g ∈ d.W)
      ∨ (spec.core.tail g ∉ d.W ∧ spec.core.head g ∉ d.W ∧ g ≠ d.f ∧ g ∉ d.X)
      ∨ g ∈ d.X ∨ g = d.f := by
  by_cases ht : spec.core.tail g ∈ d.W
  · by_cases hh : spec.core.head g ∈ d.W
    · exact Or.inl ⟨ht, hh⟩
    · exact Or.inr (Or.inr (d.cutSub g (Or.inl ⟨ht, hh⟩)))
  · by_cases hh : spec.core.head g ∈ d.W
    · exact Or.inr (Or.inr (d.cutSub g (Or.inr ⟨hh, ht⟩)))
    · refine Or.inr (Or.inl ⟨ht, hh, ?_, ?_⟩)
      · rintro rfl
        rcases d.crossF with ⟨h, -⟩ | ⟨h, -⟩
        · exact ht h
        · exact hh h
      · intro hX
        rcases d.crossX g hX with ⟨h, -⟩ | ⟨h, -⟩
        · exact ht h
        · exact hh h

/-! ### Evaluating the divisor chain

The four evaluations the legality and step theorems run on: at an interior point
of an untouched slot, at a point of the bridge, at a point of a crossing slot,
and at a core vertex. -/

/-- A front never sits at an interior offset of another slot. -/
theorem frontF_ne_slotPoint (hunit : spec.IsUnit) {k : ℕ} (hk : k ≤ N) {g : Fin p}
    (hg : g ≠ d.f) {o : ℕ} (h0 : 0 < o) (hoN : o < N) :
    d.frontF k ≠ spec.slotPoint N hN g o := by
  unfold frontF
  rw [spec.sidePoint_eq_slotPoint N hN d.f d.v k]
  set c := spec.sideOffset N d.f d.v k with hc
  have hcle : c ≤ N := spec.sideOffset_le N d.f d.v hk
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · rw [hc0, spec.slotPoint_zero N hN d.f]
    exact spec.coreVertex_ne_slotPoint N hN hunit _ g h0 hoN
  · by_cases hcN : c = N
    · rw [hcN, spec.slotPoint_last N hN hunit d.f]
      exact spec.coreVertex_ne_slotPoint N hN hunit _ g h0 hoN
    · intro heq
      exact hg (spec.slot_eq_of_slotPoint_eq N hN hunit hc0 (by omega) h0 hoN heq).symm

theorem frontX_ne_slotPoint (hunit : spec.IsUnit) {k : ℕ} {e : Fin p} (_he : e ∈ d.X)
    (hk : d.t e + k ≤ N) {g : Fin p} (hg : g ≠ e) {o : ℕ} (h0 : 0 < o) (hoN : o < N) :
    d.frontX e k ≠ spec.slotPoint N hN g o := by
  unfold frontX
  rw [spec.sidePoint_eq_slotPoint N hN e (d.z e) (d.t e + k)]
  set c := spec.sideOffset N e (d.z e) (d.t e + k) with hc
  have hcle : c ≤ N := spec.sideOffset_le N e (d.z e) hk
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · rw [hc0, spec.slotPoint_zero N hN e]
    exact spec.coreVertex_ne_slotPoint N hN hunit _ g h0 hoN
  · by_cases hcN : c = N
    · rw [hcN, spec.slotPoint_last N hN hunit e]
      exact spec.coreVertex_ne_slotPoint N hN hunit _ g h0 hoN
    · intro heq
      exact hg (spec.slot_eq_of_slotPoint_eq N hN hunit hc0 (by omega) h0 hoN heq).symm

/-- Away from the bridge and the crossing slots the chain is just `R`. -/
theorem bridgeDiv_apply_of_slot_other (hunit : spec.IsUnit) {k : ℕ} (hk : k ≤ N)
    (hkX : ∀ e ∈ d.X, d.t e + k ≤ N) {g : Fin p} (hgf : g ≠ d.f) (hgX : g ∉ d.X)
    {o : ℕ} (h0 : 0 < o) (hoN : o < N) :
    d.bridgeDiv k (spec.slotPoint N hN g o) = d.R (spec.slotPoint N hN g o) := by
  have hz : (∑ e ∈ d.X, one_chip (d.frontX e k) (spec.slotPoint N hN g o)) = 0 :=
    Finset.sum_eq_zero fun e he => one_chip_apply_other' _ _
      (d.frontX_ne_slotPoint hunit he (hkX e he) (by rintro rfl; exact hgX he) h0 hoN).symm
  rw [d.bridgeDiv_apply k,
    one_chip_apply_other' _ _ (d.frontF_ne_slotPoint hunit hk hgf h0 hoN).symm, hz]
  ring

/-- On the bridge the chain carries exactly the `f`-chip. -/
theorem bridgeDiv_apply_frontF (hunit : spec.IsUnit) {k c : ℕ} (hk : k ≤ N)
    (hkX : ∀ e ∈ d.X, d.t e + k ≤ N) (h0 : 0 < c) (hcN : c < N) :
    d.bridgeDiv k (spec.sidePoint N hN d.f d.v c)
      = (if c = k then (1 : ℤ) else 0) + d.R (spec.sidePoint N hN d.f d.v c) := by
  have hxs : spec.sidePoint N hN d.f d.v c
      = spec.slotPoint N hN d.f (spec.sideOffset N d.f d.v c) :=
    spec.sidePoint_eq_slotPoint N hN d.f d.v c
  have hint0 : 0 < spec.sideOffset N d.f d.v c := spec.sideOffset_pos N d.f d.v h0 hcN
  have hintN : spec.sideOffset N d.f d.v c < N := spec.sideOffset_lt N d.f d.v h0 hcN
  rw [d.bridgeDiv_apply k]
  have hzero : (∑ e ∈ d.X, one_chip (d.frontX e k) (spec.sidePoint N hN d.f d.v c)) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rw [hxs]
    exact one_chip_apply_other' _ _
      (d.frontX_ne_slotPoint hunit he (hkX e he)
        (by rintro rfl; exact d.notMemF he) hint0 hintN).symm
  rw [hzero]
  by_cases hck : c = k
  · rw [ite_eq_left hck, hck]
    unfold frontF
    rw [one_chip_apply_v]
    ring
  · rw [ite_eq_right hck]
    have hne : spec.sidePoint N hN d.f d.v c ≠ d.frontF k :=
      spec.sidePoint_ne N hN hunit d.f d.v (le_of_lt hcN) hk hck
    rw [one_chip_apply_other' _ _ hne]
    ring

/-- On a crossing slot the chain carries exactly that slot's chip. -/
theorem bridgeDiv_apply_frontX (hunit : spec.IsUnit) {k c : ℕ} {e : Fin p} (he : e ∈ d.X)
    (hk : k ≤ N) (hkX : ∀ e' ∈ d.X, d.t e' + k ≤ N) (h0 : 0 < c) (hcN : c < N) :
    d.bridgeDiv k (spec.sidePoint N hN e (d.z e) c)
      = (if c = d.t e + k then (1 : ℤ) else 0)
        + d.R (spec.sidePoint N hN e (d.z e) c) := by
  have hxs : spec.sidePoint N hN e (d.z e) c
      = spec.slotPoint N hN e (spec.sideOffset N e (d.z e) c) :=
    spec.sidePoint_eq_slotPoint N hN e (d.z e) c
  have hint0 : 0 < spec.sideOffset N e (d.z e) c := spec.sideOffset_pos N e (d.z e) h0 hcN
  have hintN : spec.sideOffset N e (d.z e) c < N := spec.sideOffset_lt N e (d.z e) h0 hcN
  rw [d.bridgeDiv_apply k]
  have hf0 : one_chip (d.frontF k) (spec.sidePoint N hN e (d.z e) c) = 0 := by
    rw [hxs]
    exact one_chip_apply_other' _ _
      (d.frontF_ne_slotPoint hunit hk (d.ne_f_of_mem_X he) hint0 hintN).symm
  rw [hf0, Finset.sum_eq_single_of_mem e he (fun e' he' hne => ?_)]
  · by_cases hct : c = d.t e + k
    · rw [ite_eq_left hct, hct]
      unfold frontX
      rw [one_chip_apply_v]
      ring
    · rw [ite_eq_right hct]
      have hne : spec.sidePoint N hN e (d.z e) c ≠ d.frontX e k :=
        spec.sidePoint_ne N hN hunit e (d.z e) (le_of_lt hcN) (hkX e he) hct
      rw [one_chip_apply_other' _ _ hne]
      ring
  · rw [hxs]
    exact one_chip_apply_other' _ _
      (d.frontX_ne_slotPoint hunit he' (hkX e' he') (Ne.symm hne) hint0 hintN).symm

/-- At a core vertex only a landing chip, or the `k = 0` chip at `v`, shows up. -/
theorem bridgeDiv_apply_coreVertex (hunit : spec.IsUnit) {k : ℕ} (hkN : k < N)
    (hkX : ∀ e ∈ d.X, d.t e + k ≤ N) (u : Fin n) :
    d.bridgeDiv k ((spec.scale N hN).coreVertex u)
      = (if k = 0 ∧ d.v = u then (1 : ℤ) else 0)
        + (∑ e ∈ d.X,
            (if d.t e + k = N ∧ spec.core.otherEnd e (d.z e) = u then (1 : ℤ) else 0))
        + d.R ((spec.scale N hN).coreVertex u) := by
  rw [d.bridgeDiv_apply k]
  congr 2
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · unfold frontF
      rw [spec.sidePoint_zero N hN hunit d.f d.incF]
      by_cases hvu : d.v = u
      · rw [ite_eq_left ⟨rfl, hvu⟩, hvu, one_chip_apply_v]
      · rw [ite_eq_right (fun h => hvu h.2)]
        exact one_chip_apply_other' _ _ (fun h => hvu (Sum.inl.inj h).symm)
    · rw [ite_eq_right (by omega : ¬ (k = 0 ∧ d.v = u))]
      unfold frontF
      rw [spec.sidePoint_eq_slotPoint N hN d.f d.v k]
      exact one_chip_apply_other' _ _
        (spec.coreVertex_ne_slotPoint N hN hunit u d.f
          (spec.sideOffset_pos N d.f d.v hk0 hkN)
          (spec.sideOffset_lt N d.f d.v hk0 hkN))
  · refine Finset.sum_congr rfl fun e he => ?_
    have h1 : 1 ≤ d.t e + k := d.one_le_offset_add he
    have h2 : d.t e + k ≤ N := hkX e he
    by_cases hlast : d.t e + k = N
    · by_cases hou : spec.core.otherEnd e (d.z e) = u
      · rw [ite_eq_left ⟨hlast, hou⟩]
        unfold frontX
        rw [hlast, spec.sidePoint_last N hN hunit e (d.z e), hou, one_chip_apply_v]
      · rw [ite_eq_right (fun h => hou h.2)]
        unfold frontX
        rw [hlast, spec.sidePoint_last N hN hunit e (d.z e)]
        exact one_chip_apply_other' _ _ (fun h => hou (Sum.inl.inj h).symm)
    · rw [ite_eq_right (fun h => hlast h.1)]
      unfold frontX
      rw [spec.sidePoint_eq_slotPoint N hN e (d.z e) (d.t e + k)]
      exact one_chip_apply_other' _ _
        (spec.coreVertex_ne_slotPoint N hN hunit u e
          (spec.sideOffset_pos N e (d.z e) (o := d.t e + k) (by omega) (by omega))
          (spec.sideOffset_lt N e (d.z e) (o := d.t e + k) (by omega) (by omega)))

/-! ## Legality of the `k`-th set -/

/-- Every slot at a core vertex of `W` has its offset-one point inside the set,
with the single exception of the bridge at `v` at step `k = 0`. -/
theorem sidePoint_one_mem_bridgeSet (hunit : spec.IsUnit) {k : ℕ} (hk : k < d.tauStar)
    {u : Fin n} (huW : u ∈ d.W) {g : Fin p} (hinc : spec.core.Incident g u) :
    (g = d.f ∧ u = d.v ∧ k = 0) ∨ spec.sidePoint N hN g u 1 ∈ d.bridgeSet k := by
  have h2N := d.two_le_scale
  have hkN : k < N := by have := d.tauStar_le; omega
  rcases d.slot_cases g with ⟨ht, hh⟩ | ⟨ht, hh, -, -⟩ | hX | hf
  · refine Or.inr ?_
    rw [spec.sidePoint_eq_slotPoint N hN g u 1]
    exact d.mem_bridgeSet_of_inside hunit k ht hh
      (spec.sideOffset_le N g u (by omega))
  · exfalso
    rcases hinc with h | h
    · exact ht (by rw [h]; exact huW)
    · exact hh (by rw [h]; exact huW)
  · refine Or.inr ?_
    have huz : u = d.z g :=
      d.eq_of_mem_W (d.crossX g hX) hinc (d.incX g hX) huW (d.memX g hX)
    rw [huz]
    rw [d.mem_bridgeSet_frontX_iff hunit hX
      (by have := d.offset_add_le hk hX; omega) (by omega)]
    have := d.onePos g hX
    omega
  · subst hf
    have huv : u = d.v := d.eq_of_mem_W d.crossF hinc d.incF huW d.memW
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Or.inl ⟨rfl, huv, rfl⟩
    · refine Or.inr ?_
      rw [huv, d.mem_bridgeSet_frontF_iff hunit hkN (by omega)]
      omega

/-- **Legality of the chain.**  For `k < τ*` the `k`-th set of the chain is legal
for the `k`-th divisor of the chain. -/
theorem bridgeSet_legal (hunit : spec.IsUnit) (hR : effective d.R) {k : ℕ}
    (hk : k < d.tauStar) :
    legal_set (spec.scale N hN).graph (d.bridgeDiv k) (d.bridgeSet k) := by
  classical
  have h2N := d.two_le_scale
  have hkN : k < N := by have := d.tauStar_le; omega
  have hkX : ∀ e ∈ d.X, d.t e + k ≤ N := fun e he => by
    have := d.offset_add_le hk he; omega
  intro x hx
  rcases x with u | ⟨g, j⟩
  · -- a core vertex of `W`
    have huW : u ∈ d.W := (d.coreVertex_mem_bridgeSet_iff k u).mp hx
    show outdeg_S (spec.scale N hN).graph (d.bridgeSet k)
      ((spec.scale N hN).coreVertex u) ≤ d.bridgeDiv k ((spec.scale N hN).coreVertex u)
    have hnbr := fun (g : Fin p) (hg : spec.core.Incident g u) =>
      d.sidePoint_one_mem_bridgeSet hunit hk huW hg
    by_cases hcase : u = d.v ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hcase
      have hone : outdeg_S (spec.scale N hN).graph (d.bridgeSet 0)
          ((spec.scale N hN).coreVertex d.v) ≤ 1 := by
        refine outdeg_le_one_of_nbrs_mem (u := spec.sidePoint N hN d.f d.v 1) ?_ ?_
        · intro y hy hyne
          obtain ⟨g, hginc, rfl⟩ :=
            spec.exists_slot_of_coreVertex_adj N hN hunit h2N d.v hy
          rcases hnbr g hginc with ⟨rfl, -, -⟩ | h
          · exact absurd rfl hyne
          · exact h
        · rw [spec.num_edges_coreVertex_sidePoint N hN hunit h2N d.incF]
      refine le_trans hone ?_
      rw [d.bridgeDiv_apply_coreVertex hunit hkN hkX d.v, ite_eq_left ⟨rfl, rfl⟩]
      have h1 : (0 : ℤ) ≤ ∑ e ∈ d.X,
          (if d.t e + 0 = N ∧ spec.core.otherEnd e (d.z e) = d.v then (1 : ℤ) else 0) :=
        Finset.sum_nonneg fun e _ => by split_ifs <;> norm_num
      have h2 := hR ((spec.scale N hN).coreVertex d.v)
      omega
    · have hzero : outdeg_S (spec.scale N hN).graph (d.bridgeSet k)
          ((spec.scale N hN).coreVertex u) = 0 := by
        refine outdeg_eq_zero_of_nbrs_mem fun y hy => ?_
        obtain ⟨g, hginc, rfl⟩ :=
          spec.exists_slot_of_coreVertex_adj N hN hunit h2N u hy
        rcases hnbr g hginc with ⟨-, h1, h2⟩ | h
        · exact absurd ⟨h1, h2⟩ hcase
        · exact h
      rw [hzero]
      exact d.effective_bridgeDiv hR k _
  · -- an interior fine vertex
    have hL := spec.length_scale N hN hunit g
    have ho0 : 0 < j.val + 1 := by omega
    have hoN : j.val + 1 < N := by have := j.isLt; omega
    have hxs : (spec.scale N hN).interiorVertex g j = spec.slotPoint N hN g (j.val + 1) :=
      spec.interiorVertex_eq_slotPoint N hN hunit g j
    have hxmem : spec.slotPoint N hN g (j.val + 1) ∈ d.bridgeSet k := hxs ▸ hx
    show outdeg_S (spec.scale N hN).graph (d.bridgeSet k)
      ((spec.scale N hN).interiorVertex g j)
        ≤ d.bridgeDiv k ((spec.scale N hN).interiorVertex g j)
    rw [hxs]
    rcases d.slot_cases g with ⟨ht, hh⟩ | ⟨ht, hh, hgf, hgX⟩ | hX | hf
    · -- a slot inside `W`: both neighbours are in the set
      have hz : outdeg_S (spec.scale N hN).graph (d.bridgeSet k)
          (spec.slotPoint N hN g (j.val + 1)) = 0 := by
        rw [spec.outdeg_slotPoint N hN hunit _ g ho0 hoN,
          ite_eq_left (d.mem_bridgeSet_of_inside hunit k ht hh (by omega)),
          ite_eq_left (d.mem_bridgeSet_of_inside hunit k ht hh (by omega))]
        norm_num
      rw [hz]
      exact d.effective_bridgeDiv hR k _
    · exact absurd hxmem
        (d.not_mem_bridgeSet_of_outside hunit k ht hh hgf hgX (by omega))
    · -- a crossing slot: the front has outdegree one and carries the chip
      set c := spec.sideOffset N g (d.z g) (j.val + 1) with hc
      have hc0 : 0 < c := spec.sideOffset_pos N g (d.z g) ho0 hoN
      have hcN : c < N := spec.sideOffset_lt N g (d.z g) ho0 hoN
      have hxc : spec.sidePoint N hN g (d.z g) c = spec.slotPoint N hN g (j.val + 1) := by
        rw [spec.sidePoint_eq_slotPoint N hN g (d.z g) c, hc,
          spec.sideOffset_sideOffset N g (d.z g) (by omega)]
      have hbnd : d.t g + k < N := by have := d.offset_add_le hk hX; omega
      have hmem : c ≤ d.t g + k := by
        rw [← d.mem_bridgeSet_frontX_iff hunit hX hbnd (le_of_lt hcN), hxc]
        exact hxmem
      rw [← hxc, spec.outdeg_sidePoint N hN hunit _ g (d.z g) hc0 hcN,
        ite_eq_left ((d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mpr (by omega))]
      by_cases hnext : c + 1 ≤ d.t g + k
      · rw [ite_eq_left ((d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mpr hnext)]
        simpa using d.effective_bridgeDiv hR k _
      · rw [ite_eq_right (fun hcon =>
          hnext ((d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mp hcon))]
        rw [d.bridgeDiv_apply_frontX hunit hX (by omega) hkX hc0 hcN,
          ite_eq_left (by omega : c = d.t g + k)]
        have := hR (spec.sidePoint N hN g (d.z g) c)
        omega
    · -- the bridge itself
      subst hf
      set c := spec.sideOffset N d.f d.v (j.val + 1) with hc
      have hc0 : 0 < c := spec.sideOffset_pos N d.f d.v ho0 hoN
      have hcN : c < N := spec.sideOffset_lt N d.f d.v ho0 hoN
      have hxc : spec.sidePoint N hN d.f d.v c = spec.slotPoint N hN d.f (j.val + 1) := by
        rw [spec.sidePoint_eq_slotPoint N hN d.f d.v c, hc,
          spec.sideOffset_sideOffset N d.f d.v (by omega)]
      have hmem : c ≤ k := by
        rw [← d.mem_bridgeSet_frontF_iff hunit hkN (le_of_lt hcN), hxc]
        exact hxmem
      rw [← hxc, spec.outdeg_sidePoint N hN hunit _ d.f d.v hc0 hcN,
        ite_eq_left ((d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mpr (by omega))]
      by_cases hnext : c + 1 ≤ k
      · rw [ite_eq_left ((d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mpr hnext)]
        simpa using d.effective_bridgeDiv hR k _
      · rw [ite_eq_right (fun hcon =>
          hnext ((d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mp hcon))]
        rw [d.bridgeDiv_apply_frontF hunit (by omega) hkX hc0 hcN,
          ite_eq_left (by omega : c = k)]
        have := hR (spec.sidePoint N hN d.f d.v c)
        omega

/-! ## The firing step -/

/-- **The landing rule.**  For a core vertex `u` off the near side, the slots at
`u` whose offset-one point lies in the `k`-th set are exactly the crossing slots
whose chip lands on `u` at the next step. -/
theorem landing_iff (hunit : spec.IsUnit) {k : ℕ} (hk : k < d.tauStar) {u : Fin n}
    (huW : u ∉ d.W) (g : Fin p) :
    g ∈ d.X.filter (fun e => d.t e + (k + 1) = N ∧ spec.core.otherEnd e (d.z e) = u)
      ↔ (spec.core.Incident g u ∧ spec.sidePoint N hN g u 1 ∈ d.bridgeSet k) := by
  have h2N := d.two_le_scale
  have htau := d.tauStar_le
  have hkN : k < N := by omega
  constructor
  · intro hg
    obtain ⟨hX, hlast, hou⟩ := Finset.mem_filter.mp hg
    have hzW := d.memX g hX
    have hzu : d.z g ≠ u := fun h => huW (h ▸ hzW)
    have hinc : spec.core.Incident g u := by
      rw [← hou]; exact spec.core.incident_otherEnd g (d.z g)
    refine ⟨hinc, ?_⟩
    rw [spec.sidePoint_swap N hN (d.incX g hX) hinc hzu (by omega),
      d.mem_bridgeSet_frontX_iff hunit hX (by omega) (by omega)]
    omega
  · rintro ⟨hinc, hmem⟩
    rcases d.slot_cases g with ⟨ht, hh⟩ | ⟨ht, hh, hgf, hgX⟩ | hX | hf
    · exfalso
      rcases hinc with h | h
      · exact huW (by rw [← h]; exact ht)
      · exact huW (by rw [← h]; exact hh)
    · exfalso
      rw [spec.sidePoint_eq_slotPoint N hN g u 1] at hmem
      exact d.not_mem_bridgeSet_of_outside hunit k ht hh hgf hgX
        (spec.sideOffset_le N g u (by omega)) hmem
    · have hzW := d.memX g hX
      have hzu : d.z g ≠ u := fun h => huW (h ▸ hzW)
      have hou : spec.core.otherEnd g (d.z g) = u :=
        (spec.eq_otherEnd_of_incident (d.incX g hX) hinc hzu).symm
      rw [spec.sidePoint_swap N hN (d.incX g hX) hinc hzu (by omega),
        d.mem_bridgeSet_frontX_iff hunit hX (by have := d.offset_add_le hk hX; omega)
          (by omega)] at hmem
      have := d.offset_add_le hk hX
      exact Finset.mem_filter.mpr ⟨hX, by omega, hou⟩
    · exfalso
      subst hf
      have hvu : d.v ≠ u := fun h => huW (h ▸ d.memW)
      rw [spec.sidePoint_swap N hN d.incF hinc hvu (by omega),
        d.mem_bridgeSet_frontF_iff hunit hkN (by omega)] at hmem
      omega

/-- **The step.**  Firing the `k`-th set carries the `k`-th divisor to the
`(k+1)`-st: every front advances one fine step outward. -/
theorem bridgeSet_step (hunit : spec.IsUnit) {k : ℕ} (hk : k < d.tauStar) :
    set_firing (spec.scale N hN).graph (d.bridgeDiv k) (d.bridgeSet k)
      = d.bridgeDiv (k + 1) := by
  classical
  have h2N := d.two_le_scale
  have htau := d.tauStar_le
  have hkN : k < N := by omega
  have hk1N : k + 1 < N := by omega
  have hkX : ∀ e ∈ d.X, d.t e + k ≤ N - 1 := fun e he => d.offset_add_le hk he
  have hkXle : ∀ e ∈ d.X, d.t e + k ≤ N := fun e he => by have := hkX e he; omega
  have hkX1 : ∀ e ∈ d.X, d.t e + (k + 1) ≤ N := fun e he => by have := hkX e he; omega
  funext x
  rcases x with u | ⟨g, j⟩
  · -- **core vertices**
    have hDk := d.bridgeDiv_apply_coreVertex hunit hkN hkXle u
    have hDk1 := d.bridgeDiv_apply_coreVertex hunit hk1N hkX1 u
    have hsum0 : (∑ e ∈ d.X,
        (if d.t e + k = N ∧ spec.core.otherEnd e (d.z e) = u then (1 : ℤ) else 0)) = 0 :=
      Finset.sum_eq_zero fun e he => ite_eq_right (fun h => by have := hkX e he; omega)
    show set_firing (spec.scale N hN).graph (d.bridgeDiv k) (d.bridgeSet k)
        ((spec.scale N hN).coreVertex u)
      = d.bridgeDiv (k + 1) ((spec.scale N hN).coreVertex u)
    by_cases huW : u ∈ d.W
    · -- on the near side: only the very first firing moves a chip off `v`
      have hmemS : (spec.scale N hN).coreVertex u ∈ d.bridgeSet k :=
        (d.coreVertex_mem_bridgeSet_iff k u).mpr huW
      have hnbr := fun (g : Fin p) (hg : spec.core.Incident g u) =>
        d.sidePoint_one_mem_bridgeSet hunit hk huW hg
      have hsum1 : (∑ e ∈ d.X,
          (if d.t e + (k + 1) = N ∧ spec.core.otherEnd e (d.z e) = u then (1 : ℤ) else 0))
            = 0 :=
        Finset.sum_eq_zero fun e he => ite_eq_right (fun h =>
          (spec.core.otherEnd_not_mem_of_crosses (d.incX e he) (d.memX e he)
            (d.crossX e he)) (by rw [h.2]; exact huW))
      have houtdeg : outdeg_S (spec.scale N hN).graph (d.bridgeSet k)
          ((spec.scale N hN).coreVertex u) = (if u = d.v ∧ k = 0 then (1 : ℤ) else 0) := by
        by_cases hcase : u = d.v ∧ k = 0
        · rw [ite_eq_left hcase]
          obtain ⟨hu, hk0⟩ := hcase
          have hfne : spec.sidePoint N hN d.f d.v 1 ∉ d.bridgeSet k := by
            rw [d.mem_bridgeSet_frontF_iff hunit hkN (by omega)]
            omega
          have hedge : num_edges (spec.scale N hN).graph
              ((spec.scale N hN).coreVertex u) (spec.sidePoint N hN d.f d.v 1) = 1 := by
            rw [hu]
            exact spec.num_edges_coreVertex_sidePoint N hN hunit h2N d.incF
          refine le_antisymm ?_ (one_le_outdeg hfne (by omega))
          refine outdeg_le_one_of_nbrs_mem (u := spec.sidePoint N hN d.f d.v 1) ?_
            (by omega)
          intro y hy hyne
          obtain ⟨g, hginc, rfl⟩ :=
            spec.exists_slot_of_coreVertex_adj N hN hunit h2N u hy
          rcases hnbr g hginc with ⟨hgf, hgu, -⟩ | h
          · exact absurd (show spec.sidePoint N hN g u 1 = spec.sidePoint N hN d.f d.v 1
              by rw [hgf, hgu]) hyne
          · exact h
        · rw [ite_eq_right hcase]
          refine outdeg_eq_zero_of_nbrs_mem fun y hy => ?_
          obtain ⟨g, hginc, rfl⟩ :=
            spec.exists_slot_of_coreVertex_adj N hN hunit h2N u hy
          rcases hnbr g hginc with ⟨-, h1, h2⟩ | h
          · exact absurd ⟨h1, h2⟩ hcase
          · exact h
      have hzero1 : (if k + 1 = 0 ∧ d.v = u then (1 : ℤ) else 0) = 0 :=
        ite_eq_right (fun h => by have h1 := h.1; omega)
      rw [set_firing_apply_of_mem _ _ hmemS, houtdeg, hDk, hDk1, hsum0, hsum1, hzero1]
      by_cases hcase : u = d.v ∧ k = 0
      · have e1 : (if u = d.v ∧ k = 0 then (1 : ℤ) else 0) = 1 := ite_eq_left hcase
        have e2 : (if k = 0 ∧ d.v = u then (1 : ℤ) else 0) = 1 :=
          ite_eq_left ⟨hcase.2, hcase.1.symm⟩
        rw [e1, e2]
        ring
      · have e1 : (if u = d.v ∧ k = 0 then (1 : ℤ) else 0) = 0 := ite_eq_right hcase
        have e2 : (if k = 0 ∧ d.v = u then (1 : ℤ) else 0) = 0 :=
          ite_eq_right (fun h => hcase ⟨h.2.symm, h.1⟩)
        rw [e1, e2]
        ring
    · -- off the near side: the landing chips arrive
      have hnotS : (spec.scale N hN).coreVertex u ∉ d.bridgeSet k := fun hc =>
        huW ((d.coreVertex_mem_bridgeSet_iff k u).mp hc)
      set A : Finset (Fin p) :=
        d.X.filter (fun e => d.t e + (k + 1) = N ∧ spec.core.otherEnd e (d.z e) = u)
        with hAdef
      have houtdeg : outdeg_S (spec.scale N hN).graph (d.bridgeSet k)ᶜ
          ((spec.scale N hN).coreVertex u) = (A.card : ℤ) := by
        refine spec.outdeg_coreVertex_eq N hN hunit h2N _ u A (fun g => ?_)
        constructor
        · intro hg
          obtain ⟨h1, h2⟩ := (d.landing_iff hunit hk huW g).mp hg
          exact ⟨h1, by simpa using h2⟩
        · rintro ⟨h1, h2⟩
          exact (d.landing_iff hunit hk huW g).mpr ⟨h1, by simpa using h2⟩
      have hcard : (A.card : ℤ) = ∑ e ∈ d.X,
          (if d.t e + (k + 1) = N ∧ spec.core.otherEnd e (d.z e) = u then (1 : ℤ) else 0) := by
        rw [hAdef, Finset.card_filter, Nat.cast_sum]
        exact Finset.sum_congr rfl fun e _ => by split_ifs <;> norm_num
      have hzeroA : (if k = 0 ∧ d.v = u then (1 : ℤ) else 0) = 0 :=
        ite_eq_right (fun h => huW (by rw [← h.2]; exact d.memW))
      have hzero1 : (if k + 1 = 0 ∧ d.v = u then (1 : ℤ) else 0) = 0 :=
        ite_eq_right (fun h => by have h1 := h.1; omega)
      rw [set_firing_apply_of_not_mem _ _ hnotS, houtdeg, hcard, hDk, hDk1, hsum0,
        hzeroA, hzero1]
      ring
  · -- **interior fine vertices**
    have hL := spec.length_scale N hN hunit g
    have ho0 : 0 < j.val + 1 := by omega
    have hoN : j.val + 1 < N := by have := j.isLt; omega
    have hxs : (spec.scale N hN).interiorVertex g j = spec.slotPoint N hN g (j.val + 1) :=
      spec.interiorVertex_eq_slotPoint N hN hunit g j
    show set_firing (spec.scale N hN).graph (d.bridgeDiv k) (d.bridgeSet k)
        ((spec.scale N hN).interiorVertex g j)
      = d.bridgeDiv (k + 1) ((spec.scale N hN).interiorVertex g j)
    rw [hxs]
    rcases d.slot_cases g with ⟨ht, hh⟩ | ⟨ht, hh, hgf, hgX⟩ | hX | hf
    · -- a slot inside `W`: untouched, and fully contained
      have hgf : g ≠ d.f := by
        rintro rfl; exact d.not_both_mem_of_crosses d.crossF ⟨ht, hh⟩
      have hgX : g ∉ d.X := fun hc => d.not_both_mem_of_crosses (d.crossX g hc) ⟨ht, hh⟩
      rw [set_firing_apply_of_mem _ _
          (d.mem_bridgeSet_of_inside hunit k ht hh (o := j.val + 1) (by omega)),
        spec.outdeg_slotPoint N hN hunit _ g ho0 hoN,
        ite_eq_left (d.mem_bridgeSet_of_inside hunit k ht hh (by omega)),
        ite_eq_left (d.mem_bridgeSet_of_inside hunit k ht hh (by omega)),
        d.bridgeDiv_apply_of_slot_other hunit (by omega) hkXle hgf hgX ho0 hoN,
        d.bridgeDiv_apply_of_slot_other hunit (by omega) hkX1 hgf hgX ho0 hoN]
      ring
    · -- a slot outside `W`: untouched, and disjoint from the set
      have hnotS : ∀ o : ℕ, o ≤ N → spec.slotPoint N hN g o ∉ d.bridgeSet k :=
        fun o ho => d.not_mem_bridgeSet_of_outside hunit k ht hh hgf hgX ho
      rw [set_firing_apply_of_not_mem _ _ (hnotS _ (by omega)),
        spec.outdeg_slotPoint N hN hunit _ g ho0 hoN,
        ite_eq_left (Finset.mem_compl.mpr (hnotS _ (by omega))),
        ite_eq_left (Finset.mem_compl.mpr (hnotS _ (by omega))),
        d.bridgeDiv_apply_of_slot_other hunit (by omega) hkXle hgf hgX ho0 hoN,
        d.bridgeDiv_apply_of_slot_other hunit (by omega) hkX1 hgf hgX ho0 hoN]
      ring
    · -- a crossing slot: its front advances one step
      have hbnd : d.t g + k < N := by have := hkX g hX; omega
      set c := spec.sideOffset N g (d.z g) (j.val + 1) with hc
      have hc0 : 0 < c := spec.sideOffset_pos N g (d.z g) ho0 hoN
      have hcN : c < N := spec.sideOffset_lt N g (d.z g) ho0 hoN
      have hxc : spec.sidePoint N hN g (d.z g) c = spec.slotPoint N hN g (j.val + 1) := by
        rw [spec.sidePoint_eq_slotPoint N hN g (d.z g) c, hc,
          spec.sideOffset_sideOffset N g (d.z g) (by omega)]
      rw [← hxc, d.bridgeDiv_apply_frontX hunit hX (by omega) hkX1 hc0 hcN]
      by_cases hin : c ≤ d.t g + k
      · rw [set_firing_apply_of_mem _ _
            ((d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mpr hin),
          spec.outdeg_sidePoint N hN hunit _ g (d.z g) hc0 hcN,
          ite_eq_left ((d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mpr (by omega)),
          d.bridgeDiv_apply_frontX hunit hX (by omega) hkXle hc0 hcN]
        by_cases hnext : c + 1 ≤ d.t g + k
        · rw [ite_eq_left ((d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mpr hnext),
            ite_eq_right (by omega : ¬ c = d.t g + k), ite_eq_right (by omega : ¬ c = d.t g + (k + 1))]
          ring
        · rw [ite_eq_right (fun hcon => hnext
              ((d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mp hcon)),
            ite_eq_left (by omega : c = d.t g + k),
            ite_eq_right (by omega : ¬ c = d.t g + (k + 1))]
          ring
      · have hnotS : spec.sidePoint N hN g (d.z g) c ∉ d.bridgeSet k := fun hcon =>
          hin ((d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mp hcon)
        rw [set_firing_apply_of_not_mem _ _ hnotS,
          spec.outdeg_sidePoint N hN hunit _ g (d.z g) hc0 hcN,
          d.bridgeDiv_apply_frontX hunit hX (by omega) hkXle hc0 hcN,
          ite_eq_right (by omega : ¬ c = d.t g + k)]
        have h2 : spec.sidePoint N hN g (d.z g) (c + 1) ∉ d.bridgeSet k := fun hcon => by
          have := (d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mp hcon
          omega
        by_cases hprev : c = d.t g + (k + 1)
        · have h1 : spec.sidePoint N hN g (d.z g) (c - 1) ∈ d.bridgeSet k :=
            (d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mpr (by omega)
          rw [ite_eq_right (by simpa using h1), ite_eq_left (Finset.mem_compl.mpr h2), ite_eq_left hprev]
          ring
        · have h1 : spec.sidePoint N hN g (d.z g) (c - 1) ∉ d.bridgeSet k := fun hcon => by
            have := (d.mem_bridgeSet_frontX_iff hunit hX hbnd (by omega)).mp hcon
            omega
          rw [ite_eq_left (Finset.mem_compl.mpr h1), ite_eq_left (Finset.mem_compl.mpr h2),
            ite_eq_right hprev]
          ring
    · -- the bridge: its front advances one step
      subst hf
      set c := spec.sideOffset N d.f d.v (j.val + 1) with hc
      have hc0 : 0 < c := spec.sideOffset_pos N d.f d.v ho0 hoN
      have hcN : c < N := spec.sideOffset_lt N d.f d.v ho0 hoN
      have hxc : spec.sidePoint N hN d.f d.v c = spec.slotPoint N hN d.f (j.val + 1) := by
        rw [spec.sidePoint_eq_slotPoint N hN d.f d.v c, hc,
          spec.sideOffset_sideOffset N d.f d.v (by omega)]
      rw [← hxc, d.bridgeDiv_apply_frontF hunit (by omega) hkX1 hc0 hcN]
      by_cases hin : c ≤ k
      · rw [set_firing_apply_of_mem _ _
            ((d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mpr hin),
          spec.outdeg_sidePoint N hN hunit _ d.f d.v hc0 hcN,
          ite_eq_left ((d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mpr (by omega)),
          d.bridgeDiv_apply_frontF hunit (by omega) hkXle hc0 hcN]
        by_cases hnext : c + 1 ≤ k
        · rw [ite_eq_left ((d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mpr hnext),
            ite_eq_right (by omega : ¬ c = k), ite_eq_right (by omega : ¬ c = k + 1)]
          ring
        · rw [ite_eq_right (fun hcon => hnext
              ((d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mp hcon)),
            ite_eq_left (by omega : c = k), ite_eq_right (by omega : ¬ c = k + 1)]
          ring
      · have hnotS : spec.sidePoint N hN d.f d.v c ∉ d.bridgeSet k := fun hcon =>
          hin ((d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mp hcon)
        rw [set_firing_apply_of_not_mem _ _ hnotS,
          spec.outdeg_sidePoint N hN hunit _ d.f d.v hc0 hcN,
          d.bridgeDiv_apply_frontF hunit (by omega) hkXle hc0 hcN,
          ite_eq_right (by omega : ¬ c = k)]
        have h2 : spec.sidePoint N hN d.f d.v (c + 1) ∉ d.bridgeSet k := fun hcon => by
          have := (d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mp hcon
          omega
        by_cases hprev : c = k + 1
        · have h1 : spec.sidePoint N hN d.f d.v (c - 1) ∈ d.bridgeSet k :=
            (d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mpr (by omega)
          rw [ite_eq_right (by simpa using h1), ite_eq_left (Finset.mem_compl.mpr h2), ite_eq_left hprev]
          ring
        · have h1 : spec.sidePoint N hN d.f d.v (c - 1) ∉ d.bridgeSet k := fun hcon => by
            have := (d.mem_bridgeSet_frontF_iff hunit hkN (by omega)).mp hcon
            omega
          rw [ite_eq_left (Finset.mem_compl.mpr h1), ite_eq_left (Finset.mem_compl.mpr h2),
            ite_eq_right hprev]
          ring

/-! ## The chain is a chain of legal moves -/

/-- **Every divisor of the chain is linearly equivalent to the state.** -/
theorem bridgeDiv_linear_equiv (hunit : spec.IsUnit) {k : ℕ} (hk : k ≤ d.tauStar) :
    linear_equiv (spec.scale N hN).graph (d.bridgeDiv 0) (d.bridgeDiv k) := by
  induction k with
  | zero => exact linear_equiv.refl _ _
  | succ i ih =>
      refine linear_equiv.trans (ih (by omega)) ?_
      rw [← d.bridgeSet_step hunit (show i < d.tauStar by omega)]
      exact linear_equiv_set_firing _ _

/-- **Reversibility.**  The complement of the `k`-th set is legal for the
`(k+1)`-st divisor (`Utilities.Gonality.legalSet_compl_setFiring`). -/
theorem bridgeSet_compl_legal (hunit : spec.IsUnit) (hR : effective d.R) {k : ℕ}
    (hk : k < d.tauStar) :
    legal_set (spec.scale N hN).graph (d.bridgeDiv (k + 1)) (d.bridgeSet k)ᶜ := by
  have h := _root_.Utilities.Gonality.legalSet_compl_setFiring
    (d.effective_bridgeDiv hR k) (d.bridgeSet_legal hunit hR hk)
  rwa [d.bridgeSet_step hunit hk] at h

/-- … and firing it walks the chain back one step. -/
theorem setFiring_bridgeSet_compl (hunit : spec.IsUnit) {k : ℕ} (hk : k < d.tauStar) :
    set_firing (spec.scale N hN).graph (d.bridgeDiv (k + 1)) (d.bridgeSet k)ᶜ
      = d.bridgeDiv k := by
  rw [← d.bridgeSet_step hunit hk]
  exact _root_.Utilities.Gonality.set_firing_compl_set_firing _ _

/-! ## The landing form -/

theorem tauStar_lt : d.tauStar < N := by
  have := d.tauStar_le
  have := d.two_le_scale
  omega

theorem offset_add_tauStar_le {e : Fin p} (he : e ∈ d.X) : d.t e + d.tauStar ≤ N := by
  have h1 := d.le_sMax he
  have h2 := d.sMax_le
  unfold tauStar
  omega

/-- **The landing divisor, at a core vertex.**  A chip arrives at `u` for each
crossing slot of *maximal* offset whose far endpoint is `u`; nothing else does. -/
theorem bridgeDiv_tauStar_apply_coreVertex (hunit : spec.IsUnit) (u : Fin n) :
    d.bridgeDiv d.tauStar ((spec.scale N hN).coreVertex u)
      = ((d.X.filter
            (fun e => d.t e = d.sMax ∧ spec.core.otherEnd e (d.z e) = u)).card : ℤ)
        + d.R ((spec.scale N hN).coreVertex u) := by
  classical
  have h2N := d.two_le_scale
  have htau := d.one_le_tauStar
  have hsm := d.sMax_le
  rw [d.bridgeDiv_apply_coreVertex hunit d.tauStar_lt (fun e he => d.offset_add_tauStar_le he) u,
    ite_eq_right (fun h => by have h1 := h.1; omega)]
  have hcard : ((d.X.filter
        (fun e => d.t e = d.sMax ∧ spec.core.otherEnd e (d.z e) = u)).card : ℤ)
      = ∑ e ∈ d.X, (if d.t e + d.tauStar = N ∧ spec.core.otherEnd e (d.z e) = u
          then (1 : ℤ) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have h1 := d.le_sMax he
    have h2 : d.t e + d.tauStar = N ↔ d.t e = d.sMax := by
      unfold tauStar
      omega
    by_cases hc : d.t e = d.sMax ∧ spec.core.otherEnd e (d.z e) = u
    · rw [ite_eq_left hc, ite_eq_left ⟨h2.mpr hc.1, hc.2⟩]
      norm_num
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h2.mp h.1, h.2⟩)]
      norm_num
  rw [hcard]
  ring

/-- **The landing divisor, on the bridge.**  Its `f`-chip sits at the interior
offset `τ*` from `v`, and `1 ≤ τ* ≤ N − 1`. -/
theorem bridgeDiv_tauStar_apply_frontF (hunit : spec.IsUnit) :
    d.bridgeDiv d.tauStar (spec.sidePoint N hN d.f d.v d.tauStar)
      = 1 + d.R (spec.sidePoint N hN d.f d.v d.tauStar) := by
  have htau := d.one_le_tauStar
  rw [d.bridgeDiv_apply_frontF hunit (le_of_lt d.tauStar_lt)
      (fun e he => d.offset_add_tauStar_le he) (by omega) d.tauStar_lt,
    ite_eq_left rfl]

/-- **The landing divisor, on a crossing slot of non-maximal offset.**  Its chip
is still interior. -/
theorem bridgeDiv_tauStar_apply_frontX (hunit : spec.IsUnit) {e : Fin p} (he : e ∈ d.X)
    (hlt : d.t e < d.sMax) :
    d.bridgeDiv d.tauStar (spec.sidePoint N hN e (d.z e) (d.t e + d.tauStar))
      = 1 + d.R (spec.sidePoint N hN e (d.z e) (d.t e + d.tauStar)) := by
  have h1 := d.onePos e he
  have h2 := d.sMax_le
  have h3 : d.t e + d.tauStar < N := by unfold tauStar; omega
  rw [d.bridgeDiv_apply_frontX hunit he (le_of_lt d.tauStar_lt)
      (fun e' he' => d.offset_add_tauStar_le he') (by omega) h3,
    ite_eq_left rfl]

/-! ## Uniqueness of the legal sets of `D_k`

Write `D_k = bridgeDiv k` and `S_k = bridgeSet k`.  For `1 ≤ k < τ*` the only
proper legal sets of `D_k` are `S_k` and `S_{k−1}ᶜ`.  The
statement needs the rest divisor `R` to be *confined* — the raw form of "`D_k` is
a state divisor with one chip per chip slot" — and it needs the connectivity
input that `G` minus the chip slots has exactly the two sides `W` and `Wᶜ`. -/

/-- **The confinement hypotheses on the rest divisor**, in raw form.

`chipSlots` is the list of slots that may carry a chip: the bridge, the crossing
slots, and whatever slots `R` lives on.  The last field is the connectivity
input: every set closed in `G − chipSlots` is `∅`, `W`, `Wᶜ` or everything, i.e.
`W` and `Wᶜ` are the two components of `G − chipSlots`. -/
structure Confined where
  /-- The slots that may carry a chip. -/
  chipSlots : Finset (Fin p)
  /-- The bridge is one of them … -/
  memF : d.f ∈ chipSlots
  /-- … and so is every crossing slot. -/
  subX : d.X ⊆ chipSlots
  /-- `R` is effective. -/
  eff : effective d.R
  /-- `R` carries no chip on a core vertex. -/
  coreFree : ∀ u : Fin n, d.R ((spec.scale N hN).coreVertex u) = 0
  /-- `R` carries no chip on a slot outside `chipSlots`. -/
  slotFree : ∀ g : Fin p, g ∉ chipSlots → ∀ j : ℕ, 0 < j → j < N →
    d.R (spec.slotPoint N hN g j) = 0
  /-- `R` carries no chip on a crossing slot — in particular none on `f` or on any
  `e ∈ X`, whose chips are the fronts of the chain. -/
  crossFree : ∀ g : Fin p, spec.core.Crosses d.W g → ∀ j : ℕ, 0 < j → j < N →
    d.R (spec.slotPoint N hN g j) = 0
  /-- `R` carries at most one chip on each slot interior. -/
  oneChip : ∀ g : Fin p, ∑ j ∈ Finset.Ioo 0 N, d.R (spec.slotPoint N hN g j) ≤ 1
  /-- **Connectivity**: `W` and `Wᶜ` are the two components of `G − chipSlots`. -/
  closedOff : ∀ U : Finset (Fin n), spec.core.ClosedOff chipSlots U →
    U = ∅ ∨ U = d.W ∨ U = d.Wᶜ ∨ U = Finset.univ

namespace Confined

variable {d}

/-- Away from the fronts the chain is chipless on core vertices. -/
theorem bridgeDiv_coreVertex (c : d.Confined) (hunit : spec.IsUnit) {k : ℕ} (hk0 : 1 ≤ k)
    (hk : k < d.tauStar) (u : Fin n) :
    d.bridgeDiv k ((spec.scale N hN).coreVertex u) = 0 := by
  have h2N := d.two_le_scale
  have htau := d.tauStar_le
  have hkX : ∀ e ∈ d.X, d.t e + k ≤ N - 1 := fun e he => d.offset_add_le hk he
  rw [d.bridgeDiv_apply_coreVertex hunit (by omega) (fun e he => by
      have := hkX e he; omega) u,
    ite_eq_right (fun h => by have h1 := h.1; omega), c.coreFree u,
    Finset.sum_eq_zero (fun e he => ite_eq_right (fun h => by
      have := hkX e he; have h1 := h.1; omega))]
  ring

/-- A slot outside `chipSlots` is chipless for the chain. -/
theorem bridgeDiv_slotFree (c : d.Confined) (hunit : spec.IsUnit) {k : ℕ} (hk : k < d.tauStar)
    {g : Fin p} (hg : g ∉ c.chipSlots) {j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    d.bridgeDiv k (spec.slotPoint N hN g j) = 0 := by
  have htau := d.tauStar_le
  have h2N := d.two_le_scale
  rw [d.bridgeDiv_apply_of_slot_other hunit (by omega)
      (fun e he => by have := d.offset_add_le hk he; omega)
      (by rintro rfl; exact hg c.memF) (fun h => hg (c.subX h)) hj0 hjN,
    c.slotFree g hg j hj0 hjN]

/-- **At most one chip per slot interior** for the chain, which is what all the
propagation lemmas consume. -/
theorem bridgeDiv_interior_le_one (c : d.Confined) (hunit : spec.IsUnit) {k : ℕ} (_hk0 : 1 ≤ k)
    (hk : k < d.tauStar) (g : Fin p) :
    ∑ j ∈ Finset.Ioo 0 N, d.bridgeDiv k (spec.slotPoint N hN g j) ≤ 1 := by
  classical
  have h2N := d.two_le_scale
  have htau := d.tauStar_le
  have hkN : k ≤ N := by omega
  have hkXle : ∀ e ∈ d.X, d.t e + k ≤ N := fun e he => by
    have := d.offset_add_le hk he; omega
  by_cases hgf : g = d.f
  · subst hgf
    have hrw : ∀ j ∈ Finset.Ioo 0 N, d.bridgeDiv k (spec.slotPoint N hN d.f j)
        = (if j = spec.sideOffset N d.f d.v k then (1 : ℤ) else 0) := by
      intro j hj
      rw [Finset.mem_Ioo] at hj
      have hxj : spec.slotPoint N hN d.f j
          = spec.sidePoint N hN d.f d.v (spec.sideOffset N d.f d.v j) := by
        rw [spec.sidePoint_eq_slotPoint N hN d.f d.v,
          spec.sideOffset_sideOffset N d.f d.v (by omega)]
      rw [hxj, d.bridgeDiv_apply_frontF hunit hkN hkXle
          (spec.sideOffset_pos N d.f d.v hj.1 hj.2)
          (spec.sideOffset_lt N d.f d.v hj.1 hj.2),
        ← hxj, c.crossFree d.f d.crossF j hj.1 hj.2]
      have hiff : spec.sideOffset N d.f d.v j = k ↔ j = spec.sideOffset N d.f d.v k := by
        constructor
        · intro h; rw [← h, spec.sideOffset_sideOffset N d.f d.v (by omega)]
        · intro h; rw [h, spec.sideOffset_sideOffset N d.f d.v hkN]
      by_cases hc : j = spec.sideOffset N d.f d.v k
      · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]; ring
      · rw [ite_eq_right (fun hcon => hc (hiff.mp hcon)), ite_eq_right hc]; ring
    rw [Finset.sum_congr rfl hrw, Finset.sum_ite_eq' (Finset.Ioo 0 N)
      (spec.sideOffset N d.f d.v k) (fun _ => (1 : ℤ))]
    split_ifs <;> norm_num
  · by_cases hgX : g ∈ d.X
    · have hrw : ∀ j ∈ Finset.Ioo 0 N, d.bridgeDiv k (spec.slotPoint N hN g j)
          = (if j = spec.sideOffset N g (d.z g) (d.t g + k) then (1 : ℤ) else 0) := by
        intro j hj
        rw [Finset.mem_Ioo] at hj
        have hxj : spec.slotPoint N hN g j
            = spec.sidePoint N hN g (d.z g) (spec.sideOffset N g (d.z g) j) := by
          rw [spec.sidePoint_eq_slotPoint N hN g (d.z g),
            spec.sideOffset_sideOffset N g (d.z g) (by omega)]
        rw [hxj, d.bridgeDiv_apply_frontX hunit hgX hkN hkXle
            (spec.sideOffset_pos N g (d.z g) hj.1 hj.2)
            (spec.sideOffset_lt N g (d.z g) hj.1 hj.2),
          ← hxj, c.crossFree g (d.crossX g hgX) j hj.1 hj.2]
        have hiff : spec.sideOffset N g (d.z g) j = d.t g + k
            ↔ j = spec.sideOffset N g (d.z g) (d.t g + k) := by
          constructor
          · intro h; rw [← h, spec.sideOffset_sideOffset N g (d.z g) (by omega)]
          · intro h; rw [h, spec.sideOffset_sideOffset N g (d.z g) (hkXle g hgX)]
        by_cases hc : j = spec.sideOffset N g (d.z g) (d.t g + k)
        · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]; ring
        · rw [ite_eq_right (fun hcon => hc (hiff.mp hcon)), ite_eq_right hc]; ring
      rw [Finset.sum_congr rfl hrw, Finset.sum_ite_eq' (Finset.Ioo 0 N)
        (spec.sideOffset N g (d.z g) (d.t g + k)) (fun _ => (1 : ℤ))]
      split_ifs <;> norm_num
    · have hrw : ∀ j ∈ Finset.Ioo 0 N, d.bridgeDiv k (spec.slotPoint N hN g j)
          = d.R (spec.slotPoint N hN g j) := by
        intro j hj
        rw [Finset.mem_Ioo] at hj
        exact d.bridgeDiv_apply_of_slot_other hunit hkN hkXle hgf hgX hj.1 hj.2
      rw [Finset.sum_congr rfl hrw]
      exact c.oneChip g

/-- **Propagation pins `T` on a crossing slot.**  If the `W`-side endpoint of `g`
lies in `T` and the far endpoint does not, then `T` fills the slot from that
endpoint up to the chip at offset `a`, and stops there. -/
theorem cross_mem_iff (c : d.Confined) (hunit : spec.IsUnit) {k : ℕ} (hk0 : 1 ≤ k)
    (hk : k < d.tauStar) {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph (d.bridgeDiv k) T)
    {g : Fin p} {z : Fin n} (hinc : spec.core.Incident g z) {a : ℕ}
    (ha0 : 0 < a) (haN : a < N)
    (hchip : 1 ≤ d.bridgeDiv k (spec.sidePoint N hN g z a))
    (hzT : (spec.scale N hN).coreVertex z ∈ T)
    (hfarT : spec.sidePoint N hN g z N ∉ T)
    {cc : ℕ} (hcc : cc ≤ N) :
    spec.sidePoint N hN g z cc ∈ T ↔ cc ≤ a := by
  have hDeff : effective (d.bridgeDiv k) := d.effective_bridgeDiv c.eff k
  have hone := c.bridgeDiv_interior_le_one hunit hk0 hk g
  have hzD : d.bridgeDiv k ((spec.scale N hN).coreVertex z) = 0 :=
    c.bridgeDiv_coreVertex hunit hk0 hk z
  constructor
  · intro hmem
    by_contra hlt
    push Not at hlt
    by_cases hccN : cc = N
    · exact hfarT (hccN ▸ hmem)
    · exact spec.not_mem_beyond_chip N hN hunit hDeff hT g hone ha0 haN hchip hfarT
        hlt (by omega) hmem
  · intro hle
    exact spec.propagate_upto_chip N hN hunit hDeff hT g hinc hzT hzD hone ha0 haN
      hchip cc hle

/-- **The `D_k` lemma.**  For `1 ≤ k < τ*` the divisor `D_k = bridgeDiv k` has
exactly two proper legal sets, `S_k = bridgeSet k` and `S_{k−1}ᶜ`. -/
theorem legal_set_unique (c : d.Confined) (hunit : spec.IsUnit) {k : ℕ} (hk0 : 1 ≤ k)
    (hk : k < d.tauStar) {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph (d.bridgeDiv k) T)
    (hTne : T ≠ ∅) (hTuniv : T ≠ Finset.univ) :
    T = d.bridgeSet k ∨ T = (d.bridgeSet (k - 1))ᶜ := by
  classical
  have h2N := d.two_le_scale
  have htau := d.tauStar_le
  have hkN : k < N := by omega
  have hkm : k - 1 < d.tauStar := by omega
  have hDeff : effective (d.bridgeDiv k) := d.effective_bridgeDiv c.eff k
  have hcore := c.bridgeDiv_coreVertex hunit hk0 hk
  have hone := c.bridgeDiv_interior_le_one hunit hk0 hk
  have hkXle : ∀ e ∈ d.X, d.t e + k ≤ N := fun e he => by
    have := d.offset_add_le hk he; omega
  -- the two kinds of front carry a chip
  have hchipF : 1 ≤ d.bridgeDiv k (spec.sidePoint N hN d.f d.v k) := by
    rw [d.bridgeDiv_apply_frontF hunit (by omega) hkXle (by omega) hkN, ite_eq_left rfl]
    have := c.eff (spec.sidePoint N hN d.f d.v k)
    omega
  have hchipX : ∀ e ∈ d.X,
      1 ≤ d.bridgeDiv k (spec.sidePoint N hN e (d.z e) (d.t e + k)) := by
    intro e he
    have hb : d.t e + k < N := by have := d.offset_add_le hk he; omega
    rw [d.bridgeDiv_apply_frontX hunit he (by omega) hkXle
      (by have := d.onePos e he; omega) hb, ite_eq_left rfl]
    have := c.eff (spec.sidePoint N hN e (d.z e) (d.t e + k))
    omega
  -- the core part of `T`, and its closure off the chip slots
  set U : Finset (Fin n) :=
    Finset.univ.filter (fun u => (spec.scale N hN).coreVertex u ∈ T) with hUdef
  have hUmem : ∀ u : Fin n, u ∈ U ↔ (spec.scale N hN).coreVertex u ∈ T := by
    intro u
    rw [hUdef]
    simp
  have hUclosed : spec.core.ClosedOff c.chipSlots U := by
    intro g hg hcross
    have hfree : ∀ j ∈ Finset.Ioo 0 N, d.bridgeDiv k (spec.slotPoint N hN g j) = 0 :=
      fun j hj => c.bridgeDiv_slotFree hunit hk hg (Finset.mem_Ioo.mp hj).1
        (Finset.mem_Ioo.mp hj).2
    rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨-, hh⟩ := spec.core_closure N hN hunit hT g (Or.inl rfl)
        ((hUmem _).mp h1) (hcore _) hfree
      exact h2 ((hUmem _).mpr hh)
    · obtain ⟨ht, -⟩ := spec.core_closure N hN hunit hT g (Or.inr rfl)
        ((hUmem _).mp h1) (hcore _) hfree
      exact h2 ((hUmem _).mpr ht)
  rcases c.closedOff U hUclosed with hU | hU | hU | hU
  · -- `U = ∅`: `slotInterior_disjoint_of_chip_le_one` empties every slot, so `T = ∅`
    exfalso
    have hnocore : ∀ u : Fin n, (spec.scale N hN).coreVertex u ∉ T := by
      intro u hmem
      have hmemU : u ∈ U := (hUmem u).mpr hmem
      rw [hU] at hmemU
      exact absurd hmemU (Finset.notMem_empty u)
    refine hTne (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
    rcases x with u | ⟨g, j⟩
    · exact hnocore u hx
    · have hL := spec.length_scale N hN hunit g
      have hxs := spec.interiorVertex_eq_slotPoint N hN hunit g j
      exact (spec.slotInterior_disjoint_of_chip_le_one N hN hunit hDeff hT g (hone g)
        (hnocore _) (hnocore _) (t := j.val + 1) (by omega)
        (by have := j.isLt; omega)) (hxs ▸ hx)
  · -- `U = W`: the set is `S_k`
    left
    have hcoreT : ∀ w : Fin n, ((spec.scale N hN).coreVertex w ∈ T ↔ w ∈ d.W) := by
      intro w
      rw [← hUmem w, hU]
    refine Finset.ext fun x => ?_
    rcases x with u | ⟨g, j⟩
    · show (spec.scale N hN).coreVertex u ∈ T
        ↔ (spec.scale N hN).coreVertex u ∈ d.bridgeSet k
      rw [hcoreT u, d.coreVertex_mem_bridgeSet_iff k u]
    · have hL := spec.length_scale N hN hunit g
      have ho0 : 0 < j.val + 1 := by omega
      have hoN : j.val + 1 < N := by have := j.isLt; omega
      have hxs := spec.interiorVertex_eq_slotPoint N hN hunit g j
      show (spec.scale N hN).interiorVertex g j ∈ T
        ↔ (spec.scale N hN).interiorVertex g j ∈ d.bridgeSet k
      rw [hxs]
      rcases d.slot_cases g with ⟨ht, hh⟩ | ⟨ht, hh, hgf, hgX⟩ | hX | hf
      · constructor
        · intro _
          exact d.mem_bridgeSet_of_inside hunit k ht hh (o := j.val + 1) (by omega)
        · intro _
          exact spec.propagate_both_ends N hN hunit hDeff hT g ((hcoreT _).mpr ht)
            (hcore _) ((hcoreT _).mpr hh) (hcore _) (hone g) (by omega)
      · constructor
        · intro hmem
          exact absurd hmem (spec.slotInterior_disjoint_of_chip_le_one N hN hunit hDeff
            hT g (hone g) (fun hc => ht ((hcoreT _).mp hc))
            (fun hc => hh ((hcoreT _).mp hc)) ho0 hoN)
        · intro hmem
          exact absurd hmem
            (d.not_mem_bridgeSet_of_outside hunit k ht hh hgf hgX (by omega))
      · have hb : d.t g + k < N := by have := d.offset_add_le hk hX; omega
        set cc := spec.sideOffset N g (d.z g) (j.val + 1) with hcc
        have hcc0 : 0 < cc := spec.sideOffset_pos N g (d.z g) ho0 hoN
        have hccN : cc < N := spec.sideOffset_lt N g (d.z g) ho0 hoN
        have hxc : spec.sidePoint N hN g (d.z g) cc
            = spec.slotPoint N hN g (j.val + 1) := by
          rw [spec.sidePoint_eq_slotPoint N hN g (d.z g) cc, hcc,
            spec.sideOffset_sideOffset N g (d.z g) (by omega)]
        have hfarT : spec.sidePoint N hN g (d.z g) N ∉ T := by
          rw [spec.sidePoint_last N hN hunit g (d.z g)]
          intro hcon
          exact (spec.core.otherEnd_not_mem_of_crosses (d.incX g hX) (d.memX g hX)
            (d.crossX g hX)) ((hcoreT _).mp hcon)
        rw [← hxc, c.cross_mem_iff hunit hk0 hk hT (d.incX g hX)
            (by have := d.onePos g hX; omega) hb (hchipX g hX)
            ((hcoreT _).mpr (d.memX g hX)) hfarT (le_of_lt hccN),
          d.mem_bridgeSet_frontX_iff hunit hX hb (le_of_lt hccN)]
      · subst hf
        set cc := spec.sideOffset N d.f d.v (j.val + 1) with hcc
        have hcc0 : 0 < cc := spec.sideOffset_pos N d.f d.v ho0 hoN
        have hccN : cc < N := spec.sideOffset_lt N d.f d.v ho0 hoN
        have hxc : spec.sidePoint N hN d.f d.v cc
            = spec.slotPoint N hN d.f (j.val + 1) := by
          rw [spec.sidePoint_eq_slotPoint N hN d.f d.v cc, hcc,
            spec.sideOffset_sideOffset N d.f d.v (by omega)]
        have hfarT : spec.sidePoint N hN d.f d.v N ∉ T := by
          rw [spec.sidePoint_last N hN hunit d.f d.v]
          intro hcon
          exact d.farF ((hcoreT _).mp hcon)
        rw [← hxc, c.cross_mem_iff hunit hk0 hk hT d.incF (by omega) hkN hchipF
            ((hcoreT _).mpr d.memW) hfarT (le_of_lt hccN),
          d.mem_bridgeSet_frontF_iff hunit hkN (le_of_lt hccN)]
  · -- `U = Wᶜ`: the set is `S_{k-1}ᶜ`
    right
    have hcoreT : ∀ w : Fin n, ((spec.scale N hN).coreVertex w ∈ T ↔ w ∉ d.W) := by
      intro w
      rw [← hUmem w, hU, Finset.mem_compl]
    have hkXm : ∀ e ∈ d.X, d.t e + (k - 1) < N := fun e he => by
      have := d.offset_add_le hk he; omega
    refine Finset.ext fun x => ?_
    rw [Finset.mem_compl]
    rcases x with u | ⟨g, j⟩
    · show (spec.scale N hN).coreVertex u ∈ T
        ↔ (spec.scale N hN).coreVertex u ∉ d.bridgeSet (k - 1)
      rw [hcoreT u, d.coreVertex_mem_bridgeSet_iff (k - 1) u]
    · have hL := spec.length_scale N hN hunit g
      have ho0 : 0 < j.val + 1 := by omega
      have hoN : j.val + 1 < N := by have := j.isLt; omega
      have hxs := spec.interiorVertex_eq_slotPoint N hN hunit g j
      show (spec.scale N hN).interiorVertex g j ∈ T
        ↔ (spec.scale N hN).interiorVertex g j ∉ d.bridgeSet (k - 1)
      rw [hxs]
      rcases d.slot_cases g with ⟨ht, hh⟩ | ⟨ht, hh, hgf, hgX⟩ | hX | hf
      · constructor
        · intro hmem
          exact absurd hmem (spec.slotInterior_disjoint_of_chip_le_one N hN hunit hDeff
            hT g (hone g) (fun hc => (hcoreT _).mp hc ht)
            (fun hc => (hcoreT _).mp hc hh) ho0 hoN)
        · intro hmem
          exact absurd (d.mem_bridgeSet_of_inside hunit (k - 1) ht hh
            (o := j.val + 1) (by omega)) hmem
      · constructor
        · intro _
          exact d.not_mem_bridgeSet_of_outside hunit (k - 1) ht hh hgf hgX
            (o := j.val + 1) (by omega)
        · intro _
          exact spec.propagate_both_ends N hN hunit hDeff hT g ((hcoreT _).mpr ht)
            (hcore _) ((hcoreT _).mpr hh) (hcore _) (hone g) (by omega)
      · -- a crossing slot, read from its far endpoint
        have hb : d.t g + k < N := by have := d.offset_add_le hk hX; omega
        have ht1 : 1 ≤ d.t g := d.onePos g hX
        obtain ⟨w, hw⟩ : ∃ w : Fin n, w = spec.core.otherEnd g (d.z g) := ⟨_, rfl⟩
        have hwW : w ∉ d.W := by
          rw [hw]
          exact spec.core.otherEnd_not_mem_of_crosses (d.incX g hX) (d.memX g hX)
            (d.crossX g hX)
        have hincw : spec.core.Incident g w := by
          rw [hw]; exact spec.core.incident_otherEnd g (d.z g)
        have hzw : d.z g ≠ w := fun hcon => hwW (hcon ▸ d.memX g hX)
        set cc := spec.sideOffset N g (d.z g) (j.val + 1) with hcc
        have hcc0 : 0 < cc := spec.sideOffset_pos N g (d.z g) ho0 hoN
        have hccN : cc < N := spec.sideOffset_lt N g (d.z g) ho0 hoN
        have hxc : spec.sidePoint N hN g (d.z g) cc
            = spec.slotPoint N hN g (j.val + 1) := by
          rw [spec.sidePoint_eq_slotPoint N hN g (d.z g) cc, hcc,
            spec.sideOffset_sideOffset N g (d.z g) (by omega)]
        have hswap : ∀ b : ℕ, b ≤ N →
            spec.sidePoint N hN g w b = spec.sidePoint N hN g (d.z g) (N - b) :=
          fun b hb' => spec.sidePoint_swap N hN (d.incX g hX) hincw hzw hb'
        have hchipw : 1 ≤ d.bridgeDiv k (spec.sidePoint N hN g w (N - (d.t g + k))) := by
          rw [hswap _ (by omega), show N - (N - (d.t g + k)) = d.t g + k by omega]
          exact hchipX g hX
        have hfarw : spec.sidePoint N hN g w N ∉ T := by
          rw [hswap N le_rfl, Nat.sub_self, spec.sidePoint_zero N hN hunit g (d.incX g hX)]
          intro hcon
          exact (hcoreT (d.z g)).mp hcon (d.memX g hX)
        have hkey := c.cross_mem_iff hunit hk0 hk hT hincw
          (a := N - (d.t g + k)) (by omega) (by omega) hchipw
          ((hcoreT w).mpr hwW) hfarw (cc := N - cc) (by omega)
        rw [hswap _ (by omega), show N - (N - cc) = cc by omega] at hkey
        rw [← hxc, hkey, d.mem_bridgeSet_frontX_iff hunit hX (hkXm g hX)
          (le_of_lt hccN)]
        omega
      · -- the bridge, read from its far endpoint
        subst hf
        obtain ⟨w, hw⟩ : ∃ w : Fin n, w = spec.core.otherEnd d.f d.v := ⟨_, rfl⟩
        have hwW : w ∉ d.W := by rw [hw]; exact d.farF
        have hincw : spec.core.Incident d.f w := by
          rw [hw]; exact spec.core.incident_otherEnd d.f d.v
        have hzw : d.v ≠ w := fun hcon => hwW (hcon ▸ d.memW)
        set cc := spec.sideOffset N d.f d.v (j.val + 1) with hcc
        have hcc0 : 0 < cc := spec.sideOffset_pos N d.f d.v ho0 hoN
        have hccN : cc < N := spec.sideOffset_lt N d.f d.v ho0 hoN
        have hxc : spec.sidePoint N hN d.f d.v cc
            = spec.slotPoint N hN d.f (j.val + 1) := by
          rw [spec.sidePoint_eq_slotPoint N hN d.f d.v cc, hcc,
            spec.sideOffset_sideOffset N d.f d.v (by omega)]
        have hswap : ∀ b : ℕ, b ≤ N →
            spec.sidePoint N hN d.f w b = spec.sidePoint N hN d.f d.v (N - b) :=
          fun b hb' => spec.sidePoint_swap N hN d.incF hincw hzw hb'
        have hchipw : 1 ≤ d.bridgeDiv k (spec.sidePoint N hN d.f w (N - k)) := by
          rw [hswap _ (by omega), show N - (N - k) = k by omega]
          exact hchipF
        have hfarw : spec.sidePoint N hN d.f w N ∉ T := by
          rw [hswap N le_rfl, Nat.sub_self, spec.sidePoint_zero N hN hunit d.f d.incF]
          intro hcon
          exact (hcoreT d.v).mp hcon d.memW
        have hkey := c.cross_mem_iff hunit hk0 hk hT hincw (a := N - k)
          (by omega) (by omega) hchipw ((hcoreT w).mpr hwW) hfarw
          (cc := N - cc) (by omega)
        rw [hswap _ (by omega), show N - (N - cc) = cc by omega] at hkey
        rw [← hxc, hkey, d.mem_bridgeSet_frontF_iff hunit (by omega) (le_of_lt hccN)]
        omega
  · -- `U = V(G)`: everything fills, so `T = V`
    exfalso
    have hallcore : ∀ u : Fin n, (spec.scale N hN).coreVertex u ∈ T := fun u =>
      (hUmem u).mp (by rw [hU]; exact Finset.mem_univ u)
    refine hTuniv (Finset.eq_univ_iff_forall.mpr fun x => ?_)
    rcases x with u | ⟨g, j⟩
    · exact hallcore u
    · have hL := spec.length_scale N hN hunit g
      have hxs := spec.interiorVertex_eq_slotPoint N hN hunit g j
      show (spec.scale N hN).interiorVertex g j ∈ T
      rw [hxs]
      exact spec.propagate_both_ends N hN hunit hDeff hT g (hallcore _) (hcore _)
        (hallcore _) (hcore _) (hone g) (by have := j.isLt; omega)

end Confined

end BridgeData

end Spec

end SubdivisionGraph

end Utilities.Certificate

