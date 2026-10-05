import Utilities.Iso.FossilTopology
import Utilities.Gonality.CoreBridgeless
import Utilities.Gluing.SeparatingEdgePath
import Utilities.Subdivision.CoreBridgeCut
import Utilities.Subdivision.SlotIntervalFiring
import Utilities.Subdivision.SubdivisionChipDescent

/-!
# Contracting every bridge, at every scale

The **fossil** `Utilities.fossil G` of a graph `G` contracts all of its bridges; it is connected
of the same genus when `G` is, and its unit presentation has a bridgeless core
(`Gonality.core_bridgeless_of_twoEdgeCutCondition`, `twoEdgeCutCondition_fossil`). This file
contracts every bridge at once, at every scale `N`, and lifts rank lower bounds back along the
contraction. Instead of presenting `G` as an iterated `bridgeGraph` and applying
`rank_bridgePushforward` once per bridge and per unit step:

* `contractionMap` sends the `N`-fold refinement `G^(N)` of the unit presentation of `G` onto
  the `N`-fold refinement of the unit presentation of the fossil. A core vertex goes to its
  fossil class; an interior point of a bridge slot goes to the class of the bridge; an interior
  point of any other slot goes to the same point of the matching fossil slot.
* It is a valid graph contraction (`contraction_valid`), by a bijection between the unit steps of
  the target and the non-contracted unit steps of the source (`valid_of_stepInjection`).
* Its fibres consist of linearly equivalent points (`fibresEquivalent`). A bridge of `G` is a
  separating edge, and its `N` unit steps are separating edges of `G^(N)`: the first by
  `CoreBridgeCut.toOneBridgeCut`, the others by firing one bivalent point at a time
  (`linearEquiv_chain`). Two vertices of `G` with equivalent one-chip divisors are then equivalent
  in `G^(N)` too, by `eq_of_chipEquivalent_of_separating_normalized`.
* For a valid contraction with linearly equivalent fibres, `rank_geq_of_contraction` lifts rank
  lower bounds from the target to the source: the chips that sit at bridge endpoints, or on a
  pendant tree, are moved inside their fibre.
* The pushforward commutes with `embed` (`pushDiv_embed`), so a divisor prescribed on the
  vertices of `G` goes to the corresponding divisor of the fossil, and a divisor of the fossil's
  refinement is lifted by choosing a preimage of every chip (`liftDiv`).

All divisor algebra is done for abstract graphs; the concrete subdivision vertex types only enter
through `num_edges` computations.
-/

namespace Utilities.Subdivision.BridgeLift

open Finset
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open MarkedGraphs MarkedGraphs.Certificate

/-! ## 1.  Contractions whose fibres are linearly equivalent -/

section Contraction

variable {K K' : CFGraph} (c : GraphContractionCertificate K K')

/-- Fibre summation as an additive homomorphism. -/
def pushDivHom : CFDiv K →+ CFDiv K' where
  toFun := c.pushDiv
  map_zero' := c.pushDiv_zero
  map_add' := c.pushDiv_add

@[simp] theorem pushDivHom_apply (D : CFDiv K) : pushDivHom c D = c.pushDiv D := rfl

variable (hsurj : Function.Surjective c.vertexMap)

/-- A chosen preimage of every target vertex. -/
noncomputable def rep : K'.V → K.V := Function.surjInv hsurj

theorem vertexMap_rep (b : K'.V) : c.vertexMap (rep c hsurj b) = b :=
  Function.surjInv_eq hsurj b

/-- Lift a target divisor by putting each coefficient at the chosen preimage. -/
noncomputable def liftDiv (D : CFDiv K') : CFDiv K :=
  ∑ b : K'.V, D b • one_chip (rep c hsurj b)

theorem pushDiv_liftDiv (D : CFDiv K') : c.pushDiv (liftDiv c hsurj D) = D := by
  classical
  change pushDivHom c (∑ b : K'.V, D b • one_chip (rep c hsurj b)) = D
  rw [map_sum]
  simp_rw [map_zsmul, pushDivHom_apply, GraphContractionCertificate.pushDiv_one_chip,
    vertexMap_rep]
  exact (divisor_eq_sum_smul_oneChip D).symm

theorem effective_liftDiv {D : CFDiv K'} (hD : effective D) :
    effective (liftDiv c hsurj D) := by
  intro x
  simp only [liftDiv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun b _ => mul_nonneg (hD b) (eff_one_chip _ x)

theorem deg_liftDiv (D : CFDiv K') : deg (liftDiv c hsurj D) = deg D := by
  rw [← c.deg_pushDiv, pushDiv_liftDiv]

private theorem sum_smul_rep_eq_liftDiv_pushDiv (D : CFDiv K) :
    (∑ x : K.V, D x • one_chip (rep c hsurj (c.vertexMap x))) =
      liftDiv c hsurj (c.pushDiv D) := by
  classical
  funext w
  simp only [liftDiv, GraphContractionCertificate.pushDiv_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (c.vertexMap x)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · simp

/-- The fibres of `c` consist of linearly equivalent one-chip divisors. -/
def FibresEquivalent : Prop :=
  ∀ x y : K.V, c.vertexMap x = c.vertexMap y → linear_equiv K (one_chip x) (one_chip y)

theorem linear_equiv_liftDiv_pushDiv (hfib : FibresEquivalent c) (D : CFDiv K) :
    linear_equiv K D (liftDiv c hsurj (c.pushDiv D)) := by
  conv_lhs => rw [divisor_eq_sum_smul_oneChip D]
  rw [← sum_smul_rep_eq_liftDiv_pushDiv c hsurj D]
  apply linear_equiv_sum
  intro x
  exact linear_equiv_zsmul (hfib _ _ (vertexMap_rep c hsurj _).symm) (D x)

include hsurj in
theorem linear_equiv_of_pushDiv_eq (hfib : FibresEquivalent c) {D E : CFDiv K}
    (h : c.pushDiv D = c.pushDiv E) : linear_equiv K D E := by
  apply linear_equiv.trans (linear_equiv_liftDiv_pushDiv c hsurj hfib D)
  rw [h]
  exact (linear_equiv_liftDiv_pushDiv c hsurj hfib E).symm

include hsurj in
/-- Reflection of linear equivalence through a valid contraction with linearly equivalent
fibres: pull the target script back, and redistribute the rest inside the fibres. -/
theorem linear_equiv_of_pushDiv (hfib : FibresEquivalent c) (hValid : c.Valid) {D E : CFDiv K}
    (h : linear_equiv K' (c.pushDiv D) (c.pushDiv E)) : linear_equiv K D E := by
  unfold linear_equiv at h ⊢
  obtain ⟨tau, hTau⟩ := (principal_iff_eq_prin K' (c.pushDiv E - c.pushDiv D)).mp h
  let P : CFDiv K := prin K (c.pullScript tau)
  have hPush : c.pushDiv (E - D) = c.pushDiv P := by
    rw [c.pushDiv_sub, hTau]
    exact (c.pushDiv_prin_pullScript hValid tau).symm
  have hKernel : linear_equiv K (E - D) P := linear_equiv_of_pushDiv_eq c hsurj hfib hPush
  have hP : P ∈ principal_divisors K :=
    (principal_iff_eq_prin K P).mpr ⟨c.pullScript tau, rfl⟩
  have hDifference : P - (E - D) ∈ principal_divisors K := hKernel
  have hRecovered := (principal_divisors K).sub_mem hP hDifference
  convert hRecovered using 1
  abel

include hsurj in
/-- **Rank lower bounds lift through the contraction**, for all contracted edges at once. -/
theorem rank_geq_of_contraction (hfib : FibresEquivalent c) (hValid : c.Valid) (D : CFDiv K)
    (k : ℤ) (h : rank_geq K' (c.pushDiv D) k) : rank_geq K D k := by
  intro E hE
  have hE' : c.pushDiv E ∈ eff_of_degree K' k :=
    ⟨c.effective_pushDiv hE.1, by rw [c.deg_pushDiv]; exact hE.2⟩
  obtain ⟨F', hF', hlin⟩ := h _ hE'
  refine ⟨liftDiv c hsurj F', effective_liftDiv c hsurj hF', ?_⟩
  apply linear_equiv_of_pushDiv c hsurj hfib hValid
  rw [pushDiv_liftDiv, c.pushDiv_sub]
  exact hlin

end Contraction

/-! ## 2.  Validity from a bijection of unit steps -/

section StepValidity

variable {K K' : CFGraph} {St St' : Type*} [Fintype St] [Fintype St']

private theorem num_edges_eq_sum_split (u : St → K.V × K.V)
    (hK : ∀ x y, num_edges K x y =
      (Finset.univ.filter fun s => u s = (x, y) ∨ u s = (y, x)).card)
    (hloop : ∀ s, (u s).1 ≠ (u s).2) (x y : K.V) :
    num_edges K x y =
      ∑ s, ((if u s = (x, y) then 1 else 0) + (if u s = (y, x) then 1 else 0)) := by
  rw [hK, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h1 : u s = (x, y)
  · have h2 : u s ≠ (y, x) := by
      intro h2
      apply hloop s
      rw [h1] at h2 ⊢
      exact (Prod.mk.inj h2).1
    rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]
  · by_cases h2 : u s = (y, x)
    · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]
    · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg h1, if_neg h2]

/-- Summing the two orientations of one unordered pair over a condition on ordered pairs. -/
private theorem pair_sum_split {V : Type*} [Fintype V] [DecidableEq V] (C : V → V → Prop)
    [DecidableRel C] (z : V × V) :
    (∑ x : V, ∑ y : V, (if C x y then
      ((if z = (x, y) then 1 else 0) + (if z = (y, x) then 1 else 0)) else 0 : ℕ)) =
      (if C z.1 z.2 then 1 else 0) + (if C z.2 z.1 then 1 else 0) := by
  have hsingle : ∀ D : V → V → Prop, ∀ [DecidableRel D],
      (∑ x : V, ∑ y : V, (if D x y then (if z = (x, y) then 1 else 0) else 0 : ℕ)) =
        if D z.1 z.2 then 1 else 0 := by
    intro D _
    rw [Finset.sum_eq_single z.1]
    · rw [Finset.sum_eq_single z.2]
      · simp
      · intro y _ hy
        have : z ≠ (z.1, y) := fun h => hy (by rw [h])
        simp [this]
      · simp
    · intro x _ hx
      apply Finset.sum_eq_zero
      intro y _
      have : z ≠ (x, y) := fun h => hx (by rw [h])
      simp [this]
    · simp
  have hsplit : ∀ x y : V, (if C x y then
      ((if z = (x, y) then 1 else 0) + (if z = (y, x) then 1 else 0)) else 0 : ℕ) =
      (if C x y then (if z = (x, y) then 1 else 0) else 0) +
        (if C x y then (if z = (y, x) then 1 else 0) else 0) := by
    intro x y
    split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [hsingle C, Finset.sum_comm, hsingle (fun y x => C x y)]

/-- A surjective vertex map is a valid contraction when the unit steps of the target correspond
injectively to unit steps of the source, with matching endpoints, and every other source step
is contracted to a point. -/
theorem valid_of_stepInjection (u : St → K.V × K.V) (u' : St' → K'.V × K'.V)
    (hK : ∀ x y, num_edges K x y =
      (Finset.univ.filter fun s => u s = (x, y) ∨ u s = (y, x)).card)
    (hK' : ∀ a b, num_edges K' a b =
      (Finset.univ.filter fun s => u' s = (a, b) ∨ u' s = (b, a)).card)
    (hloop : ∀ s, (u s).1 ≠ (u s).2) (hloop' : ∀ s', (u' s').1 ≠ (u' s').2)
    (π : K.V → K'.V) (hsurj : Function.Surjective π)
    (w : St' → St) (hw : Function.Injective w)
    (hu' : ∀ s', u' s' = (π (u (w s')).1, π (u (w s')).2))
    (hoff : ∀ s, s ∉ Set.range w → π (u s).1 = π (u s).2) :
    (GraphContractionCertificate.mk π : GraphContractionCertificate K K').Valid := by
  classical
  refine ⟨hsurj, ?_⟩
  intro a b hab
  let F : St → ℕ := fun s =>
    (if π (u s).1 = a ∧ π (u s).2 = b then 1 else 0) +
      (if π (u s).2 = a ∧ π (u s).1 = b then 1 else 0)
  -- the right side, grouped by unit step
  have hRight : (∑ x : K.V, ∑ y : K.V,
      if π x = a ∧ π y = b then num_edges K x y else 0) = ∑ s, F s := by
    have hterm : ∀ x y : K.V, (if π x = a ∧ π y = b then num_edges K x y else 0) =
        ∑ s, (if π x = a ∧ π y = b then
          ((if u s = (x, y) then 1 else 0) + (if u s = (y, x) then 1 else 0)) else 0) := by
      intro x y
      rw [num_edges_eq_sum_split u hK hloop x y]
      by_cases hxy : π x = a ∧ π y = b
      · simp only [hxy, and_self, if_true]
      · simp only [hxy, if_false, Finset.sum_const_zero]
    simp_rw [hterm]
    calc (∑ x : K.V, ∑ y : K.V, ∑ s, (if π x = a ∧ π y = b then
          ((if u s = (x, y) then 1 else 0) + (if u s = (y, x) then 1 else 0)) else 0))
        = ∑ x : K.V, ∑ s, ∑ y : K.V, (if π x = a ∧ π y = b then
          ((if u s = (x, y) then 1 else 0) + (if u s = (y, x) then 1 else 0)) else 0) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ s, ∑ x : K.V, ∑ y : K.V, (if π x = a ∧ π y = b then
          ((if u s = (x, y) then 1 else 0) + (if u s = (y, x) then 1 else 0)) else 0) :=
          Finset.sum_comm
      _ = ∑ s, F s := Finset.sum_congr rfl fun s _ =>
          pair_sum_split (fun x y => π x = a ∧ π y = b) (u s)
  -- the left side, through the step injection
  have hLeft : num_edges K' a b = ∑ s', F (w s') := by
    rw [num_edges_eq_sum_split u' hK' hloop' a b]
    apply Finset.sum_congr rfl
    intro s' _
    have hc : (π (u (w s')).1 = b ∧ π (u (w s')).2 = a) ↔
        (π (u (w s')).2 = a ∧ π (u (w s')).1 = b) := and_comm
    simp only [F, hu' s', Prod.mk.injEq, hc]
  have hOff : ∑ s', F (w s') = ∑ s, F s := by
    have hmap := Finset.sum_map Finset.univ ⟨w, hw⟩ F
    simp only [Function.Embedding.coeFn_mk] at hmap
    rw [← hmap]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro s _ hs
    have hnot : s ∉ Set.range w := by
      rintro ⟨s', rfl⟩
      exact hs (Finset.mem_map.mpr ⟨s', Finset.mem_univ _, rfl⟩)
    have hsame := hoff s hnot
    have h1 : ¬(π (u s).1 = a ∧ π (u s).2 = b) :=
      fun h => hab (h.1.symm.trans (hsame.trans h.2))
    have h2 : ¬(π (u s).2 = a ∧ π (u s).1 = b) :=
      fun h => hab (h.1.symm.trans (hsame.symm.trans h.2))
    simp only [F, h1, h2, if_false, add_zero]
  change num_edges K' a b = ∑ x : K.V, ∑ y : K.V,
      if π x = a ∧ π y = b then num_edges K x y else 0
  rw [hRight, hLeft, hOff]

end StepValidity

/-! ## 3.  Small combinatorial tools -/

section Tools

/-- Two elements of a sigma type with `Fin` fibres are equal when their indices and the values of
their coordinates agree.  This avoids `HEq` on the subdivision vertex and step types. -/
theorem sigma_fin_ext {ι : Type*} {L : ι → ℕ} {a b : Σ i, Fin (L i)} (h1 : a.1 = b.1)
    (h2 : a.2.val = b.2.val) : a = b := by
  obtain ⟨i, x⟩ := a
  obtain ⟨k, y⟩ := b
  simp only at h1 h2
  subst h1
  rw [Fin.ext h2]

/-- An equivalence matching two maps whose fibres have equal sizes. -/
theorem exists_equiv_of_card_fibre {ι β α : Type*} [Fintype ι] [Fintype β] [DecidableEq α]
    (f : ι → α) (g : β → α)
    (h : ∀ a, Fintype.card {i // f i = a} = Fintype.card {b // g b = a}) :
    ∃ e : ι ≃ β, ∀ i, g (e i) = f i := by
  classical
  let e : ι ≃ β := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun a => Fintype.equivOfCardEq (h a)).trans
      (Equiv.sigmaFiberEquiv g))
  exact ⟨e, fun i => ((Fintype.equivOfCardEq (h (f i))) ⟨i, rfl⟩).2⟩

/-- A separating edge seen from the other side. -/
def cutSwap {G : CFGraph} {x y : G.V} (cut : SeparatingEdgeCut G x y) :
    SeparatingEdgeCut G y x where
  side := Finset.univ \ cut.side
  left_mem := by simpa using cut.right_not_mem
  right_not_mem := by simpa using cut.left_mem
  cross_num_edges := by
    intro a b ha hb
    have ha' : a ∉ cut.side := by simpa using ha
    have hb' : b ∈ cut.side := by simpa using hb
    rw [num_edges_symmetric, cut.cross_num_edges b a hb' ha']
    by_cases h1 : b = x <;> by_cases h2 : a = y <;> simp [h1, h2]

/-- A one-bridge presentation exhibits a separating edge. -/
def toSeparatingEdgeCut {K : CFGraph} (cut : OneBridgeCut K) :
    SeparatingEdgeCut K cut.leftAttach cut.rightAttach where
  side := cut.left
  left_mem := cut.leftAttach_mem
  right_not_mem := fun h => (Finset.disjoint_left.mp cut.disjoint) h cut.rightAttach_mem
  cross_num_edges := by
    intro a b ha hb
    have hbR : b ∈ cut.right := (cut.vertex_cover b).resolve_left hb
    exact cut.cross_num_edges a b ha hbR

/-- Firing one bivalent vertex `x` with neighbours `p` and `q`. -/
theorem prin_one_chip_of_bivalent {K : CFGraph} {x p q : K.V}
    (hnb : ∀ y, (num_edges K x y : ℤ) = (if y = p then 1 else 0) + (if y = q then 1 else 0)) :
    prin K (one_chip x) = one_chip p + one_chip q - (2 : ℤ) • one_chip x := by
  have hxx := hnb x
  rw [num_edges_self_zero] at hxx
  have hxp : x ≠ p := by
    intro h
    rw [if_pos h] at hxx
    split_ifs at hxx <;> omega
  have hxq : x ≠ q := by
    intro h
    rw [if_pos h] at hxx
    split_ifs at hxx <;> omega
  have hsum : ∑ u : K.V, (num_edges K x u : ℤ) = 2 := by
    simp_rw [hnb, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    norm_num
  funext v
  rw [prin_apply]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_chip]
  by_cases hv : v = x
  · subst hv
    have hrw : ∀ u : K.V, ((if u = v then (1 : ℤ) else 0) - 1) * (num_edges K v u : ℤ) =
        (if u = v then (num_edges K v u : ℤ) else 0) - (num_edges K v u : ℤ) := by
      intro u
      split_ifs <;> ring
    simp only [if_true]
    rw [Finset.sum_congr rfl fun u _ => hrw u, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _), num_edges_self_zero, hsum, if_neg hxp, if_neg hxq]
    norm_num
  · have hrw : ∀ u : K.V, ((if u = x then (1 : ℤ) else 0) - (if v = x then 1 else 0)) *
        (num_edges K v u : ℤ) = if u = x then (num_edges K v u : ℤ) else 0 := by
      intro u
      rw [if_neg hv]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun u _ => hrw u, Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
      num_edges_symmetric, hnb v, if_neg hv]
    ring

/-- **Chips slide along a path of bivalent vertices.** If the first step of the path joins
equivalent one-chip divisors, every point of the path is equivalent to its start. -/
theorem linearEquiv_chain {K : CFGraph} (pt : ℕ → K.V) (L : ℕ)
    (hnb : ∀ t, 0 < t → t < L → ∀ y, (num_edges K (pt t) y : ℤ) =
      (if y = pt (t - 1) then 1 else 0) + (if y = pt (t + 1) then 1 else 0))
    (h01 : 1 ≤ L → linear_equiv K (one_chip (pt 0)) (one_chip (pt 1))) :
    ∀ t, t ≤ L → linear_equiv K (one_chip (pt 0)) (one_chip (pt t)) := by
  have hstep : ∀ t, t + 1 ≤ L → linear_equiv K (one_chip (pt t)) (one_chip (pt (t + 1))) := by
    intro t
    induction t with
    | zero => intro h; exact h01 (by omega)
    | succ t ih =>
        intro ht
        have hprev := ih (by omega)
        have hprin := prin_one_chip_of_bivalent (hnb (t + 1) (by omega) (by omega))
        simp only [Nat.add_sub_cancel] at hprin
        unfold linear_equiv at hprev ⊢
        have hmem : prin K (one_chip (pt (t + 1))) ∈ principal_divisors K :=
          (principal_iff_eq_prin K _).mpr ⟨_, rfl⟩
        have hsum := (principal_divisors K).add_mem hmem hprev
        rw [hprin] at hsum
        convert hsum using 1
        rw [two_smul]
        abel
  intro t
  induction t with
  | zero => intro _; exact linear_equiv.refl K _
  | succ t ih => intro ht; exact (ih (by omega)).trans (hstep t ht)

end Tools

/-! ## 4.  Bridges of a graph and of its unit presentation -/

section Bridges

open UnitSubdivisionPresentation

variable (G : CFGraph)

@[simp] theorem spec_core_tail (s : Fin G.edges.card) :
    (spec G).core.tail s = vertexEquiv G (edgeAt G s).1 := rfl

@[simp] theorem spec_core_head (s : Fin G.edges.card) :
    (spec G).core.head s = vertexEquiv G (edgeAt G s).2 := rfl

/-- Edge multiplicities count slots of the unit presentation. -/
theorem num_edges_eq_card_slots (x y : G.V) :
    num_edges G x y =
      (Finset.univ.filter fun s : Fin G.edges.card =>
        edgeAt G s = (x, y) ∨ edgeAt G s = (y, x)).card := by
  classical
  have hmap : (Finset.univ.filter fun occ : G.edges =>
        ((occ : G.V × G.V) = (x, y) ∨ (occ : G.V × G.V) = (y, x))).map
        (edgeEquiv G).toEmbedding
      = Finset.univ.filter fun s : Fin G.edges.card =>
        edgeAt G s = (x, y) ∨ edgeAt G s = (y, x) := by
    ext s
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨occ, hocc, rfl⟩
      rwa [edgeAt_edgeEquiv]
    · intro hs
      exact ⟨(edgeEquiv G).symm s, hs, by simp⟩
  rw [← hmap, Finset.card_map,
    card_filter_occurrences G.edges (fun e => e = (x, y) ∨ e = (y, x))]
  rfl

variable {G}

/-- A separating edge `a-b` of `G`, carried by the slot `e`, is a valid bridge cut of the core
of the unit presentation. -/
theorem valid_of_separatingEdgeCut {a b : G.V} (cut : SeparatingEdgeCut G a b)
    (e : Fin G.edges.card) (he : edgeAt G e = (a, b)) :
    (CoreBridgeCut.Data.mk (core := (spec G).core)
      (Finset.univ.filter fun i => (vertexEquiv G).symm i ∈ cut.side) e).Valid := by
  classical
  have hab1 : num_edges G a b = 1 := cut.num_edges_endpoints
  -- two different slots with the endpoints `a, b` would give multiplicity two
  have htwo : ∀ f : Fin G.edges.card, f ≠ e →
      edgeAt G f = (a, b) ∨ edgeAt G f = (b, a) → False := by
    intro f hf hfab
    have hcard := num_edges_eq_card_slots G a b
    have h2 : 1 < (Finset.univ.filter fun s : Fin G.edges.card =>
        edgeAt G s = (a, b) ∨ edgeAt G s = (b, a)).card :=
      Finset.one_lt_card.mpr ⟨e, by simp [he], f, by simpa using hfab, Ne.symm hf⟩
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp [he, cut.left_mem]
  · simp [he, cut.right_not_mem]
  · intro f hf
    simp only [spec_core_tail, spec_core_head, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_apply_apply]
    have hslot : 0 < num_edges G (edgeAt G f).1 (edgeAt G f).2 := by
      rw [num_edges_eq_card_slots, Finset.card_pos]
      exact ⟨f, by simp⟩
    constructor
    · intro hx
      by_contra hy
      have := cut.cross_num_edges _ _ hx hy
      split_ifs at this with hxy
      · exact htwo f hf (Or.inl (Prod.ext hxy.1 hxy.2))
      · omega
    · intro hy
      by_contra hx
      have := cut.cross_num_edges _ _ hy hx
      rw [num_edges_symmetric] at this
      split_ifs at this with hxy
      · exact htwo f hf (Or.inr (Prod.ext hxy.2 hxy.1))
      · omega

/-- The endpoints of a separating edge are carried by some slot, in one orientation. -/
theorem exists_slot_of_separatingEdgeCut {a b : G.V} (cut : SeparatingEdgeCut G a b) :
    ∃ e : Fin G.edges.card, edgeAt G e = (a, b) ∨ edgeAt G e = (b, a) := by
  have h := cut.num_edges_endpoints
  rw [num_edges_eq_card_slots] at h
  have hpos : 0 < (Finset.univ.filter fun s : Fin G.edges.card =>
      edgeAt G s = (a, b) ∨ edgeAt G s = (b, a)).card := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  exact ⟨e, (Finset.mem_filter.mp he).2⟩

/-- An edge whose endpoints have equivalent one-chip divisors is a separating edge. -/
theorem separatingEdgeCut_of_chipEquivalent (hG : graph_connected G) (e : Fin G.edges.card)
    (h : fossilVertex G (edgeAt G e).1 = fossilVertex G (edgeAt G e).2) :
    Nonempty (SeparatingEdgeCut G (edgeAt G e).1 (edgeAt G e).2) := by
  have hab := edgeAt_fst_ne_snd G e
  have hequiv := (fossilVertex_eq_iff G _ _).mp h
  unfold chipEquivalent linear_equiv at hequiv
  obtain ⟨sigma, hSigma⟩ := (principal_iff_eq_prin G _).mp hequiv
  have hPrincipal := hSigma.symm
  obtain ⟨z, cut, hSide⟩ := exists_separatingEdgeCut_of_prin_eq_oneChip_sub hG hab hPrincipal
  have hb : (edgeAt G e).2 ∉ cut.side := by
    rw [hSide]
    exact target_not_mem_topSet_of_prin_eq_oneChip_sub hab hPrincipal
  have hcross := cut.cross_num_edges _ _ cut.left_mem hb
  have hpos : 0 < num_edges G (edgeAt G e).1 (edgeAt G e).2 := by
    rw [num_edges_eq_card_slots, Finset.card_pos]
    exact ⟨e, by simp⟩
  have hz : (edgeAt G e).2 = z := by
    by_contra hz
    rw [if_neg (fun h => hz h.2)] at hcross
    omega
  subst hz
  exact ⟨cut⟩

end Bridges

/-! ## 5.  Chips along a bridge slot of a refinement -/

section BridgeSlot

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

theorem tailNeighbor_scale_eq_slotPoint_one (hunit : spec.IsUnit) (e : Fin p) :
    (spec.scale N hN).tailNeighbor e = spec.slotPoint N hN e 1 := by
  have hlen := spec.length_scale N hN hunit e
  unfold Spec.tailNeighbor Spec.stepRight
  by_cases h1 : N = 1
  · subst h1
    rw [dif_pos (by dsimp only; omega), spec.slotPoint_last 1 hN hunit e]
    rfl
  · rw [dif_neg (by dsimp only; omega)]
    exact spec.interiorVertex_eq_slotPoint N hN hunit e ⟨0, by omega⟩

/-- On a refinement of a unit presentation, every point of a bridge slot is equivalent to the
tail of the slot. -/
theorem slotPoint_linearEquiv (hunit : spec.IsUnit) {c : CoreBridgeCut.Data spec.core}
    (hc : c.Valid) :
    ∀ t, t ≤ N → linear_equiv (spec.scale N hN).graph
      (one_chip (spec.slotPoint N hN c.bridge 0)) (one_chip (spec.slotPoint N hN c.bridge t)) := by
  apply linearEquiv_chain
  · intro t h0 ht y
    have hadj := spec.slotPoint_adj_iff N hN hunit c.bridge h0 ht y
    have hle := spec.num_edges_slotPoint_le_one N hN hunit c.bridge h0 ht y
    have hne := spec.slotPoint_ne N hN hunit c.bridge (s := t - 1) (t := t + 1)
      (by omega) (by omega) (by omega)
    by_cases h1 : y = spec.slotPoint N hN c.bridge (t - 1)
    · have h2 : y ≠ spec.slotPoint N hN c.bridge (t + 1) := h1 ▸ hne
      rw [if_pos h1, if_neg h2]
      have := hadj.mpr (Or.inl h1)
      omega
    · by_cases h2 : y = spec.slotPoint N hN c.bridge (t + 1)
      · rw [if_neg h1, if_pos h2]
        have := hadj.mpr (Or.inr h2)
        omega
      · rw [if_neg h1, if_neg h2]
        have : ¬ 0 < num_edges (spec.scale N hN).graph (spec.slotPoint N hN c.bridge t) y :=
          fun h => (hadj.mp h).elim h1 h2
        omega
  · intro _
    rw [spec.slotPoint_zero N hN, ← tailNeighbor_scale_eq_slotPoint_one spec N hN hunit]
    exact (toSeparatingEdgeCut
      (CoreBridgeCut.Data.toOneBridgeCut (spec := spec.scale N hN) c hc)).chipEquivalent

end BridgeSlot

/-! ## 6.  Pushforward commutes with embedding -/

section Embed

private theorem sum_fibre_ite {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (g : V → W) (P : W → Prop) [DecidablePred P] (E : V → ℤ) :
    (∑ y : W, if P y then ∑ x : V, (if g x = y then E x else 0) else 0) =
      ∑ x : V, if P (g x) then E x else 0 := by
  have h1 : ∀ y : W, (if P y then ∑ x : V, (if g x = y then E x else 0) else 0) =
      ∑ x : V, if P y ∧ g x = y then E x else 0 := by
    intro y
    by_cases hy : P y
    · simp only [hy, true_and, if_true]
    · simp only [hy, false_and, if_false, Finset.sum_const_zero]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (g x)]
  · simp
  · intro y _ hy
    rw [if_neg (fun h => hy h.2.symm)]
  · simp

/-- Pushing an embedded divisor forward is embedding the pushed divisor, when the two
contractions commute with the two embeddings. -/
theorem pushDiv_comp {B K B' K' : CFGraph} (c : GraphContractionCertificate K K')
    (c₁ : GraphContractionCertificate B B') (f : B.V → K.V) (f' : B'.V → K'.V)
    (hcomm : ∀ x, c.vertexMap (f x) = f' (c₁.vertexMap x)) (E : CFDiv B) :
    c.pushDiv (fun y => ∑ x, if f x = y then E x else 0) =
      fun b => ∑ x', if f' x' = b then c₁.pushDiv E x' else 0 := by
  classical
  funext b
  simp only [GraphContractionCertificate.pushDiv_apply]
  rw [sum_fibre_ite f (fun y => c.vertexMap y = b) E,
    sum_fibre_ite c₁.vertexMap (fun y => f' y = b) E]
  apply Finset.sum_congr rfl
  intro x _
  rw [hcomm x]

end Embed

/-! ## 7.  Contracting every bridge of a refinement at once -/

section UnitLengths

open UnitSubdivisionPresentation

/-! Every slot of a refined unit presentation has length `N`.  These lemmas move offsets between
the refinements of two unit presentations without unfolding either one. -/

theorem length_scale_unit (X : CFGraph) (N : ℕ) (hN : 0 < N) (e : Fin X.edges.card) :
    ((spec X).scale N hN).length e = N := by
  rw [Spec.scale_length, spec_length, mul_one]

variable {X Y : CFGraph} {N : ℕ} {hN : 0 < N} {e : Fin X.edges.card} {e' : Fin Y.edges.card}
  {k : ℕ}

theorem lt_scale_unit (h : k < ((spec X).scale N hN).length e) :
    k < ((spec Y).scale N hN).length e' := by
  rw [length_scale_unit] at h ⊢
  exact h

theorem lt_scale_unit_sub (h : k < ((spec X).scale N hN).length e - 1) :
    k < ((spec Y).scale N hN).length e' - 1 := by
  rw [length_scale_unit] at h ⊢
  exact h

end UnitLengths

section ContractionMap

open UnitSubdivisionPresentation

variable (G : CFGraph)

/-- A slot is **kept** when its endpoints lie in different fossil classes; otherwise it is a
bridge, and it is contracted. -/
def Kept (e : Fin G.edges.card) : Prop :=
  fossilVertex G (edgeAt G e).1 ≠ fossilVertex G (edgeAt G e).2

noncomputable instance (e : Fin G.edges.card) : Decidable (Kept G e) := by
  unfold Kept; infer_instance

/-- The edge multiset of the fossil, typed by fossil classes. -/
noncomputable abbrev fossilEdges : Multiset (FossilVertex G × FossilVertex G) :=
  (G.edges.map (fossilEdge G)).filter fun edge => edge.1 ≠ edge.2

theorem card_fibre_slots (x : FossilVertex G × FossilVertex G) :
    Fintype.card {e : {e : Fin G.edges.card // Kept G e} //
        fossilEdge G (edgeAt G e.1) = x} =
      Fintype.card {o : fossilEdges G // (o : FossilVertex G × FossilVertex G) = x} := by
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (Kept G)
    (fun e => fossilEdge G (edgeAt G e) = x))]
  rw [Fintype.card_congr (Equiv.subtypeEquiv (p := fun e => Kept G e ∧
      fossilEdge G (edgeAt G e) = x)
    (q := fun o : G.edges => fossilVertex G (o : G.V × G.V).1 ≠
      fossilVertex G (o : G.V × G.V).2 ∧ fossilEdge G (o : G.V × G.V) = x)
    (edgeEquiv G).symm (fun e => Iff.rfl))]
  rw [Fintype.card_subtype, Fintype.card_subtype,
    card_filter_occurrences G.edges (fun y => fossilVertex G y.1 ≠ fossilVertex G y.2 ∧
      fossilEdge G y = x),
    card_filter_occurrences (fossilEdges G) (fun y => y = x)]
  rw [Multiset.filter_filter, Multiset.filter_map, Multiset.card_map]
  congr 1
  exact Multiset.filter_congr (fun y _ => and_comm)

/-- The fibre-preserving matching of kept slots with fossil edge occurrences. -/
theorem exists_keptEquiv : ∃ φ : {e : Fin G.edges.card // Kept G e} ≃ fossilEdges G,
    ∀ e, ((φ e : fossilEdges G) : FossilVertex G × FossilVertex G) =
      fossilEdge G (edgeAt G e.1) :=
  exists_equiv_of_card_fibre _ _ (fun x => by convert card_fibre_slots G x)

/-- The kept slots of `G` are the slots of its fossil. -/
noncomputable def slotEquiv : {e : Fin G.edges.card // Kept G e} ≃ Fin (fossil G).edges.card :=
  (Classical.choose (exists_keptEquiv G)).trans
    ((Equiv.refl _ : fossilEdges G ≃ (fossil G).edges).trans (edgeEquiv (fossil G)))

theorem edgeAt_slotEquiv (e : {e : Fin G.edges.card // Kept G e}) :
    edgeAt (fossil G) (slotEquiv G e) = fossilEdge G (edgeAt G e.1) := by
  have h := Classical.choose_spec (exists_keptEquiv G) e
  exact (edgeAt_edgeEquiv (fossil G) (Classical.choose (exists_keptEquiv G) e)).trans h

/-- Core vertices go to their fossil classes. -/
noncomputable def coreMap (i : Fin (Fintype.card G.V)) : Fin (Fintype.card (fossil G).V) :=
  vertexEquiv (fossil G) (fossilVertex G ((vertexEquiv G).symm i))

@[simp] theorem coreMap_vertexEquiv (v : G.V) :
    coreMap G (vertexEquiv G v) = vertexEquiv (fossil G) (fossilVertex G v) := by
  simp [coreMap]

theorem tail_slotEquiv (e : {e : Fin G.edges.card // Kept G e}) :
    (spec (fossil G)).core.tail (slotEquiv G e) = coreMap G ((spec G).core.tail e.1) := by
  rw [spec_core_tail, spec_core_tail, edgeAt_slotEquiv, coreMap_vertexEquiv]
  rfl

theorem head_slotEquiv (e : {e : Fin G.edges.card // Kept G e}) :
    (spec (fossil G)).core.head (slotEquiv G e) = coreMap G ((spec G).core.head e.1) := by
  rw [spec_core_head, spec_core_head, edgeAt_slotEquiv, coreMap_vertexEquiv]
  rfl

theorem coreMap_head_of_not_kept {e : Fin G.edges.card} (h : ¬ Kept G e) :
    coreMap G ((spec G).core.head e) = coreMap G ((spec G).core.tail e) := by
  unfold Kept at h
  push Not at h
  rw [spec_core_head, spec_core_tail, coreMap_vertexEquiv, coreMap_vertexEquiv, h]

variable (N : ℕ) (hN : 0 < N)

/-- **The contraction of every bridge**, on the `N`-fold refinement. -/
noncomputable def contractionMap :
    ((spec G).scale N hN).Vertex → ((spec (fossil G)).scale N hN).Vertex
  | Sum.inl i => Sum.inl (coreMap G i)
  | Sum.inr ⟨e, j⟩ =>
      if h : Kept G e then
        Sum.inr ⟨slotEquiv G ⟨e, h⟩, ⟨j.val, lt_scale_unit_sub j.isLt⟩⟩
      else Sum.inl (coreMap G ((spec G).core.tail e))

@[simp] theorem contractionMap_inl (i : Fin (Fintype.card G.V)) :
    contractionMap G N hN (Sum.inl i) = Sum.inl (coreMap G i) := rfl

theorem contractionMap_kept {e : Fin G.edges.card} (h : Kept G e)
    (j : Fin (((spec G).scale N hN).length e - 1)) :
    contractionMap G N hN (Sum.inr ⟨e, j⟩) =
      Sum.inr ⟨slotEquiv G ⟨e, h⟩, ⟨j.val, lt_scale_unit_sub j.isLt⟩⟩ := by
  simp only [contractionMap, dif_pos h]

theorem contractionMap_not_kept {e : Fin G.edges.card} (h : ¬ Kept G e)
    (j : Fin (((spec G).scale N hN).length e - 1)) :
    contractionMap G N hN (Sum.inr ⟨e, j⟩) = Sum.inl (coreMap G ((spec G).core.tail e)) := by
  simp only [contractionMap, dif_neg h]

theorem stepLeft_congr {n p : ℕ} (T : Spec n p) {e₁ e₂ : Fin p} (h : e₁ = e₂)
    {j₁ : Fin (T.length e₁)} {j₂ : Fin (T.length e₂)} (hj : j₁.val = j₂.val) :
    T.stepLeft e₁ j₁ = T.stepLeft e₂ j₂ := by
  subst h
  rw [Fin.ext hj]

theorem stepRight_congr {n p : ℕ} (T : Spec n p) {e₁ e₂ : Fin p} (h : e₁ = e₂)
    {j₁ : Fin (T.length e₁)} {j₂ : Fin (T.length e₂)} (hj : j₁.val = j₂.val) :
    T.stepRight e₁ j₁ = T.stepRight e₂ j₂ := by
  subst h
  rw [Fin.ext hj]

theorem contractionMap_stepLeft_kept (e : {e : Fin G.edges.card // Kept G e})
    (j : Fin (((spec G).scale N hN).length e.1)) :
    contractionMap G N hN (((spec G).scale N hN).stepLeft e.1 j) =
      ((spec (fossil G)).scale N hN).stepLeft (slotEquiv G e)
        ⟨j.val, lt_scale_unit j.isLt⟩ := by
  unfold Spec.stepLeft
  by_cases hz : j.val = 0
  · rw [dif_pos hz, dif_pos (by exact hz)]
    simp only [Spec.coreVertex, contractionMap_inl, Spec.scale_core, tail_slotEquiv]
  · rw [dif_neg hz, dif_neg (by exact hz)]
    simp only [Spec.interiorVertex, contractionMap_kept G N hN e.2]

theorem contractionMap_stepRight_kept (e : {e : Fin G.edges.card // Kept G e})
    (j : Fin (((spec G).scale N hN).length e.1)) :
    contractionMap G N hN (((spec G).scale N hN).stepRight e.1 j) =
      ((spec (fossil G)).scale N hN).stepRight (slotEquiv G e)
        ⟨j.val, lt_scale_unit j.isLt⟩ := by
  unfold Spec.stepRight
  by_cases hl : j.val + 1 = N
  · rw [dif_pos (hl.trans (length_scale_unit _ _ _ _).symm),
      dif_pos (hl.trans (length_scale_unit _ _ _ _).symm)]
    simp only [Spec.coreVertex, contractionMap_inl, Spec.scale_core, head_slotEquiv]
  · rw [dif_neg (fun h => hl (h.trans (length_scale_unit _ _ _ _))),
      dif_neg (fun h => hl (h.trans (length_scale_unit _ _ _ _)))]
    simp only [Spec.interiorVertex, contractionMap_kept G N hN e.2]

theorem contractionMap_stepLeft_not_kept {e : Fin G.edges.card} (h : ¬ Kept G e)
    (j : Fin (((spec G).scale N hN).length e)) :
    contractionMap G N hN (((spec G).scale N hN).stepLeft e j) =
      Sum.inl (coreMap G ((spec G).core.tail e)) := by
  unfold Spec.stepLeft
  by_cases hz : j.val = 0
  · rw [dif_pos hz]
    rfl
  · rw [dif_neg hz]
    exact contractionMap_not_kept G N hN h _

theorem contractionMap_stepRight_not_kept {e : Fin G.edges.card} (h : ¬ Kept G e)
    (j : Fin (((spec G).scale N hN).length e)) :
    contractionMap G N hN (((spec G).scale N hN).stepRight e j) =
      Sum.inl (coreMap G ((spec G).core.tail e)) := by
  unfold Spec.stepRight
  by_cases hl : j.val + 1 = ((spec G).scale N hN).length e
  · rw [dif_pos hl]
    exact congrArg Sum.inl (coreMap_head_of_not_kept G h)
  · rw [dif_neg hl]
    exact contractionMap_not_kept G N hN h _

/-- The unit steps of the fossil refinement, as unit steps of the refinement of `G`. -/
noncomputable def stepLift (s : ((spec (fossil G)).scale N hN).Step) :
    ((spec G).scale N hN).Step :=
  ⟨((slotEquiv G).symm s.1).1, ⟨s.2.val, lt_scale_unit s.2.isLt⟩⟩

theorem stepLift_injective : Function.Injective (stepLift G N hN) := by
  intro s₁ s₂ h
  have h1 : ((slotEquiv G).symm s₁.1).1 = ((slotEquiv G).symm s₂.1).1 :=
    congrArg Sigma.fst h
  have h2 : s₁.2.val = s₂.2.val :=
    congrArg (fun s : ((spec G).scale N hN).Step => s.2.val) h
  exact sigma_fin_ext ((slotEquiv G).symm.injective (Subtype.ext h1)) h2

theorem contractionMap_surjective : Function.Surjective (contractionMap G N hN) := by
  rintro (i | ⟨e', j⟩)
  · refine ⟨Sum.inl (vertexEquiv G (fossilRepresentative G ((vertexEquiv (fossil G)).symm i))),
      ?_⟩
    rw [contractionMap_inl, coreMap_vertexEquiv]
    have h := fossilVertex_representative G ((vertexEquiv (fossil G)).symm i)
    exact congrArg Sum.inl ((congrArg (vertexEquiv (fossil G)) h).trans
      (Equiv.apply_symm_apply _ _))
  · refine ⟨Sum.inr ⟨((slotEquiv G).symm e').1, ⟨j.val, lt_scale_unit_sub j.isLt⟩⟩, ?_⟩
    rw [contractionMap_kept G N hN ((slotEquiv G).symm e').2]
    exact congrArg Sum.inr (sigma_fin_ext (Equiv.apply_symm_apply _ _) rfl)

/-- **The contraction is valid**: between distinct target vertices, the target multiplicity is
the sum of source multiplicities between the fibres. -/
theorem contraction_valid :
    (GraphContractionCertificate.mk (contractionMap G N hN) :
      GraphContractionCertificate ((spec G).scale N hN).graph
        ((spec (fossil G)).scale N hN).graph).Valid := by
  classical
  refine valid_of_stepInjection ((spec G).scale N hN).unitEdge
    ((spec (fossil G)).scale N hN).unitEdge
    (Spec.num_edges_eq_card_filter_steps _) (Spec.num_edges_eq_card_filter_steps _)
    (fun s => Spec.stepLeft_ne_stepRight _ s.1 s.2)
    (fun s => Spec.stepLeft_ne_stepRight _ s.1 s.2)
    _ (contractionMap_surjective G N hN) (stepLift G N hN) (stepLift_injective G N hN) ?_ ?_
  · intro s
    have hs : slotEquiv G ((slotEquiv G).symm s.1) = s.1 := Equiv.apply_symm_apply _ _
    simp only [Spec.unitEdge, stepLift]
    rw [contractionMap_stepLeft_kept G N hN ((slotEquiv G).symm s.1),
      contractionMap_stepRight_kept G N hN ((slotEquiv G).symm s.1)]
    exact Prod.ext (stepLeft_congr _ hs.symm rfl) (stepRight_congr _ hs.symm rfl)
  · rintro ⟨e, j⟩ hs
    by_cases hk : Kept G e
    · exfalso
      apply hs
      refine ⟨⟨slotEquiv G ⟨e, hk⟩, ⟨j.val, lt_scale_unit j.isLt⟩⟩, ?_⟩
      exact sigma_fin_ext (congrArg Subtype.val (Equiv.symm_apply_apply _ _)) rfl
    · simp only [Spec.unitEdge]
      rw [contractionMap_stepLeft_not_kept G N hN hk, contractionMap_stepRight_not_kept G N hN hk]

end ContractionMap

/-! ## 8.  The fibres of the contraction are linearly equivalent -/

section Fibres

open UnitSubdivisionPresentation

variable (G : CFGraph) (N : ℕ) (hN : 0 < N)

/-- The two ends of a separating edge of `G` are equivalent in every refinement. -/
theorem core_linearEquiv_of_cut {a b : G.V} (cut : SeparatingEdgeCut G a b) :
    linear_equiv ((spec G).scale N hN).graph (one_chip (Sum.inl (vertexEquiv G a)))
      (one_chip (Sum.inl (vertexEquiv G b))) := by
  have hunit := Gonality.isUnit_unitSpec G
  have key : ∀ {x y : G.V} (cut : SeparatingEdgeCut G x y) (e : Fin G.edges.card),
      edgeAt G e = (x, y) → linear_equiv ((spec G).scale N hN).graph
        (one_chip (Sum.inl (vertexEquiv G x))) (one_chip (Sum.inl (vertexEquiv G y))) := by
    intro x y cut e he
    have h := slotPoint_linearEquiv (spec G) N hN hunit (valid_of_separatingEdgeCut cut e he)
      N le_rfl
    rw [Spec.slotPoint_zero, Spec.slotPoint_last _ _ _ hunit] at h
    dsimp only at h
    rw [spec_core_tail, spec_core_head, he] at h
    exact h
  obtain ⟨e, he | he⟩ := exists_slot_of_separatingEdgeCut cut
  · exact key cut e he
  · exact (key (cutSwap cut) e he).symm

/-- Equivalent one-chip divisors of `G` stay equivalent in every refinement. -/
theorem core_linearEquiv (hG : graph_connected G) {v w : G.V}
    (hvw : linear_equiv G (one_chip v) (one_chip w)) :
    linear_equiv ((spec G).scale N hN).graph (one_chip (Sum.inl (vertexEquiv G v)))
      (one_chip (Sum.inl (vertexEquiv G w))) := by
  classical
  let K := ((spec G).scale N hN).graph
  let rho : firing_script G := fun u =>
    (((Fintype.equivFin (FossilVertex K)) (fossilVertex K (Sum.inl (vertexEquiv G u)))).val : ℤ)
  have key : ∀ u u' : G.V, rho u = rho u' ↔
      linear_equiv K (one_chip (Sum.inl (vertexEquiv G u)))
        (one_chip (Sum.inl (vertexEquiv G u'))) := by
    intro u u'
    simp only [rho, Nat.cast_inj, Fin.val_inj, Equiv.apply_eq_iff_eq]
    exact fossilVertex_eq_iff K _ _
  exact (key v w).mp (eq_of_chipEquivalent_of_separating_normalized hG rho
    (fun cut => (key _ _).mpr (core_linearEquiv_of_cut G N hN cut)) hvw)

/-- An interior point of a bridge slot is equivalent to the tail of the bridge. -/
theorem interior_linearEquiv (hG : graph_connected G) {e : Fin G.edges.card} (hk : ¬ Kept G e)
    (j : Fin (((spec G).scale N hN).length e - 1)) :
    linear_equiv ((spec G).scale N hN).graph (one_chip (Sum.inr ⟨e, j⟩))
      (one_chip (Sum.inl ((spec G).core.tail e))) := by
  have hunit := Gonality.isUnit_unitSpec G
  unfold Kept at hk
  push Not at hk
  obtain ⟨cut⟩ := separatingEdgeCut_of_chipEquivalent hG e hk
  have hv := valid_of_separatingEdgeCut cut e rfl
  have hj : j.val + 1 ≤ N := by
    have := j.isLt
    have := length_scale_unit G N hN e
    omega
  have h := slotPoint_linearEquiv (spec G) N hN hunit hv (j.val + 1) hj
  rw [Spec.slotPoint_zero, ← Spec.interiorVertex_eq_slotPoint (spec G) N hN hunit _ j] at h
  exact h.symm

/-- Every source vertex is either equivalent to a vertex of `G` with the same image, or an
interior point of a kept slot. -/
theorem classify (hG : graph_connected G) (x : ((spec G).scale N hN).Vertex) :
    (∃ v : G.V, linear_equiv ((spec G).scale N hN).graph (one_chip x)
        (one_chip (Sum.inl (vertexEquiv G v))) ∧
      contractionMap G N hN x = Sum.inl (vertexEquiv (fossil G) (fossilVertex G v))) ∨
    (∃ (e : Fin G.edges.card) (h : Kept G e) (j : Fin (((spec G).scale N hN).length e - 1)),
      x = Sum.inr ⟨e, j⟩ ∧
      contractionMap G N hN x = Sum.inr ⟨slotEquiv G ⟨e, h⟩, ⟨j.val, lt_scale_unit_sub j.isLt⟩⟩) := by
  rcases x with i | ⟨e, j⟩
  · left
    refine ⟨(vertexEquiv G).symm i, ?_, rfl⟩
    rw [Equiv.apply_symm_apply]
  · by_cases hk : Kept G e
    · exact Or.inr ⟨e, hk, j, rfl, contractionMap_kept G N hN hk j⟩
    · left
      refine ⟨(edgeAt G e).1, interior_linearEquiv G N hN hG hk j, ?_⟩
      rw [contractionMap_not_kept G N hN hk, spec_core_tail, coreMap_vertexEquiv]

/-- **The fibres of the bridge contraction consist of linearly equivalent points.** -/
theorem fibresEquivalent (hG : graph_connected G) :
    FibresEquivalent (GraphContractionCertificate.mk (contractionMap G N hN) :
      GraphContractionCertificate ((spec G).scale N hN).graph
        ((spec (fossil G)).scale N hN).graph) := by
  intro x y hxy
  change contractionMap G N hN x = contractionMap G N hN y at hxy
  rcases classify G N hN hG x with ⟨v, hv, hxv⟩ | ⟨e, he, j, rfl, hx⟩ <;>
    rcases classify G N hN hG y with ⟨w, hw, hyw⟩ | ⟨f, hf, k, rfl, hy⟩
  · have hfv : fossilVertex G v = fossilVertex G w := by
      rw [hxv, hyw] at hxy
      exact (vertexEquiv (fossil G)).injective (Sum.inl.inj hxy)
    exact hv.trans ((core_linearEquiv G N hN hG ((fossilVertex_eq_iff G v w).mp hfv)).trans
      hw.symm)
  · rw [hxv, hy] at hxy
    cases hxy
  · rw [hx, hyw] at hxy
    cases hxy
  · rw [hx, hy] at hxy
    have h1 := Sum.inr.inj hxy
    have hσ : slotEquiv G ⟨e, he⟩ = slotEquiv G ⟨f, hf⟩ := congrArg Sigma.fst h1
    have hef : e = f := congrArg Subtype.val ((slotEquiv G).injective hσ)
    have hjk : j.val = k.val :=
      congrArg (fun z : ((spec (fossil G)).scale N hN).Interior => z.2.val) h1
    have hsame : (⟨e, j⟩ : ((spec G).scale N hN).Interior) = ⟨f, k⟩ := sigma_fin_ext hef hjk
    rw [hsame]

end Fibres

/-! ## 9.  The bridge lift -/

section Lift

open UnitSubdivisionPresentation

variable (G : CFGraph)

/-- The contraction on the unit presentation itself. -/
noncomputable def baseMap : (spec G).Vertex → (spec (fossil G)).Vertex
  | Sum.inl i => Sum.inl (coreMap G i)
  | Sum.inr x => (noInterior G x).elim

theorem contractionMap_fineOf (N : ℕ) (hN : 0 < N) (x : (spec G).Vertex) :
    contractionMap G N hN ((spec G).fineOf N hN x) =
      (spec (fossil G)).fineOf N hN (baseMap G x) := by
  rcases x with i | x
  · rfl
  · exact (noInterior G x).elim

/-- The prescribed divisor is carried to the prescribed divisor of the fossil, at every scale. -/
theorem pushDiv_embed (N : ℕ) (hN : 0 < N) (E : CFDiv (spec G).graph) :
    (GraphContractionCertificate.mk (contractionMap G N hN) :
      GraphContractionCertificate ((spec G).scale N hN).graph
        ((spec (fossil G)).scale N hN).graph).pushDiv ((spec G).embed N hN E) =
      (spec (fossil G)).embed N hN
        ((GraphContractionCertificate.mk (baseMap G) :
          GraphContractionCertificate (spec G).graph (spec (fossil G)).graph).pushDiv E) := by
  unfold Spec.embed
  exact pushDiv_comp (B := (spec G).graph) (K := ((spec G).scale N hN).graph)
    (B' := (spec (fossil G)).graph) (K' := ((spec (fossil G)).scale N hN).graph) _ _
    ((spec G).fineOf N hN) ((spec (fossil G)).fineOf N hN) (contractionMap_fineOf G N hN) E

end Lift

end Utilities.Subdivision.BridgeLift
