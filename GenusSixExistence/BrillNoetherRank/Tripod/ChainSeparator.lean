module

public import DraismaVargasCount.CorePencilCoverProducer
public import Utilities.Subdivision.BivalentPaths

@[expose] public section

/-!
# Rank one through bivalent chains

The graph-theoretic half of the rank-determining set of
`Research/genus-six-brill-noether-rank.md`, §7.4 (Odd multiplicity gives an odd scale), in the
form described in §8.2 (Where the Lean proof differs from the prose): Luo's criterion, certified
directly by paths of bivalent vertices.

`Spec.rank_ge_one_of_reaches_coreVertices` (the finite form of Luo's theorem for a subdivided
loopless core) tests rank one at **every** core vertex. On a subdivision carrying the markers of
an expansion datum, some core vertices are bivalent markers, and
`CorePencilCoverProducer.rank_ge_one_of_markerFree` removes the need to test at a marker by
moving it onto a reached vertex of its own chain. That still asks for a reached vertex strictly
inside **every** `double` chain. Here only the chains that close up into a loop need one:

* `rank_ge_one_of_fib_loopDoubles` — on a connected subdivision `T` of the small core of an
  expansion datum, a divisor reaching every `D.fib` image and, for each `double` slot whose chain
  is a loop, some vertex strictly inside that chain, has rank at least one.

The proof applies the strong-separator lemma
(`StrongSeparator.rank_ge_one_of_strongSeparatorCertificate`) directly to the reached set, with a
certificate built from **bivalent paths** (`Utilities.Subdivision.BivalentPaths.BivalentPath`,
with the slot paths `slotPath`): a walk whose interior vertices see
only their two path neighbours. A slot of `T` is one (`slotPath`), and so is the chain
`j₁ ⋯ j₂` of a `double` slot through its marker (`chainPath`): the marker is bivalent by
`MarkerPair`. Every vertex outside the reached set lies strictly inside one of these paths
(a non-`double` slot, or a `double` chain), and a maximal unreached interval of such a path with
distinct reached ends is a strong-separator cell (`BivalentPath.Gap.cell`). The ends are distinct
unless the path is a loop chain, whose reached interior vertex splits it. This is Luo's criterion:
the closure of every complementary component is contractible.
-/

namespace GenusSixExistence.Tripod.ChainSeparator

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.StrongSeparator
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Count.CorePencilCoverProducer
  (MarkerPair chainVertex chainStep chainVertex_zero chainVertex_first chainVertex_last
    chainVertex_of_lt chainVertex_of_gt chainVertex_shift unitEdge_chainStep
    stepLeft_eq_pathVertex stepRight_eq_pathVertex marker_or_exists_fib markerPair_of_double)

open Utilities.Subdivision.BivalentPaths

/-! ## 1.  The chain of a marker pair is a bivalent path -/

section SpecPaths

variable {n p : ℕ} (T : Spec n p)

variable {j₁ j₂ : Fin p}

theorem chainVertex_eq_slotVtx_first {t : ℕ} (ht : t ≤ T.length j₁) :
    chainVertex T j₁ j₂ t = slotVtx T j₁ t :=
  kindVertex_double_le j₁ j₂ _ ht

variable (hpair : MarkerPair T.core j₁ j₂)
include hpair

theorem chainVertex_eq_slotVtx_second (i : ℕ) :
    chainVertex T j₁ j₂ (T.length j₁ + i) = slotVtx T j₂ i :=
  chainVertex_shift T hpair.2.1 i

/-- The unit steps at a marker: the first step of `j₂` and the last step of `j₁`. -/
theorem marker_step_cases (s : T.Step) (y : T.Vertex)
    (h : T.unitEdge s = (T.coreVertex (T.core.head j₁), y) ∨
      T.unitEdge s = (y, T.coreVertex (T.core.head j₁))) :
    (s = ⟨j₂, ⟨0, T.length_pos j₂⟩⟩ ∧ y = chainVertex T j₁ j₂ (T.length j₁ + 1)) ∨
      (s = ⟨j₁, ⟨T.length j₁ - 1, by have := T.length_pos j₁; omega⟩⟩ ∧
        y = chainVertex T j₁ j₂ (T.length j₁ - 1)) := by
  obtain ⟨j, o⟩ := s
  have ho := o.isLt
  rcases h with h | h
  · simp only [Spec.unitEdge, Prod.mk.injEq] at h
    obtain ⟨hl, hr⟩ := h
    unfold Spec.stepLeft at hl
    by_cases ho0 : o.val = 0
    · rw [dite_eq_left ho0] at hl
      have hj : j = j₂ := hpair.2.2.2 j (Sum.inl.inj hl)
      subst hj
      left
      refine ⟨by congr 1; exact Fin.ext ho0, ?_⟩
      rw [← hr, chainVertex_eq_slotVtx_second T hpair 1,
        slotVtx_of_le T j (T.length_pos j), stepRight_eq_pathVertex]
      exact PathHelpers.pathVertex_congr T j _ _ (by simp [ho0])
    · rw [dite_eq_right ho0] at hl
      exact absurd hl (by simp [Spec.interiorVertex, Spec.coreVertex])
  · simp only [Spec.unitEdge, Prod.mk.injEq] at h
    obtain ⟨hl, hr⟩ := h
    unfold Spec.stepRight at hr
    by_cases hoL : o.val + 1 = T.length j
    · rw [dite_eq_left hoL] at hr
      have hj : j = j₁ := hpair.2.2.1 j (Sum.inl.inj hr)
      subst hj
      right
      refine ⟨by congr 1; exact Fin.ext (by simp; omega), ?_⟩
      rw [← hl, chainVertex_eq_slotVtx_first T (by omega), slotVtx_of_le T j (by omega),
        stepLeft_eq_pathVertex]
      exact PathHelpers.pathVertex_congr T j _ _ (by simp; omega)
    · rw [dite_eq_right hoL] at hr
      exact absurd hr (by simp [Spec.interiorVertex, Spec.coreVertex])

theorem chain_adj {t : ℕ} (ht : t < T.length j₁ + T.length j₂) :
    0 < num_edges T.graph (chainVertex T j₁ j₂ t) (chainVertex T j₁ j₂ (t + 1)) :=
  (T.num_edges_pos_iff _ _).mpr ⟨chainStep T j₁ j₂ t, Or.inl (unitEdge_chainStep T hpair.2.1 ht)⟩

theorem chain_nbr {t : ℕ} (h0 : 0 < t) (hL : t < T.length j₁ + T.length j₂) (y : T.Vertex)
    (h : 0 < num_edges T.graph (chainVertex T j₁ j₂ t) y) :
    y = chainVertex T j₁ j₂ (t - 1) ∨ y = chainVertex T j₁ j₂ (t + 1) := by
  rcases lt_trichotomy t (T.length j₁) with hlt | heq | hgt
  · rw [chainVertex_eq_slotVtx_first T hlt.le] at h
    rw [chainVertex_eq_slotVtx_first T (by omega), chainVertex_eq_slotVtx_first T (by omega)]
    exact slot_nbr T j₁ h0 hlt y h
  · subst heq
    rw [chainVertex_first] at h
    obtain ⟨s, hs⟩ := (T.num_edges_pos_iff _ _).mp h
    rcases marker_step_cases T hpair s y hs with ⟨-, hy⟩ | ⟨-, hy⟩
    · exact Or.inr hy
    · exact Or.inl hy
  · obtain ⟨i, rfl⟩ : ∃ i, t = T.length j₁ + i := ⟨t - T.length j₁, by omega⟩
    rw [chainVertex_eq_slotVtx_second T hpair] at h
    rw [show T.length j₁ + i - 1 = T.length j₁ + (i - 1) by omega,
      show T.length j₁ + i + 1 = T.length j₁ + (i + 1) by omega,
      chainVertex_eq_slotVtx_second T hpair, chainVertex_eq_slotVtx_second T hpair]
    exact slot_nbr T j₂ (by omega) (by omega) y h

theorem chain_mult {t : ℕ} (h0 : 0 < t) (hL : t < T.length j₁ + T.length j₂)
    (hne : chainVertex T j₁ j₂ (t - 1) ≠ chainVertex T j₁ j₂ (t + 1)) (y : T.Vertex) :
    num_edges T.graph (chainVertex T j₁ j₂ t) y ≤ 1 := by
  classical
  rcases lt_trichotomy t (T.length j₁) with hlt | heq | hgt
  · rw [chainVertex_eq_slotVtx_first T hlt.le]
    exact slot_mult T j₁ h0 hlt y
  · subst heq
    rw [chainVertex_first, T.num_edges_eq_card_filter_steps]
    refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases marker_step_cases T hpair a y ha with ⟨ha', hya⟩ | ⟨ha', hya⟩ <;>
      rcases marker_step_cases T hpair b y hb with ⟨hb', hyb⟩ | ⟨hb', hyb⟩
    · rw [ha', hb']
    · exact absurd (hyb.symm.trans hya) hne
    · exact absurd (hya.symm.trans hyb) hne
    · rw [ha', hb']
  · obtain ⟨i, rfl⟩ : ∃ i, t = T.length j₁ + i := ⟨t - T.length j₁, by omega⟩
    rw [chainVertex_eq_slotVtx_second T hpair]
    exact slot_mult T j₂ (by omega) (by omega) y

/-- On the first slot strictly before the marker, or on the second strictly after it, a chain
vertex is an interior vertex of that slot; the other chain vertices are core vertices. -/
theorem chain_cross {s t : ℕ} (hs : s < T.length j₁) (ht : T.length j₁ < t)
    (htL : t ≤ T.length j₁ + T.length j₂)
    (h : chainVertex T j₁ j₂ s = chainVertex T j₁ j₂ t) :
    s = 0 ∧ t = T.length j₁ + T.length j₂ := by
  obtain ⟨i, rfl⟩ : ∃ i, t = T.length j₁ + i := ⟨t - T.length j₁, by omega⟩
  rw [chainVertex_eq_slotVtx_first T hs.le, chainVertex_eq_slotVtx_second T hpair] at h
  have hj : j₁ ≠ j₂ := hpair.1
  by_cases hiL : i = T.length j₂
  · refine ⟨?_, by omega⟩
    by_contra hs0
    rw [slotVtx_interior T j₁ (by omega) hs, hiL, slotVtx_length] at h
    exact absurd h (by simp [Spec.interiorVertex, Spec.coreVertex])
  · exfalso
    rw [slotVtx_interior T j₂ (by omega) (by omega)] at h
    by_cases hs0 : s = 0
    · rw [hs0, slotVtx_zero] at h
      exact absurd h (by simp [Spec.interiorVertex, Spec.coreVertex])
    · rw [slotVtx_interior T j₁ (by omega) hs] at h
      exact hj (congrArg Sigma.fst (Sum.inr.inj h))

theorem chain_inj {s t : ℕ} (hs : s ≤ T.length j₁ + T.length j₂)
    (ht : t ≤ T.length j₁ + T.length j₂)
    (h : chainVertex T j₁ j₂ s = chainVertex T j₁ j₂ t) :
    s = t ∨ (s = 0 ∧ t = T.length j₁ + T.length j₂) ∨
      (s = T.length j₁ + T.length j₂ ∧ t = 0) := by
  by_cases hs1 : s < T.length j₁
  · by_cases ht1 : T.length j₁ < t
    · exact Or.inr (Or.inl (chain_cross T hpair hs1 ht1 ht h))
    · left
      rw [chainVertex_eq_slotVtx_first T hs1.le, chainVertex_eq_slotVtx_first T (by omega)] at h
      exact slot_inj T j₁ (by omega) (by omega) h
  · by_cases ht1 : t < T.length j₁
    · by_cases hs2 : T.length j₁ < s
      · have h' := chain_cross T hpair ht1 hs2 hs h.symm
        exact Or.inr (Or.inr ⟨h'.2, h'.1⟩)
      · left
        rw [chainVertex_eq_slotVtx_first T (by omega), chainVertex_eq_slotVtx_first T ht1.le] at h
        exact slot_inj T j₁ (by omega) (by omega) h
    · left
      obtain ⟨i, rfl⟩ : ∃ i, s = T.length j₁ + i := ⟨s - T.length j₁, by omega⟩
      obtain ⟨i', rfl⟩ : ∃ i', t = T.length j₁ + i' := ⟨t - T.length j₁, by omega⟩
      rw [chainVertex_eq_slotVtx_second T hpair, chainVertex_eq_slotVtx_second T hpair] at h
      have := slot_inj T j₂ (by omega) (by omega) h
      omega

/-- **The chain of a marker pair is a bivalent path.** -/
def chainPath : BivalentPath T.graph where
  len := T.length j₁ + T.length j₂
  vtx := chainVertex T j₁ j₂
  adj := fun _ ht ↦ chain_adj T hpair ht
  nbr := fun _ h0 hL y h ↦ chain_nbr T hpair h0 hL y h
  mult := fun _ h0 hL hne y ↦ chain_mult T hpair h0 hL hne y
  inj := fun _ _ hs ht h ↦ chain_inj T hpair hs ht h

end SpecPaths

/-! ## 2.  The certificate, and rank one -/

section Rank

variable {n p N Q : ℕ}

/-- **Rank one, the graph half** (§7.4). On a connected subdivision `T` of the small core of an
expansion datum, a divisor that reaches every `D.fib` image and, for every `double` slot displaying a
loop, some vertex strictly inside its chain, has rank at least one.

The reached set of the hypotheses contains the `D.fib` images, hence both ends of every
non-`double` slot and of every `double` chain; a vertex outside an enlargement of it lies
strictly inside one of these paths, and a maximal gap there is a strong-separator cell. -/
theorem rank_ge_one_of_fib_loopDoubles (D : ExpansionData n p N Q)
    (T : Spec n p) (hCond : D.Conditions T.core) (hConn : graph_connected T.graph)
    (R : Set T.Vertex) (hFib : ∀ a : Fin N, T.coreVertex (D.fib a) ∈ R)
    (hLoop : ∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ →
      T.core.tail j₁ = T.core.head j₂ →
      ∃ t, 0 < t ∧ t < T.length j₁ + T.length j₂ ∧
        kindVertex T (T.core.tail j₁) (SlotKind.double j₁ j₂) t ∈ R)
    (Dv : CFDiv T.graph) (hReach : ∀ w ∈ R, winnable T.graph (Dv - one_chip w)) :
    rank T.graph Dv ≥ 1 := by
  classical
  set S : Finset T.Vertex := Finset.univ.filter (· ∈ R) with hS
  have hmemS : ∀ w, w ∈ S ↔ w ∈ R := fun w ↦ by simp [hS]
  -- `S` is nonempty: every core vertex is a fibre image or a marker of a slot between images
  have hSne : S.Nonempty := by
    rcases marker_or_exists_fib hCond (⟨0, T.core_nonempty⟩ : Fin n) with
      ⟨e, -, -, -, -⟩ | ⟨a, -⟩
    · exact ⟨_, (hmemS _).mpr (hFib (D.bigCore.tail e))⟩
    · exact ⟨_, (hmemS _).mpr (hFib a)⟩
  refine rank_ge_one_of_strongSeparatorCertificate hConn hSne ?_
    (fun s hs ↦ hReach s ((hmemS s).mp hs))
  intro R' hSR' _ hProper
  have hR' : ∀ w ∈ R, w ∈ R' := fun w hw ↦ hSR' ((hmemS w).mpr hw)
  have hFib' : ∀ a, T.coreVertex (D.fib a) ∈ R' := fun a ↦ hR' _ (hFib a)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ R' := by
    by_contra h
    push Not at h
    exact hProper (Finset.eq_univ_of_forall h)
  -- a vertex strictly inside the chain of a `double` slot
  have hChain : ∀ (e : Fin Q) (j₁ j₂ : Fin p) (hk : D.kind e = SlotKind.double j₁ j₂) (c : ℕ),
      c < T.length j₁ + T.length j₂ → chainVertex T j₁ j₂ c ∉ R' →
      Nonempty (ExpansionCell T.graph R') := by
    intro e j₁ j₂ hk c hcL hc
    have hpair : MarkerPair T.core j₁ j₂ := markerPair_of_double hCond hk
    obtain ⟨hT, -, hH⟩ := (ExpansionData.compatible_of_conditions hCond e).2.2 j₁ j₂ hk
    refine (chainPath T hpair).exists_cell R' hcL hc ?_ ?_ ?_
    · show chainVertex T j₁ j₂ 0 ∈ R'
      rw [chainVertex_zero, ← hT]
      exact hFib' _
    · show chainVertex T j₁ j₂ (T.length j₁ + T.length j₂) ∈ R'
      rw [chainVertex_last T le_rfl, ← hH]
      exact hFib' _
    · by_cases hloop : T.core.tail j₁ = T.core.head j₂
      · obtain ⟨r, hr0, hrL, hr⟩ := hLoop e j₁ j₂ hk hloop
        exact Or.inr ⟨r, hr0, hrL, hR' _ hr⟩
      · left
        show chainVertex T j₁ j₂ 0 ≠ chainVertex T j₁ j₂ (T.length j₁ + T.length j₂)
        rw [chainVertex_zero, chainVertex_last T le_rfl]
        exact fun h ↦ hloop (Sum.inl.inj h)
  rcases x with w | ⟨j, o⟩
  · -- a core vertex outside `R'` is a marker
    rcases marker_or_exists_fib hCond w with ⟨e, j₁, j₂, hk, hw⟩ | ⟨a, rfl⟩
    · refine hChain e j₁ j₂ hk (T.length j₁) (by have := T.length_pos j₂; omega) ?_
      rw [chainVertex_first, hw]
      exact hx
    · exact absurd (hFib' a) hx
  · have ho := o.isLt
    rcases ExpansionData.exists_carrier hCond j with ⟨hk, -⟩ | ⟨j₂, hk, -⟩ | ⟨j₁, hk, -⟩
    · -- a slot carried singly: its ends are fibre images
      obtain ⟨hT, hH⟩ := (ExpansionData.compatible_of_conditions hCond (D.owner j)).2.1 j hk
      refine (slotPath T j).exists_cell R' (c := o.val + 1) (by
        show o.val + 1 < T.length j
        omega) ?_ ?_ ?_ (Or.inl ?_)
      · show slotVtx T j (o.val + 1) ∉ R'
        rw [slotVtx_interior T j (by omega) (by omega)]
        exact hx
      · show slotVtx T j 0 ∈ R'
        rw [slotVtx_zero, ← hT]
        exact hFib' _
      · show slotVtx T j (T.length j) ∈ R'
        rw [slotVtx_length, ← hH]
        exact hFib' _
      · show slotVtx T j 0 ≠ slotVtx T j (T.length j)
        rw [slotVtx_zero, slotVtx_length]
        exact fun h ↦ T.core_loopless j (Sum.inl.inj h)
    · -- the first half of a `double` chain
      refine hChain (D.owner j) j j₂ hk (o.val + 1) (by have := T.length_pos j₂; omega) ?_
      rw [chainVertex_of_lt T (by omega) (by omega)]
      exact hx
    · -- the second half of a `double` chain
      refine hChain (D.owner j) j₁ j hk (T.length j₁ + o.val + 1) (by omega) ?_
      rw [chainVertex_of_gt T (by omega) (by omega)]
      have hEq : (⟨T.length j₁ + o.val + 1 - T.length j₁ - 1, by omega⟩ :
          Fin (T.length j - 1)) = o := Fin.ext (by simp only; omega)
      rw [hEq]
      exact hx

end Rank

end GenusSixExistence.Tripod.ChainSeparator
