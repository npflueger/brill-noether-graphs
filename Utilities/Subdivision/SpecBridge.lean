import Utilities.Subdivision.CoreBridgeCut
import Utilities.Gluing.BridgeContraction
import Utilities.Subdivision.LaplacianEquiv
import Utilities.Subdivision.SubdivisionConnectivity
import Utilities.Gonality.GonalityTransport

/-!
# Contracting a bridge slot of a subdivision specification

A core with a bridge (for instance one attaching a pendant cycle) need not
have a trivalent loopless stable model.  This file provides the reduction that
removes bridges before a stable model is formed: every bridge of the core is
contracted, and the pencil is transported back across each bridge, since
Brill--Noether existence is unchanged by the contraction.

## What is here

* **Bridges of a core.**  `IsBridge core e` says the slot `e` admits a valid
  `CoreBridgeCut.Data` (a tail side containing the tail and not the head, every
  other slot on one side).  On a connected core this is exactly "removing `e`
  disconnects".  `Bridgeless` negates it for every slot; both are decidable.

* **The contracted specification.**  `contractBridge spec c h : Spec n p` for
  `spec : Spec (n+1) (p+1)` and a valid cut `c` at the slot `c.bridge`: the head
  of the bridge is merged into its tail (`merge`), the slot is deleted through
  `Fin.succAbove`, all other lengths are inherited.  The core stays loopless
  (`contractBridge_core_loopless`: a bridge is parallel to nothing), the genus
  `p - n` is preserved on the nose, and connectivity is preserved
  (`contractBridge_connected`).

* **The decomposition at a bridge slot.**  `spec.graph` is `LaplacianEquiv` to
  `bridgeGraph L R x y` (`bridgeEquiv`), where `L`, `R` are the two sides of
  the first unit step of the bridge slot, and the specification obtained by
  contracting that unit step is `LaplacianEquiv` to `vertexWedge L R x y`.
  Contracting the first unit step of a slot of length one *is* `contractBridge`
  (`contractEquiv`); for a slot of length at least two it is `shorten`, the
  same specification with the slot one unit shorter (`shortenEquiv`).  Both
  are instances of one lemma, `laplacianEquivWedgeOfSteps`, which asks only
  for a vertex bijection and a step bijection compatible with the two graph
  presentations; the multiset bookkeeping is done once, in
  `wedge_edges_eq`.

* **Transport.**  `bnExists_contractBridge_iff`: Brill--Noether existence on
  the contracted specification is equivalent to Brill--Noether existence on the
  original, in every rank and degree, for every slot length.  The length is
  handled by induction, shortening the bridge one unit at a time with
  `shortenEquiv` and finishing with `contractEquiv`; the step is
  `Utilities.BNExists_bridge_iff_vertexWedge`.  The equivalence commutes with
  `Spec.scale`, so the same holds for every uniform refinement, and
  `regularSubdivisionGonality` is preserved.

* **Iteration.**  `exists_bridgeless`: every connected specification reduces,
  by a finite chain of bridge contractions, to a connected bridgeless
  specification of the same genus with the composite transport, in the plain
  and in the scaled form.
-/

namespace DraismaVargas.LocalCases.SpecBridge

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open MarkedGraphs.Certificate
open ExplicitPotential
open Finset

/-! ## 1.  Bridges of a core -/

section Bridges

variable {n p : ℕ}

instance {core : Core n p} (c : CoreBridgeCut.Data core) : Decidable c.Valid :=
  decidable_of_iff _ (CoreBridgeCut.Data.check_eq_true_iff c)

/-- A slot is a **bridge** when some tail side exhibits it as the unique
crossing slot. -/
def IsBridge (core : Core n p) (e : Fin p) : Prop :=
  ∃ left : Finset (Fin n), (CoreBridgeCut.Data.mk (core := core) left e).Valid

instance (core : Core n p) (e : Fin p) : Decidable (IsBridge core e) := by
  unfold IsBridge; infer_instance

/-- No slot is a bridge. -/
def Bridgeless (core : Core n p) : Prop := ∀ e : Fin p, ¬ IsBridge core e

instance (core : Core n p) : Decidable (Bridgeless core) := by
  unfold Bridgeless; infer_instance

theorem isBridge_of_valid {core : Core n p} (c : CoreBridgeCut.Data core) (h : c.Valid) :
    IsBridge core c.bridge := ⟨c.left, h⟩

theorem not_valid_of_bridgeless {core : Core n p} (hB : Bridgeless core)
    (c : CoreBridgeCut.Data core) : ¬ c.Valid :=
  fun h => hB c.bridge (isBridge_of_valid c h)

theorem exists_valid_of_not_bridgeless {core : Core n p} (hB : ¬ Bridgeless core) :
    ∃ c : CoreBridgeCut.Data core, c.Valid := by
  unfold Bridgeless at hB
  push Not at hB
  obtain ⟨e, left, hv⟩ := hB
  exact ⟨⟨left, e⟩, hv⟩

end Bridges

/-! ## 2.  Merging the head of a bridge into its tail -/

section Merge

variable {n : ℕ}

/-- Send `w` to the label of `v` and every other vertex to its own label in
`Fin n`, the labels being read off `Fin.succAbove w`. -/
def merge (w v : Fin (n + 1)) (hvw : v ≠ w) (u : Fin (n + 1)) : Fin n :=
  if h : u = w then (finSuccAboveEquiv w).symm ⟨v, hvw⟩
  else (finSuccAboveEquiv w).symm ⟨u, h⟩

theorem succAbove_merge (w v : Fin (n + 1)) (hvw : v ≠ w) {u : Fin (n + 1)} (hu : u ≠ w) :
    w.succAbove (merge w v hvw u) = u := by
  unfold merge
  rw [dif_neg hu]
  have := (finSuccAboveEquiv w).apply_symm_apply ⟨u, hu⟩
  rw [finSuccAboveEquiv_apply] at this
  exact congrArg Subtype.val this

theorem merge_succAbove (w v : Fin (n + 1)) (hvw : v ≠ w) (i : Fin n) :
    merge w v hvw (w.succAbove i) = i := by
  unfold merge
  rw [dif_neg (Fin.succAbove_ne w i)]
  have := (finSuccAboveEquiv w).symm_apply_apply i
  rw [finSuccAboveEquiv_apply] at this
  exact this

theorem merge_self (w v : Fin (n + 1)) (hvw : v ≠ w) :
    merge w v hvw w = merge w v hvw v := by
  unfold merge
  rw [dif_pos rfl, dif_neg hvw]

theorem merge_inj (w v : Fin (n + 1)) (hvw : v ≠ w) {a b : Fin (n + 1)}
    (ha : a ≠ w) (hb : b ≠ w) (h : merge w v hvw a = merge w v hvw b) : a = b := by
  rw [← succAbove_merge w v hvw ha, ← succAbove_merge w v hvw hb, h]

theorem eq_of_merge_eq_merge_self (w v : Fin (n + 1)) (hvw : v ≠ w) {a : Fin (n + 1)}
    (ha : a ≠ w) (h : merge w v hvw a = merge w v hvw w) : a = v := by
  rw [merge_self] at h
  exact merge_inj w v hvw ha hvw h

end Merge

/-! ## 3.  The contracted core and the contracted specification -/

section Contraction

variable {n p : ℕ}

/-- Contract the slot `e` of a loopless core: merge its head into its tail and
delete the slot. -/
def contractCore (core : Core (n + 1) (p + 1)) (e : Fin (p + 1))
    (he : core.tail e ≠ core.head e) : Core n p where
  tail i := merge (core.head e) (core.tail e) he (core.tail (e.succAbove i))
  head i := merge (core.head e) (core.tail e) he (core.head (e.succAbove i))

variable (spec : Spec (n + 1) (p + 1)) (c : CoreBridgeCut.Data spec.core)

include spec c in
theorem one_le_of_valid : 0 < n := by
  by_contra hn
  obtain rfl : n = 0 := by omega
  have h1 := (spec.core.tail c.bridge).isLt
  have h2 := (spec.core.head c.bridge).isLt
  exact spec.core_loopless c.bridge (Fin.ext (by omega))

theorem contractCore_loopless (h : c.Valid) (i : Fin p) :
    (contractCore spec.core c.bridge (spec.core_loopless c.bridge)).tail i ≠
      (contractCore spec.core c.bridge (spec.core_loopless c.bridge)).head i := by
  intro hEq
  set w := spec.core.head c.bridge with hw
  set v := spec.core.tail c.bridge with hv
  have hvw : v ≠ w := spec.core_loopless c.bridge
  have hk : c.bridge.succAbove i ≠ c.bridge := Fin.succAbove_ne _ _
  have hSide := h.2.2 (c.bridge.succAbove i) hk
  have hLoop := spec.core_loopless (c.bridge.succAbove i)
  change merge w v hvw (spec.core.tail (c.bridge.succAbove i)) =
    merge w v hvw (spec.core.head (c.bridge.succAbove i)) at hEq
  by_cases hT : spec.core.tail (c.bridge.succAbove i) = w
  · by_cases hH : spec.core.head (c.bridge.succAbove i) = w
    · exact hLoop (hT.trans hH.symm)
    · rw [hT] at hEq
      have := eq_of_merge_eq_merge_self w v hvw hH hEq.symm
      rw [hT, this] at hSide
      exact h.2.1 (hSide.mpr h.1)
  · by_cases hH : spec.core.head (c.bridge.succAbove i) = w
    · rw [hH] at hEq
      have := eq_of_merge_eq_merge_self w v hvw hT hEq
      rw [hH, this] at hSide
      exact h.2.1 (hSide.mp h.1)
    · exact hLoop (merge_inj w v hvw hT hH hEq)

/-- **Contract a bridge slot.**  The head of the bridge is merged into its
tail, the slot is deleted, every other length is inherited. -/
def contractBridge (h : c.Valid) : Spec n p :=
  Spec.ofCore (contractCore spec.core c.bridge (spec.core_loopless c.bridge))
    (one_le_of_valid spec c) (contractCore_loopless spec c h)
    (fun i => spec.length (c.bridge.succAbove i))
    (fun i => spec.length_pos (c.bridge.succAbove i))

@[simp] theorem contractBridge_core (h : c.Valid) :
    (contractBridge spec c h).core =
      contractCore spec.core c.bridge (spec.core_loopless c.bridge) := rfl

@[simp] theorem contractBridge_length (h : c.Valid) (i : Fin p) :
    (contractBridge spec c h).length i = spec.length (c.bridge.succAbove i) := rfl

theorem contractBridge_core_loopless (h : c.Valid) :
    ∀ i : Fin p, (contractBridge spec c h).core.tail i ≠ (contractBridge spec c h).core.head i :=
  contractCore_loopless spec c h

/-- Contracting a bridge preserves connectivity of the core. -/
theorem contractBridge_connected (h : c.Valid) (hConn : spec.core.Connected) :
    (contractBridge spec c h).core.Connected := by
  intro S ⟨v₀, w₀, hv₀, hw₀⟩
  set w := spec.core.head c.bridge with hw
  set v := spec.core.tail c.bridge with hv
  have hvw : v ≠ w := spec.core_loopless c.bridge
  let S' : Finset (Fin (n + 1)) := Finset.univ.filter fun u => merge w v hvw u ∈ S
  have hmemS' : ∀ u, u ∈ S' ↔ merge w v hvw u ∈ S := by
    intro u; simp [S']
  obtain ⟨k, hk⟩ := hConn S' ⟨w.succAbove v₀, w.succAbove w₀,
    by rw [hmemS', merge_succAbove]; exact hv₀,
    by rw [hmemS', merge_succAbove]; exact hw₀⟩
  have hkne : k ≠ c.bridge := by
    intro hkb
    subst hkb
    rw [hmemS', hmemS', ← hv, ← hw, merge_self] at hk
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 h1
    · exact h2 h1
  obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hkne
  refine ⟨i, ?_⟩
  rw [hmemS', hmemS'] at hk
  change (merge w v hvw (spec.core.tail (c.bridge.succAbove i)) ∈ S ∧
      merge w v hvw (spec.core.head (c.bridge.succAbove i)) ∉ S) ∨
    (merge w v hvw (spec.core.head (c.bridge.succAbove i)) ∈ S ∧
      merge w v hvw (spec.core.tail (c.bridge.succAbove i)) ∉ S)
  rw [hi]
  exact hk

end Contraction

/-! ## 4.  The two sides of a bridge slot -/

noncomputable section Sides

variable {n p : ℕ} (spec : Spec n p) (c : CoreBridgeCut.Data spec.core)

/-- The tail side after subdivision (`CoreBridgeCut.Data.leftVertices`). -/
abbrev leftSet : Finset spec.Vertex := CoreBridgeCut.Data.leftVertices spec c

abbrev LeftV := {z : spec.Vertex // z ∈ leftSet spec c}

abbrev RightV := {z : spec.Vertex // z ∉ leftSet spec c}

/-- The first unit step of the bridge slot: the one unit edge across the cut. -/
def bridgeStep : spec.Step := ⟨c.bridge, ⟨0, spec.length_pos c.bridge⟩⟩

/-- A unit step with both ends on the tail side. -/
def BothLeft (t : spec.Step) : Prop :=
  spec.stepLeft t.1 t.2 ∈ leftSet spec c ∧ spec.stepRight t.1 t.2 ∈ leftSet spec c

/-- A unit step with both ends on the head side. -/
def BothRight (t : spec.Step) : Prop :=
  spec.stepLeft t.1 t.2 ∉ leftSet spec c ∧ spec.stepRight t.1 t.2 ∉ leftSet spec c

instance (t : spec.Step) : Decidable (BothLeft spec c t) := by unfold BothLeft; infer_instance
instance (t : spec.Step) : Decidable (BothRight spec c t) := by unfold BothRight; infer_instance

theorem stepLeft_bridgeStep :
    spec.stepLeft (bridgeStep spec c).1 (bridgeStep spec c).2 =
      spec.coreVertex (spec.core.tail c.bridge) := by
  simp [bridgeStep]

theorem stepRight_bridgeStep :
    spec.stepRight (bridgeStep spec c).1 (bridgeStep spec c).2 = spec.tailNeighbor c.bridge := rfl

theorem tailNeighbor_not_mem (h : c.Valid) : spec.tailNeighbor c.bridge ∉ leftSet spec c :=
  (c.mem_rightVertices_iff spec _).mp (c.tailNeighbor_mem_rightVertices spec h)

theorem not_bothLeft_bridgeStep (h : c.Valid) : ¬ BothLeft spec c (bridgeStep spec c) := by
  intro hb
  rw [BothLeft, stepRight_bridgeStep] at hb
  exact tailNeighbor_not_mem spec c h hb.2

theorem not_bothRight_bridgeStep (h : c.Valid) : ¬ BothRight spec c (bridgeStep spec c) := by
  intro hb
  rw [BothRight, stepLeft_bridgeStep] at hb
  exact hb.1 (c.tail_mem_leftVertices spec h)

theorem not_bothLeft_and_bothRight (t : spec.Step) :
    ¬ (BothLeft spec c t ∧ BothRight spec c t) :=
  fun hb => hb.2.1 hb.1.1

/-- Every unit step is on the tail side, on the head side, or is the bridge
step. -/
theorem step_trichotomy (h : c.Valid) (t : spec.Step) :
    BothLeft spec c t ∨ BothRight spec c t ∨ t = bridgeStep spec c := by
  by_cases hL : spec.stepLeft t.1 t.2 ∈ leftSet spec c <;>
    by_cases hR : spec.stepRight t.1 t.2 ∈ leftSet spec c
  · exact Or.inl ⟨hL, hR⟩
  · right; right
    obtain ⟨hEdge, hZero⟩ := c.step_eq_bridge_zero_of_left_right spec h t.1 t.2 hL
      ((c.mem_rightVertices_iff spec _).mpr hR)
    rcases t with ⟨edge, offset⟩
    change edge = c.bridge at hEdge
    change offset.val = 0 at hZero
    subst hEdge
    have hoff : offset = ⟨0, spec.length_pos c.bridge⟩ := Fin.ext hZero
    rw [hoff]
    rfl
  · exact (c.not_step_right_left spec h t.1 t.2
      ⟨(c.mem_rightVertices_iff spec _).mpr hL, hR⟩).elim
  · exact Or.inr (Or.inl ⟨hL, hR⟩)

theorem bothLeft_or_bothRight_iff (h : c.Valid) (t : spec.Step) :
    (BothLeft spec c t ∨ BothRight spec c t) ↔ t ≠ bridgeStep spec c := by
  constructor
  · rintro (hb | hb) rfl
    · exact not_bothLeft_bridgeStep spec c h hb
    · exact not_bothRight_bridgeStep spec c h hb
  · intro hne
    rcases step_trichotomy spec c h t with hb | hb | hb
    · exact Or.inl hb
    · exact Or.inr hb
    · exact (hne hb).elim

/-- The tail-side factor: the unit steps with both ends on the tail side.
Reducible, so that its vertex type is `LeftV` at every transparency. -/
abbrev leftGraph (h : c.Valid) : CFGraph where
  V := LeftV spec c
  instNonempty := ⟨⟨spec.coreVertex (spec.core.tail c.bridge), c.tail_mem_leftVertices spec h⟩⟩
  edges := ((Finset.univ : Finset spec.Step).val.filter (BothLeft spec c)).pmap
    (fun t ht => ((⟨spec.stepLeft t.1 t.2, ht.1⟩ : LeftV spec c),
      (⟨spec.stepRight t.1 t.2, ht.2⟩ : LeftV spec c)))
    (fun t ht => (Multiset.mem_filter.mp ht).2)
  loopless := by
    intro z hz
    rw [Multiset.mem_pmap] at hz
    obtain ⟨t, _, hEq⟩ := hz
    apply spec.stepLeft_ne_stepRight t.1 t.2
    have h1 := congrArg (fun q => q.1.val) hEq
    have h2 := congrArg (fun q => q.2.val) hEq
    exact h1.trans h2.symm

/-- The head-side factor: the unit steps with both ends on the head side. -/
abbrev rightGraph (h : c.Valid) : CFGraph where
  V := RightV spec c
  instNonempty := ⟨⟨spec.tailNeighbor c.bridge, tailNeighbor_not_mem spec c h⟩⟩
  edges := ((Finset.univ : Finset spec.Step).val.filter (BothRight spec c)).pmap
    (fun t ht => ((⟨spec.stepLeft t.1 t.2, ht.1⟩ : RightV spec c),
      (⟨spec.stepRight t.1 t.2, ht.2⟩ : RightV spec c)))
    (fun t ht => (Multiset.mem_filter.mp ht).2)
  loopless := by
    intro z hz
    rw [Multiset.mem_pmap] at hz
    obtain ⟨t, _, hEq⟩ := hz
    apply spec.stepLeft_ne_stepRight t.1 t.2
    have h1 := congrArg (fun q => q.1.val) hEq
    have h2 := congrArg (fun q => q.2.val) hEq
    exact h1.trans h2.symm

/-- The tail of the bridge, on the tail side. -/
def leftGlue (h : c.Valid) : (leftGraph spec c h).V :=
  ⟨spec.coreVertex (spec.core.tail c.bridge), c.tail_mem_leftVertices spec h⟩

/-- The first-step neighbour of the tail, on the head side. -/
def rightGlue (h : c.Valid) : (rightGraph spec c h).V :=
  ⟨spec.tailNeighbor c.bridge, tailNeighbor_not_mem spec c h⟩

/-- Which side a vertex is on. -/
def side (h : c.Valid) (z : spec.Vertex) : (leftGraph spec c h).V ⊕ (rightGraph spec c h).V :=
  if hz : z ∈ leftSet spec c then Sum.inl ⟨z, hz⟩ else Sum.inr ⟨z, hz⟩

theorem side_of_mem (h : c.Valid) {z : spec.Vertex} (hz : z ∈ leftSet spec c) :
    side spec c h z = Sum.inl ⟨z, hz⟩ := by
  simp [side, hz]

theorem side_of_not_mem (h : c.Valid) {z : spec.Vertex} (hz : z ∉ leftSet spec c) :
    side spec c h z = Sum.inr ⟨z, hz⟩ := by
  simp [side, hz]

theorem side_injective (h : c.Valid) : Function.Injective (side spec c h) := by
  intro a b hab
  by_cases ha : a ∈ leftSet spec c <;> by_cases hb : b ∈ leftSet spec c
  · rw [side_of_mem spec c h ha, side_of_mem spec c h hb] at hab
    exact congrArg Subtype.val (Sum.inl.inj hab)
  · rw [side_of_mem spec c h ha, side_of_not_mem spec c h hb] at hab
    exact (Sum.inl_ne_inr hab).elim
  · rw [side_of_not_mem spec c h ha, side_of_mem spec c h hb] at hab
    exact (Sum.inr_ne_inl hab).elim
  · rw [side_of_not_mem spec c h ha, side_of_not_mem spec c h hb] at hab
    exact congrArg Subtype.val (Sum.inr.inj hab)

theorem side_surjective (h : c.Valid) : Function.Surjective (side spec c h) := by
  rintro (⟨z, hz⟩ | ⟨z, hz⟩)
  · exact ⟨z, side_of_mem spec c h hz⟩
  · exact ⟨z, side_of_not_mem spec c h hz⟩

/-- The vertex bijection of the bridge decomposition. -/
noncomputable def sideEquiv (h : c.Valid) : spec.Vertex ≃ ((leftGraph spec c h).V ⊕ (rightGraph spec c h).V) :=
  Equiv.ofBijective _ ⟨side_injective spec c h, side_surjective spec c h⟩

@[simp] theorem sideEquiv_apply (h : c.Valid) (z : spec.Vertex) : sideEquiv spec c h z = side spec c h z := rfl

/-- The unit steps other than the bridge step, as the sum of the two sides. -/
theorem filter_bothLeft_add_filter_bothRight (h : c.Valid) :
    (Finset.univ : Finset spec.Step).val.filter (BothLeft spec c) +
        (Finset.univ : Finset spec.Step).val.filter (BothRight spec c) =
      (Finset.univ : Finset spec.Step).val.filter (· ≠ bridgeStep spec c) := by
  rw [Multiset.filter_add_filter]
  have hAnd : (Finset.univ : Finset spec.Step).val.filter
      (fun t => BothLeft spec c t ∧ BothRight spec c t) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro t _ ht
    exact not_bothLeft_and_bothRight spec c t ht
  rw [hAnd, add_zero]
  apply Multiset.filter_congr
  intro t _
  exact bothLeft_or_bothRight_iff spec c h t

/-- All unit steps: the bridge step and the rest. -/
theorem univ_val_eq_cons :
    (Finset.univ : Finset spec.Step).val =
      bridgeStep spec c ::ₘ
        (Finset.univ : Finset spec.Step).val.filter (· ≠ bridgeStep spec c) := by
  have h1 := Multiset.filter_add_not (· = bridgeStep spec c) (Finset.univ : Finset spec.Step).val
  rw [Multiset.filter_eq', Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _),
    Multiset.replicate_one, Multiset.singleton_add] at h1
  exact h1.symm

/-- The edges of the tail-side factor, pushed forward by any function that
factors through the ambient vertex set. -/
theorem leftGraph_edges_map (h : c.Valid) {α : Type} (F : (leftGraph spec c h).V → α) (G : spec.Vertex → α)
    (hFG : ∀ z (hz : z ∈ leftSet spec c), F ⟨z, hz⟩ = G z) :
    (leftGraph spec c h).edges.map (fun e => (F e.1, F e.2)) =
      ((Finset.univ : Finset spec.Step).val.filter (BothLeft spec c)).map
        (fun t => (G (spec.stepLeft t.1 t.2), G (spec.stepRight t.1 t.2))) := by
  refine (Multiset.map_pmap (fun e : (leftGraph spec c h).V × (leftGraph spec c h).V =>
    (F e.1, F e.2)) _ _ _).trans ?_
  refine (Multiset.pmap_congr _ ?_).trans
    (Multiset.pmap_eq_map (BothLeft spec c) _ _ (fun t ht => (Multiset.mem_filter.mp ht).2))
  intro t _ h₁ _
  simp only [hFG]

/-- The edges of the head-side factor, pushed forward by any function that
factors through the ambient vertex set. -/
theorem rightGraph_edges_map (h : c.Valid) {α : Type} (F : (rightGraph spec c h).V → α) (G : spec.Vertex → α)
    (hFG : ∀ z (hz : z ∉ leftSet spec c), F ⟨z, hz⟩ = G z) :
    (rightGraph spec c h).edges.map (fun e => (F e.1, F e.2)) =
      ((Finset.univ : Finset spec.Step).val.filter (BothRight spec c)).map
        (fun t => (G (spec.stepLeft t.1 t.2), G (spec.stepRight t.1 t.2))) := by
  refine (Multiset.map_pmap (fun e : (rightGraph spec c h).V × (rightGraph spec c h).V =>
    (F e.1, F e.2)) _ _ _).trans ?_
  refine (Multiset.pmap_congr _ ?_).trans
    (Multiset.pmap_eq_map (BothRight spec c) _ _ (fun t ht => (Multiset.mem_filter.mp ht).2))
  intro t _ h₁ _
  simp only [hFG]

/-! ## 5.  A subdivision graph presented by its unit steps -/

/-- **Transport principle.**  If the edge multiset of `X` is literally the
image of the unit steps of `spec₂` under a vertex bijection, then that
bijection preserves every edge multiplicity. -/
def laplacianEquivOfEdges {n₂ p₂ : ℕ} (spec₂ : Spec n₂ p₂) (X : CFGraph)
    (φ : spec₂.Vertex ≃ X.V)
    (hX : X.edges = (Finset.univ : Finset spec₂.Step).val.map
      (fun s => (φ (spec₂.stepLeft s.1 s.2), φ (spec₂.stepRight s.1 s.2)))) :
    LaplacianEquiv spec₂.graph X where
  toEquiv := φ
  num_edges_eq := by
    intro a b
    rw [spec₂.num_edges_eq_card_filter_steps, Finset.card_def, Finset.filter_val]
    unfold num_edges
    rw [hX, Multiset.filter_map, Multiset.card_map]
    congr 1
    apply Multiset.filter_congr
    intro s _
    simp only [Function.comp_apply, Spec.unitEdge, Prod.mk.injEq, φ.injective.eq_iff]

/-- The bridge graph of the two sides, presented by the unit steps of `spec`. -/
theorem bridgeGraph_edges_eq (h : c.Valid) :
    (bridgeGraph (leftGraph spec c h) (rightGraph spec c h) (leftGlue spec c h)
        (rightGlue spec c h)).edges =
      (Finset.univ : Finset spec.Step).val.map
        (fun t => (side spec c h (spec.stepLeft t.1 t.2), side spec c h (spec.stepRight t.1 t.2))) := by
  rw [bridgeGraph_edges,
    leftGraph_edges_map spec c h Sum.inl (side spec c h) (fun z hz => (side_of_mem spec c h hz).symm),
    rightGraph_edges_map spec c h Sum.inr (side spec c h)
      (fun z hz => (side_of_not_mem spec c h hz).symm),
    ← Multiset.map_add, filter_bothLeft_add_filter_bothRight spec c h]
  conv_rhs => rw [univ_val_eq_cons spec c, Multiset.map_cons]
  congr 1
  rw [stepLeft_bridgeStep, stepRight_bridgeStep,
    side_of_mem spec c h (c.tail_mem_leftVertices spec h),
    side_of_not_mem spec c h (tailNeighbor_not_mem spec c h)]
  rfl

/-- **The first half of the decomposition.**  A subdivision specification is
Laplacian-equivalent to the bridge graph of the two sides of any bridge slot. -/
noncomputable def bridgeEquiv (h : c.Valid) :
    LaplacianEquiv spec.graph
      (bridgeGraph (leftGraph spec c h) (rightGraph spec c h) (leftGlue spec c h)
        (rightGlue spec c h)) :=
  laplacianEquivOfEdges spec _ (sideEquiv spec c h) (bridgeGraph_edges_eq spec c h)

/-! ## 6.  The wedge of the two sides -/

/-- The wedge: the bridge graph with its bridge contracted. -/
abbrev wedge (h : c.Valid) : CFGraph :=
  vertexWedge (leftGraph spec c h) (rightGraph spec c h) (leftGlue spec c h) (rightGlue spec c h)

/-- The contraction map from the ambient vertices to the wedge. -/
def toWedge (h : c.Valid) (z : spec.Vertex) : (wedge spec c h).V :=
  contractBridgeVertex (leftGraph spec c h) (rightGraph spec c h) (leftGlue spec c h)
    (rightGlue spec c h) (side spec c h z)

theorem toWedge_of_mem (h : c.Valid) {z : spec.Vertex} (hz : z ∈ leftSet spec c) :
    toWedge spec c h z = Sum.inl ⟨z, hz⟩ := by
  rw [toWedge, side_of_mem spec c h hz]
  rfl

theorem toWedge_of_not_mem (h : c.Valid) {z : spec.Vertex} (hz : z ∉ leftSet spec c) :
    toWedge spec c h z =
      wedgeRightVertex (leftGraph spec c h) (rightGraph spec c h) (leftGlue spec c h)
        (rightGlue spec c h) ⟨z, hz⟩ := by
  rw [toWedge, side_of_not_mem spec c h hz]
  rfl

theorem toWedge_tailNeighbor (h : c.Valid) :
    toWedge spec c h (spec.tailNeighbor c.bridge) = Sum.inl (leftGlue spec c h) := by
  rw [toWedge_of_not_mem spec c h (tailNeighbor_not_mem spec c h)]
  exact wedgeRightVertex_marked _ _ _ _

theorem toWedge_of_not_mem_of_ne (h : c.Valid) {z : spec.Vertex} (hz : z ∉ leftSet spec c)
    (hne : z ≠ spec.tailNeighbor c.bridge) :
    toWedge spec c h z =
      Sum.inr ⟨⟨z, hz⟩, fun hEq => hne (congrArg Subtype.val hEq)⟩ := by
  rw [toWedge_of_not_mem spec c h hz]
  exact wedgeRightVertex_unmarked _ _ _ _ _ _

/-- The contraction map is injective away from the contracted unit edge. -/
theorem toWedge_inj (h : c.Valid) {a b : spec.Vertex} (ha : a ≠ spec.tailNeighbor c.bridge)
    (hb : b ≠ spec.tailNeighbor c.bridge) (hab : toWedge spec c h a = toWedge spec c h b) :
    a = b := by
  by_cases haL : a ∈ leftSet spec c <;> by_cases hbL : b ∈ leftSet spec c
  · rw [toWedge_of_mem spec c h haL, toWedge_of_mem spec c h hbL] at hab
    exact congrArg Subtype.val (Sum.inl.inj hab)
  · rw [toWedge_of_mem spec c h haL, toWedge_of_not_mem_of_ne spec c h hbL hb] at hab
    exact (Sum.inl_ne_inr hab).elim
  · rw [toWedge_of_not_mem_of_ne spec c h haL ha, toWedge_of_mem spec c h hbL] at hab
    exact (Sum.inr_ne_inl hab).elim
  · rw [toWedge_of_not_mem_of_ne spec c h haL ha, toWedge_of_not_mem_of_ne spec c h hbL hb] at hab
    exact congrArg (fun q => q.val.val) (Sum.inr.inj hab)

/-- The wedge, presented by the unit steps of `spec` other than the bridge
step. -/
theorem wedge_edges_eq (h : c.Valid) :
    (wedge spec c h).edges =
      ((Finset.univ : Finset spec.Step).val.filter (· ≠ bridgeStep spec c)).map
        (fun t => (toWedge spec c h (spec.stepLeft t.1 t.2),
          toWedge spec c h (spec.stepRight t.1 t.2))) := by
  have hl := leftGraph_edges_map spec c h
    (Sum.inl : (leftGraph spec c h).V → (wedge spec c h).V) (toWedge spec c h)
    (fun z hz => (toWedge_of_mem spec c h hz).symm)
  have hr := rightGraph_edges_map spec c h
    (wedgeRightVertex (leftGraph spec c h) (rightGraph spec c h) (leftGlue spec c h)
      (rightGlue spec c h) : (rightGraph spec c h).V → (wedge spec c h).V) (toWedge spec c h)
    (fun z hz => (toWedge_of_not_mem spec c h hz).symm)
  refine (vertexWedge_edges _ _ _ _).trans ?_
  refine (congrArg₂ (· + ·) hl hr).trans ?_
  refine (Multiset.map_add _ _ _).symm.trans ?_
  rw [filter_bothLeft_add_filter_bothRight spec c h]
  exact rfl

/-- **The generic second half of the decomposition.**  A specification whose
vertices are in bijection with the wedge, and whose unit steps are in
bijection with the unit steps of `spec` other than the bridge step,
compatibly with the contraction map, is Laplacian-equivalent to the wedge. -/
noncomputable def laplacianEquivWedgeOfSteps (h : c.Valid) {n₂ p₂ : ℕ} (spec₂ : Spec n₂ p₂)
    (φ : spec₂.Vertex ≃ (wedge spec c h).V) (ψ : spec₂.Step → spec.Step)
    (hinj : Function.Injective ψ) (hne : ∀ s, ψ s ≠ bridgeStep spec c)
    (hsurj : ∀ t, t ≠ bridgeStep spec c → ∃ s, ψ s = t)
    (hL : ∀ s, φ (spec₂.stepLeft s.1 s.2) = toWedge spec c h (spec.stepLeft (ψ s).1 (ψ s).2))
    (hR : ∀ s, φ (spec₂.stepRight s.1 s.2) = toWedge spec c h (spec.stepRight (ψ s).1 (ψ s).2)) :
    LaplacianEquiv spec₂.graph (wedge spec c h) := by
  refine laplacianEquivOfEdges spec₂ _ φ ?_
  rw [wedge_edges_eq spec c h]
  have hFilter : (Finset.univ : Finset spec.Step).filter (· ≠ bridgeStep spec c) =
      (Finset.univ : Finset spec₂.Step).map ⟨ψ, hinj⟩ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro ht
      obtain ⟨s, hs⟩ := hsurj t ht
      exact ⟨s, hs⟩
    · rintro ⟨s, rfl⟩
      exact hne s
  have hVal := congrArg Finset.val hFilter
  rw [Finset.filter_val, Finset.map_val] at hVal
  rw [hVal, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro s _
  simp only [Function.comp_apply, Function.Embedding.coeFn_mk, hL, hR]

end Sides


/-! ## 7.  Unit steps, in raw constructor form -/

section StepLemmas

variable {n p : ℕ} (spec : Spec n p)

theorem stepLeft_of_zero (e : Fin p) (j : Fin (spec.length e)) (hj : j.val = 0) :
    spec.stepLeft e j = Sum.inl (spec.core.tail e) := by
  unfold Spec.stepLeft
  rw [dif_pos hj]
  rfl

theorem stepLeft_of_ne_zero (e : Fin p) (j : Fin (spec.length e)) (hj : j.val ≠ 0) :
    spec.stepLeft e j = Sum.inr ⟨e, ⟨j.val - 1, by have := j.isLt; omega⟩⟩ := by
  unfold Spec.stepLeft
  rw [dif_neg hj]
  rfl

theorem stepRight_of_last (e : Fin p) (j : Fin (spec.length e)) (hj : j.val + 1 = spec.length e) :
    spec.stepRight e j = Sum.inl (spec.core.head e) := by
  unfold Spec.stepRight
  rw [dif_pos hj]
  rfl

theorem stepRight_of_ne_last (e : Fin p) (j : Fin (spec.length e))
    (hj : j.val + 1 ≠ spec.length e) :
    spec.stepRight e j = Sum.inr ⟨e, ⟨j.val, by have := j.isLt; omega⟩⟩ := by
  unfold Spec.stepRight
  rw [dif_neg hj]
  rfl

end StepLemmas

/-! ## 8.  Contracting a bridge slot of length one -/

noncomputable section ContractOne

variable {n p : ℕ} (spec : Spec (n + 1) (p + 1)) (c : CoreBridgeCut.Data spec.core) (h : c.Valid)

theorem tailNeighbor_of_length_one (hlen : spec.length c.bridge = 1) :
    spec.tailNeighbor c.bridge = Sum.inl (spec.core.head c.bridge) :=
  stepRight_of_last spec c.bridge _ (by simp [hlen])

/-- Lift a vertex of the contracted specification to the original one: a
core vertex to the vertex it labels (never the deleted head), an interior
vertex to the same interior vertex of the same slot. -/
def liftVertex : (contractBridge spec c h).Vertex → spec.Vertex
  | Sum.inl i => Sum.inl ((spec.core.head c.bridge).succAbove i)
  | Sum.inr ⟨i, j⟩ => Sum.inr ⟨c.bridge.succAbove i, j⟩

theorem liftVertex_inl (i : Fin n) :
    liftVertex spec c h (Sum.inl i) = Sum.inl ((spec.core.head c.bridge).succAbove i) := rfl

theorem liftVertex_ne_tailNeighbor (hlen : spec.length c.bridge = 1)
    (z : (contractBridge spec c h).Vertex) :
    liftVertex spec c h z ≠ spec.tailNeighbor c.bridge := by
  rw [tailNeighbor_of_length_one spec c hlen]
  rcases z with i | ⟨i, j⟩
  · intro hEq
    exact Fin.succAbove_ne _ i (Sum.inl.inj hEq)
  · exact Sum.inr_ne_inl

theorem liftVertex_injective : Function.Injective (liftVertex spec c h) := by
  rintro (i | ⟨i, j⟩) (i' | ⟨i', j'⟩) hEq
  · rw [Fin.succAbove_right_injective (Sum.inl.inj hEq)]
  · exact (Sum.inl_ne_inr hEq).elim
  · exact (Sum.inr_ne_inl hEq).elim
  · have hSigma := Sum.inr.inj hEq
    have hi : i = i' := Fin.succAbove_right_injective (congrArg Sigma.fst hSigma)
    subst hi
    have hj : j = j' := eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
    rw [hj]

/-- The vertex map of the length-one contraction into the wedge. -/
def contractVertex (z : (contractBridge spec c h).Vertex) : (wedge spec c h).V :=
  toWedge spec c h (liftVertex spec c h z)

theorem contractVertex_injective (hlen : spec.length c.bridge = 1) :
    Function.Injective (contractVertex spec c h) := by
  intro a b hab
  exact liftVertex_injective spec c h
    (toWedge_inj spec c h (liftVertex_ne_tailNeighbor spec c h hlen a)
      (liftVertex_ne_tailNeighbor spec c h hlen b) hab)

theorem contractVertex_surjective (hlen : spec.length c.bridge = 1) :
    Function.Surjective (contractVertex spec c h) := by
  rintro (⟨z, hz⟩ | ⟨⟨z, hz⟩, hne⟩)
  · rcases z with u | ⟨k, j⟩
    · have hu : u ∈ c.left := (c.mem_leftVertices_core spec u).mp hz
      have huw : u ≠ spec.core.head c.bridge := fun hEq => h.2.1 (hEq ▸ hu)
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq huw
      subst hi
      exact ⟨Sum.inl i, toWedge_of_mem spec c h hz⟩
    · have hk : k ≠ c.bridge := by
        intro hEq
        subst hEq
        exact h.2.1 ((c.mem_leftVertices_interior spec _ j).mp hz).2
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hk
      subst hi
      exact ⟨Sum.inr ⟨i, j⟩, toWedge_of_mem spec c h hz⟩
  · have hne' : z ≠ spec.tailNeighbor c.bridge := fun hEq => hne (Subtype.ext hEq)
    have hneCore : z ≠ Sum.inl (spec.core.head c.bridge) := by
      rw [← tailNeighbor_of_length_one spec c hlen]; exact hne'
    rcases z with u | ⟨k, j⟩
    · have huw : u ≠ spec.core.head c.bridge := fun hEq => hneCore (congrArg Sum.inl hEq)
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq huw
      subst hi
      exact ⟨Sum.inl i, toWedge_of_not_mem_of_ne spec c h hz hne'⟩
    · have hk : k ≠ c.bridge := by
        intro hEq
        subst hEq
        have := j.isLt
        omega
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hk
      subst hi
      exact ⟨Sum.inr ⟨i, j⟩, toWedge_of_not_mem_of_ne spec c h hz hne'⟩

/-- The vertex bijection of the length-one contraction. -/
def contractVertexEquiv (hlen : spec.length c.bridge = 1) :
    (contractBridge spec c h).Vertex ≃ (wedge spec c h).V :=
  Equiv.ofBijective _ ⟨contractVertex_injective spec c h hlen,
    contractVertex_surjective spec c h hlen⟩

/-- A unit step of the contracted specification is a unit step of an
uncontracted slot. -/
def contractStep : (contractBridge spec c h).Step → spec.Step
  | ⟨i, j⟩ => ⟨c.bridge.succAbove i, j⟩

theorem contractStep_injective : Function.Injective (contractStep spec c h) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hEq
  have hi : i = i' := Fin.succAbove_right_injective (congrArg Sigma.fst hEq)
  subst hi
  have hj : j = j' := eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
  rw [hj]

theorem contractStep_ne (s : (contractBridge spec c h).Step) :
    contractStep spec c h s ≠ bridgeStep spec c := by
  obtain ⟨i, j⟩ := s
  intro hEq
  exact Fin.succAbove_ne c.bridge i (congrArg Sigma.fst hEq)

theorem contractStep_surjective (hlen : spec.length c.bridge = 1) (t : spec.Step)
    (ht : t ≠ bridgeStep spec c) : ∃ s, contractStep spec c h s = t := by
  obtain ⟨k, j⟩ := t
  by_cases hk : k = c.bridge
  · subst hk
    exfalso
    apply ht
    have hj : j = ⟨0, spec.length_pos c.bridge⟩ := Fin.ext (by have := j.isLt; omega)
    rw [hj]
    rfl
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hk
    subst hi
    exact ⟨⟨i, j⟩, rfl⟩

/-- Merging the head into the tail is invisible on the wedge. -/
theorem toWedge_succAbove_merge (hlen : spec.length c.bridge = 1) (u : Fin (n + 1)) :
    toWedge spec c h (Sum.inl ((spec.core.head c.bridge).succAbove
      (merge (spec.core.head c.bridge) (spec.core.tail c.bridge) (spec.core_loopless c.bridge) u))) =
      toWedge spec c h (Sum.inl u) := by
  by_cases hu : u = spec.core.head c.bridge
  · subst hu
    rw [merge_self, succAbove_merge _ _ _ (spec.core_loopless c.bridge),
      ← tailNeighbor_of_length_one spec c hlen, toWedge_tailNeighbor]
    exact toWedge_of_mem spec c h (c.tail_mem_leftVertices spec h)
  · rw [succAbove_merge _ _ _ hu]

theorem contract_stepLeft (hlen : spec.length c.bridge = 1)
    (s : (contractBridge spec c h).Step) :
    contractVertex spec c h ((contractBridge spec c h).stepLeft s.1 s.2) =
      toWedge spec c h (spec.stepLeft (contractStep spec c h s).1 (contractStep spec c h s).2) := by
  obtain ⟨i, j⟩ := s
  show contractVertex spec c h ((contractBridge spec c h).stepLeft i j) =
    toWedge spec c h (spec.stepLeft (c.bridge.succAbove i) j)
  by_cases hj : j.val = 0
  · rw [stepLeft_of_zero _ _ _ hj, stepLeft_of_zero spec _ _ hj]
    exact toWedge_succAbove_merge spec c h hlen _
  · rw [stepLeft_of_ne_zero _ _ _ hj, stepLeft_of_ne_zero spec _ _ hj]
    rfl

theorem contract_stepRight (hlen : spec.length c.bridge = 1)
    (s : (contractBridge spec c h).Step) :
    contractVertex spec c h ((contractBridge spec c h).stepRight s.1 s.2) =
      toWedge spec c h (spec.stepRight (contractStep spec c h s).1 (contractStep spec c h s).2) := by
  obtain ⟨i, j⟩ := s
  show contractVertex spec c h ((contractBridge spec c h).stepRight i j) =
    toWedge spec c h (spec.stepRight (c.bridge.succAbove i) j)
  by_cases hj : j.val + 1 = spec.length (c.bridge.succAbove i)
  · rw [stepRight_of_last _ _ _ hj, stepRight_of_last spec _ _ hj]
    exact toWedge_succAbove_merge spec c h hlen _
  · rw [stepRight_of_ne_last _ _ _ hj, stepRight_of_ne_last spec _ _ hj]
    rfl

/-- **The second half of the decomposition, at length one.**  Contracting a
bridge slot of length one is Laplacian-equivalent to the wedge of the two
sides. -/
def contractEquiv (hlen : spec.length c.bridge = 1) :
    LaplacianEquiv (contractBridge spec c h).graph (wedge spec c h) :=
  laplacianEquivWedgeOfSteps spec c h (contractBridge spec c h)
    (contractVertexEquiv spec c h hlen) (contractStep spec c h)
    (contractStep_injective spec c h) (contractStep_ne spec c h)
    (contractStep_surjective spec c h hlen)
    (contract_stepLeft spec c h hlen) (contract_stepRight spec c h hlen)

/-- Transport across a bridge slot of length one. -/
theorem bnExists_contractBridge_iff_of_length_one (hlen : spec.length c.bridge = 1) (r d : ℤ) :
    BNExists (contractBridge spec c h).graph r d ↔ BNExists spec.graph r d :=
  ((contractEquiv spec c h hlen).bnExists_iff r d).trans
    ((BNExists_bridge_iff_vertexWedge _ _ _ _ r d).symm.trans
      ((bridgeEquiv spec c h).bnExists_iff r d).symm)

end ContractOne

/-! ## 9.  Shortening a bridge slot of length at least two -/

section ShortenDef

variable {n p : ℕ} (spec : Spec n p)

/-- The same specification with the slot `e` one unit shorter. -/
def shorten (e : Fin p) (h2 : 2 ≤ spec.length e) : Spec n p :=
  Spec.ofCore spec.core spec.core_nonempty spec.core_loopless
    (fun k => if k = e then spec.length e - 1 else spec.length k)
    (fun k => by
      by_cases hk : k = e
      · simp only [hk, if_true]; omega
      · simp only [hk, if_false]; exact spec.length_pos k)

@[simp] theorem shorten_core (e : Fin p) (h2 : 2 ≤ spec.length e) :
    (shorten spec e h2).core = spec.core := rfl

theorem shorten_length_self (e : Fin p) (h2 : 2 ≤ spec.length e) :
    (shorten spec e h2).length e = spec.length e - 1 := by
  show (if e = e then spec.length e - 1 else spec.length e) = _
  simp

theorem shorten_length_of_ne (e : Fin p) (h2 : 2 ≤ spec.length e) {k : Fin p} (hk : k ≠ e) :
    (shorten spec e h2).length k = spec.length k := by
  show (if k = e then spec.length e - 1 else spec.length k) = _
  simp [hk]

end ShortenDef

noncomputable section Shorten

variable {n p : ℕ} (spec : Spec n p) (c : CoreBridgeCut.Data spec.core) (h : c.Valid)
  (h2 : 2 ≤ spec.length c.bridge)

theorem tailNeighbor_of_two_le :
    spec.tailNeighbor c.bridge = Sum.inr ⟨c.bridge, ⟨0, by omega⟩⟩ :=
  stepRight_of_ne_last spec c.bridge _ (by simp; omega)

/-- Lift a vertex of the shortened specification to the original one: the
interior of the bridge slot is shifted one unit towards the head, so that the
first interior vertex is never hit. -/
def shortenLift : (shorten spec c.bridge h2).Vertex → spec.Vertex
  | Sum.inl u => Sum.inl u
  | Sum.inr ⟨k, j⟩ =>
      if hk : k = c.bridge then
        Sum.inr ⟨c.bridge, ⟨j.val + 1, by
          have := j.isLt; have hl : (shorten spec c.bridge h2).length k = spec.length c.bridge - 1 := by rw [hk, shorten_length_self]
          omega⟩⟩
      else
        Sum.inr ⟨k, ⟨j.val, by
          have := j.isLt; have hl := shorten_length_of_ne spec c.bridge h2 hk; omega⟩⟩

theorem shortenLift_inl (u : Fin n) : shortenLift spec c h2 (Sum.inl u) = Sum.inl u := rfl

theorem shortenLift_inr_self (j : Fin ((shorten spec c.bridge h2).length c.bridge - 1)) :
    shortenLift spec c h2 (Sum.inr ⟨c.bridge, j⟩) =
      Sum.inr ⟨c.bridge, ⟨j.val + 1, by
        have := j.isLt; have hl := shorten_length_self spec c.bridge h2; omega⟩⟩ := by
  simp [shortenLift]

theorem shortenLift_inr_of_ne {k : Fin p} (hk : k ≠ c.bridge)
    (j : Fin ((shorten spec c.bridge h2).length k - 1)) :
    shortenLift spec c h2 (Sum.inr ⟨k, j⟩) =
      Sum.inr ⟨k, ⟨j.val, by
        have := j.isLt; have hl := shorten_length_of_ne spec c.bridge h2 hk; omega⟩⟩ := by
  simp [shortenLift, hk]

theorem shortenLift_ne_tailNeighbor (z : (shorten spec c.bridge h2).Vertex) :
    shortenLift spec c h2 z ≠ spec.tailNeighbor c.bridge := by
  rw [tailNeighbor_of_two_le spec c h2]
  rcases z with u | ⟨k, j⟩
  · exact Sum.inl_ne_inr
  · by_cases hk : k = c.bridge
    · subst hk
      rw [shortenLift_inr_self]
      intro hEq
      have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hEq)).2)
      simp at this
    · rw [shortenLift_inr_of_ne spec c h2 hk]
      intro hEq
      exact hk (congrArg Sigma.fst (Sum.inr.inj hEq))

theorem shortenLift_injective : Function.Injective (shortenLift spec c h2) := by
  rintro (u | ⟨k, j⟩) (u' | ⟨k', j'⟩) hEq
  · rw [shortenLift_inl, shortenLift_inl] at hEq
    rw [Sum.inl.inj hEq]
  · rw [shortenLift_inl] at hEq
    by_cases hk' : k' = c.bridge
    · subst hk'
      rw [shortenLift_inr_self] at hEq
      exact (Sum.inl_ne_inr hEq).elim
    · rw [shortenLift_inr_of_ne spec c h2 hk'] at hEq
      exact (Sum.inl_ne_inr hEq).elim
  · rw [shortenLift_inl] at hEq
    by_cases hk : k = c.bridge
    · subst hk
      rw [shortenLift_inr_self] at hEq
      exact (Sum.inr_ne_inl hEq).elim
    · rw [shortenLift_inr_of_ne spec c h2 hk] at hEq
      exact (Sum.inr_ne_inl hEq).elim
  · by_cases hk : k = c.bridge <;> by_cases hk' : k' = c.bridge
    · subst hk; subst hk'
      rw [shortenLift_inr_self, shortenLift_inr_self] at hEq
      have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hEq)).2)
      have hj : j = j' := Fin.ext (by simpa using this)
      rw [hj]
    · subst hk
      rw [shortenLift_inr_self, shortenLift_inr_of_ne spec c h2 hk'] at hEq
      exact (hk' (congrArg Sigma.fst (Sum.inr.inj hEq)).symm).elim
    · subst hk'
      rw [shortenLift_inr_of_ne spec c h2 hk, shortenLift_inr_self] at hEq
      exact (hk (congrArg Sigma.fst (Sum.inr.inj hEq))).elim
    · rw [shortenLift_inr_of_ne spec c h2 hk, shortenLift_inr_of_ne spec c h2 hk'] at hEq
      have hkk : k = k' := congrArg Sigma.fst (Sum.inr.inj hEq)
      subst hkk
      have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hEq)).2)
      have hj : j = j' := Fin.ext this
      rw [hj]

/-- The vertex map of the shortening into the wedge. -/
def shortenVertex (z : (shorten spec c.bridge h2).Vertex) : (wedge spec c h).V :=
  toWedge spec c h (shortenLift spec c h2 z)

theorem shortenVertex_injective : Function.Injective (shortenVertex spec c h h2) := by
  intro a b hab
  exact shortenLift_injective spec c h2
    (toWedge_inj spec c h (shortenLift_ne_tailNeighbor spec c h2 a)
      (shortenLift_ne_tailNeighbor spec c h2 b) hab)

theorem shortenVertex_surjective : Function.Surjective (shortenVertex spec c h h2) := by
  rintro (⟨z, hz⟩ | ⟨⟨z, hz⟩, hne⟩)
  · rcases z with u | ⟨k, j⟩
    · exact ⟨Sum.inl u, toWedge_of_mem spec c h hz⟩
    · have hk : k ≠ c.bridge := by
        intro hEq
        subst hEq
        exact h.2.1 ((c.mem_leftVertices_interior spec _ j).mp hz).2
      refine ⟨Sum.inr ⟨k, ⟨j.val, by
        rw [shorten_length_of_ne spec c.bridge h2 hk]; exact j.isLt⟩⟩, ?_⟩
      rw [shortenVertex, shortenLift_inr_of_ne spec c h2 hk]
      exact toWedge_of_mem spec c h hz
  · have hne' : z ≠ spec.tailNeighbor c.bridge := fun hEq => hne (Subtype.ext hEq)
    rcases z with u | ⟨k, j⟩
    · exact ⟨Sum.inl u, toWedge_of_not_mem_of_ne spec c h hz hne'⟩
    · by_cases hk : k = c.bridge
      · subst hk
        have hj0 : j.val ≠ 0 := by
          intro hj0
          apply hne'
          rw [tailNeighbor_of_two_le spec c h2]
          have hfin : j = ⟨0, by omega⟩ := Fin.ext hj0
          rw [hfin]
        refine ⟨Sum.inr ⟨c.bridge, ⟨j.val - 1, by
          rw [shorten_length_self]; have := j.isLt; omega⟩⟩, ?_⟩
        rw [shortenVertex, shortenLift_inr_self]
        have hfin : (⟨j.val - 1 + 1, by have := j.isLt; omega⟩ : Fin (spec.length c.bridge - 1)) = j :=
          Fin.ext (by simp; omega)
        rw [hfin]
        exact toWedge_of_not_mem_of_ne spec c h hz hne'
      · refine ⟨Sum.inr ⟨k, ⟨j.val, by
          rw [shorten_length_of_ne spec c.bridge h2 hk]; exact j.isLt⟩⟩, ?_⟩
        rw [shortenVertex, shortenLift_inr_of_ne spec c h2 hk]
        exact toWedge_of_not_mem_of_ne spec c h hz hne'

/-- The vertex bijection of the shortening. -/
def shortenVertexEquiv : (shorten spec c.bridge h2).Vertex ≃ (wedge spec c h).V :=
  Equiv.ofBijective _ ⟨shortenVertex_injective spec c h h2, shortenVertex_surjective spec c h h2⟩

/-- A unit step of the shortened specification is a unit step of the original
one: on the bridge slot it is shifted one unit towards the head. -/
def shortenStep : (shorten spec c.bridge h2).Step → spec.Step
  | ⟨k, j⟩ =>
      if hk : k = c.bridge then
        ⟨c.bridge, ⟨j.val + 1, by
          have := j.isLt; have hl : (shorten spec c.bridge h2).length k = spec.length c.bridge - 1 := by rw [hk, shorten_length_self]
          omega⟩⟩
      else
        ⟨k, ⟨j.val, by
          have := j.isLt; have hl := shorten_length_of_ne spec c.bridge h2 hk; omega⟩⟩

theorem shortenStep_self (j : Fin ((shorten spec c.bridge h2).length c.bridge)) :
    shortenStep spec c h2 ⟨c.bridge, j⟩ =
      ⟨c.bridge, ⟨j.val + 1, by have := j.isLt; have hl := shorten_length_self spec c.bridge h2; omega⟩⟩ := by
  simp [shortenStep]

theorem shortenStep_of_ne {k : Fin p} (hk : k ≠ c.bridge)
    (j : Fin ((shorten spec c.bridge h2).length k)) :
    shortenStep spec c h2 ⟨k, j⟩ =
      ⟨k, ⟨j.val, by
        have := j.isLt; have hl := shorten_length_of_ne spec c.bridge h2 hk; omega⟩⟩ := by
  simp [shortenStep, hk]

theorem shortenStep_injective : Function.Injective (shortenStep spec c h2) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ hEq
  by_cases hk : k = c.bridge <;> by_cases hk' : k' = c.bridge
  · subst hk; subst hk'
    rw [shortenStep_self, shortenStep_self] at hEq
    have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp hEq).2)
    have hj : j = j' := Fin.ext (by simpa using this)
    rw [hj]
  · subst hk
    rw [shortenStep_self, shortenStep_of_ne spec c h2 hk'] at hEq
    exact (hk' (congrArg Sigma.fst hEq).symm).elim
  · subst hk'
    rw [shortenStep_of_ne spec c h2 hk, shortenStep_self] at hEq
    exact (hk (congrArg Sigma.fst hEq)).elim
  · rw [shortenStep_of_ne spec c h2 hk, shortenStep_of_ne spec c h2 hk'] at hEq
    have hkk : k = k' := congrArg Sigma.fst hEq
    subst hkk
    have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp hEq).2)
    have hj : j = j' := Fin.ext this
    rw [hj]

theorem shortenStep_ne (s : (shorten spec c.bridge h2).Step) :
    shortenStep spec c h2 s ≠ bridgeStep spec c := by
  obtain ⟨k, j⟩ := s
  by_cases hk : k = c.bridge
  · subst hk
    rw [shortenStep_self]
    intro hEq
    have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp hEq).2)
    simp at this
  · rw [shortenStep_of_ne spec c h2 hk]
    intro hEq
    exact hk (congrArg Sigma.fst hEq)

theorem shortenStep_surjective (t : spec.Step) (ht : t ≠ bridgeStep spec c) :
    ∃ s, shortenStep spec c h2 s = t := by
  obtain ⟨k, j⟩ := t
  by_cases hk : k = c.bridge
  · subst hk
    have hj0 : j.val ≠ 0 := by
      intro hj0
      apply ht
      have hfin : j = ⟨0, spec.length_pos c.bridge⟩ := Fin.ext hj0
      rw [hfin]
      rfl
    refine ⟨⟨c.bridge, ⟨j.val - 1, by rw [shorten_length_self]; have := j.isLt; omega⟩⟩, ?_⟩
    rw [shortenStep_self]
    have hfin : (⟨j.val - 1 + 1, by have := j.isLt; omega⟩ : Fin (spec.length c.bridge)) = j :=
      Fin.ext (by simp; omega)
    rw [hfin]
  · refine ⟨⟨k, ⟨j.val, by rw [shorten_length_of_ne spec c.bridge h2 hk]; exact j.isLt⟩⟩, ?_⟩
    rw [shortenStep_of_ne spec c h2 hk]

theorem shorten_stepLeft (s : (shorten spec c.bridge h2).Step) :
    shortenVertex spec c h h2 ((shorten spec c.bridge h2).stepLeft s.1 s.2) =
      toWedge spec c h (spec.stepLeft (shortenStep spec c h2 s).1 (shortenStep spec c h2 s).2) := by
  obtain ⟨k, j⟩ := s
  dsimp only
  by_cases hk : k = c.bridge
  · subst hk
    rw [shortenStep_self]
    by_cases hj : j.val = 0
    · rw [stepLeft_of_zero _ _ _ hj, stepLeft_of_ne_zero spec _ _ (by simp)]
      have hfin : (⟨j.val + 1 - 1, by have := j.isLt; simp; omega⟩ : Fin (spec.length c.bridge - 1)) =
          ⟨0, by omega⟩ := Fin.ext (by simp [hj])
      rw [hfin, ← tailNeighbor_of_two_le spec c h2, toWedge_tailNeighbor]
      exact toWedge_of_mem spec c h (c.tail_mem_leftVertices spec h)
    · rw [stepLeft_of_ne_zero _ _ _ hj, stepLeft_of_ne_zero spec _ _ (by simp)]
      rw [shortenVertex, shortenLift_inr_self]
      congr 3
      exact Fin.ext (by simp; omega)
  · rw [shortenStep_of_ne spec c h2 hk]
    by_cases hj : j.val = 0
    · rw [stepLeft_of_zero _ _ _ hj, stepLeft_of_zero spec _ _ hj]
      rfl
    · rw [stepLeft_of_ne_zero _ _ _ hj, stepLeft_of_ne_zero spec _ _ hj]
      rw [shortenVertex, shortenLift_inr_of_ne spec c h2 hk]

theorem shorten_stepRight (s : (shorten spec c.bridge h2).Step) :
    shortenVertex spec c h h2 ((shorten spec c.bridge h2).stepRight s.1 s.2) =
      toWedge spec c h (spec.stepRight (shortenStep spec c h2 s).1 (shortenStep spec c h2 s).2) := by
  obtain ⟨k, j⟩ := s
  dsimp only
  by_cases hk : k = c.bridge
  · subst hk
    rw [shortenStep_self]
    have hl := shorten_length_self spec c.bridge h2
    by_cases hj : j.val + 1 = spec.length c.bridge - 1
    · rw [stepRight_of_last _ _ _ (by omega), stepRight_of_last spec _ _ (by simp; omega)]
      rfl
    · rw [stepRight_of_ne_last _ _ _ (by omega), stepRight_of_ne_last spec _ _ (by simp; omega)]
      rw [shortenVertex, shortenLift_inr_self]
  · rw [shortenStep_of_ne spec c h2 hk]
    have hl := shorten_length_of_ne spec c.bridge h2 hk
    by_cases hj : j.val + 1 = spec.length k
    · rw [stepRight_of_last _ _ _ (by omega), stepRight_of_last spec _ _ hj]
      rfl
    · rw [stepRight_of_ne_last _ _ _ (by omega), stepRight_of_ne_last spec _ _ hj]
      rw [shortenVertex, shortenLift_inr_of_ne spec c h2 hk]

/-- **The second half of the decomposition, at length at least two.**
Shortening a bridge slot by one unit is Laplacian-equivalent to the wedge of
the two sides of its first unit step. -/
def shortenEquiv : LaplacianEquiv (shorten spec c.bridge h2).graph (wedge spec c h) :=
  laplacianEquivWedgeOfSteps spec c h (shorten spec c.bridge h2)
    (shortenVertexEquiv spec c h h2) (shortenStep spec c h2)
    (shortenStep_injective spec c h2) (shortenStep_ne spec c h2)
    (shortenStep_surjective spec c h2)
    (shorten_stepLeft spec c h h2) (shorten_stepRight spec c h h2)

include h in
/-- Transport across one unit of a bridge slot of length at least two. -/
theorem bnExists_shorten_iff (r d : ℤ) :
    BNExists (shorten spec c.bridge h2).graph r d ↔ BNExists spec.graph r d :=
  ((shortenEquiv spec c h h2).bnExists_iff r d).trans
    ((BNExists_bridge_iff_vertexWedge _ _ _ _ r d).symm.trans
      ((bridgeEquiv spec c h).bnExists_iff r d).symm)

end Shorten

/-! ## 10.  Transport across a bridge slot of any length -/

section Transport

variable {n p : ℕ}

theorem ofCore_congr (core : Core n p) (ne : 0 < n)
    (lp : ∀ e, core.tail e ≠ core.head e) {l₁ l₂ : Fin p → ℕ} (hl : l₁ = l₂)
    (p₁ : ∀ e, 0 < l₁ e) (p₂ : ∀ e, 0 < l₂ e) :
    Spec.ofCore core ne lp l₁ p₁ = Spec.ofCore core ne lp l₂ p₂ := by
  subst hl
  rfl

/-- Shortening the bridge first does not change the contraction. -/
theorem contractBridge_shorten (spec : Spec (n + 1) (p + 1)) (c : CoreBridgeCut.Data spec.core)
    (h : c.Valid) (h2 : 2 ≤ spec.length c.bridge) :
    contractBridge (shorten spec c.bridge h2) c h = contractBridge spec c h := by
  unfold contractBridge
  apply ofCore_congr
  funext i
  exact shorten_length_of_ne spec c.bridge h2 (Fin.succAbove_ne _ _)

theorem bnExists_contractBridge_iff_aux (L : ℕ) :
    ∀ (spec : Spec (n + 1) (p + 1)) (c : CoreBridgeCut.Data spec.core) (h : c.Valid),
      spec.length c.bridge = L + 1 →
      ∀ r d : ℤ, (BNExists (contractBridge spec c h).graph r d ↔ BNExists spec.graph r d) := by
  induction L with
  | zero =>
      intro spec c h hlen r d
      exact bnExists_contractBridge_iff_of_length_one spec c h hlen r d
  | succ L ih =>
      intro spec c h hlen r d
      have h2 : 2 ≤ spec.length c.bridge := by omega
      have hlen' : (shorten spec c.bridge h2).length c.bridge = L + 1 := by
        rw [shorten_length_self]; omega
      rw [← contractBridge_shorten spec c h h2]
      exact (ih (shorten spec c.bridge h2) c h hlen' r d).trans
        (bnExists_shorten_iff spec c h h2 r d)

/-- **Transport across a bridge slot.**  Brill--Noether existence, in every
rank and degree, is the same on a specification and on the specification
obtained by contracting a bridge slot of any length. -/
theorem bnExists_contractBridge_iff (spec : Spec (n + 1) (p + 1))
    (c : CoreBridgeCut.Data spec.core) (h : c.Valid) (r d : ℤ) :
    BNExists (contractBridge spec c h).graph r d ↔ BNExists spec.graph r d :=
  bnExists_contractBridge_iff_aux (spec.length c.bridge - 1) spec c h
    (by have := spec.length_pos c.bridge; omega) r d

/-- The pencil transports back across a bridge. -/
theorem bnExists_of_contractBridge (spec : Spec (n + 1) (p + 1))
    (c : CoreBridgeCut.Data spec.core) (h : c.Valid) {r d : ℤ}
    (hBN : BNExists (contractBridge spec c h).graph r d) : BNExists spec.graph r d :=
  (bnExists_contractBridge_iff spec c h r d).mp hBN

end Transport

/-! ## 11.  Uniform refinements and the regular-subdivision gonality -/

section Scale

variable {n p : ℕ}

/-- Contraction commutes with uniform refinement. -/
theorem contractBridge_scale (spec : Spec (n + 1) (p + 1)) (c : CoreBridgeCut.Data spec.core)
    (h : c.Valid) (k : ℕ) (hk : 0 < k) :
    (contractBridge spec c h).scale k hk = contractBridge (spec.scale k hk) c h := rfl

theorem bnExists_contractBridge_scale_iff (spec : Spec (n + 1) (p + 1))
    (c : CoreBridgeCut.Data spec.core) (h : c.Valid) (k : ℕ) (hk : 0 < k) (r d : ℤ) :
    BNExists ((contractBridge spec c h).scale k hk).graph r d ↔
      BNExists (spec.scale k hk).graph r d := by
  rw [contractBridge_scale]
  exact bnExists_contractBridge_iff (spec.scale k hk) c h r d

/-- Two connected graphs with the same rank-one Brill--Noether existence in
every degree have the same divisorial gonality. -/
theorem divisorialGonality_eq_of_bnExists_iff {G H : CFGraph}
    (hG : graph_connected G) (hH : graph_connected H)
    (hiff : ∀ d : ℤ, BNExists G 1 d ↔ BNExists H 1 d) :
    Gonality.divisorialGonality G = Gonality.divisorialGonality H := by
  apply le_antisymm
  · have := Gonality.divisorialGonality_le_of_BNExists
      ((hiff _).mpr (Gonality.BNExists_one_divisorialGonality hH))
    exact_mod_cast this
  · have := Gonality.divisorialGonality_le_of_BNExists
      ((hiff _).mp (Gonality.BNExists_one_divisorialGonality hG))
    exact_mod_cast this

/-- Two connected specifications with the same rank-one Brill--Noether
existence on every uniform refinement have the same regular-subdivision
gonality. -/
theorem regularSubdivisionGonality_eq_of_iff {n₁ p₁ n₂ p₂ : ℕ}
    (spec₁ : Spec n₁ p₁) (spec₂ : Spec n₂ p₂)
    (h₁ : spec₁.core.Connected) (h₂ : spec₂.core.Connected)
    (hiff : ∀ (k : ℕ) (hk : 0 < k) (d : ℤ),
      BNExists (spec₁.scale k hk).graph 1 d ↔ BNExists (spec₂.scale k hk).graph 1 d) :
    spec₁.regularSubdivisionGonality = spec₂.regularSubdivisionGonality := by
  unfold Spec.regularSubdivisionGonality
  congr 1
  ext d
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (divisorialGonality_eq_of_bnExists_iff
      ((spec₁.scale k hk).graph_connected_of_coreConnected h₁)
      ((spec₂.scale k hk).graph_connected_of_coreConnected h₂) (hiff k hk)).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, divisorialGonality_eq_of_bnExists_iff
      ((spec₁.scale k hk).graph_connected_of_coreConnected h₁)
      ((spec₂.scale k hk).graph_connected_of_coreConnected h₂) (hiff k hk)⟩

/-- Contracting a bridge preserves the regular-subdivision gonality. -/
theorem regularSubdivisionGonality_contractBridge (spec : Spec (n + 1) (p + 1))
    (c : CoreBridgeCut.Data spec.core) (h : c.Valid) (hConn : spec.core.Connected) :
    (contractBridge spec c h).regularSubdivisionGonality = spec.regularSubdivisionGonality :=
  regularSubdivisionGonality_eq_of_iff _ _ (contractBridge_connected spec c h hConn) hConn
    (fun k hk d => bnExists_contractBridge_scale_iff spec c h k hk 1 d)

end Scale

/-! ## 12.  Every connected specification reduces to a bridgeless one -/

section Iterate

/-- **Iterated bridge contraction with composite transport.**  Every connected
specification reduces, by a finite chain of bridge contractions, to a
connected **bridgeless** specification of the same genus, with no more
vertices and slots, such that Brill--Noether existence agrees in every rank
and degree, on the specification itself and on every uniform refinement. -/
theorem exists_bridgeless {n p : ℕ} (spec : Spec n p) (hConn : spec.core.Connected) :
    ∃ (n' p' : ℕ) (spec' : Spec n' p'),
      spec'.core.Connected ∧ Bridgeless spec'.core ∧
      n' ≤ n ∧ p' ≤ p ∧ (p' : ℤ) - n' = (p : ℤ) - n ∧
      (∀ r d : ℤ, BNExists spec'.graph r d ↔ BNExists spec.graph r d) ∧
      (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
        BNExists (spec'.scale k hk).graph r d ↔ BNExists (spec.scale k hk).graph r d) := by
  induction p using Nat.strong_induction_on generalizing n with
  | h p ih =>
    by_cases hB : Bridgeless spec.core
    · exact ⟨n, p, spec, hConn, hB, le_rfl, le_rfl, rfl, fun _ _ => Iff.rfl,
        fun _ _ _ _ => Iff.rfl⟩
    · obtain ⟨c, hc⟩ := exists_valid_of_not_bridgeless hB
      cases n with
      | zero => exact absurd spec.core_nonempty (lt_irrefl 0)
      | succ n =>
        cases p with
        | zero => exact c.bridge.elim0
        | succ p =>
          obtain ⟨n', p', spec', h1, h2, h3, h4, h5, h6, h7⟩ :=
            ih p (Nat.lt_succ_self p) (contractBridge spec c hc)
              (contractBridge_connected spec c hc hConn)
          refine ⟨n', p', spec', h1, h2, by omega, by omega, by push_cast; omega, ?_, ?_⟩
          · intro r d
            exact (h6 r d).trans (bnExists_contractBridge_iff spec c hc r d)
          · intro k hk r d
            exact (h7 k hk r d).trans (bnExists_contractBridge_scale_iff spec c hc k hk r d)

/-- The genus of the subdivision graph is preserved along the reduction. -/
theorem genus_graph_eq_of_genus_eq {n p n' p' : ℕ} (spec : Spec n p) (spec' : Spec n' p')
    (hg : (p' : ℤ) - n' = (p : ℤ) - n) : genus spec'.graph = genus spec.graph := by
  rw [Spec.genus_graph, Spec.genus_graph]
  omega

/-- The regular-subdivision gonality is preserved along the reduction. -/
theorem exists_bridgeless_gonality {n p : ℕ} (spec : Spec n p) (hConn : spec.core.Connected) :
    ∃ (n' p' : ℕ) (spec' : Spec n' p'),
      spec'.core.Connected ∧ Bridgeless spec'.core ∧
      (p' : ℤ) - n' = (p : ℤ) - n ∧
      (∀ d : ℤ, BNExists spec'.graph 1 d → BNExists spec.graph 1 d) ∧
      spec'.regularSubdivisionGonality = spec.regularSubdivisionGonality := by
  obtain ⟨n', p', spec', h1, h2, -, -, h5, h6, h7⟩ := exists_bridgeless spec hConn
  exact ⟨n', p', spec', h1, h2, h5, fun d => (h6 1 d).mp,
    regularSubdivisionGonality_eq_of_iff spec' spec h1 hConn (fun k hk d => h7 k hk 1 d)⟩

end Iterate

end DraismaVargas.LocalCases.SpecBridge
