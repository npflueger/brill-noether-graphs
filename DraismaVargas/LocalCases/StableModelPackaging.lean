import DraismaVargas.LocalCases.BridgeReduction
import Utilities.Pseudocore.PseudocorePresentation
import Utilities.Subdivision.OneEdgeSplitRefinement

/-!
# The cubic stable model of an arbitrary connected specification

`StableModelReduction.exists_stableModel` takes a `Marking` and a `Stable`
hypothesis as input; `BridgeReduction.bridgeless_reduction` supplies `Stable`
from bridgelessness.  The reduction of a connected specification to a cubic
model therefore also needs the `Marking` itself, and the fact that the
bivalent suppression producing it preserves bridgelessness.  This file
supplies both and composes the whole reduction.

## 1.  Reorienting slots

`reverseCore C rev` reverses the slots flagged by `rev`.  Reversal is an
isomorphism of the presented graph — it is a `Spec.Relabeling` with
`coreEquiv` and `slotEquiv` the identity and `reversed := rev`
(`reverseRelabeling`) — so it moves nothing: valence
(`slotValence_reverseCore`), bridgelessness (`bridgeless_reverseCore`),
connectivity (`connected_reverseCore`), Brill--Noether existence
(`bnExists_reverseSpec`) and every uniform refinement (`reverseSpec_scale`,
an equation of specifications) are all unchanged.

## 2--3.  Bivalent suppression, named and iterated

`PseudocorePresentation.exists_merge` proves that suppressing a bivalent core
vertex preserves the subdivided graph, but it hides the merged specification
behind an existential, so nothing can be said about the merged specification's
*core* or about its uniform refinements.  `mergedSpec` names it — the same
construction, with the concatenated slot at `splitSlot` and its two halves at
`data.first` and `data.second` — and then:

* `mergedSpec_laplacianEquiv` is `exists_merge` for the named object: `spec` is
  a `Spec.Relabeling` of the canonical one-slot split of `mergedSpec`
  (`mergeRelabeling`), whose `canonicalSplitLaplacianEquiv` is in `Utilities`;
* `mergedSpec_scale` is an **equation**, `(mergedSpec spec).scale k =
  mergedSpec (spec.scale k)`, because `k * (L₁ + L₂) = k * L₁ + k * L₂`.  This
  is what `exists_merge` cannot say and what carries the transport to every
  uniform refinement, hence to `regularSubdivisionGonality`;
* `bridgeless_mergedCore` is the new combinatorial step: **bivalent suppression
  preserves bridgelessness.**  A valid cut of the merged core is pulled back by
  putting the suppressed vertex on the side of the far end of its first slot.
  If the merged bridge is the concatenated slot, the original bridge is the
  second half; otherwise it is the slot underlying the merged one.

`exists_reducedSpec` iterates, by strong induction on the vertex count, to a
`Reduced` core, carrying connectivity, bridgelessness, the genus and the
transport in both the plain and the scaled form.

## 4--5.  The marking, and the reorientation it needs

On a reduced core, the `Utilities` lemma `exists_markedShapeAt` produces a
`MarkedShape`:
every vertex is either stable or a bivalent marker whose two slots run to one
stable partner.  That is **not** a `Marking`: `Marking` (and through it
`CoreExpansion.ExpansionData.MarkerIsolated`) demands that of the two slots at a marker
exactly one has its *head* there, and a reduced core can have both ends
pointing in.

`markerRev` is the reorientation: at each marker the lower-indexed of the two
incident slots is made to point **into** it and the higher-indexed one **out**
of it (`otherSlot`, `isLo`, `oriented_of_isLo`, `oriented_of_not_isLo`).  No
slot joins two markers — the partner of a marker is stable — so the two rules
never conflict.  `orientedMarking` is the resulting `Marking`, and
`orientedMarking_isMarker` identifies its markers with the shape's, so
`orientedMarking_base` is `MarkedShape.base_stable` transported across a
reversal.

## 6--7.  The composite

`exists_markedSpec_of_bridgeless` and `exists_markedSpec` are the `Marking`
**derived**: every connected specification of genus at least two is presented,
after the three moves, by a connected bridgeless specification carrying a
base-stable `Marking`, with the transport — a Laplacian equivalence when the
input is already bridgeless.  `BridgeReduction.stable_of_bridgeless` then
upgrades the marking to `Stable` for free.

`exists_cubicModel` is the reduction: from a connected `spec` of genus at least
two,
contract every bridge, suppress every bivalent vertex, reorient at the markers,
and expand.  The output is a cubic loopless connected `spec'` with
`2 p' = 3 n'` — the count `StableModelReduction.dimension_forced` pins — and a
`TopologicalValid` `GraphContractionCertificate` onto the reduced
representative `spec₀`, whose Brill--Noether existence agrees with the
original in every rank and degree and on every uniform refinement, so that
`regularSubdivisionGonality` agrees as well.  `exists_cubicModel_graph` is the
same statement for the subdivided graphs, in the form the rest of the
construction consumes.

**Which clause fails, exactly.**  In `exists_cubicModel` the certificate lands
on `spec₀`, not on `spec`.  `exists_cubicModel_of_bridgeless` isolates the
reason: on a **bridgeless** `spec` the certificate does land on `spec` itself,
because suppression and reorientation are Laplacian equivalences and
`GraphContractionCertificate.postcomposeLaplacianEquiv` carries the certificate
and its `TopologicalValid` across one.  The single step that cannot be carried
back is **bridge contraction**, which genuinely changes the graph; what it
supplies instead is `SpecBridge.bnExists_contractBridge_iff`, an equivalence of
Brill--Noether existence in every rank, degree and scale — and that is what the
transport of a pencil back to the requested graph consumes.  So the certificate
composes across two of the three moves, and the
third is replaced by a transport, not by a certificate.

## 8.  Non-vacuity

`theta_cubicModel` runs the composite on the theta graph, which is already
bridgeless, reduced and cubic.  `dumbbell_cubicModel` runs it on the dumbbell
of `StableModelReduction` — the pendant-loop example there, which is neither
bridgeless nor `Stable` — and returns a cubic model with the transport and the
gonality equality back to the dumbbell.
-/

namespace DraismaVargas.LocalCases.StableModelPackaging

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.PseudocorePresentation
open MarkedGraphs.Certificate
open ExplicitPotential
open DraismaVargas.LocalCases.StableModelReduction
open DraismaVargas.LocalCases.SpecBridge
open DraismaVargas.LocalCases.BridgeReduction

/-! ## 1.  Reorienting slots -/

section Reverse

variable {n p : ℕ}

/-- Reverse every slot flagged by `rev`. -/
def reverseCore (C : Core n p) (rev : Fin p → Bool) : Core n p where
  tail := fun e => if rev e then C.head e else C.tail e
  head := fun e => if rev e then C.tail e else C.head e

@[simp] theorem reverseCore_tail (C : Core n p) (rev : Fin p → Bool) (e : Fin p) :
    (reverseCore C rev).tail e = if rev e then C.head e else C.tail e := rfl

@[simp] theorem reverseCore_head (C : Core n p) (rev : Fin p → Bool) (e : Fin p) :
    (reverseCore C rev).head e = if rev e then C.tail e else C.head e := rfl

theorem reverseCore_loopless (C : Core n p) (rev : Fin p → Bool)
    (h : ∀ e : Fin p, C.tail e ≠ C.head e) :
    ∀ e : Fin p, (reverseCore C rev).tail e ≠ (reverseCore C rev).head e := by
  intro e
  simp only [reverseCore_tail, reverseCore_head]
  split
  · exact (h e).symm
  · exact h e

/-- The involution of slot ends induced by a reversal. -/
def revFlip (rev : Fin p → Bool) (x : Fin p × Bool) : Fin p × Bool :=
  (x.1, xor (rev x.1) x.2)

theorem revFlip_involutive (rev : Fin p → Bool) : Function.Involutive (revFlip rev) := by
  intro x
  obtain ⟨e, s⟩ := x
  cases h : rev e <;> cases s <;> simp [revFlip, h]

theorem mem_slotEnds_reverseCore (C : Core n p) (rev : Fin p → Bool) (w : Fin n)
    (x : Fin p × Bool) :
    x ∈ slotEnds (reverseCore C rev) w ↔ revFlip rev x ∈ slotEnds C w := by
  obtain ⟨e, s⟩ := x
  cases h : rev e <;> cases s <;>
    simp [mem_slotEnds, revFlip, h]

theorem slotEnds_reverseCore (C : Core n p) (rev : Fin p → Bool) (w : Fin n) :
    slotEnds (reverseCore C rev) w = (slotEnds C w).image (revFlip rev) := by
  ext x
  rw [mem_slotEnds_reverseCore, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨revFlip rev x, hx, revFlip_involutive rev x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [revFlip_involutive rev y]

@[simp] theorem slotValence_reverseCore (C : Core n p) (rev : Fin p → Bool) (w : Fin n) :
    slotValence (reverseCore C rev) w = slotValence C w := by
  unfold slotValence
  rw [slotEnds_reverseCore, Finset.card_image_of_injective _ (revFlip_involutive rev).injective]

theorem isBridge_of_reverseCore {C : Core n p} {rev : Fin p → Bool} {e : Fin p}
    (h : IsBridge (reverseCore C rev) e) : IsBridge C e := by
  obtain ⟨S, hTail, hHead, hOther⟩ := h
  simp only [reverseCore_tail, reverseCore_head] at hTail hHead
  by_cases hr : rev e = true
  · refine ⟨Sᶜ, ?_, ?_, ?_⟩
    · rw [if_pos hr] at hHead
      simpa using hHead
    · rw [if_pos hr] at hTail
      simpa using hTail
    · intro k hk
      have := hOther k hk
      simp only [reverseCore_tail, reverseCore_head] at this
      by_cases hrk : rev k = true
      · rw [if_pos hrk, if_pos hrk] at this
        simp only [Finset.mem_compl]
        exact not_congr this.symm
      · rw [if_neg hrk, if_neg hrk] at this
        simp only [Finset.mem_compl]
        exact not_congr this
  · refine ⟨S, ?_, ?_, ?_⟩
    · rwa [if_neg hr] at hTail
    · rwa [if_neg hr] at hHead
    · intro k hk
      have := hOther k hk
      simp only [reverseCore_tail, reverseCore_head] at this
      by_cases hrk : rev k = true
      · rw [if_pos hrk, if_pos hrk] at this
        exact this.symm
      · rw [if_neg hrk, if_neg hrk] at this
        exact this

theorem bridgeless_reverseCore {C : Core n p} (rev : Fin p → Bool) (h : Bridgeless C) :
    Bridgeless (reverseCore C rev) :=
  fun e hb => h e (isBridge_of_reverseCore hb)

theorem connected_reverseCore {C : Core n p} (rev : Fin p → Bool) (h : C.Connected) :
    (reverseCore C rev).Connected := by
  intro S hS
  obtain ⟨k, hk⟩ := h S hS
  refine ⟨k, ?_⟩
  simp only [reverseCore_tail, reverseCore_head]
  by_cases hrk : rev k = true
  · rw [if_pos hrk, if_pos hrk]
    exact hk.symm
  · rw [if_neg hrk, if_neg hrk]
    exact hk

/-- The specification with the flagged slots reversed. -/
def reverseSpec (spec : Spec n p) (rev : Fin p → Bool) : Spec n p where
  core := reverseCore spec.core rev
  length := spec.length
  core_nonempty := spec.core_nonempty
  core_loopless := reverseCore_loopless spec.core rev spec.core_loopless
  length_pos := spec.length_pos

@[simp] theorem reverseSpec_core (spec : Spec n p) (rev : Fin p → Bool) :
    (reverseSpec spec rev).core = reverseCore spec.core rev := rfl

theorem reverseSpec_scale (spec : Spec n p) (rev : Fin p → Bool) (k : ℕ) (hk : 0 < k) :
    (reverseSpec spec rev).scale k hk = reverseSpec (spec.scale k hk) rev := rfl

/-- Reversal is a relabeling: it changes no length and no unordered endpoint
pair, only the recorded orientation. -/
def reverseRelabeling (spec : Spec n p) (rev : Fin p → Bool) :
    spec.Relabeling (reverseSpec spec rev) where
  coreEquiv := Equiv.refl _
  slotEquiv := Equiv.refl _
  reversed := rev
  length_eq := fun _ => rfl
  tail_eq := fun _ => rfl
  head_eq := fun _ => rfl

theorem bnExists_reverseSpec (spec : Spec n p) (rev : Fin p → Bool) (r d : ℤ) :
    BNExists spec.graph r d ↔ BNExists (reverseSpec spec rev).graph r d :=
  (Spec.laplacianEquiv _ _ (reverseRelabeling spec rev)).bnExists_iff r d

end Reverse


/-! ## 2.  Suppressing one bivalent core vertex -/

section Merge

variable {n p : ℕ} {C : Core (n + 1) (p + 1)}

/-- The vertex permutation moving the suppressed vertex onto the last index. -/
def vSwap (data : MergeData C) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap data.vertex (Fin.last n)

/-- The slot permutation moving the second suppressed slot onto the last index. -/
def sSwap (data : MergeData C) : Equiv.Perm (Fin (p + 1)) :=
  Equiv.swap data.second.1 (Fin.last p)

@[simp] theorem vSwap_vertex (data : MergeData C) :
    vSwap data data.vertex = Fin.last n := by simp [vSwap]

theorem vSwap_ne_last (data : MergeData C) {u : Fin (n + 1)} (hu : u ≠ data.vertex) :
    vSwap data u ≠ Fin.last n :=
  swap_ne_last _ hu

@[simp] theorem sSwap_second (data : MergeData C) :
    sSwap data data.second.1 = Fin.last p := by simp [sSwap]

theorem sSwap_ne_last (data : MergeData C) {E : Fin (p + 1)} (hE : E ≠ data.second.1) :
    sSwap data E ≠ Fin.last p :=
  swap_ne_last _ hE

/-- The label in `Fin n` of a vertex other than the suppressed one. -/
def vmap (hn : 0 < n) (data : MergeData C) (u : Fin (n + 1)) : Fin n :=
  shrink hn (vSwap data u)

/-- The label in `Fin p` of a slot other than the second suppressed one. -/
def smap (hp : 0 < p) (data : MergeData C) (E : Fin (p + 1)) : Fin p :=
  shrink hp (sSwap data E)

/-- The slot of the merged core carrying the concatenation. -/
def splitSlot (hp : 0 < p) (data : MergeData C) : Fin p := smap hp data data.first.1

/-- The slot of `C` underlying a slot of the merged core. -/
def pre (data : MergeData C) (e : Fin p) : Fin (p + 1) :=
  sSwap data (Fin.castSucc e)

theorem castSucc_vmap (hn : 0 < n) (data : MergeData C) {u : Fin (n + 1)}
    (hu : u ≠ data.vertex) : Fin.castSucc (vmap hn data u) = vSwap data u :=
  castSucc_shrink hn (vSwap_ne_last data hu)

theorem vmap_inj (hn : 0 < n) (data : MergeData C) {u u' : Fin (n + 1)}
    (hu : u ≠ data.vertex) (hu' : u' ≠ data.vertex) (h : vmap hn data u = vmap hn data u') :
    u = u' := by
  refine (vSwap data).injective ?_
  rw [← castSucc_vmap hn data hu, ← castSucc_vmap hn data hu', h]

/-- Every label of the merged core comes from a vertex other than the
suppressed one. -/
def unmap (data : MergeData C) (i : Fin n) : Fin (n + 1) :=
  (vSwap data).symm (Fin.castSucc i)

theorem unmap_ne (data : MergeData C) (i : Fin n) : unmap data i ≠ data.vertex := by
  intro h
  have h2 : (Fin.castSucc i : Fin (n + 1)) = Fin.last n := by
    have hc := congrArg (vSwap data) h
    rw [vSwap_vertex] at hc
    simp [unmap] at hc
  exact absurd h2 (Fin.castSucc_ne_last i)

@[simp] theorem vmap_unmap (hn : 0 < n) (data : MergeData C) (i : Fin n) :
    vmap hn data (unmap data i) = i := by
  simp [vmap, unmap]

theorem castSucc_smap (hp : 0 < p) (data : MergeData C) {E : Fin (p + 1)}
    (hE : E ≠ data.second.1) : Fin.castSucc (smap hp data E) = sSwap data E :=
  castSucc_shrink hp (sSwap_ne_last data hE)

@[simp] theorem pre_smap (hp : 0 < p) (data : MergeData C) {E : Fin (p + 1)}
    (hE : E ≠ data.second.1) : pre data (smap hp data E) = E := by
  unfold pre
  rw [castSucc_smap hp data hE]
  simp [sSwap]

@[simp] theorem smap_pre (hp : 0 < p) (data : MergeData C) (e : Fin p) :
    smap hp data (pre data e) = e := by
  simp [smap, pre, sSwap]

theorem pre_ne_second (data : MergeData C) (e : Fin p) :
    pre data e ≠ data.second.1 := by
  intro h
  have h2 : (Fin.castSucc e : Fin (p + 1)) = Fin.last p := by
    have hc := congrArg (sSwap data) h
    rw [sSwap_second] at hc
    simp [pre, sSwap] at hc
  exact absurd h2 (Fin.castSucc_ne_last e)

@[simp] theorem pre_splitSlot (hp : 0 < p) (data : MergeData C) :
    pre data (splitSlot hp data) = data.first.1 :=
  pre_smap hp data data.slots_ne

theorem smap_eq_splitSlot_iff (hp : 0 < p) (data : MergeData C) {E : Fin (p + 1)}
    (hE : E ≠ data.second.1) : smap hp data E = splitSlot hp data ↔ E = data.first.1 := by
  constructor
  · intro h
    have hc := congrArg (pre data) h
    rwa [pre_smap hp data hE, pre_splitSlot] at hc
  · intro h; rw [h, splitSlot]


theorem pre_inj (data : MergeData C) {e e' : Fin p}
    (h : pre data e = pre data e') : e = e' := by
  have h2 : (sSwap data) (Fin.castSucc e) = (sSwap data) (Fin.castSucc e') := h
  exact Fin.castSucc_injective p ((sSwap data).injective h2)

theorem pre_ne_first (hp : 0 < p) (data : MergeData C) {e : Fin p}
    (he : e ≠ splitSlot hp data) : pre data e ≠ data.first.1 := by
  intro h
  exact he (pre_inj data (h.trans (pre_splitSlot hp data).symm))

/-! ### The two suppressed slot ends -/

theorem first_vertex (data : MergeData C) :
    (C.head data.first.1 = data.vertex ∧ farEnd C data.first = C.tail data.first.1) ∨
      (C.tail data.first.1 = data.vertex ∧ farEnd C data.first = C.head data.first.1) := by
  have h := (mem_slotEnds C data.vertex data.first).mp data.first_mem
  cases hs : data.first.2 with
  | true =>
      rw [hs] at h
      simp only [if_true] at h
      exact Or.inl ⟨h, by simp [farEnd, hs]⟩
  | false =>
      rw [hs] at h
      simp only [Bool.false_eq_true, if_false] at h
      exact Or.inr ⟨h, by simp [farEnd, hs]⟩

theorem second_vertex (data : MergeData C) :
    (C.head data.second.1 = data.vertex ∧ farEnd C data.second = C.tail data.second.1) ∨
      (C.tail data.second.1 = data.vertex ∧ farEnd C data.second = C.head data.second.1) := by
  have h := (mem_slotEnds C data.vertex data.second).mp data.second_mem
  cases hs : data.second.2 with
  | true =>
      rw [hs] at h
      simp only [if_true] at h
      exact Or.inl ⟨h, by simp [farEnd, hs]⟩
  | false =>
      rw [hs] at h
      simp only [Bool.false_eq_true, if_false] at h
      exact Or.inr ⟨h, by simp [farEnd, hs]⟩

theorem farFirst_ne_vertex (hL : ∀ e : Fin (p + 1), C.tail e ≠ C.head e)
    (data : MergeData C) : farEnd C data.first ≠ data.vertex := by
  rcases first_vertex data with ⟨hv, hf⟩ | ⟨hv, hf⟩
  · rw [hf, ← hv]; exact hL _
  · rw [hf, ← hv]; exact fun h => hL _ h.symm

theorem farSecond_ne_vertex (hL : ∀ e : Fin (p + 1), C.tail e ≠ C.head e)
    (data : MergeData C) : farEnd C data.second ≠ data.vertex := by
  rcases second_vertex data with ⟨hv, hf⟩ | ⟨hv, hf⟩
  · rw [hf, ← hv]; exact hL _
  · rw [hf, ← hv]; exact fun h => hL _ h.symm

theorem avoid (hL : ∀ e : Fin (p + 1), C.tail e ≠ C.head e) (data : MergeData C)
    {E : Fin (p + 1)} (h1 : E ≠ data.first.1) (h2 : E ≠ data.second.1) :
    C.tail E ≠ data.vertex ∧ C.head E ≠ data.vertex := by
  constructor
  · intro h
    rcases data.slot_eq_of_tail hL h with h' | h'
    · exact h1 h'
    · exact h2 h'
  · intro h
    rcases data.slot_eq_of_head hL h with h' | h'
    · exact h1 h'
    · exact h2 h'

/-! ### The merged core -/

/-- The core with the bivalent vertex suppressed: the two slots at it are
concatenated into the single slot `splitSlot`. -/
def mergedCore (hn : 0 < n) (hp : 0 < p) (data : MergeData C) : Core n p where
  tail := fun e => if e = splitSlot hp data then vmap hn data (farEnd C data.first)
    else vmap hn data (C.tail (pre data e))
  head := fun e => if e = splitSlot hp data then vmap hn data (farEnd C data.second)
    else vmap hn data (C.head (pre data e))

@[simp] theorem mergedCore_tail_split (hn : 0 < n) (hp : 0 < p) (data : MergeData C) :
    (mergedCore hn hp data).tail (splitSlot hp data) = vmap hn data (farEnd C data.first) := by
  simp [mergedCore]

@[simp] theorem mergedCore_head_split (hn : 0 < n) (hp : 0 < p) (data : MergeData C) :
    (mergedCore hn hp data).head (splitSlot hp data) = vmap hn data (farEnd C data.second) := by
  simp [mergedCore]

theorem mergedCore_tail_of_ne (hn : 0 < n) (hp : 0 < p) (data : MergeData C) {e : Fin p}
    (he : e ≠ splitSlot hp data) :
    (mergedCore hn hp data).tail e = vmap hn data (C.tail (pre data e)) := by
  simp [mergedCore, he]

theorem mergedCore_head_of_ne (hn : 0 < n) (hp : 0 < p) (data : MergeData C) {e : Fin p}
    (he : e ≠ splitSlot hp data) :
    (mergedCore hn hp data).head e = vmap hn data (C.head (pre data e)) := by
  simp [mergedCore, he]

theorem mergedCore_loopless (hn : 0 < n) (hp : 0 < p)
    (hL : ∀ e : Fin (p + 1), C.tail e ≠ C.head e) (data : MergeData C) :
    ∀ e : Fin p, (mergedCore hn hp data).tail e ≠ (mergedCore hn hp data).head e := by
  intro e
  by_cases he : e = splitSlot hp data
  · subst he
    rw [mergedCore_tail_split, mergedCore_head_split]
    intro h
    exact data.far_ne
      (vmap_inj hn data (farFirst_ne_vertex hL data) (farSecond_ne_vertex hL data) h)
  · rw [mergedCore_tail_of_ne hn hp data he, mergedCore_head_of_ne hn hp data he]
    intro h
    obtain ⟨ht, hh⟩ := avoid hL data (pre_ne_first hp data he) (pre_ne_second data e)
    exact hL _ (vmap_inj hn data ht hh h)


/-! ### The merged specification -/

/-- The specification with the bivalent vertex suppressed: the two slots at it
become one slot of the summed length. -/
def mergedSpec (hn : 0 < n) (hp : 0 < p) (spec : Spec (n + 1) (p + 1))
    (data : MergeData spec.core) : Spec n p where
  core := mergedCore hn hp data
  length := fun e => if e = splitSlot hp data
    then spec.length data.first.1 + spec.length data.second.1
    else spec.length (pre data e)
  core_nonempty := hn
  core_loopless := mergedCore_loopless hn hp spec.core_loopless data
  length_pos := by
    intro e
    by_cases he : e = splitSlot hp data
    · rw [if_pos he]
      exact Nat.add_pos_left (spec.length_pos _) _
    · rw [if_neg he]
      exact spec.length_pos _

@[simp] theorem mergedSpec_core (hn : 0 < n) (hp : 0 < p) (spec : Spec (n + 1) (p + 1))
    (data : MergeData spec.core) : (mergedSpec hn hp spec data).core = mergedCore hn hp data :=
  rfl

@[simp] theorem mergedSpec_length_split (hn : 0 < n) (hp : 0 < p)
    (spec : Spec (n + 1) (p + 1)) (data : MergeData spec.core) :
    (mergedSpec hn hp spec data).length (splitSlot hp data)
      = spec.length data.first.1 + spec.length data.second.1 := by
  simp [mergedSpec]

theorem mergedSpec_length_of_ne (hn : 0 < n) (hp : 0 < p) (spec : Spec (n + 1) (p + 1))
    (data : MergeData spec.core) {e : Fin p} (he : e ≠ splitSlot hp data) :
    (mergedSpec hn hp spec data).length e = spec.length (pre data e) := by
  simp [mergedSpec, he]

/-- The orientation flags carrying `spec` onto the canonical split of its
merge. -/
def rev (data : MergeData C) (E : Fin (p + 1)) : Bool :=
  if E = data.second.1 then decide (C.head E = data.vertex)
  else decide (C.tail E = data.vertex)

theorem rev_of_avoid (hL : ∀ e : Fin (p + 1), C.tail e ≠ C.head e) (data : MergeData C)
    {E : Fin (p + 1)} (h1 : E ≠ data.first.1) (h2 : E ≠ data.second.1) :
    rev data E = false := by
  simp only [rev, if_neg h2, decide_eq_false_iff_not]
  exact (avoid hL data h1 h2).1

theorem firstPair (hL : ∀ e : Fin (p + 1), C.tail e ≠ C.head e) (data : MergeData C) :
    (if rev data data.first.1 then vSwap data (C.head data.first.1)
        else vSwap data (C.tail data.first.1)) = vSwap data (farEnd C data.first) ∧
      (if rev data data.first.1 then vSwap data (C.tail data.first.1)
        else vSwap data (C.head data.first.1)) = Fin.last n := by
  have hrev : rev data data.first.1 = decide (C.tail data.first.1 = data.vertex) := by
    simp only [rev, if_neg data.slots_ne]
  by_cases hcase : C.tail data.first.1 = data.vertex
  · have hflag : rev data data.first.1 = true := by rw [hrev, hcase]; simp
    have hfar : farEnd C data.first = C.head data.first.1 := by
      rcases first_vertex data with ⟨hv, -⟩ | ⟨-, hf⟩
      · exact absurd (hcase.trans hv.symm) (hL _)
      · exact hf
    rw [hflag]
    exact ⟨by simp [hfar], by simp [hcase]⟩
  · have hflag : rev data data.first.1 = false := by rw [hrev]; simp [hcase]
    have hhead : C.head data.first.1 = data.vertex := by
      rcases first_vertex data with ⟨hv, -⟩ | ⟨hv, -⟩
      · exact hv
      · exact absurd hv hcase
    have hfar : farEnd C data.first = C.tail data.first.1 := by
      rcases first_vertex data with ⟨-, hf⟩ | ⟨hv, -⟩
      · exact hf
      · exact absurd hv hcase
    rw [hflag]
    exact ⟨by simp [hfar], by simp [hhead]⟩

theorem secondPair (hL : ∀ e : Fin (p + 1), C.tail e ≠ C.head e) (data : MergeData C) :
    (if rev data data.second.1 then vSwap data (C.head data.second.1)
        else vSwap data (C.tail data.second.1)) = Fin.last n ∧
      (if rev data data.second.1 then vSwap data (C.tail data.second.1)
        else vSwap data (C.head data.second.1)) = vSwap data (farEnd C data.second) := by
  have hrev : rev data data.second.1 = decide (C.head data.second.1 = data.vertex) := by
    simp [rev]
  by_cases hcase : C.head data.second.1 = data.vertex
  · have hflag : rev data data.second.1 = true := by rw [hrev, hcase]; simp
    have hfar : farEnd C data.second = C.tail data.second.1 := by
      rcases second_vertex data with ⟨-, hf⟩ | ⟨hv, -⟩
      · exact hf
      · exact absurd (hv.trans hcase.symm) (hL _)
    rw [hflag]
    exact ⟨by simp [hcase], by simp [hfar]⟩
  · have hflag : rev data data.second.1 = false := by rw [hrev]; simp [hcase]
    have htail : C.tail data.second.1 = data.vertex := by
      rcases second_vertex data with ⟨hv, -⟩ | ⟨hv, -⟩
      · exact absurd hv hcase
      · exact hv
    have hfar : farEnd C data.second = C.head data.second.1 := by
      rcases second_vertex data with ⟨hv, -⟩ | ⟨-, hf⟩
      · exact absurd hv hcase
      · exact hf
    rw [hflag]
    exact ⟨by simp [htail], by simp [hfar]⟩


/-! ### `spec` is the canonical split of its merge -/

/-- The canonical one-slot split of the merged specification. -/
def splitTarget (hn : 0 < n) (hp : 0 < p) (spec : Spec (n + 1) (p + 1))
    (data : MergeData spec.core) : Spec (n + 1) (p + 1) :=
  OneEdgeSplitRefinement.splitSpec (mergedSpec hn hp spec data) (splitSlot hp data)
    (spec.length data.first.1) (spec.length data.second.1)
    (spec.length_pos _) (spec.length_pos _)

variable (hn : 0 < n) (hp : 0 < p) (spec : Spec (n + 1) (p + 1))

theorem splitTarget_tail_castSucc (data : MergeData spec.core) (e : Fin p) :
    (splitTarget hn hp spec data).core.tail (Fin.castSucc e)
      = Fin.castSucc ((mergedCore hn hp data).tail e) := by
  simp [splitTarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
    OneEdgeSplitRefinement.oldVertex]

theorem splitTarget_tail_last (data : MergeData spec.core) :
    (splitTarget hn hp spec data).core.tail (Fin.last p) = Fin.last n := by
  simp [splitTarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
    OneEdgeSplitRefinement.splitVertex]

theorem splitTarget_head_castSucc (data : MergeData spec.core) (e : Fin p) :
    (splitTarget hn hp spec data).core.head (Fin.castSucc e)
      = if e = splitSlot hp data then Fin.last n
        else Fin.castSucc ((mergedCore hn hp data).head e) := by
  simp [splitTarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
    OneEdgeSplitRefinement.oldVertex, OneEdgeSplitRefinement.splitVertex]

theorem splitTarget_head_last (data : MergeData spec.core) :
    (splitTarget hn hp spec data).core.head (Fin.last p)
      = Fin.castSucc ((mergedCore hn hp data).head (splitSlot hp data)) := by
  simp [splitTarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
    OneEdgeSplitRefinement.oldVertex]

theorem splitTarget_length_castSucc (data : MergeData spec.core) (e : Fin p) :
    (splitTarget hn hp spec data).length (Fin.castSucc e)
      = if e = splitSlot hp data then spec.length data.first.1
        else (mergedSpec hn hp spec data).length e := by
  simp [splitTarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitLength]

theorem splitTarget_length_last (data : MergeData spec.core) :
    (splitTarget hn hp spec data).length (Fin.last p) = spec.length data.second.1 := by
  simp [splitTarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitLength]

/-- **`spec` is a relabeling of the canonical split of its merge.**  The
vertex permutation moves the suppressed vertex to the last index, the slot
permutation moves the second suppressed slot to the last index, and `rev`
records which slot occurrences run the other way. -/
def mergeRelabeling (data : MergeData spec.core) :
    spec.Relabeling (splitTarget hn hp spec data) where
  coreEquiv := vSwap data
  slotEquiv := sSwap data
  reversed := rev data
  length_eq := by
    intro E
    by_cases h2 : E = data.second.1
    · subst h2
      rw [sSwap_second, splitTarget_length_last]
    · by_cases h1 : E = data.first.1
      · subst h1
        rw [← castSucc_smap hp data h2, splitTarget_length_castSucc]
        simp [splitSlot]
      · rw [← castSucc_smap hp data h2, splitTarget_length_castSucc,
          if_neg (fun h => h1 ((smap_eq_splitSlot_iff hp data h2).mp h)),
          mergedSpec_length_of_ne hn hp spec data
            (fun h => h1 ((smap_eq_splitSlot_iff hp data h2).mp h)),
          pre_smap hp data h2]
  tail_eq := by
    intro E
    by_cases h2 : E = data.second.1
    · subst h2
      rw [sSwap_second, splitTarget_tail_last]
      exact (secondPair spec.core_loopless data).1.symm
    · by_cases h1 : E = data.first.1
      · subst h1
        rw [← castSucc_smap hp data h2, splitTarget_tail_castSucc]
        have hsplit : smap hp data data.first.1 = splitSlot hp data := rfl
        rw [hsplit, mergedCore_tail_split,
          castSucc_vmap hn data (farFirst_ne_vertex spec.core_loopless data)]
        exact (firstPair spec.core_loopless data).1.symm
      · have hne : smap hp data E ≠ splitSlot hp data :=
          fun h => h1 ((smap_eq_splitSlot_iff hp data h2).mp h)
        rw [← castSucc_smap hp data h2, splitTarget_tail_castSucc,
          mergedCore_tail_of_ne hn hp data hne, pre_smap hp data h2,
          castSucc_vmap hn data (avoid spec.core_loopless data h1 h2).1,
          rev_of_avoid spec.core_loopless data h1 h2]
        simp
  head_eq := by
    intro E
    by_cases h2 : E = data.second.1
    · subst h2
      rw [sSwap_second, splitTarget_head_last, mergedCore_head_split,
        castSucc_vmap hn data (farSecond_ne_vertex spec.core_loopless data)]
      exact (secondPair spec.core_loopless data).2.symm
    · by_cases h1 : E = data.first.1
      · subst h1
        rw [← castSucc_smap hp data h2, splitTarget_head_castSucc]
        have hsplit : smap hp data data.first.1 = splitSlot hp data := rfl
        rw [hsplit, if_pos rfl]
        exact (firstPair spec.core_loopless data).2.symm
      · have hne : smap hp data E ≠ splitSlot hp data :=
          fun h => h1 ((smap_eq_splitSlot_iff hp data h2).mp h)
        rw [← castSucc_smap hp data h2, splitTarget_head_castSucc, if_neg hne,
          mergedCore_head_of_ne hn hp data hne, pre_smap hp data h2,
          castSucc_vmap hn data (avoid spec.core_loopless data h1 h2).2,
          rev_of_avoid spec.core_loopless data h1 h2]
        simp


/-! ### Transport across the merge -/

theorem spec_eq {m q : ℕ} {s t : Spec m q} (hc : s.core = t.core) (hl : s.length = t.length) :
    s = t := by
  cases s
  cases t
  cases hc
  cases hl
  rfl

/-- **Suppressing a bivalent vertex preserves the subdivided graph.**  This is
`PseudocorePresentation.exists_merge` with the merged specification named, so
that it can be compared with its own uniform refinements. -/
theorem mergedSpec_laplacianEquiv (data : MergeData spec.core) :
    Nonempty (LaplacianEquiv spec.graph (mergedSpec hn hp spec data).graph) :=
  ⟨(Spec.laplacianEquiv spec (splitTarget hn hp spec data)
      (mergeRelabeling hn hp spec data)).trans
    (OneEdgeSplitRefinement.canonicalSplitLaplacianEquiv (mergedSpec hn hp spec data)
      (splitSlot hp data) (spec.length data.first.1) (spec.length data.second.1)
      (spec.length_pos _) (spec.length_pos _) (by simp)).symm⟩

/-- **The merge commutes with uniform refinement.**  Both sides concatenate the
same two slots; the lengths agree because `k * (L₁ + L₂) = k * L₁ + k * L₂`. -/
theorem mergedSpec_scale (data : MergeData spec.core) (k : ℕ) (hk : 0 < k) :
    (mergedSpec hn hp spec data).scale k hk = mergedSpec hn hp (spec.scale k hk) data := by
  refine spec_eq rfl ?_
  funext e
  by_cases he : e = splitSlot hp data
  · simp [Spec.scale, mergedSpec, he, Nat.mul_add]
  · simp [Spec.scale, mergedSpec, he]

theorem bnExists_mergedSpec (data : MergeData spec.core) (r d : ℤ) :
    BNExists (mergedSpec hn hp spec data).graph r d ↔ BNExists spec.graph r d := by
  obtain ⟨equivalence⟩ := mergedSpec_laplacianEquiv hn hp spec data
  exact (equivalence.bnExists_iff r d).symm

theorem bnExists_mergedSpec_scale (data : MergeData spec.core) (k : ℕ) (hk : 0 < k) (r d : ℤ) :
    BNExists ((mergedSpec hn hp spec data).scale k hk).graph r d ↔
      BNExists (spec.scale k hk).graph r d := by
  rw [mergedSpec_scale hn hp spec data k hk]
  exact bnExists_mergedSpec hn hp (spec.scale k hk) data r d

theorem mergedSpec_coreConnected (data : MergeData spec.core) (hConn : spec.core.Connected) :
    (mergedSpec hn hp spec data).core.Connected := by
  obtain ⟨equivalence⟩ := mergedSpec_laplacianEquiv hn hp spec data
  exact core_connected_of_graph_connected _
    (equivalence.graphConnected (spec.graph_connected_of_coreConnected hConn))


/-! ### Suppression preserves bridgelessness -/

/-- **Bivalent suppression preserves bridgelessness.**  A bridge of the merged
core is a bridge of the original: the cut is pulled back by putting the
suppressed vertex on the side of the far end of its first slot.  If the merged
bridge is the concatenated slot, the original bridge is the second half;
otherwise it is the slot underlying the merged one. -/
theorem bridgeless_mergedCore (hn : 0 < n) (hp : 0 < p)
    (hL : ∀ e : Fin (p + 1), C.tail e ≠ C.head e) (data : MergeData C)
    (hB : Bridgeless C) : Bridgeless (mergedCore hn hp data) := by
  classical
  intro k hbridge
  obtain ⟨S, hTail, hHead, hOther⟩ := hbridge
  have haV : farEnd C data.first ≠ data.vertex := farFirst_ne_vertex hL data
  have hbV : farEnd C data.second ≠ data.vertex := farSecond_ne_vertex hL data
  set A : Finset (Fin (n + 1)) := Finset.univ.filter
    (fun u => if u = data.vertex then vmap hn data (farEnd C data.first) ∈ S
      else vmap hn data u ∈ S) with hAdef
  have hmemV : data.vertex ∈ A ↔ vmap hn data (farEnd C data.first) ∈ S := by
    simp [hAdef]
  have hmemU : ∀ u : Fin (n + 1), u ≠ data.vertex → (u ∈ A ↔ vmap hn data u ∈ S) := by
    intro u hu
    simp [hAdef, hu]
  have hCrossFirst : C.tail data.first.1 ∈ A ↔ C.head data.first.1 ∈ A := by
    rcases first_vertex data with ⟨hv, hf⟩ | ⟨hv, hf⟩
    · rw [hv, ← hf, hmemU _ haV, hmemV]
    · rw [hv, ← hf, hmemV, hmemU _ haV]
  have hGeneric : ∀ F : Fin (p + 1), F ≠ data.first.1 → F ≠ data.second.1 →
      smap hp data F ≠ k → (C.tail F ∈ A ↔ C.head F ∈ A) := by
    intro F h1 h2 h3
    obtain ⟨ht, hh⟩ := avoid hL data h1 h2
    have hne : smap hp data F ≠ splitSlot hp data :=
      fun h => h1 ((smap_eq_splitSlot_iff hp data h2).mp h)
    have hcross := hOther (smap hp data F) h3
    rw [mergedCore_tail_of_ne hn hp data hne, mergedCore_head_of_ne hn hp data hne,
      pre_smap hp data h2] at hcross
    rw [hmemU _ ht, hmemU _ hh]
    exact hcross
  by_cases hk : k = splitSlot hp data
  · subst hk
    rw [mergedCore_tail_split] at hTail
    rw [mergedCore_head_split] at hHead
    rcases second_vertex data with ⟨hv, hf⟩ | ⟨hv, hf⟩
    · refine hB data.second.1 ⟨Aᶜ, ?_, ?_, ?_⟩
      · rw [← hf, Finset.mem_compl, hmemU _ hbV]
        exact hHead
      · rw [hv, Finset.mem_compl, not_not, hmemV]
        exact hTail
      · intro F hF
        simp only [Finset.mem_compl]
        by_cases h1 : F = data.first.1
        · subst h1
          exact not_congr hCrossFirst
        · exact not_congr (hGeneric F h1 hF
            (fun h => h1 ((smap_eq_splitSlot_iff hp data hF).mp h)))
    · refine hB data.second.1 ⟨A, ?_, ?_, ?_⟩
      · rw [hv, hmemV]
        exact hTail
      · rw [← hf, hmemU _ hbV]
        exact hHead
      · intro F hF
        by_cases h1 : F = data.first.1
        · subst h1
          exact hCrossFirst
        · exact hGeneric F h1 hF (fun h => h1 ((smap_eq_splitSlot_iff hp data hF).mp h))
  · have hE1 : pre data k ≠ data.first.1 := pre_ne_first hp data hk
    have hE2 : pre data k ≠ data.second.1 := pre_ne_second data k
    obtain ⟨ht, hh⟩ := avoid hL data hE1 hE2
    have hsplitNe : splitSlot hp data ≠ k := fun h => hk h.symm
    have hab : vmap hn data (farEnd C data.first) ∈ S ↔
        vmap hn data (farEnd C data.second) ∈ S := by
      have hcross := hOther (splitSlot hp data) hsplitNe
      rwa [mergedCore_tail_split, mergedCore_head_split] at hcross
    have hCrossSecond : C.tail data.second.1 ∈ A ↔ C.head data.second.1 ∈ A := by
      rcases second_vertex data with ⟨hv, hf⟩ | ⟨hv, hf⟩
      · rw [hv, ← hf, hmemU _ hbV, hmemV, hab]
      · rw [hv, ← hf, hmemV, hmemU _ hbV, hab]
    refine hB (pre data k) ⟨A, ?_, ?_, ?_⟩
    · rw [hmemU _ ht]
      rw [mergedCore_tail_of_ne hn hp data hk] at hTail
      exact hTail
    · rw [hmemU _ hh]
      rw [mergedCore_head_of_ne hn hp data hk] at hHead
      exact hHead
    · intro F hF
      by_cases h1 : F = data.first.1
      · subst h1
        exact hCrossFirst
      · by_cases h2 : F = data.second.1
        · subst h2
          exact hCrossSecond
        · refine hGeneric F h1 h2 ?_
          intro h
          exact hF (by rw [← h, pre_smap hp data h2])


end Merge

/-! ## 3.  Iterated suppression -/

/-- **Bivalent suppression, iterated, with every invariant carried.**  Every
connected bridgeless specification presents its graph over a **reduced**
connected bridgeless core of the same genus, with an explicit Laplacian
equivalence of graphs — on the specification and on every uniform refinement.
This is `PseudocorePresentation.exists_reduced` with the bridgelessness of §2
and the scale compatibility of `mergedSpec_scale`; the latter is what
`exists_reduced` cannot supply, because it never names the merged
specification. -/
theorem exists_reducedSpec : ∀ n : ℕ, ∀ (p : ℕ) (spec : Spec n p),
    spec.core.Connected → Bridgeless spec.core →
    ∃ (n' p' : ℕ) (spec' : Spec n' p'),
      Reduced spec'.core ∧ spec'.core.Connected ∧ Bridgeless spec'.core ∧
      (p' : ℤ) - n' = (p : ℤ) - n ∧
      Nonempty (LaplacianEquiv spec'.graph spec.graph) ∧
      (∀ (k : ℕ) (hk : 0 < k),
        Nonempty (LaplacianEquiv (spec'.scale k hk).graph (spec.scale k hk).graph)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p spec hConn hB
    by_cases hEmpty : Reduced spec.core
    · exact ⟨n, p, spec, hEmpty, hConn, hB, rfl, ⟨⟨Equiv.refl _, fun _ _ => rfl⟩⟩,
        fun _ _ => ⟨⟨Equiv.refl _, fun _ _ => rfl⟩⟩⟩
    · rw [Reduced, not_isEmpty_iff] at hEmpty
      obtain ⟨data⟩ := hEmpty
      have hVertexBound : 2 ≤ n := by
        have hNe : (farEnd spec.core data.first).val ≠ (farEnd spec.core data.second).val :=
          fun h => data.far_ne (Fin.ext h)
        have h1 := (farEnd spec.core data.first).isLt
        have h2 := (farEnd spec.core data.second).isLt
        omega
      have hSlotBound : 2 ≤ p := by
        have hNe : (data.first.1).val ≠ (data.second.1).val := fun h => data.slots_ne (Fin.ext h)
        have h1 := (data.first.1).isLt
        have h2 := (data.second.1).isLt
        omega
      obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
      obtain ⟨p₀, rfl⟩ : ∃ p₀, p = p₀ + 1 := ⟨p - 1, by omega⟩
      have hn : 0 < n₀ := by omega
      have hp : 0 < p₀ := by omega
      obtain ⟨n', p', spec', h1, h2, h3, h4, h5, h6⟩ :=
        ih n₀ (by omega) p₀ (mergedSpec hn hp spec data)
          (mergedSpec_coreConnected hn hp spec data hConn)
          (bridgeless_mergedCore hn hp spec.core_loopless data hB)
      refine ⟨n', p', spec', h1, h2, h3, ?_, ?_, ?_⟩
      · push_cast at h4 ⊢
        omega
      · obtain ⟨e1⟩ := h5
        obtain ⟨e2⟩ := mergedSpec_laplacianEquiv hn hp spec data
        exact ⟨e1.trans e2.symm⟩
      · intro k hk
        obtain ⟨e1⟩ := h6 k hk
        obtain ⟨e2⟩ := mergedSpec_laplacianEquiv hn hp (spec.scale k hk) data
        rw [mergedSpec_scale hn hp spec data k hk] at e1
        exact ⟨e1.trans e2.symm⟩

/-! ## 4.  Slot pairs at a bivalent vertex -/

section Pairs

variable {N P : ℕ}

/-- The slots incident to a core vertex, counted without orientation. -/
def incidentSlots (C : Core N P) (w : Fin N) : Finset (Fin P) :=
  Finset.univ.filter fun e => C.tail e = w ∨ C.head e = w

theorem mem_incidentSlots (C : Core N P) (w : Fin N) (e : Fin P) :
    e ∈ incidentSlots C w ↔ (C.tail e = w ∨ C.head e = w) := by
  simp [incidentSlots]

theorem card_incidentSlots_eq (C : Core N P)
    (hLoop : ∀ e : Fin P, C.tail e ≠ C.head e) (w : Fin N) :
    (incidentSlots C w).card = slotValence C w :=
  card_incidentSlots C hLoop w

/-- The other slot at a bivalent vertex; `j` itself when there is none. -/
def otherSlot (C : Core N P) (j : Fin P) (w : Fin N) : Fin P :=
  if h : ((incidentSlots C w).erase j).Nonempty then ((incidentSlots C w).erase j).min' h
  else j

/-- `j` is the lower of the two slots at `w`. -/
def isLo (C : Core N P) (j : Fin P) (w : Fin N) : Bool := decide (j ≤ otherSlot C j w)

variable {C : Core N P} {w : Fin N}

theorem otherSlot_spec (hcard : (incidentSlots C w).card = 2) {j : Fin P}
    (hj : j ∈ incidentSlots C w) :
    otherSlot C j w ∈ incidentSlots C w ∧ otherSlot C j w ≠ j ∧
      ∀ j' ∈ incidentSlots C w, j' = j ∨ j' = otherSlot C j w := by
  classical
  have herase : ((incidentSlots C w).erase j).card = 1 := by
    rw [Finset.card_erase_of_mem hj, hcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp herase
  have hzmem : z ∈ (incidentSlots C w).erase j := by rw [hz]; simp
  have hne : ((incidentSlots C w).erase j).Nonempty := ⟨z, hzmem⟩
  have hmem : otherSlot C j w ∈ (incidentSlots C w).erase j := by
    rw [otherSlot, dif_pos hne]
    exact Finset.min'_mem _ _
  have hos : otherSlot C j w = z := by
    rw [hz, Finset.mem_singleton] at hmem
    exact hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [hos]
    exact Finset.mem_of_mem_erase hzmem
  · rw [hos]
    exact Finset.ne_of_mem_erase hzmem
  · intro j' hj'
    by_cases h : j' = j
    · exact Or.inl h
    · right
      have hj'e : j' ∈ (incidentSlots C w).erase j := Finset.mem_erase.mpr ⟨h, hj'⟩
      rw [hz, Finset.mem_singleton] at hj'e
      rw [hj'e, hos]

theorem otherSlot_mem (hcard : (incidentSlots C w).card = 2) {j : Fin P}
    (hj : j ∈ incidentSlots C w) : otherSlot C j w ∈ incidentSlots C w :=
  (otherSlot_spec hcard hj).1

theorem otherSlot_ne (hcard : (incidentSlots C w).card = 2) {j : Fin P}
    (hj : j ∈ incidentSlots C w) : otherSlot C j w ≠ j :=
  (otherSlot_spec hcard hj).2.1

theorem eq_or_eq_otherSlot (hcard : (incidentSlots C w).card = 2) {j : Fin P}
    (hj : j ∈ incidentSlots C w) {j' : Fin P} (hj' : j' ∈ incidentSlots C w) :
    j' = j ∨ j' = otherSlot C j w :=
  (otherSlot_spec hcard hj).2.2 j' hj'

theorem otherSlot_otherSlot (hcard : (incidentSlots C w).card = 2) {j : Fin P}
    (hj : j ∈ incidentSlots C w) : otherSlot C (otherSlot C j w) w = j := by
  have hmem := otherSlot_mem hcard hj
  have hne := otherSlot_ne hcard hmem
  rcases eq_or_eq_otherSlot hcard hj (otherSlot_mem hcard hmem) with h | h
  · exact h
  · exact absurd h hne

theorem isLo_otherSlot (hcard : (incidentSlots C w).card = 2) {j : Fin P}
    (hj : j ∈ incidentSlots C w) :
    isLo C (otherSlot C j w) w = true ↔ isLo C j w = false := by
  have hne : otherSlot C j w ≠ j := otherSlot_ne hcard hj
  simp only [isLo, otherSlot_otherSlot hcard hj, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · intro h hj'
    exact hne (le_antisymm h hj')
  · intro h
    exact le_of_not_ge h

end Pairs


/-! ## 5.  The marking of a reduced core -/

section Shape

variable {N P : ℕ} {spec : Spec N P} (shape : MarkedShape spec)

/-- **The reorientation step.**  The `MarkedShape` of `Utilities` only records
that the two slots at a marker run to a common partner; `Marking` additionally demands
that exactly one of them has its *head* at the marker.  `markerRev` reverses
whichever of the two occurrences points the wrong way: the lower-indexed slot
is made to point into the marker, the higher one out of it. -/
def markerRev (j : Fin P) : Bool :=
  (shape.isMarker (spec.core.tail j) && isLo spec.core j (spec.core.tail j)) ||
    (shape.isMarker (spec.core.head j) && !isLo spec.core j (spec.core.head j))

/-- The reoriented specification: the same graph, the same core up to slot
orientation, but now carrying a `Marking`. -/
def orientedSpec : Spec N P := reverseSpec spec (markerRev shape)

theorem orientedSpec_core :
    (orientedSpec shape).core = reverseCore spec.core (markerRev shape) := rfl

theorem marker_card {w : Fin N} (hw : shape.isMarker w = true) :
    (incidentSlots spec.core w).card = 2 := by
  rw [card_incidentSlots_eq spec.core spec.core_loopless w]
  exact shape.marker_slotValence w hw

theorem mem_incidentSlots_of_head {j : Fin P} {w : Fin N}
    (h : (orientedSpec shape).core.head j = w) : j ∈ incidentSlots spec.core w := by
  rw [mem_incidentSlots]
  have hh : (if markerRev shape j then spec.core.tail j else spec.core.head j) = w := h
  by_cases hr : markerRev shape j = true
  · rw [if_pos hr] at hh
    exact Or.inl hh
  · rw [if_neg hr] at hh
    exact Or.inr hh

theorem mem_incidentSlots_of_tail {j : Fin P} {w : Fin N}
    (h : (orientedSpec shape).core.tail j = w) : j ∈ incidentSlots spec.core w := by
  rw [mem_incidentSlots]
  have hh : (if markerRev shape j then spec.core.head j else spec.core.tail j) = w := h
  by_cases hr : markerRev shape j = true
  · rw [if_pos hr] at hh
    exact Or.inr hh
  · rw [if_neg hr] at hh
    exact Or.inl hh

theorem oriented_of_isLo {w : Fin N} (hw : shape.isMarker w = true) {j : Fin P}
    (hj : j ∈ incidentSlots spec.core w) (hlo : isLo spec.core j w = true) :
    (orientedSpec shape).core.head j = w ∧
      (orientedSpec shape).core.tail j = shape.partner w := by
  have hpb := shape.partner_base w hw
  rw [mem_incidentSlots] at hj
  rcases hj with ht | hh
  · have hh : spec.core.head j = shape.partner w := shape.head_eq_partner w hw j ht
    have hrev : markerRev shape j = true := by simp [markerRev, ht, hh, hw, hpb, hlo]
    constructor
    · show (if markerRev shape j then spec.core.tail j else spec.core.head j) = w
      rw [if_pos hrev, ht]
    · show (if markerRev shape j then spec.core.head j else spec.core.tail j) = shape.partner w
      rw [if_pos hrev, hh]
  · have ht : spec.core.tail j = shape.partner w := shape.tail_eq_partner w hw j hh
    have hrev : markerRev shape j = false := by simp [markerRev, ht, hh, hw, hpb, hlo]
    constructor
    · show (if markerRev shape j then spec.core.tail j else spec.core.head j) = w
      rw [if_neg (by rw [hrev]; simp), hh]
    · show (if markerRev shape j then spec.core.head j else spec.core.tail j) = shape.partner w
      rw [if_neg (by rw [hrev]; simp), ht]

theorem oriented_of_not_isLo {w : Fin N} (hw : shape.isMarker w = true) {j : Fin P}
    (hj : j ∈ incidentSlots spec.core w) (hlo : isLo spec.core j w = false) :
    (orientedSpec shape).core.tail j = w ∧
      (orientedSpec shape).core.head j = shape.partner w := by
  have hpb := shape.partner_base w hw
  rw [mem_incidentSlots] at hj
  rcases hj with ht | hh
  · have hh : spec.core.head j = shape.partner w := shape.head_eq_partner w hw j ht
    have hrev : markerRev shape j = false := by simp [markerRev, ht, hh, hw, hpb, hlo]
    constructor
    · show (if markerRev shape j then spec.core.head j else spec.core.tail j) = w
      rw [if_neg (by rw [hrev]; simp), ht]
    · show (if markerRev shape j then spec.core.tail j else spec.core.head j) = shape.partner w
      rw [if_neg (by rw [hrev]; simp), hh]
  · have ht : spec.core.tail j = shape.partner w := shape.tail_eq_partner w hw j hh
    have hrev : markerRev shape j = true := by simp [markerRev, ht, hh, hw, hpb, hlo]
    constructor
    · show (if markerRev shape j then spec.core.head j else spec.core.tail j) = w
      rw [if_pos hrev, hh]
    · show (if markerRev shape j then spec.core.tail j else spec.core.head j) = shape.partner w
      rw [if_pos hrev, ht]

/-- The outgoing half of a loop: the slot whose head is a marker and which is
the lower of the two slots there. -/
def orientedFirst (j : Fin P) : Bool :=
  shape.isMarker ((orientedSpec shape).core.head j) &&
    isLo spec.core j ((orientedSpec shape).core.head j)

/-- The returning half of a loop. -/
def orientedSecond (j : Fin P) : Bool :=
  shape.isMarker ((orientedSpec shape).core.tail j) &&
    !isLo spec.core j ((orientedSpec shape).core.tail j)

/-- The partner half of a loop. -/
def orientedMate (j : Fin P) : Fin P :=
  otherSlot spec.core j
    (if shape.isMarker ((orientedSpec shape).core.head j) then (orientedSpec shape).core.head j
      else (orientedSpec shape).core.tail j)


theorem first_bundle {j : Fin P} (hj : orientedFirst shape j = true) :
    shape.isMarker ((orientedSpec shape).core.head j) = true ∧
    (orientedSpec shape).core.tail j = shape.partner ((orientedSpec shape).core.head j) ∧
    (orientedSpec shape).core.tail (orientedMate shape j) = (orientedSpec shape).core.head j ∧
    (orientedSpec shape).core.head (orientedMate shape j) =
      shape.partner ((orientedSpec shape).core.head j) ∧
    orientedMate shape (orientedMate shape j) = j ∧
    orientedSecond shape (orientedMate shape j) = true ∧
    orientedSecond shape j = false ∧
    (∀ j' : Fin P, (orientedSpec shape).core.head j' = (orientedSpec shape).core.head j →
      j' = j) ∧
    (∀ j' : Fin P, (orientedSpec shape).core.tail j' = (orientedSpec shape).core.head j →
      j' = orientedMate shape j) := by
  rw [orientedFirst, Bool.and_eq_true] at hj
  obtain ⟨hw, hlo⟩ := hj
  set w := (orientedSpec shape).core.head j with hwdef
  have hjmem : j ∈ incidentSlots spec.core w := mem_incidentSlots_of_head shape rfl
  have hcard := marker_card shape hw
  have hmate : orientedMate shape j = otherSlot spec.core j w := by
    rw [orientedMate, ← hwdef, if_pos hw]
  set m := otherSlot spec.core j w with hmdef
  have hmmem : m ∈ incidentSlots spec.core w := otherSlot_mem hcard hjmem
  have hmlo : isLo spec.core m w = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hcon := (isLo_otherSlot hcard hjmem).mp hc
    rw [hlo] at hcon
    exact Bool.noConfusion hcon
  obtain ⟨-, hjtail⟩ := oriented_of_isLo shape hw hjmem hlo
  obtain ⟨hmtail, hmhead⟩ := oriented_of_not_isLo shape hw hmmem hmlo
  have hpne : shape.partner w ≠ w := shape.partner_ne w hw
  have hpb : shape.isMarker (shape.partner w) = false := shape.partner_base w hw
  have hmate_m : orientedMate shape m = j := by
    rw [orientedMate, hmhead, if_neg (by rw [hpb]; simp), hmtail]
    exact otherSlot_otherSlot hcard hjmem
  have hsecond_m : orientedSecond shape m = true := by
    rw [orientedSecond, hmtail, hw, hmlo]
    simp
  have hsecond_j : orientedSecond shape j = false := by
    rw [orientedSecond, hjtail, hpb]
    simp
  have huniqueHead : ∀ j' : Fin P, (orientedSpec shape).core.head j' = w → j' = j := by
    intro j' h'
    rcases eq_or_eq_otherSlot hcard hjmem (mem_incidentSlots_of_head shape h') with h | h
    · exact h
    · rw [h, hmhead] at h'
      exact absurd h' hpne
  have huniqueTail : ∀ j' : Fin P, (orientedSpec shape).core.tail j' = w → j' = m := by
    intro j' h'
    rcases eq_or_eq_otherSlot hcard hjmem (mem_incidentSlots_of_tail shape h') with h | h
    · rw [h, hjtail] at h'
      exact absurd h' hpne
    · exact h
  refine ⟨hw, hjtail, ?_, ?_, ?_, ?_, hsecond_j, huniqueHead, ?_⟩
  · rw [hmate]; exact hmtail
  · rw [hmate]; exact hmhead
  · rw [hmate]; exact hmate_m
  · rw [hmate]; exact hsecond_m
  · simp only [hmate]; exact huniqueTail

theorem second_bundle {j : Fin P} (hj : orientedSecond shape j = true) :
    orientedFirst shape (orientedMate shape j) = true ∧
      orientedMate shape (orientedMate shape j) = j := by
  rw [orientedSecond, Bool.and_eq_true] at hj
  obtain ⟨hw, hnlo⟩ := hj
  set w := (orientedSpec shape).core.tail j with hwdef
  have hlo : isLo spec.core j w = false := by simpa using hnlo
  have hjmem : j ∈ incidentSlots spec.core w := mem_incidentSlots_of_tail shape rfl
  have hcard := marker_card shape hw
  have hpb : shape.isMarker (shape.partner w) = false := shape.partner_base w hw
  obtain ⟨hjtail, hjhead⟩ := oriented_of_not_isLo shape hw hjmem hlo
  have hmate : orientedMate shape j = otherSlot spec.core j w := by
    rw [orientedMate, hjhead, if_neg (by rw [hpb]; simp), hjtail]
  set m := otherSlot spec.core j w with hmdef
  have hmmem : m ∈ incidentSlots spec.core w := otherSlot_mem hcard hjmem
  have hmlo : isLo spec.core m w = true := (isLo_otherSlot hcard hjmem).mpr hlo
  obtain ⟨hmhead, -⟩ := oriented_of_isLo shape hw hmmem hmlo
  have hfirst_m : orientedFirst shape m = true := by
    rw [orientedFirst, hmhead, hw, hmlo]
    simp
  have hmate_m : orientedMate shape m = j := by
    rw [orientedMate, hmhead, if_pos hw]
    exact otherSlot_otherSlot hcard hjmem
  exact ⟨by rw [hmate]; exact hfirst_m, by rw [hmate]; exact hmate_m⟩

/-- **The marking derived from a reduced core.**  Every marker of the
`MarkedShape` of `Utilities` carries exactly two slots to one stable partner;
after
`markerRev` the lower-indexed one has its head at the marker and the higher one
its tail, which is exactly `Marking`. -/
def orientedMarking : Marking (orientedSpec shape).core where
  first := orientedFirst shape
  second := orientedSecond shape
  mate := orientedMate shape
  second_of_first := fun _ hj => (first_bundle shape hj).2.2.2.2.2.1
  first_of_second := fun _ hj => (second_bundle shape hj).1
  mate_mate_first := fun _ hj => (first_bundle shape hj).2.2.2.2.1
  mate_mate_second := fun _ hj => (second_bundle shape hj).2
  second_eq_false := fun _ hj => (first_bundle shape hj).2.2.2.2.2.2.1
  tail_mate := fun _ hj => (first_bundle shape hj).2.2.1
  head_mate := fun _ hj => ((first_bundle shape hj).2.2.2.1).trans
    ((first_bundle shape hj).2.1).symm
  head_unique := fun _ hj => (first_bundle shape hj).2.2.2.2.2.2.2.1
  tail_unique := fun _ hj => (first_bundle shape hj).2.2.2.2.2.2.2.2

theorem orientedMarking_isMarker (w : Fin N) :
    (orientedMarking shape).IsMarker w ↔ shape.isMarker w = true := by
  constructor
  · rintro ⟨j, hj, hjw⟩
    have := (first_bundle shape hj).1
    rwa [hjw] at this
  · intro hw
    have hcard := marker_card shape hw
    have hne : (incidentSlots spec.core w).Nonempty := by
      rw [← Finset.card_pos, hcard]
      norm_num
    obtain ⟨j, hj⟩ := hne
    by_cases hlo : isLo spec.core j w = true
    · obtain ⟨hh, -⟩ := oriented_of_isLo shape hw hj hlo
      refine ⟨j, ?_, hh⟩
      show orientedFirst shape j = true
      rw [orientedFirst, hh, hw, hlo]
      simp
    · rw [Bool.not_eq_true] at hlo
      have hm := otherSlot_mem hcard hj
      have hmlo := (isLo_otherSlot hcard hj).mpr hlo
      obtain ⟨hh, -⟩ := oriented_of_isLo shape hw hm hmlo
      refine ⟨otherSlot spec.core j w, ?_, hh⟩
      show orientedFirst shape (otherSlot spec.core j w) = true
      rw [orientedFirst, hh, hw, hmlo]
      simp

theorem orientedMarking_base (w : Fin N) (h : ¬ (orientedMarking shape).IsMarker w) :
    3 ≤ slotValence (orientedSpec shape).core w := by
  have hw : shape.isMarker w = false := by
    cases hc : shape.isMarker w with
    | false => rfl
    | true => exact absurd ((orientedMarking_isMarker shape w).mpr hc) h
  have hval : slotValence (orientedSpec shape).core w = slotValence spec.core w :=
    slotValence_reverseCore spec.core (markerRev shape) w
  rw [hval]
  exact shape.base_stable w hw

end Shape


/-! ## 6.  Valence on a bridgeless core -/

section Valence

variable {n p : ℕ} {C : Core n p}

theorem two_le_card_vertices (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j) (hnp : n < p) :
    2 ≤ n := by
  by_contra h
  have hp : 0 < p := by omega
  interval_cases n
  · exact (C.tail ⟨0, hp⟩).elim0
  · exact hLoop ⟨0, hp⟩ (Subsingleton.elim _ _)

theorem two_le_slotValence (hn : 2 ≤ n) (hLoop : ∀ j : Fin p, C.tail j ≠ C.head j)
    (hConn : C.Connected) (hB : Bridgeless C) (w : Fin n) : 2 ≤ slotValence C w := by
  have h1 : slotValence C w ≠ 1 := leafless_of_bridgeless hLoop hB w
  have h0 : slotValence C w ≠ 0 := by
    intro h
    have hEnds : slotEnds C w = ∅ := Finset.card_eq_zero.mp h
    obtain ⟨u, hu⟩ : ∃ u : Fin n, u ≠ w := by
      by_cases hw : w.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro hc
        have hv := congrArg Fin.val hc
        simp only at hv
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro hc
        have hv := congrArg Fin.val hc
        simp only at hv
        omega
    obtain ⟨e, he⟩ := hConn {w} ⟨w, u, Finset.mem_singleton_self w, by simp [hu]⟩
    rcases he with ⟨h1', -⟩ | ⟨h1', -⟩
    · rw [Finset.mem_singleton] at h1'
      have hmem : (e, false) ∈ slotEnds C w := (mem_slotEnds_false e w).mpr h1'
      rw [hEnds] at hmem
      simp at hmem
    · rw [Finset.mem_singleton] at h1'
      have hmem : (e, true) ∈ slotEnds C w := (mem_slotEnds_true e w).mpr h1'
      rw [hEnds] at hmem
      simp at hmem
  omega

end Valence

/-! ## 7.  The stable model of an arbitrary connected specification -/

/-- **The `Marking` derived, not assumed — on a bridgeless specification.**
Bivalent suppression and the reorientation at the markers are both changes of
presentation, so the reduced representative is *Laplacian equivalent* to the
given specification, on the specification and on every uniform refinement. -/
theorem exists_markedSpec_of_bridgeless {n p : ℕ} (spec : Spec n p)
    (hConn : spec.core.Connected) (hB : Bridgeless spec.core) (hGenus : n < p) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀) (mk : Marking spec₀.core),
      (∀ w : Fin n₀, ¬ mk.IsMarker w → 3 ≤ slotValence spec₀.core w) ∧
        spec₀.core.Connected ∧ Bridgeless spec₀.core ∧ n₀ < p₀ ∧
        (p₀ : ℤ) - n₀ = (p : ℤ) - n ∧
        Nonempty (LaplacianEquiv spec₀.graph spec.graph) ∧
        (∀ (k : ℕ) (hk : 0 < k),
          Nonempty (LaplacianEquiv (spec₀.scale k hk).graph (spec.scale k hk).graph)) := by
  obtain ⟨n₂, p₂, spec₂, hred₂, hc₂, hb₂, hg, he, hes⟩ := exists_reducedSpec n p spec hConn hB
  have hlt : n₂ < p₂ := by
    have hpos : (0 : ℤ) < (p₂ : ℤ) - n₂ := by
      rw [hg]
      have : (n : ℤ) < p := by exact_mod_cast hGenus
      omega
    exact_mod_cast (by omega : (n₂ : ℤ) < p₂)
  have hn₂ : 2 ≤ n₂ := two_le_card_vertices spec₂.core_loopless hlt
  have hdeg : ∀ w : Fin n₂, 2 ≤ slotValence spec₂.core w :=
    fun w => two_le_slotValence hn₂ spec₂.core_loopless hc₂ hb₂ w
  have hgc₂ : graph_connected spec₂.graph := spec₂.graph_connected_of_coreConnected hc₂
  obtain ⟨shape⟩ : Nonempty (MarkedShape spec₂) := by
    refine exists_markedShapeAt (g := p₂ + 1 - n₂) spec₂ hred₂ hgc₂ ?_ ?_ hdeg
    · rw [Spec.genus_graph]
      have : (n₂ : ℤ) < p₂ := by exact_mod_cast hlt
      push_cast [Nat.cast_sub (by omega : n₂ ≤ p₂ + 1)]
      omega
    · omega
  refine ⟨n₂, p₂, orientedSpec shape, orientedMarking shape, orientedMarking_base shape,
    connected_reverseCore _ hc₂, bridgeless_reverseCore _ hb₂, hlt, hg, ?_, ?_⟩
  · obtain ⟨e⟩ := he
    exact ⟨(Spec.laplacianEquiv _ _ (reverseRelabeling spec₂ (markerRev shape))).symm.trans e⟩
  · intro k hk
    obtain ⟨e⟩ := hes k hk
    refine ⟨?_⟩
    rw [orientedSpec, reverseSpec_scale]
    exact (Spec.laplacianEquiv _ _
      (reverseRelabeling (spec₂.scale k hk) (markerRev shape))).symm.trans e

/-- **The `Marking` derived, not assumed.**  Every connected specification of
genus at least two is presented — after bridge contraction, bivalent
suppression and the reorientation at the markers — by a connected
**bridgeless** specification carrying a `Marking` whose non-marker vertices all
have slot valence at least three, with Brill--Noether existence unchanged in
every rank and degree and on every uniform refinement.  This is what
`StableModelReduction.exists_stableModel` takes as input, and would otherwise
have to be handed. -/
theorem exists_markedSpec {n p : ℕ} (spec : Spec n p) (hConn : spec.core.Connected)
    (hGenus : n < p) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀) (mk : Marking spec₀.core),
      (∀ w : Fin n₀, ¬ mk.IsMarker w → 3 ≤ slotValence spec₀.core w) ∧
        spec₀.core.Connected ∧ Bridgeless spec₀.core ∧ n₀ < p₀ ∧
        (p₀ : ℤ) - n₀ = (p : ℤ) - n ∧
        (∀ r d : ℤ, BNExists spec₀.graph r d ↔ BNExists spec.graph r d) ∧
        (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
          BNExists (spec₀.scale k hk).graph r d ↔ BNExists (spec.scale k hk).graph r d) := by
  obtain ⟨n₁, p₁, spec₁, hc₁, hb₁, -, hg₁, hbn₁, hbns₁, -, -⟩ := bridgeless_reduction spec hConn
  have hlt₁ : n₁ < p₁ := by
    have hpos : (0 : ℤ) < (p₁ : ℤ) - n₁ := by
      rw [hg₁]
      have : (n : ℤ) < p := by exact_mod_cast hGenus
      omega
    exact_mod_cast (by omega : (n₁ : ℤ) < p₁)
  obtain ⟨n₀, p₀, spec₀, mk, hbase, hc₀, hb₀, hlt₀, hg₀, ⟨e⟩, hes⟩ :=
    exists_markedSpec_of_bridgeless spec₁ hc₁ hb₁ hlt₁
  refine ⟨n₀, p₀, spec₀, mk, hbase, hc₀, hb₀, hlt₀, hg₀.trans hg₁, ?_, ?_⟩
  · exact fun r d => (e.bnExists_iff r d).trans (hbn₁ r d)
  · intro k hk r d
    obtain ⟨ek⟩ := hes k hk
    exact (ek.bnExists_iff r d).trans (hbns₁ k hk r d)

/-- **On a bridgeless specification the certificate lands on the specification
itself.**  Bivalent suppression and the reorientation at the markers are
Laplacian equivalences, so the `GraphContractionCertificate` produced by
`StableModelReduction.exists_stableModel` on the reduced representative can be
carried back to `spec` by
`GraphContractionCertificate.postcomposeLaplacianEquiv`, `TopologicalValid` and
all.  **Bridge contraction is the only step that cannot be carried back**: it
changes the graph, and its pencil transport
(`SpecBridge.bnExists_contractBridge_iff`) is an equivalence of Brill--Noether
existence, not a contraction certificate. -/
theorem exists_cubicModel_of_bridgeless {n p : ℕ} (spec : Spec n p)
    (hConn : spec.core.Connected) (hB : Bridgeless spec.core) (hGenus : n < p) :
    ∃ (n' p' : ℕ) (spec' : Spec n' p')
      (c : GraphContractionCertificate spec'.graph spec.graph),
      2 * p' = 3 * n' ∧ (p' : ℤ) - n' = (p : ℤ) - n ∧
        spec'.core.Cubic ∧ spec'.core.Connected ∧ c.TopologicalValid := by
  obtain ⟨n₀, p₀, spec₀, mk, hbase, hc₀, hb₀, hlt₀, hg₀, ⟨e⟩, -⟩ :=
    exists_markedSpec_of_bridgeless spec hConn hB hGenus
  have hstable : Stable mk := stable_of_bridgeless mk spec₀.core_loopless hbase hb₀
  obtain ⟨n', p', spec', c, h1, h2, h3, h4, h5⟩ :=
    exists_stableModel spec₀ mk hstable hc₀ hlt₀
  refine ⟨n', p', spec', c.postcomposeLaplacianEquiv e, h1, ?_, h3, h4,
    GraphContractionCertificate.topologicalValid_postcomposeLaplacianEquiv c e h5⟩
  have hn'p' : n' ≤ p' := by omega
  have h2' : p' + 1 - n' = p₀ + 1 - n₀ := h2
  have hg' : (p' : ℤ) - n' = (p₀ : ℤ) - n₀ := by omega
  rw [hg', hg₀]

/-- **The cubic stable model.**  Every connected specification of genus at least
two has a
**cubic** stable model, with no `Marking` and no `Stable` hypothesis taken as
input.

The reduced representative `spec₀` is reached in three moves — contract every
bridge (`BridgeReduction.bridgeless_reduction`), suppress every bivalent core
vertex (`exists_reducedSpec`), reorient the slots at every marker
(`orientedSpec`) — and Brill--Noether existence agrees with the original
specification in every rank and degree, on the specification itself and on
every uniform refinement, so the regular-subdivision gonalities agree too.
The cubic model `spec'` carries the `TopologicalValid`
`GraphContractionCertificate` onto `spec₀` along which a pencil is transported
back. -/
theorem exists_cubicModel {n p : ℕ} (spec : Spec n p) (hConn : spec.core.Connected)
    (hGenus : n < p) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀) (n' p' : ℕ) (spec' : Spec n' p')
      (c : GraphContractionCertificate spec'.graph spec₀.graph),
      2 * p' = 3 * n' ∧ (p' : ℤ) - n' = (p : ℤ) - n ∧
        spec'.core.Cubic ∧ spec'.core.Connected ∧ c.TopologicalValid ∧
        spec₀.core.Connected ∧ (p₀ : ℤ) - n₀ = (p : ℤ) - n ∧
        (∀ r d : ℤ, BNExists spec₀.graph r d ↔ BNExists spec.graph r d) ∧
        (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
          BNExists (spec₀.scale k hk).graph r d ↔ BNExists (spec.scale k hk).graph r d) ∧
        spec₀.regularSubdivisionGonality = spec.regularSubdivisionGonality := by
  obtain ⟨n₀, p₀, spec₀, mk, hbase, hc₀, hb₀, hlt₀, hg₀, hbn₀, hbns₀⟩ :=
    exists_markedSpec spec hConn hGenus
  have hstable : Stable mk := stable_of_bridgeless mk spec₀.core_loopless hbase hb₀
  obtain ⟨n', p', spec', c, h1, h2, h3, h4, h5⟩ :=
    exists_stableModel spec₀ mk hstable hc₀ hlt₀
  refine ⟨n₀, p₀, spec₀, n', p', spec', c, h1, ?_, h3, h4, h5, hc₀, hg₀, hbn₀, hbns₀, ?_⟩
  · have hn'p' : n' ≤ p' := by omega
    have h2' : p' + 1 - n' = p₀ + 1 - n₀ := h2
    have hg' : (p' : ℤ) - n' = (p₀ : ℤ) - n₀ := by omega
    rw [hg', hg₀]
  · exact regularSubdivisionGonality_eq_of_iff spec₀ spec hc₀ hConn (fun k hk d => hbns₀ k hk 1 d)

/-- **The size of the stable model is forced**, and it is the size
`StableModelReduction.dimension_forced` reads off the certified payload: the
two clauses `2 p' = 3 n'` and `p' - n' = g - 1` of `exists_cubicModel` give
`n' = 2 (g - 1)` and `p' = 3 (g - 1)`, the vertex and edge counts of a cubic
graph of genus `g`. -/
theorem cubicModel_size {n' p' : ℕ} (hCount : 2 * p' = 3 * n') {m : ℤ}
    (hGenus : (p' : ℤ) - n' = m) : (p' : ℤ) = 3 * m ∧ (n' : ℤ) = 2 * m := by
  omega

/-- **The cubic stable model, in graph form**: graph connectivity in and out,
the even-genus hypothesis, the edge count `2 p' = 3 n'` that
`StableModelReduction.dimension_forced` pins, the genus on the nose, and the
`TopologicalValid` contraction certificate together with the Brill--Noether
transport along which a pencil is carried back. -/
theorem exists_cubicModel_graph {n p : ℕ} (spec : Spec n p)
    (hConn : graph_connected spec.graph) (hGenus : 6 ≤ p + 1 - n) :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀) (n' p' : ℕ) (spec' : Spec n' p')
      (c : GraphContractionCertificate spec'.graph spec₀.graph),
      2 * p' = 3 * n' ∧ p' + 1 - n' = p + 1 - n ∧ graph_connected spec'.graph ∧
        spec'.core.Cubic ∧ c.TopologicalValid ∧
        graph_connected spec₀.graph ∧ p₀ + 1 - n₀ = p + 1 - n ∧
        (∀ r d : ℤ, BNExists spec₀.graph r d ↔ BNExists spec.graph r d) ∧
        (∀ (k : ℕ) (hk : 0 < k) (r d : ℤ),
          BNExists (spec₀.scale k hk).graph r d ↔ BNExists (spec.scale k hk).graph r d) ∧
        spec₀.regularSubdivisionGonality = spec.regularSubdivisionGonality := by
  have hlt : n < p := by omega
  obtain ⟨n₀, p₀, spec₀, n', p', spec', c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    exists_cubicModel spec (core_connected_of_graph_connected spec hConn) hlt
  have hn'p' : n' ≤ p' := by omega
  have hn₀p₀ : n₀ ≤ p₀ := by
    have : (0 : ℤ) ≤ (p₀ : ℤ) - n₀ := by
      rw [h7]
      have : (n : ℤ) < p := by exact_mod_cast hlt
      omega
    omega
  refine ⟨n₀, p₀, spec₀, n', p', spec', c, h1, by omega, ?_, h3, h5,
    spec₀.graph_connected_of_coreConnected h6, by omega, h8, h9, h10⟩
  exact spec'.graph_connected_of_coreConnected h4

/-! ## 8.  Non-vacuity -/

/-- The theta graph with unit lengths: the smallest connected specification
that is already bridgeless, reduced and cubic. -/
def thetaCore : Core 2 3 where
  tail := ![0, 0, 0]
  head := ![1, 1, 1]

/-- The theta graph as a specification with unit lengths. -/
def thetaSpec : Spec 2 3 :=
  Spec.ofCore thetaCore (by decide) (by decide) (fun _ => 1) (fun _ => Nat.one_pos)

theorem theta_connected : thetaSpec.core.Connected :=
  (ExplicitPotential.Core.connectedCheck_eq_true_iff thetaCore).mp (by decide)

theorem theta_bridgeless : Bridgeless thetaSpec.core := by decide

/-- **The sharp composite on the theta graph**: the theta is bridgeless, so the
contraction certificate lands on the theta itself. -/
theorem theta_cubicModel_onSpec :
    ∃ (n' p' : ℕ) (spec' : Spec n' p')
      (c : GraphContractionCertificate spec'.graph thetaSpec.graph),
      2 * p' = 3 * n' ∧ spec'.core.Cubic ∧ spec'.core.Connected ∧ c.TopologicalValid := by
  obtain ⟨n', p', spec', c, h1, -, h3, h4, h5⟩ :=
    exists_cubicModel_of_bridgeless thetaSpec theta_connected theta_bridgeless (by norm_num)
  exact ⟨n', p', spec', c, h1, h3, h4, h5⟩

/-- **The composite on the theta graph.** -/
theorem theta_cubicModel :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀) (n' p' : ℕ) (spec' : Spec n' p'),
      2 * p' = 3 * n' ∧ spec'.core.Cubic ∧ spec'.core.Connected ∧
        (p' : ℤ) - n' = 1 ∧
        spec₀.regularSubdivisionGonality = thetaSpec.regularSubdivisionGonality := by
  obtain ⟨n₀, p₀, spec₀, n', p', spec', -, h1, h2, h3, h4, -, -, -, -, -, hgon⟩ :=
    exists_cubicModel thetaSpec theta_connected (by norm_num)
  exact ⟨n₀, p₀, spec₀, n', p', spec', h1, h3, h4, by rw [h2]; norm_num, hgon⟩

/-- **The composite on the dumbbell**, the pendant-loop example of
`StableModelReduction`: it is not bridgeless, it is not `Stable`, and it still
has a cubic model with the
transport back. -/
theorem dumbbell_cubicModel :
    ∃ (n₀ p₀ : ℕ) (spec₀ : Spec n₀ p₀) (n' p' : ℕ) (spec' : Spec n' p'),
      2 * p' = 3 * n' ∧ spec'.core.Cubic ∧ spec'.core.Connected ∧
        (p' : ℤ) - n' = 1 ∧
        (∀ r d : ℤ, BNExists spec₀.graph r d ↔ BNExists dumbbellSpec.graph r d) ∧
        spec₀.regularSubdivisionGonality = dumbbellSpec.regularSubdivisionGonality := by
  obtain ⟨n₀, p₀, spec₀, n', p', spec', -, h1, h2, h3, h4, -, -, -, hbn, -, hgon⟩ :=
    exists_cubicModel dumbbellSpec dumbbell_connected (by norm_num)
  exact ⟨n₀, p₀, spec₀, n', p', spec', h1, h3, h4, by rw [h2]; norm_num, hbn, hgon⟩

end DraismaVargas.LocalCases.StableModelPackaging
