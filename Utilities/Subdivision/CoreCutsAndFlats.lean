import Utilities.Subdivision.SubdivisionConnectivity

/-!
# Core cuts, components, bridges and flats

Graph theory for a finite core `G` (an `ExplicitPotential.Core n p`, with
vertices `Fin n` and edge slots `Fin p`), independent of subdivisions and
divisors.  Throughout, `E` is a set of slots and `G − E` is the core with those
slots deleted.

* `Crosses`, `cut`, `Incident`, `otherEnd`, `ConnectedOff` describe cuts after
  deleting a set of slots; `Connected` is the case with no deleted slots.
* `ClosedOff`, `IsComponentOff`, `componentsOff`, `componentCount`,
  `edgesInside`, `genusOff`, `BridgelessOff`, `IsBridgeOff`, `Bridgeless`,
  and `IsNearSide` describe deletion components and bridge sides.
  `exists_isNearSide` shows that a bridge `f` of a connected `G − E` has a cut
  confined to `E ∪ {f}`, and `nearSide_unique` that the side of that cut
  containing a given vertex is unique.  `sum_card_componentsOff` and
  `sum_card_edgesInside` say that the components of `G − E` partition the
  vertices and the slots outside `E`.
* `flatOff E` is, when `G − E` is connected, the closure of `E` in the
  cographic matroid, expressed directly through bridges and cuts, with no
  matroid API.  It is closed (`no_cut_subset_flatOff`); it is unchanged when a
  slot of `E` is exchanged for a bridge of `G − E`, provided the complement
  stays connected (`flatOff_swap_eq`); and deleting it leaves
  `|flatOff E| − |E| + 1` components (`componentCount_flatOff`).

These facts supply the graph-theoretic part of the genus-six odd-subdivision
descent, but have no genus, degree, or parity restriction themselves.
-/

namespace Utilities.Certificate

open Finset

namespace ExplicitPotential.Core

variable {n p : ℕ} (core : ExplicitPotential.Core n p)


/-! ## Deleting edges from the core

`ExplicitPotential.Core.Connected` is the cut formulation of connectedness for
a core.  The version relative to the deletion of a set `E` of slots is
introduced here; `Connected` is the case `E = ∅` (`connectedOff_empty_iff`). -/

/-- The slot `e` **crosses** the vertex cut `(W, Wᶜ)`. -/
def Crosses (W : Finset (Fin n)) (e : Fin p) : Prop :=
  (core.tail e ∈ W ∧ core.head e ∉ W) ∨ (core.head e ∈ W ∧ core.tail e ∉ W)

instance (W : Finset (Fin n)) (e : Fin p) : Decidable (core.Crosses W e) := by
  unfold Crosses; infer_instance

/-- The edge cut `∂_G(W)`: the slots crossing `(W, Wᶜ)`. -/
def cut (W : Finset (Fin n)) : Finset (Fin p) :=
  Finset.univ.filter (core.Crosses W)

/-- The slot `e` is incident to the vertex `v`. -/
def Incident (e : Fin p) (v : Fin n) : Prop :=
  core.tail e = v ∨ core.head e = v

/-- The endpoint of `e` other than `v` (the tail, if `v` is not the tail). -/
def otherEnd (e : Fin p) (v : Fin n) : Fin n :=
  if core.tail e = v then core.head e else core.tail e

/-- **`G − E` is connected**: every non-trivial vertex cut is crossed by a slot
outside `E`.  This is `ExplicitPotential.Core.Connected` relativised to the
deletion of `E`, in the same cut formulation. -/
def ConnectedOff (E : Finset (Fin p)) : Prop :=
  ∀ S : Finset (Fin n), (∃ v w : Fin n, v ∈ S ∧ w ∉ S) →
    ∃ e : Fin p, e ∉ E ∧ core.Crosses S e

/-- Deleting nothing recovers `Core.Connected`. -/
theorem connectedOff_empty_iff :
    core.ConnectedOff ∅ ↔ core.Connected := by
  constructor
  · intro h S hS
    obtain ⟨e, -, he⟩ := h S hS
    exact ⟨e, he⟩
  · intro h S hS
    obtain ⟨e, he⟩ := h S hS
    exact ⟨e, by simp, he⟩

/-- Deleting more slots can only destroy connectedness. -/
theorem connectedOff_mono {E F : Finset (Fin p)} (hEF : E ⊆ F)
    (h : core.ConnectedOff F) : core.ConnectedOff E := by
  intro S hS
  obtain ⟨e, he, hcross⟩ := h S hS
  exact ⟨e, fun hmem => he (hEF hmem), hcross⟩

/-! ## Closed sets, components, bridges -/

/-- `W` is **closed** in `G − E`: no slot outside `E` crosses `(W, Wᶜ)`. -/
def ClosedOff (E : Finset (Fin p)) (W : Finset (Fin n)) : Prop :=
  ∀ e : Fin p, e ∉ E → ¬ core.Crosses W e

instance (E : Finset (Fin p)) (W : Finset (Fin n)) :
    Decidable (core.ClosedOff E W) := by
  unfold ClosedOff; infer_instance

/-- `W` is a **component** of `G − E`: non-empty, closed, and minimal among
non-empty closed subsets of itself. -/
def IsComponentOff (E : Finset (Fin p)) (W : Finset (Fin n)) : Prop :=
  W.Nonempty ∧ core.ClosedOff E W ∧
    ∀ S : Finset (Fin n), S ⊆ W → S.Nonempty → core.ClosedOff E S → S = W

instance (E : Finset (Fin p)) (W : Finset (Fin n)) :
    Decidable (core.IsComponentOff E W) := by
  unfold IsComponentOff; infer_instance

/-- The components of `G − E`. -/
def componentsOff (E : Finset (Fin p)) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (core.IsComponentOff E)

/-- The number of components of `G − E`, written `c(G − E)` below. -/
def componentCount (E : Finset (Fin p)) : ℕ := (core.componentsOff E).card

/-- The slots of `G − E` with both endpoints in `W`: the edges of the induced
subgraph `(G − E)[W]`. -/
def edgesInside (E : Finset (Fin p)) (W : Finset (Fin n)) : Finset (Fin p) :=
  Finset.univ.filter fun e => e ∉ E ∧ core.tail e ∈ W ∧ core.head e ∈ W

/-- The cyclomatic genus of the induced subgraph `(G − E)[W]`, for a connected
`W`. -/
def genusOff (E : Finset (Fin p)) (W : Finset (Fin n)) : ℤ :=
  ((core.edgesInside E W).card : ℤ) - (W.card : ℤ) + 1

/-- `(G − E)[W]` is **bridgeless**: every non-trivial internal cut has at least
two edges. -/
def BridgelessOff (E : Finset (Fin p)) (W : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), S ⊆ W → S.Nonempty → S ≠ W →
    2 ≤ ((core.edgesInside E W).filter (core.Crosses S)).card

/-- `f` is a **bridge** of `G − E`: it lies outside `E`, `G − E` is connected,
and deleting `f` as well disconnects it. -/
def IsBridgeOff (E : Finset (Fin p)) (f : Fin p) : Prop :=
  f ∉ E ∧ core.ConnectedOff E ∧ ¬ core.ConnectedOff (insert f E)

/-- `G` itself is **bridgeless**: no slot is a bridge of `G`.  Sufficient
conditions for the core of a graph's unit presentation are proved in
`Utilities/Gonality/CoreBridgeless.lean`. -/
def Bridgeless : Prop := ∀ f : Fin p, ¬ core.IsBridgeOff ∅ f

/-- `W` is the **near side** of the bridge `f` of `G − E` at `v`: the side of
`G − (E ∪ {f})` containing `v`. -/
def IsNearSide (E : Finset (Fin p)) (f : Fin p) (v : Fin n) (W : Finset (Fin n)) :
    Prop :=
  v ∈ W ∧ W ≠ Finset.univ ∧ core.ClosedOff (insert f E) W

/-- Across a slot that crosses the cut, the far endpoint of a vertex of `W`
leaves `W`. -/
theorem otherEnd_not_mem_of_crosses {W : Finset (Fin n)} {e : Fin p} {z : Fin n}
    (hz : core.Incident e z) (hzW : z ∈ W) (hcross : core.Crosses W e) :
    core.otherEnd e z ∉ W := by
  unfold otherEnd
  by_cases hc : core.tail e = z
  · rw [if_pos hc]
    have htW : core.tail e ∈ W := by rw [hc]; exact hzW
    rcases hcross with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd htW h
  · rw [if_neg hc]
    have hhW : core.head e ∈ W := by rw [hz.resolve_left hc]; exact hzW
    rcases hcross with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd hhW h
    · exact h

/-- Across a slot that does not cross the cut, the far endpoint of a vertex of
`W` stays in `W`. -/
theorem otherEnd_mem_of_not_crosses {W : Finset (Fin n)} {e : Fin p} {z : Fin n}
    (hz : core.Incident e z) (hzW : z ∈ W) (hcross : ¬ core.Crosses W e) :
    core.otherEnd e z ∈ W := by
  unfold otherEnd
  by_cases hc : core.tail e = z
  · rw [if_pos hc]
    have htW : core.tail e ∈ W := by rw [hc]; exact hzW
    by_contra hhW
    exact hcross (Or.inl ⟨htW, hhW⟩)
  · rw [if_neg hc]
    have hhW : core.head e ∈ W := by rw [hz.resolve_left hc]; exact hzW
    by_contra htW
    exact hcross (Or.inr ⟨hhW, htW⟩)

/-- The far endpoint of a slot is an endpoint of it. -/
theorem incident_otherEnd (e : Fin p) (z : Fin n) :
    core.Incident e (core.otherEnd e z) := by
  unfold otherEnd
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- On a loopless slot the far endpoint really is a different vertex. -/
theorem otherEnd_ne {e : Fin p} {z : Fin n} (hz : core.Incident e z)
    (hloop : core.tail e ≠ core.head e) : core.otherEnd e z ≠ z := by
  have _ : core.Incident e z := hz
  unfold otherEnd
  by_cases hc : core.tail e = z
  · rw [if_pos hc]
    exact fun h => hloop (hc.trans h.symm)
  · rw [if_neg hc]
    exact hc

/-- A crossing slot has a distinguished endpoint inside `W`, the *near* end. -/
theorem exists_nearEnd {W : Finset (Fin n)} {e : Fin p}
    (hloop : core.tail e ≠ core.head e) (hcross : core.Crosses W e) :
    ∃ z : Fin n, core.Incident e z ∧ z ∈ W ∧ core.otherEnd e z ∉ W := by
  rcases hcross with ⟨ht, hh⟩ | ⟨hh, ht⟩
  · refine ⟨core.tail e, Or.inl rfl, ht, ?_⟩
    unfold otherEnd
    rw [if_pos rfl]
    exact hh
  · refine ⟨core.head e, Or.inr rfl, hh, ?_⟩
    unfold otherEnd
    rw [if_neg hloop]
    exact ht

/-- A slot has exactly two endpoints: anything incident to `e` other than `z` is
the far endpoint of `z`. -/
theorem eq_otherEnd_of_incident {e : Fin p} {u z : Fin n} (hu : core.Incident e u)
    (hz : core.Incident e z) (hne : u ≠ z) : u = core.otherEnd e z := by
  unfold otherEnd
  by_cases hc : core.tail e = z
  · rw [if_pos hc]
    rcases hu with h | h
    · exact absurd (h.symm.trans hc) hne
    · exact h.symm
  · rw [if_neg hc]
    have hhead := hz.resolve_left hc
    rcases hu with h | h
    · exact h.symm
    · exact absurd (h.symm.trans hhead) hne

/-- **The cut of a bridge.**  A bridge `f` of the connected `G − E` splits it
into exactly two components `W ∋ v` and `Wᶜ`, and the edge cut they determine
satisfies `∂_G(W) ⊆ E ∪ {f}` with `f ∈ ∂_G(W)`; in particular that cut has at
most `|E| + 1` slots.

Proof: every slot outside `E ∪ {f}` lies inside `W` or inside `Wᶜ`. -/
theorem exists_isNearSide {E : Finset (Fin p)} {f : Fin p}
    (hbridge : core.IsBridgeOff E f) (v : Fin n) :
    ∃ W : Finset (Fin n), core.IsNearSide E f v W ∧
      core.IsComponentOff (insert f E) W ∧ core.IsComponentOff (insert f E) Wᶜ ∧
      core.cut W ⊆ insert f E ∧ f ∈ core.cut W := by
  -- `W` is the component of `v` in `G − (E ∪ {f})`, realised as
  -- a closed set containing `v` of least cardinality; it is proper because
  -- `¬ ConnectedOff (insert f E)` produces *some* non-empty proper closed set,
  -- and `Wᶜ` is a component because `f` crosses every non-empty proper closed
  -- set (that is where connectedness of `G − E` enters) and cannot cross `W`,
  -- `S` and `W ∪ S` at once.
  classical
  obtain ⟨hfE, hconn, hnotconn⟩ := hbridge
  -- Closedness is stable under the Boolean operations the argument uses.
  have hcompl : ∀ S : Finset (Fin n), core.ClosedOff (insert f E) S →
      core.ClosedOff (insert f E) Sᶜ := by
    intro S hS e he hcross
    refine hS e he ?_
    simp only [Crosses, Finset.mem_compl] at hcross ⊢
    tauto
  have hsdiff : ∀ S T : Finset (Fin n), core.ClosedOff (insert f E) S →
      core.ClosedOff (insert f E) T → core.ClosedOff (insert f E) (S \ T) := by
    intro S T hS hT e he hcross
    have h1 := hS e he
    have h2 := hT e he
    simp only [Crosses, Finset.mem_sdiff] at hcross h1 h2
    tauto
  have hunion : ∀ S T : Finset (Fin n), core.ClosedOff (insert f E) S →
      core.ClosedOff (insert f E) T → core.ClosedOff (insert f E) (S ∪ T) := by
    intro S T hS hT e he hcross
    have h1 := hS e he
    have h2 := hT e he
    simp only [Crosses, Finset.mem_union] at hcross h1 h2
    tauto
  -- `G − E` is connected, so `f` is the only slot that can cross a closed set.
  have hfcrossAny : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
      core.ClosedOff (insert f E) S → core.Crosses S f := by
    intro S hSne hSproper hSclosed
    obtain ⟨x, hx⟩ := hSne
    obtain ⟨y, hy⟩ : ∃ y : Fin n, y ∉ S := by
      by_contra hcon
      exact hSproper
        (Finset.eq_univ_iff_forall.mpr fun z => not_not.mp fun h => hcon ⟨z, h⟩)
    obtain ⟨e, heE, hcrosse⟩ := hconn S ⟨x, y, hx, hy⟩
    have hmem : e ∈ insert f E := by
      by_contra hnot
      exact hSclosed e hnot hcrosse
    rcases Finset.mem_insert.mp hmem with h | h
    · rwa [h] at hcrosse
    · exact absurd h heE
  -- Some non-empty proper closed set exists: `G − (E ∪ {f})` is disconnected.
  obtain ⟨S₀, ⟨a, b, haS, hbS⟩, hclosed₀⟩ : ∃ S : Finset (Fin n),
      (∃ x y : Fin n, x ∈ S ∧ y ∉ S) ∧ core.ClosedOff (insert f E) S := by
    unfold ConnectedOff at hnotconn
    push Not at hnotconn
    obtain ⟨S, hS, hcon⟩ := hnotconn
    exact ⟨S, hS, hcon⟩
  -- The component of `v`: a closed set containing `v` of least cardinality.
  obtain ⟨W, hWmem, hWmin⟩ := Finset.exists_min_image
    (Finset.univ.filter
      (fun S : Finset (Fin n) => v ∈ S ∧ core.ClosedOff (insert f E) S))
    Finset.card
    ⟨Finset.univ, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro e _ hcross
      rcases hcross with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h (Finset.mem_univ _)⟩
  obtain ⟨hvW, hWclosed⟩ := (Finset.mem_filter.mp hWmem).2
  have hmemfilter : ∀ S : Finset (Fin n), v ∈ S → core.ClosedOff (insert f E) S →
      W.card ≤ S.card := fun S hvS hSc =>
    hWmin S (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hvS, hSc⟩)
  have hWproper : W ≠ Finset.univ := by
    intro hcon
    have hTclosed : core.ClosedOff (insert f E) (if v ∈ S₀ then S₀ else S₀ᶜ) := by
      split_ifs with h
      · exact hclosed₀
      · exact hcompl S₀ hclosed₀
    have hvT : v ∈ (if v ∈ S₀ then S₀ else S₀ᶜ) := by
      split_ifs with h
      · exact h
      · exact Finset.mem_compl.mpr h
    have hTne : (if v ∈ S₀ then S₀ else S₀ᶜ) ≠ Finset.univ := by
      split_ifs with h
      · exact fun hc => hbS (by rw [hc]; exact Finset.mem_univ _)
      · exact fun hc => (Finset.mem_compl.mp
          (show a ∈ S₀ᶜ by rw [hc]; exact Finset.mem_univ _)) haS
    have h1 := hmemfilter _ hvT hTclosed
    have h2 := (Finset.card_lt_iff_ne_univ (if v ∈ S₀ then S₀ else S₀ᶜ)).mpr hTne
    rw [hcon, Finset.card_univ] at h1
    omega
  have hWminimal : ∀ S : Finset (Fin n), S ⊆ W → S.Nonempty →
      core.ClosedOff (insert f E) S → S = W := by
    intro S hSW hSne hSc
    by_cases hvS : v ∈ S
    · exact Finset.eq_of_subset_of_card_le hSW (hmemfilter S hvS hSc)
    · exfalso
      have h1 := hmemfilter (W \ S) (Finset.mem_sdiff.mpr ⟨hvW, hvS⟩)
        (hsdiff W S hWclosed hSc)
      have h2 : (W \ S).card + S.card = W.card := Finset.card_sdiff_add_card_eq_card hSW
      have h3 : 0 < S.card := Finset.card_pos.mpr hSne
      have h4 : S.card ≤ W.card := Finset.card_le_card hSW
      omega
  have hWcne : (Wᶜ : Finset (Fin n)).Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x : Fin n, x ∉ W := by
      by_contra hcon
      exact hWproper
        (Finset.eq_univ_iff_forall.mpr fun z => not_not.mp fun h => hcon ⟨z, h⟩)
    exact ⟨x, Finset.mem_compl.mpr hx⟩
  have hfW : core.Crosses W f := hfcrossAny W ⟨v, hvW⟩ hWproper hWclosed
  have hWcminimal : ∀ S : Finset (Fin n), S ⊆ Wᶜ → S.Nonempty →
      core.ClosedOff (insert f E) S → S = Wᶜ := by
    intro S hSW hSne hSc
    by_contra hne
    have hSproper : S ≠ Finset.univ := fun hc =>
      (Finset.mem_compl.mp (hSW (by rw [hc]; exact Finset.mem_univ v))) hvW
    have hfS : core.Crosses S f := hfcrossAny S hSne hSproper hSc
    have hUproper : W ∪ S ≠ Finset.univ := by
      intro hc
      obtain ⟨x, hxWc, hxS⟩ : ∃ x : Fin n, x ∈ Wᶜ ∧ x ∉ S := by
        by_contra hcon
        push Not at hcon
        exact hne (Finset.Subset.antisymm hSW hcon)
      rcases Finset.mem_union.mp (show x ∈ W ∪ S by rw [hc]; exact Finset.mem_univ x)
        with h | h
      · exact (Finset.mem_compl.mp hxWc) h
      · exact hxS h
    have hfU : core.Crosses (W ∪ S) f :=
      hfcrossAny (W ∪ S) ⟨v, Finset.mem_union_left _ hvW⟩ hUproper
        (hunion W S hWclosed hSc)
    have hSsub : ∀ x : Fin n, x ∈ S → x ∉ W := fun x hx =>
      Finset.mem_compl.mp (hSW hx)
    simp only [Crosses, Finset.mem_union] at hfU hfS hfW
    rcases hfW with ⟨ht, hh⟩ | ⟨hh, ht⟩
    · have hhS : core.head f ∈ S := by
        rcases hfS with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd ht (hSsub _ h1)
        · exact h1
      tauto
    · have htS : core.tail f ∈ S := by
        rcases hfS with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd hh (hSsub _ h1)
      tauto
  refine ⟨W, ⟨hvW, hWproper, hWclosed⟩, ⟨⟨v, hvW⟩, hWclosed, hWminimal⟩,
    ⟨hWcne, hcompl W hWclosed, hWcminimal⟩, ?_, ?_⟩
  · intro e he
    by_contra hnot
    exact hWclosed e hnot (Finset.mem_filter.mp he).2
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ f, hfW⟩

/-- **The near side of a bridge is unique.**  Deleting a bridge `f` from the
connected `G − E` leaves exactly two components, so the only closed proper subset
of `G − (E ∪ {f})` containing `v` is the component of `v`. -/
theorem nearSide_unique {E : Finset (Fin p)} {f : Fin p}
    (hbridge : core.IsBridgeOff E f) {v : Fin n} {W W' : Finset (Fin n)}
    (hW : core.IsNearSide E f v W) (hW' : core.IsNearSide E f v W') : W = W' := by
  classical
  obtain ⟨W₀, hW₀near, hcomp, hcompc, -, -⟩ := core.exists_isNearSide hbridge v
  have hcompl : ∀ S : Finset (Fin n), core.ClosedOff (insert f E) S →
      core.ClosedOff (insert f E) Sᶜ := by
    intro S hS e he hcross
    refine hS e he ?_
    simp only [Crosses, Finset.mem_compl] at hcross ⊢
    tauto
  have hinter : ∀ S T : Finset (Fin n), core.ClosedOff (insert f E) S →
      core.ClosedOff (insert f E) T → core.ClosedOff (insert f E) (S ∩ T) := by
    intro S T hS hT e he hcross
    have h1 := hS e he
    have h2 := hT e he
    simp only [Crosses, Finset.mem_inter] at hcross h1 h2
    tauto
  -- Every near side is the component of `v`.
  have hkey : ∀ U : Finset (Fin n), core.IsNearSide E f v U → U = W₀ := by
    rintro U ⟨hvU, hUproper, hUclosed⟩
    obtain ⟨-, hW₀closed, hW₀min⟩ := hcomp
    obtain ⟨-, -, hW₀cmin⟩ := hcompc
    have hvW₀ : v ∈ W₀ := hW₀near.1
    -- `W₀ ⊆ U`: `W₀ ∩ U` is a non-empty closed subset of the component `W₀`.
    have hsub : W₀ ⊆ U := by
      have h := hW₀min (W₀ ∩ U) Finset.inter_subset_left
        ⟨v, Finset.mem_inter.mpr ⟨hvW₀, hvU⟩⟩ (hinter W₀ U hW₀closed hUclosed)
      intro x hx
      rw [← h] at hx
      exact Finset.mem_of_mem_inter_right hx
    -- `U ⊆ W₀`: otherwise `W₀ᶜ ∩ U` is a non-empty closed subset of `W₀ᶜ`, hence
    -- all of it, and `U = W₀ ∪ W₀ᶜ` is everything.
    refine Finset.Subset.antisymm (fun x hx => ?_) hsub
    by_contra hxW₀
    have hne : ((W₀ᶜ : Finset (Fin n)) ∩ U).Nonempty :=
      ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hxW₀, hx⟩⟩
    have h := hW₀cmin (W₀ᶜ ∩ U) Finset.inter_subset_left hne
      (hinter W₀ᶜ U (hcompl W₀ hW₀closed) hUclosed)
    refine hUproper (Finset.eq_univ_iff_forall.mpr fun y => ?_)
    by_cases hy : y ∈ W₀
    · exact hsub hy
    · have : y ∈ (W₀ᶜ : Finset (Fin n)) ∩ U := by
        rw [h]; exact Finset.mem_compl.mpr hy
      exact Finset.mem_of_mem_inter_right this
  rw [hkey W hW, hkey W' hW']

instance (E : Finset (Fin p)) : Decidable (core.ConnectedOff E) := by
  unfold ConnectedOff; infer_instance

instance (E : Finset (Fin p)) (f : Fin p) : Decidable (core.IsBridgeOff E f) := by
  unfold IsBridgeOff; infer_instance

/-- The **flat** `Φ = cl(E)` of a set `E` of slots, phrased without matroids: the
slots of `E` together with every slot that is a bridge of `G − E`.

When `G − E` is connected (so that `E` is independent in the cographic matroid
`M*(G)`), a slot `f ∉ E` is a bridge of `G − E` exactly when `E ∪ {f}` is
dependent in `M*(G)`, so this is the closure of `E` in `M*(G)`; the definition
here avoids any matroid API. -/
def flatOff (E : Finset (Fin p)) : Finset (Fin p) :=
  E ∪ Finset.univ.filter fun f => core.IsBridgeOff E f

theorem subset_flatOff (E : Finset (Fin p)) : E ⊆ core.flatOff E :=
  Finset.subset_union_left

/-! ### Cut algebra

Everything proved below about `ConnectedOff`, `ClosedOff`, `IsComponentOff` and
`IsBridgeOff` is a manipulation of the edge cuts `∂(W)`, so the private lemmas
of this section translate the four predicates into statements about
`Core.cut`: `ClosedOff E W` is `∂(W) ⊆ E`, and `¬ ConnectedOff E` says that `E`
contains a non-empty cut.  The one substantial fact is `cut_symmDiff`: cuts form
a group under symmetric difference, and this replaces the cographic-matroid
theory that the statements would otherwise need. -/

/-- Membership in the edge cut `∂_G(W)` is exactly the crossing predicate. -/
@[simp] theorem mem_cut {W : Finset (Fin n)} {e : Fin p} :
    e ∈ core.cut W ↔ core.Crosses W e := by
  simp [cut]

private theorem exists_split_of_crosses {W : Finset (Fin n)} {e : Fin p}
    (h : core.Crosses W e) : ∃ v w : Fin n, v ∈ W ∧ w ∉ W := by
  simp only [Crosses] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, _, h1, h2⟩
  · exact ⟨_, _, h1, h2⟩

private theorem cut_compl (W : Finset (Fin n)) : core.cut Wᶜ = core.cut W := by
  ext e
  simp only [mem_cut, Crosses, Finset.mem_compl]
  tauto

private theorem cut_union_subset (W W' : Finset (Fin n)) :
    core.cut (W ∪ W') ⊆ core.cut W ∪ core.cut W' := by
  intro e he
  simp only [mem_cut, Finset.mem_union, Crosses] at he ⊢
  tauto

private theorem cut_inter_subset (W W' : Finset (Fin n)) :
    core.cut (W ∩ W') ⊆ core.cut W ∪ core.cut W' := by
  intro e he
  simp only [mem_cut, Finset.mem_union, Finset.mem_inter, Crosses] at he ⊢
  tauto

private theorem cut_sdiff_subset (W W' : Finset (Fin n)) :
    core.cut (W \ W') ⊆ core.cut W ∪ core.cut W' := by
  intro e he
  simp only [mem_cut, Finset.mem_union, Finset.mem_sdiff, Crosses] at he ⊢
  tauto

/-- Cuts are closed under symmetric difference: `∂(W △ W') = ∂(W) △ ∂(W')`.
This is the whole content of the usual fundamental-bond manipulations in the
cographic matroid. -/
private theorem cut_symmDiff (W W' : Finset (Fin n)) :
    core.cut (symmDiff W W') = symmDiff (core.cut W) (core.cut W') := by
  ext e
  simp only [mem_cut, Finset.mem_symmDiff, Crosses]
  by_cases h1 : core.tail e ∈ W <;> by_cases h2 : core.tail e ∈ W' <;>
    by_cases h3 : core.head e ∈ W <;> by_cases h4 : core.head e ∈ W' <;>
      simp [h1, h2, h3, h4]

/-! ### Closure, connectivity and bridges, in cut form -/

/-- `W` is closed in `G − E` exactly when its edge cut is confined to `E`. -/
theorem closedOff_iff {E : Finset (Fin p)} {W : Finset (Fin n)} :
    core.ClosedOff E W ↔ core.cut W ⊆ E := by
  constructor
  · intro h e he
    by_contra hE
    exact h e hE (core.mem_cut.mp he)
  · intro h e heE hcross
    exact heE (h (core.mem_cut.mpr hcross))

private theorem not_connectedOff_of_cut {E : Finset (Fin p)} {W : Finset (Fin n)}
    (hne : (core.cut W).Nonempty) (hsub : core.cut W ⊆ E) :
    ¬ core.ConnectedOff E := by
  intro hc
  obtain ⟨e, he⟩ := hne
  obtain ⟨e', he'E, he'cross⟩ := hc W (core.exists_split_of_crosses (core.mem_cut.mp he))
  exact he'E (hsub (core.mem_cut.mpr he'cross))

private theorem exists_cut_of_not_connectedOff (hconn : core.Connected)
    {E : Finset (Fin p)} (h : ¬ core.ConnectedOff E) :
    ∃ W : Finset (Fin n), (core.cut W).Nonempty ∧ core.cut W ⊆ E := by
  unfold ConnectedOff at h
  push Not at h
  obtain ⟨S, hsplit, hno⟩ := h
  refine ⟨S, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hconn S hsplit
    exact ⟨e, core.mem_cut.mpr he⟩
  · intro e he
    by_contra hE
    exact hno e hE (core.mem_cut.mp he)

/-- Connectedness of `G − E` implies connectedness of `G`. -/
theorem connected_of_connectedOff {E : Finset (Fin p)}
    (h : core.ConnectedOff E) : core.Connected :=
  core.connectedOff_empty_iff.mp (core.connectedOff_mono (Finset.empty_subset E) h)

/-- A slot `h` is a bridge of the connected `G − E` exactly when some cut
through it is confined to `E ∪ {h}`; this is `exists_isNearSide` read as a
characterisation. -/
private theorem isBridgeOff_iff_exists_cut (hconn : core.Connected)
    {E : Finset (Fin p)} (hE : core.ConnectedOff E) (h : Fin p) :
    core.IsBridgeOff E h ↔
      ∃ W : Finset (Fin n), h ∈ core.cut W ∧ core.cut W ⊆ insert h E := by
  constructor
  · rintro ⟨hhE, -, hdisc⟩
    obtain ⟨W, hne, hsub⟩ := core.exists_cut_of_not_connectedOff hconn hdisc
    refine ⟨W, ?_, hsub⟩
    by_contra hmem
    refine core.not_connectedOff_of_cut hne (fun e he => ?_) hE
    rcases Finset.mem_insert.mp (hsub he) with rfl | he'
    · exact absurd he hmem
    · exact he'
  · rintro ⟨W, hmem, hsub⟩
    have hne : (core.cut W).Nonempty := ⟨h, hmem⟩
    refine ⟨?_, hE, core.not_connectedOff_of_cut hne hsub⟩
    intro hhE
    exact core.not_connectedOff_of_cut hne
      (by rwa [Finset.insert_eq_self.mpr hhE] at hsub) hE

/-- Membership in the flat `cl(E)`: a slot of `E`, or a bridge of `G − E`. -/
theorem mem_flatOff_iff {E : Finset (Fin p)} {h : Fin p} :
    h ∈ core.flatOff E ↔ h ∈ E ∨ core.IsBridgeOff E h := by
  simp [flatOff]

private theorem mem_flatOff_iff_exists_cut (hconn : core.Connected)
    {E : Finset (Fin p)} (hE : core.ConnectedOff E) {h : Fin p} (hhE : h ∉ E) :
    h ∈ core.flatOff E ↔
      ∃ W : Finset (Fin n), h ∈ core.cut W ∧ core.cut W ⊆ insert h E := by
  rw [mem_flatOff_iff, core.isBridgeOff_iff_exists_cut hconn hE h]
  exact or_iff_right hhE

/-! ### `flatOff E` really is a flat

`no_cut_subset_flatOff` is the closure axiom `cl(cl(E)) = cl(E)` in cut form: a
cut confined to `Φ ∪ {h}` and meeting a slot `h ∉ Φ` cannot exist, because each
bridge `b ∈ ∂(S) ∩ (Φ ∖ E)` can be cancelled by symmetric-differencing `S` with
the witness side of `b`, which strictly decreases `|∂(S) ∩ (Φ ∖ E)|` while
keeping `h` in the cut. -/

private theorem flatOff_flat_aux (hconn : core.Connected)
    {E : Finset (Fin p)} (hE : core.ConnectedOff E) {h : Fin p}
    (hhΦ : h ∉ core.flatOff E) :
    ∀ k : ℕ, ∀ S : Finset (Fin n),
      (core.cut S ∩ (core.flatOff E \ E)).card ≤ k →
      h ∈ core.cut S → core.cut S ⊆ insert h (core.flatOff E) → False := by
  have hhE : h ∉ E := fun hx => hhΦ (core.subset_flatOff E hx)
  intro k
  induction k with
  | zero =>
    intro S hcard hhS hsub
    have hempty : core.cut S ∩ (core.flatOff E \ E) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    refine hhΦ ((core.mem_flatOff_iff_exists_cut hconn hE hhE).mpr
      ⟨S, hhS, fun x hx => ?_⟩)
    rcases Finset.mem_insert.mp (hsub hx) with rfl | hxΦ
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem ?_
      by_contra hxE
      have hmem : x ∈ core.cut S ∩ (core.flatOff E \ E) :=
        Finset.mem_inter.mpr ⟨hx, Finset.mem_sdiff.mpr ⟨hxΦ, hxE⟩⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty x hmem
  | succ k ih =>
    intro S hcard hhS hsub
    rcases Finset.eq_empty_or_nonempty (core.cut S ∩ (core.flatOff E \ E)) with
      hempty | ⟨b, hb⟩
    · exact ih S (by rw [hempty]; simp) hhS hsub
    obtain ⟨hbS, hbΦE⟩ := Finset.mem_inter.mp hb
    obtain ⟨hbΦ, hbE⟩ := Finset.mem_sdiff.mp hbΦE
    have hbr : core.IsBridgeOff E b := by
      rcases core.mem_flatOff_iff.mp hbΦ with hx | hx
      · exact absurd hx hbE
      · exact hx
    obtain ⟨W, hbW, hWsub⟩ := (core.isBridgeOff_iff_exists_cut hconn hE b).mp hbr
    have hWΦ : core.cut W ⊆ core.flatOff E := by
      intro x hx
      rcases Finset.mem_insert.mp (hWsub hx) with rfl | hxE
      · exact hbΦ
      · exact core.subset_flatOff E hxE
    have hhW : h ∉ core.cut W := fun hx => hhΦ (hWΦ hx)
    have hcut : core.cut (symmDiff S W) = symmDiff (core.cut S) (core.cut W) :=
      core.cut_symmDiff S W
    refine ih (symmDiff S W) ?_ ?_ ?_
    · -- The new bad set is contained in the old one with `b` removed.
      have hsub' : core.cut (symmDiff S W) ∩ (core.flatOff E \ E) ⊆
          (core.cut S ∩ (core.flatOff E \ E)).erase b := by
        intro x hx
        obtain ⟨hxcut, hxΦE⟩ := Finset.mem_inter.mp hx
        obtain ⟨hxΦ, hxE⟩ := Finset.mem_sdiff.mp hxΦE
        rw [hcut] at hxcut
        have hxb : x ≠ b := by
          rintro rfl
          rcases Finset.mem_symmDiff.mp hxcut with ⟨-, h2⟩ | ⟨-, h2⟩
          · exact h2 hbW
          · exact h2 hbS
        refine Finset.mem_erase.mpr ⟨hxb, Finset.mem_inter.mpr ⟨?_, hxΦE⟩⟩
        rcases Finset.mem_symmDiff.mp hxcut with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · rcases Finset.mem_insert.mp (hWsub h1) with rfl | hxE'
          · exact absurd rfl hxb
          · exact absurd hxE' hxE
      have hcard' := Finset.card_le_card hsub'
      rw [Finset.card_erase_of_mem hb] at hcard'
      have hpos : 1 ≤ (core.cut S ∩ (core.flatOff E \ E)).card :=
        Finset.card_pos.mpr ⟨b, hb⟩
      omega
    · rw [hcut]
      exact Finset.mem_symmDiff.mpr (Or.inl ⟨hhS, hhW⟩)
    · intro x hx
      rw [hcut] at hx
      rcases Finset.mem_symmDiff.mp hx with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hsub h1
      · exact Finset.mem_insert_of_mem (hWΦ h1)

/-- **`Φ = flatOff E` is a flat.**  No cut confined to `Φ ∪ {h}` meets a
slot `h` outside `Φ`; equivalently, no slot outside `Φ` is a bridge of
`G − Φ`. -/
theorem no_cut_subset_flatOff (hconn : core.Connected)
    {E : Finset (Fin p)} (hE : core.ConnectedOff E) {h : Fin p}
    (hhΦ : h ∉ core.flatOff E) {S : Finset (Fin n)} (hhS : h ∈ core.cut S)
    (hsub : core.cut S ⊆ insert h (core.flatOff E)) : False :=
  core.flatOff_flat_aux hconn hE hhΦ _ S le_rfl hhS hsub

/-! ### Exchanging a slot for a bridge preserves the flat, without matroids

`flatOff_swap_eq`: if `E_w = (E_v ∖ {e₀}) ∪ {f}` with both complements
connected and `f` a bridge of `G − E_v` with cut `W₀`, then `E_v` and `E_w` have
the same flat.  No matroid appears: a cut witnessing `h ∈ Φ_v` is confined to
`E_v ∪ {h}`, and adding `∂(W₀)` to it — which is confined to `E_v ∪ {f}` and
contains both `f` and `e₀` — deletes `e₀`, inserts `f` and keeps `h`, producing
a cut confined to `E_w ∪ {h}`. -/

private theorem flatOff_subset_of_swap (hconn : core.Connected)
    {Ev Ew : Finset (Fin p)} {f e₀ : Fin p}
    (hEv : core.ConnectedOff Ev) (hEw : core.ConnectedOff Ew)
    (he₀ : e₀ ∈ Ev) (hf : f ∉ Ev) (hEwdef : Ew = insert f (Ev.erase e₀))
    {W₀ : Finset (Fin n)} (hfW₀ : f ∈ core.cut W₀) (he₀W₀ : e₀ ∈ core.cut W₀)
    (hsub₀ : core.cut W₀ ⊆ insert f Ev) :
    core.flatOff Ev ⊆ core.flatOff Ew := by
  have hfe₀ : f ≠ e₀ := fun h => hf (h ▸ he₀)
  have hfEw : f ∈ Ew := by rw [hEwdef]; exact Finset.mem_insert_self _ _
  have hmemEw : ∀ x ∈ Ev, x ≠ e₀ → x ∈ Ew := by
    intro x hx hne
    rw [hEwdef]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hx⟩)
  have he₀Ew : e₀ ∉ Ew := by
    rw [hEwdef]
    simp [Ne.symm hfe₀]
  have hinsert : insert e₀ Ew = insert f Ev := by
    rw [hEwdef, Finset.insert_comm, Finset.insert_erase he₀]
  intro h hh
  by_cases hhEw : h ∈ Ew
  · exact core.subset_flatOff Ew hhEw
  rw [core.mem_flatOff_iff_exists_cut hconn hEw hhEw]
  rcases core.mem_flatOff_iff.mp hh with hhEv | hbr
  · -- A slot of `E_v` outside `E_w` can only be the pivot `e₀`, whose cut
    -- is `W₀` itself.
    have hhe₀ : h = e₀ := by
      by_contra hne
      exact hhEw (hmemEw h hhEv hne)
    subst hhe₀
    exact ⟨W₀, he₀W₀, by rw [hinsert]; exact hsub₀⟩
  · -- A bridge of `G − E_v`: transport its cut across the exchange.
    obtain ⟨W₁, hhW₁, hsub₁⟩ := (core.isBridgeOff_iff_exists_cut hconn hEv h).mp hbr
    have hhEv : h ∉ Ev := hbr.1
    have hhf : h ≠ f := fun hh' => hhEw (hh' ▸ hfEw)
    have hhW₀ : h ∉ core.cut W₀ := by
      intro hmem
      rcases Finset.mem_insert.mp (hsub₀ hmem) with rfl | hx
      · exact hhf rfl
      · exact hhEv hx
    by_cases he₀W₁ : e₀ ∈ core.cut W₁
    · refine ⟨symmDiff W₁ W₀, ?_, ?_⟩
      · rw [core.cut_symmDiff]
        exact Finset.mem_symmDiff.mpr (Or.inl ⟨hhW₁, hhW₀⟩)
      · intro x hx
        rw [core.cut_symmDiff] at hx
        have hxe₀ : x ≠ e₀ := by
          rintro rfl
          rcases Finset.mem_symmDiff.mp hx with ⟨-, h2⟩ | ⟨-, h2⟩
          · exact h2 he₀W₀
          · exact h2 he₀W₁
        rcases Finset.mem_symmDiff.mp hx with ⟨h1, -⟩ | ⟨h1, -⟩
        · rcases Finset.mem_insert.mp (hsub₁ h1) with rfl | hxv
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hmemEw x hxv hxe₀)
        · rcases Finset.mem_insert.mp (hsub₀ h1) with rfl | hxv
          · exact Finset.mem_insert_of_mem hfEw
          · exact Finset.mem_insert_of_mem (hmemEw x hxv hxe₀)
    · refine ⟨W₁, hhW₁, fun x hx => ?_⟩
      have hxe₀ : x ≠ e₀ := fun hx' => he₀W₁ (hx' ▸ hx)
      rcases Finset.mem_insert.mp (hsub₁ hx) with rfl | hxv
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hmemEw x hxv hxe₀)

/-- **Exchange invariance of the flat.**  Let `G − E_v` and `G − E_w` be
connected, where `E_w = (E_v ∖ {e₀}) ∪ {f}` with `e₀ ∈ E_v` and `f ∉ E_v`, and
let `W₀` be a cut through `f` confined to `E_v ∪ {f}` (so `f` is a bridge of
`G − E_v`).  Then `E_v` and `E_w` have the same flat. -/
theorem flatOff_swap_eq (hconn : core.Connected)
    {Ev Ew : Finset (Fin p)} {f e₀ : Fin p}
    (hEv : core.ConnectedOff Ev) (hEw : core.ConnectedOff Ew)
    (he₀ : e₀ ∈ Ev) (hf : f ∉ Ev) (hEwdef : Ew = insert f (Ev.erase e₀))
    {W₀ : Finset (Fin n)} (hfW₀ : f ∈ core.cut W₀)
    (hsub₀ : core.cut W₀ ⊆ insert f Ev) :
    core.flatOff Ew = core.flatOff Ev := by
  have hfe₀ : f ≠ e₀ := fun h => hf (h ▸ he₀)
  have hfEw : f ∈ Ew := by rw [hEwdef]; exact Finset.mem_insert_self _ _
  have hmemEw : ∀ x ∈ Ev, x ≠ e₀ → x ∈ Ew := by
    intro x hx hne
    rw [hEwdef]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hx⟩)
  have he₀Ew : e₀ ∉ Ew := by
    rw [hEwdef]
    simp [Ne.symm hfe₀]
  have hinsert : insert e₀ Ew = insert f Ev := by
    rw [hEwdef, Finset.insert_comm, Finset.insert_erase he₀]
  have hEvdef : Ev = insert e₀ (Ew.erase f) := by
    rw [hEwdef, Finset.erase_insert (by simp [hf]), Finset.insert_erase he₀]
  -- The cut `W₀` meets the pivot: otherwise it would already be confined
  -- to `E_w`, contradicting connectedness of `G − E_w`.
  have he₀W₀ : e₀ ∈ core.cut W₀ := by
    by_contra hmem
    refine core.not_connectedOff_of_cut ⟨f, hfW₀⟩ (fun x hx => ?_) hEw
    rcases Finset.mem_insert.mp (hsub₀ hx) with rfl | hxv
    · exact hfEw
    · exact hmemEw x hxv (fun hxe => hmem (hxe ▸ hx))
  refine Finset.Subset.antisymm ?_
    (core.flatOff_subset_of_swap hconn hEv hEw he₀ hf hEwdef hfW₀ he₀W₀ hsub₀)
  exact core.flatOff_subset_of_swap hconn hEw hEv hfEw he₀Ew hEvdef he₀W₀ hfW₀
    (by rw [hinsert]; exact hsub₀)

/-! ### Components as a partition

Counting vertices, slots and components needs the components of `G − E` to be
an honest partition of `Fin n`.  `compOff E u` is the least closed set
containing `u` — the intersection of all of them, closed because
`∂(W ∩ W') ⊆ ∂(W) ∪ ∂(W')` — and it is exactly the component of `u`. -/

private theorem closedOff_empty_set (E : Finset (Fin p)) :
    core.ClosedOff E (∅ : Finset (Fin n)) := by
  intro e _ hcross
  simp only [Crosses] at hcross
  rcases hcross with ⟨h, -⟩ | ⟨h, -⟩ <;> exact Finset.notMem_empty _ h

private theorem closedOff_univ_set (E : Finset (Fin p)) :
    core.ClosedOff E (Finset.univ : Finset (Fin n)) := by
  intro e _ hcross
  simp only [Crosses] at hcross
  rcases hcross with ⟨-, h⟩ | ⟨-, h⟩ <;> exact h (Finset.mem_univ _)

private theorem closedOff_inter {E : Finset (Fin p)} {W W' : Finset (Fin n)}
    (h : core.ClosedOff E W) (h' : core.ClosedOff E W') :
    core.ClosedOff E (W ∩ W') :=
  core.closedOff_iff.mpr ((core.cut_inter_subset W W').trans
    (Finset.union_subset (core.closedOff_iff.mp h) (core.closedOff_iff.mp h')))

private theorem closedOff_union_set {E : Finset (Fin p)} {W W' : Finset (Fin n)}
    (h : core.ClosedOff E W) (h' : core.ClosedOff E W') :
    core.ClosedOff E (W ∪ W') :=
  core.closedOff_iff.mpr ((core.cut_union_subset W W').trans
    (Finset.union_subset (core.closedOff_iff.mp h) (core.closedOff_iff.mp h')))

private theorem closedOff_sdiff {E : Finset (Fin p)} {W W' : Finset (Fin n)}
    (h : core.ClosedOff E W) (h' : core.ClosedOff E W') :
    core.ClosedOff E (W \ W') :=
  core.closedOff_iff.mpr ((core.cut_sdiff_subset W W').trans
    (Finset.union_subset (core.closedOff_iff.mp h) (core.closedOff_iff.mp h')))

/-- The closed sets of `G − E`, as a `Finset`. -/
private def closedSetsOff (E : Finset (Fin p)) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (core.ClosedOff E)

private theorem mem_closedSetsOff {E : Finset (Fin p)} {W : Finset (Fin n)} :
    W ∈ core.closedSetsOff E ↔ core.ClosedOff E W := by
  simp [closedSetsOff]

/-- The component of `u` in `G − E`: the intersection of every closed set
containing `u`. -/
private def compOff (E : Finset (Fin p)) (u : Fin n) : Finset (Fin n) :=
  ((core.closedSetsOff E).filter fun W => u ∈ W).inf id

private theorem closedOff_compOff (E : Finset (Fin p)) (u : Fin n) :
    core.ClosedOff E (core.compOff E u) := by
  refine Finset.inf_induction ?_ (fun a ha b hb => ?_) ?_
  · rw [Finset.top_eq_univ]
    exact core.closedOff_univ_set E
  · rw [show a ⊓ b = a ∩ b from Finset.inf_eq_inter]
    exact core.closedOff_inter ha hb
  · intro W hW
    exact core.mem_closedSetsOff.mp (Finset.mem_filter.mp hW).1

private theorem mem_compOff_self (E : Finset (Fin p)) (u : Fin n) :
    u ∈ core.compOff E u := by
  have h : ({u} : Finset (Fin n)) ≤ core.compOff E u :=
    Finset.le_inf fun W hW =>
      Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp hW).2
  exact h (Finset.mem_singleton_self u)

private theorem compOff_subset {E : Finset (Fin p)} {u : Fin n} {W : Finset (Fin n)}
    (hW : core.ClosedOff E W) (hu : u ∈ W) : core.compOff E u ⊆ W :=
  Finset.inf_le (f := id)
    (Finset.mem_filter.mpr ⟨core.mem_closedSetsOff.mpr hW, hu⟩)

private theorem isComponentOff_compOff (E : Finset (Fin p)) (u : Fin n) :
    core.IsComponentOff E (core.compOff E u) := by
  refine ⟨⟨u, core.mem_compOff_self E u⟩, core.closedOff_compOff E u, ?_⟩
  intro S hS hSne hSclosed
  by_cases hu : u ∈ S
  · exact Finset.Subset.antisymm hS (core.compOff_subset hSclosed hu)
  · exfalso
    obtain ⟨x, hx⟩ := hSne
    have hsub := core.compOff_subset
      (core.closedOff_sdiff (core.closedOff_compOff E u) hSclosed)
      (Finset.mem_sdiff.mpr ⟨core.mem_compOff_self E u, hu⟩)
    exact (Finset.mem_sdiff.mp (hsub (hS hx))).2 hx

private theorem compOff_eq_of_isComponentOff {E : Finset (Fin p)}
    {K : Finset (Fin n)} (hK : core.IsComponentOff E K) {u : Fin n} (hu : u ∈ K) :
    core.compOff E u = K :=
  hK.2.2 _ (core.compOff_subset hK.2.1 hu) ⟨u, core.mem_compOff_self E u⟩
    (core.closedOff_compOff E u)

/-- Membership in `componentsOff E` is exactly `IsComponentOff E`. -/
theorem mem_componentsOff {E : Finset (Fin p)} {K : Finset (Fin n)} :
    K ∈ core.componentsOff E ↔ core.IsComponentOff E K := by
  simp [componentsOff]

private theorem compOff_mem_componentsOff (E : Finset (Fin p)) (u : Fin n) :
    core.compOff E u ∈ core.componentsOff E :=
  core.mem_componentsOff.mpr (core.isComponentOff_compOff E u)

private theorem eq_of_isComponentOff {E : Finset (Fin p)} {K K' : Finset (Fin n)}
    (hK : core.IsComponentOff E K) (hK' : core.IsComponentOff E K') {x : Fin n}
    (hx : x ∈ K) (hx' : x ∈ K') : K = K' := by
  rw [← core.compOff_eq_of_isComponentOff hK hx,
    ← core.compOff_eq_of_isComponentOff hK' hx']

private theorem filter_compOff_eq {E : Finset (Fin p)} {K : Finset (Fin n)}
    (hK : core.IsComponentOff E K) :
    (Finset.univ.filter fun u => core.compOff E u = K) = K := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h ▸ core.mem_compOff_self E u,
    fun h => core.compOff_eq_of_isComponentOff hK h⟩

/-- The components of `G − E` partition the vertices. -/
theorem sum_card_componentsOff (E : Finset (Fin p)) :
    ∑ K ∈ core.componentsOff E, K.card = n := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := core.compOff E) (s := (Finset.univ : Finset (Fin n)))
    (t := core.componentsOff E) fun u _ => core.compOff_mem_componentsOff E u
  rw [Finset.card_univ, Fintype.card_fin] at hfib
  refine Eq.trans (Finset.sum_congr rfl fun K hK =>
    congrArg Finset.card
      (core.filter_compOff_eq (core.mem_componentsOff.mp hK)).symm) hfib.symm

private theorem edgesInside_eq_filter {E : Finset (Fin p)} {K : Finset (Fin n)}
    (hK : core.IsComponentOff E K) :
    core.edgesInside E K
      = (Finset.univ \ E).filter fun e => core.compOff E (core.tail e) = K := by
  ext e
  simp only [edgesInside, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨heE, htail, -⟩
    exact ⟨heE, core.compOff_eq_of_isComponentOff hK htail⟩
  · rintro ⟨heE, hcomp⟩
    have htail : core.tail e ∈ K := hcomp ▸ core.mem_compOff_self E _
    have hhead : core.head e ∈ K := by
      by_contra hh
      exact hK.2.1 e heE (Or.inl ⟨htail, hh⟩)
    exact ⟨heE, htail, hhead⟩

/-- The components of `G − E` partition the slots outside `E`. -/
theorem sum_card_edgesInside (E : Finset (Fin p)) :
    (∑ K ∈ core.componentsOff E, (core.edgesInside E K).card) + E.card = p := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun e : Fin p => core.compOff E (core.tail e))
    (s := (Finset.univ \ E : Finset (Fin p))) (t := core.componentsOff E)
    fun e _ => core.compOff_mem_componentsOff E _
  have hsum : ∑ K ∈ core.componentsOff E, (core.edgesInside E K).card
      = (Finset.univ \ E : Finset (Fin p)).card := by
    rw [hfib]
    exact Finset.sum_congr rfl fun K hK =>
      congrArg Finset.card (core.edgesInside_eq_filter (core.mem_componentsOff.mp hK))
  rw [hsum, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E),
    Finset.card_univ, Fintype.card_fin]

/-! ### Counting closed sets

`card_closedSetsOff` is the identity `|{W : ∂(W) ⊆ E}| = 2^{c(G − E)}`: closed
sets are exactly the unions of components.  Together with
`card_closedSetsOff_bridges` — a two-to-one fibering, one bridge at a time —
it gives `c(G − Φ) = |Φ| − |E| + 1` (`componentCount_flatOff`) without any
matroid rank function. -/

private theorem closedOff_biUnion {E : Finset (Fin p)} :
    ∀ 𝒮 : Finset (Finset (Fin n)), (∀ W ∈ 𝒮, core.ClosedOff E W) →
      core.ClosedOff E (𝒮.biUnion id) := by
  classical
  intro 𝒮
  induction 𝒮 using Finset.induction_on with
  | empty => intro _; simpa using core.closedOff_empty_set E
  | @insert W 𝒮 _ ih =>
    intro h
    rw [Finset.biUnion_insert]
    exact core.closedOff_union_set (h W (Finset.mem_insert_self _ _))
      (ih fun X hX => h X (Finset.mem_insert_of_mem hX))

private theorem card_closedSetsOff (E : Finset (Fin p)) :
    (core.closedSetsOff E).card = 2 ^ (core.componentsOff E).card := by
  classical
  rw [← Finset.card_powerset]
  refine Finset.card_bij'
    (fun W _ => (core.componentsOff E).filter fun K => K ⊆ W)
    (fun 𝒮 _ => 𝒮.biUnion id) (fun W _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _))
    (fun 𝒮 h𝒮 => ?_) (fun W hW => ?_) (fun 𝒮 h𝒮 => ?_)
  · refine core.mem_closedSetsOff.mpr (core.closedOff_biUnion 𝒮 fun X hX => ?_)
    exact (core.mem_componentsOff.mp (Finset.mem_powerset.mp h𝒮 hX)).2.1
  · -- the union of the components inside a closed set is that set
    have hWclosed := core.mem_closedSetsOff.mp hW
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
    constructor
    · rintro ⟨K, ⟨-, hKW⟩, hxK⟩
      exact hKW hxK
    · intro hx
      exact ⟨core.compOff E x, ⟨core.compOff_mem_componentsOff E x,
        core.compOff_subset hWclosed hx⟩, core.mem_compOff_self E x⟩
  · -- the components inside a union of components are exactly its members
    ext K
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hK, hKsub⟩
      obtain ⟨x, hx⟩ := (core.mem_componentsOff.mp hK).1
      obtain ⟨K', hK', hxK'⟩ := Finset.mem_biUnion.mp (hKsub hx)
      have hK'comp := core.mem_componentsOff.mp (Finset.mem_powerset.mp h𝒮 hK')
      rwa [core.eq_of_isComponentOff (core.mem_componentsOff.mp hK) hK'comp hx hxK']
    · intro hK
      exact ⟨Finset.mem_powerset.mp h𝒮 hK, Finset.subset_biUnion_of_mem id hK⟩

/-- If `G − E` is connected then its only closed sets are `∅` and `V(G)`. -/
private theorem closedSetsOff_of_connectedOff (hconn : core.Connected)
    {E : Finset (Fin p)} (hE : core.ConnectedOff E) :
    core.closedSetsOff E = {∅, Finset.univ} := by
  classical
  ext W
  rw [core.mem_closedSetsOff]
  constructor
  · intro hW
    have hcut : core.cut W = ∅ := by
      by_contra hne
      exact core.not_connectedOff_of_cut (Finset.nonempty_iff_ne_empty.mpr hne)
        (core.closedOff_iff.mp hW) hE
    by_cases hWe : W = ∅
    · exact Finset.mem_insert.mpr (Or.inl hWe)
    · refine Finset.mem_insert_of_mem (Finset.mem_singleton.mpr ?_)
      by_contra hWu
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hWe
      obtain ⟨y, hy⟩ : ∃ y : Fin n, y ∉ W := by
        by_contra hall
        push Not at hall
        exact hWu (Finset.eq_univ_iff_forall.mpr hall)
      obtain ⟨e, he⟩ := hconn W ⟨x, y, hx, hy⟩
      have hmem : e ∈ core.cut W := core.mem_cut.mpr he
      rw [hcut] at hmem
      exact Finset.notMem_empty e hmem
  · intro hW
    rcases Finset.mem_insert.mp hW with rfl | hW'
    · exact core.closedOff_empty_set E
    · rw [Finset.mem_singleton] at hW'
      subst hW'
      exact core.closedOff_univ_set E

/-- Deleting one further bridge of `G − E` doubles the number of closed sets:
`W ↦ W △ W₀` swaps the closed sets whose cut contains the bridge with those
whose cut does not.  Iterating over `B` gives `|{W : ∂(W) ⊆ E ∪ B}| =
2^{|B| + 1}`. -/
private theorem card_closedSetsOff_bridges (hconn : core.Connected) (hn : 0 < n)
    {E : Finset (Fin p)} (hE : core.ConnectedOff E) :
    ∀ B : Finset (Fin p), (∀ b ∈ B, core.IsBridgeOff E b) →
      (core.closedSetsOff (E ∪ B)).card = 2 ^ (B.card + 1) := by
  classical
  intro B
  induction B using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.union_empty, core.closedSetsOff_of_connectedOff hconn hE]
    have hne : (∅ : Finset (Fin n)) ∉ ({Finset.univ} : Finset (Finset (Fin n))) := by
      rw [Finset.mem_singleton]
      intro h
      have hx : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
      rw [← h] at hx
      exact Finset.notMem_empty _ hx
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton, Finset.card_empty]
    norm_num
  | @insert b B hbB ih =>
    intro hall
    have hbr : core.IsBridgeOff E b := hall b (Finset.mem_insert_self _ _)
    have ihB := ih fun x hx => hall x (Finset.mem_insert_of_mem hx)
    obtain ⟨W₀, hbW₀, hW₀sub⟩ := (core.isBridgeOff_iff_exists_cut hconn hE b).mp hbr
    have hbD : b ∉ E ∪ B := by
      rw [Finset.mem_union, not_or]
      exact ⟨hbr.1, hbB⟩
    have hunion : E ∪ insert b B = insert b (E ∪ B) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have hW₀D : core.cut W₀ ⊆ insert b (E ∪ B) :=
      hW₀sub.trans (Finset.insert_subset_insert _ Finset.subset_union_left)
    have hcutmem : ∀ W : Finset (Fin n),
        b ∈ core.cut (symmDiff W W₀) ↔ b ∉ core.cut W := by
      intro W
      rw [core.cut_symmDiff, Finset.mem_symmDiff]
      constructor
      · rintro (⟨-, h2⟩ | ⟨-, h2⟩)
        · exact absurd hbW₀ h2
        · exact h2
      · exact fun h => Or.inr ⟨hbW₀, h⟩
    have hkeep : ∀ W : Finset (Fin n), core.cut W ⊆ insert b (E ∪ B) →
        core.cut (symmDiff W W₀) ⊆ insert b (E ∪ B) := by
      intro W hW x hx
      rw [core.cut_symmDiff] at hx
      rcases Finset.mem_symmDiff.mp hx with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hW h1
      · exact hW₀D h1
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := core.closedSetsOff (insert b (E ∪ B))) fun W => b ∈ core.cut W
    have hneg : (core.closedSetsOff (insert b (E ∪ B))).filter
        (fun W => ¬ b ∈ core.cut W) = core.closedSetsOff (E ∪ B) := by
      ext W
      simp only [Finset.mem_filter, core.mem_closedSetsOff, core.closedOff_iff]
      constructor
      · rintro ⟨hWsub, hbW⟩ x hx
        rcases Finset.mem_insert.mp (hWsub hx) with rfl | h
        · exact absurd hx hbW
        · exact h
      · intro hWsub
        exact ⟨fun x hx => Finset.mem_insert_of_mem (hWsub hx),
          fun hbW => hbD (hWsub hbW)⟩
    have hpos : ((core.closedSetsOff (insert b (E ∪ B))).filter
          fun W => b ∈ core.cut W).card
        = ((core.closedSetsOff (insert b (E ∪ B))).filter
          fun W => ¬ b ∈ core.cut W).card := by
      refine Finset.card_bij' (fun W _ => symmDiff W W₀) (fun W _ => symmDiff W W₀)
        (fun W hW => ?_) (fun W hW => ?_) (fun W _ => symmDiff_symmDiff_cancel_right _ _)
        (fun W _ => symmDiff_symmDiff_cancel_right _ _)
      · rw [Finset.mem_filter] at hW ⊢
        refine ⟨core.mem_closedSetsOff.mpr (core.closedOff_iff.mpr
          (hkeep W (core.closedOff_iff.mp (core.mem_closedSetsOff.mp hW.1)))), ?_⟩
        rw [hcutmem W]
        exact not_not.mpr hW.2
      · rw [Finset.mem_filter] at hW ⊢
        refine ⟨core.mem_closedSetsOff.mpr (core.closedOff_iff.mpr
          (hkeep W (core.closedOff_iff.mp (core.mem_closedSetsOff.mp hW.1)))), ?_⟩
        rw [hcutmem W]
        exact hW.2
    rw [hpos, hneg, ihB] at hsplit
    rw [hunion, ← hsplit, Finset.card_insert_of_notMem hbB]
    ring

/-- **The components of `G − cl(E)`.**  If `G − E` is connected (and the core
has a vertex) then deleting the flat `Φ = cl(E)` leaves `|Φ| − |E| + 1`
components. -/
theorem componentCount_flatOff (hconn : core.Connected) (hn : 0 < n)
    {E : Finset (Fin p)} (hE : core.ConnectedOff E) :
    core.componentCount (core.flatOff E) + E.card = (core.flatOff E).card + 1 := by
  classical
  set B : Finset (Fin p) := Finset.univ.filter (fun f => core.IsBridgeOff E f)
    with hB
  have hBbridge : ∀ b ∈ B, core.IsBridgeOff E b := by
    intro b hb
    rw [hB, Finset.mem_filter] at hb
    exact hb.2
  have hflat : core.flatOff E = E ∪ B := by rw [hB, flatOff]
  have hdisj : Disjoint E B := by
    rw [Finset.disjoint_right]
    exact fun b hb hbE => (hBbridge b hb).1 hbE
  have hcard : (core.flatOff E).card = E.card + B.card := by
    rw [hflat, Finset.card_union_of_disjoint hdisj]
  have h1 := core.card_closedSetsOff (core.flatOff E)
  have h2 : (core.closedSetsOff (core.flatOff E)).card = 2 ^ (B.card + 1) := by
    rw [hflat]
    exact core.card_closedSetsOff_bridges hconn hn hE B hBbridge
  have hcc : B.card + 1 = (core.componentsOff (core.flatOff E)).card :=
    Nat.pow_right_injective (le_refl 2) (h2.symm.trans h1)
  rw [componentCount, ← hcc, hcard]
  omega

end ExplicitPotential.Core

end Utilities.Certificate
