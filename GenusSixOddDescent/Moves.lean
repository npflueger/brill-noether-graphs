import GenusSixOddDescent.Chain
import GenusSixOddDescent.BridgeChain
import GenusSixOddDescent.HoleClass

/-!
# The moves at a state, at a general scale

A proper legal firing at a state starts either a hole branch or a bridge
chain. The crossing offsets determine the length and endpoint of a bridge
chain. All formulas work at a general subdivision scale.

The module has four parts.

* **Crossing slots.**  `crossing E W = E.filter (Crosses W)` and its nonemptiness
  (`crossing_nonempty`: `{f} ∪ X` is an edge cut of `G`, so bridgelessness of
  `G` forbids `X = ∅`), together with the observation `crosses_of_isNearSide`
  and `exists_endpoint_offset`, which locates the chip from either endpoint.
* **The crossing data.**  `nearEndpoint`, the **ℕ-valued** `offsetFromSide`,
  and `sMax`, `crossingMax`, `CrossingValid`, `tauStar` on top of them.
  ℕ-valuedness is what lets `offsetFromSide` be plugged straight into
  `BridgeData.t : Fin p → ℕ`, whereupon `d.sMax`/`spec.sMax` and
  `d.tauStar`/`spec.tauStar` agree by `rfl`; `Int.toNat` never appears
  downstream, every use going through `offsetFromSide_eq_of_chip`.
* **The adapter.**  `stateBridgeData` packages a `TypeI` state together
  with a bridge `f` of `G − E` at `v` and a near side `W` as a `BridgeData`
  (`GenusSixOddDescent/BridgeChain.lean`), so that the whole multi-firing chain
  of that module applies to the move.  `stateBridgeData_bridgeDiv_zero` says the
  chain starts at the state, and `stateBridgeData_R` describes the rest divisor:
  it is effective, chipless on the core and on every crossing slot, and carries
  exactly one chip on each non-crossing chip slot.
* **The move theorems** `moves_classified` and `bridgeSet_forced`;
  `exists_legal_bridge_move`, `dichotomy` and `swap` are in
  `GenusSixOddDescent/Swap.lean`.

Everything is stated at the abstract `Spec`; no concrete subdivided graph is
ever unfolded.  In particular the one divisor identity of the adapter is proved
through the abstract-`CFGraph` lemma `chip_rest_cancel` below.

The module imports `GenusSixOddDescent.Chain`, `GenusSixOddDescent.BridgeChain`
and `GenusSixOddDescent.HoleClass`; `GenusSixOddDescent.Swap` builds on it.
-/

namespace Utilities.Certificate

/-! ## A divisor identity at the abstract `CFGraph`

The one piece of divisor algebra this module needs is proved once, for an
abstract graph and abstract divisors, so that the downstream use is a syntactic
`exact` and no divisor of a concrete subdivided graph is ever compared
pointwise. -/

/-- Adding back the two chips that were subtracted off recovers the divisor. -/
private theorem chip_rest_cancel {G : CFGraph} (D x y : CFDiv G) :
    x + y + (D - x - y) = D := by
  abel

namespace SubdivisionGraph

namespace Spec

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-- Core vertices of a subdivision are distinct. -/
private theorem coreVertex_inj {m q : ℕ} (sp : Spec m q) {u w : Fin m}
    (h : sp.coreVertex u = sp.coreVertex w) : u = w :=
  Sum.inl.inj h

/-! ## Crossing slots -/

/-- `X`: the chip slots of the state that cross the cut `(W, Wᶜ)`.

No scale is involved, so this takes no `N hN` arguments. -/
def crossing (E : Finset (Fin p)) (W : Finset (Fin n)) : Finset (Fin p) :=
  E.filter (spec.core.Crosses W)

theorem mem_crossing {E : Finset (Fin p)} {W : Finset (Fin n)} {e : Fin p} :
    e ∈ spec.crossing E W ↔ e ∈ E ∧ spec.core.Crosses W e :=
  Finset.mem_filter

theorem crossing_subset (E : Finset (Fin p)) (W : Finset (Fin n)) :
    spec.crossing E W ⊆ E :=
  Finset.filter_subset _ _

/-- **The bridge crosses its own near side.**  `G − E` is connected, so *some*
slot outside `E` crosses the non-trivial cut `(W, Wᶜ)`, and `W` is closed in
`G − (E ∪ {f})`, so that slot is `f`. -/
theorem crosses_of_isNearSide {E : Finset (Fin p)} {f : Fin p} {v : Fin n}
    {W : Finset (Fin n)} (hconn : spec.core.ConnectedOff E)
    (hW : spec.core.IsNearSide E f v W) : spec.core.Crosses W f := by
  obtain ⟨hvW, hWne, hclosedW⟩ := hW
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w ∉ W := by
    by_contra hcon
    exact hWne (Finset.eq_univ_iff_forall.mpr fun u => not_not.mp fun h => hcon ⟨u, h⟩)
  obtain ⟨e, heE, hcross⟩ := hconn W ⟨v, w, hvW, hw⟩
  have hef : e = f := by
    by_contra hne
    exact hclosedW e (fun hmem => (Finset.mem_insert.mp hmem).elim hne heE) hcross
  rwa [hef] at hcross

/-- **Every bridge move crosses at least one chip slot**: `{f} ∪ X` is an edge
cut of `G`, so `X = ∅` would make `f` a bridge of `G` itself.  The argument is
pure cut combinatorics and never mentions the scale. -/
theorem crossing_nonempty (hbridgeless : spec.core.Bridgeless)
    {E : Finset (Fin p)} {f : Fin p} {v : Fin n} {W : Finset (Fin n)}
    (hbridge : spec.core.IsBridgeOff E f) (hW : spec.core.IsNearSide E f v W) :
    (spec.crossing E W).Nonempty := by
  obtain ⟨-, hconn, -⟩ := hbridge
  obtain ⟨hvW, hWne, hclosed⟩ := hW
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  refine hbridgeless f ⟨Finset.notMem_empty f,
    spec.core.connectedOff_mono (Finset.empty_subset E) hconn, ?_⟩
  intro hcontra
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w ∉ W := by
    by_contra hcon
    exact hWne (Finset.eq_univ_iff_forall.mpr fun u => not_not.mp fun h => hcon ⟨u, h⟩)
  obtain ⟨e, he, hcross⟩ := hcontra W ⟨v, w, hvW, hw⟩
  have hef : e ≠ f := fun h => he (by simp [h])
  have heE : e ∈ E := by
    by_contra hnot
    exact hclosed e (fun hmem => (Finset.mem_insert.mp hmem).elim hef hnot) hcross
  have : e ∈ spec.crossing E W := Finset.mem_filter.mpr ⟨heE, hcross⟩
  rw [hempty] at this
  exact absurd this (Finset.notMem_empty e)

/-- **Every interior fine point of a slot sits at an interior offset from some
endpoint.**  Read the point from the tail. -/
theorem exists_endpoint_offset (hunit : spec.IsUnit) (g : Fin p)
    (j : Fin ((spec.scale N hN).length g - 1)) :
    ∃ (z : Fin n) (t : ℕ), spec.core.Incident g z ∧ 1 ≤ t ∧ t < N ∧
      (spec.scale N hN).interiorVertex g j = spec.sidePoint N hN g z t := by
  have hL : (spec.scale N hN).length g = N := spec.length_scale N hN hunit g
  have hj : j.val < N - 1 := by have := j.isLt; omega
  refine ⟨spec.core.tail g, j.val + 1, Or.inl rfl, by omega, by omega, ?_⟩
  rw [spec.sidePoint_tail N hN g, spec.interiorVertex_eq_slotPoint N hN hunit g j]

/-! ## The crossing data

`nearEndpoint W e` is the endpoint of `e` on the near side,
and `offsetFromSide D W e` is the offset of `e`'s chip measured from it — a
**natural number**, so that it can be handed straight to `BridgeData.t`. -/

/-- The endpoint of the slot `e` lying in `W`.  Total: on a slot with no endpoint
in `W` it returns the head, which is harmless because every lemma below carries
the crossing hypothesis. -/
def nearEndpoint (W : Finset (Fin n)) (e : Fin p) : Fin n :=
  if spec.core.tail e ∈ W then spec.core.tail e else spec.core.head e

theorem nearEndpoint_incident (W : Finset (Fin n)) (e : Fin p) :
    spec.core.Incident e (spec.nearEndpoint W e) := by
  unfold nearEndpoint
  by_cases h : spec.core.tail e ∈ W
  · exact Or.inl (by rw [if_pos h])
  · exact Or.inr (by rw [if_neg h])

/-- On a crossing slot the near endpoint really is on the near side. -/
theorem nearEndpoint_mem {W : Finset (Fin n)} {e : Fin p}
    (hcross : spec.core.Crosses W e) : spec.nearEndpoint W e ∈ W := by
  unfold nearEndpoint
  by_cases h : spec.core.tail e ∈ W
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    rcases hcross with ⟨ht, -⟩ | ⟨hh, -⟩
    · exact absurd ht h
    · exact hh

/-- **The chip offset from the near side**, as a natural number.  On a slot
carrying a single interior chip this is that chip's offset from
`nearEndpoint W e`, by `offsetFromSide_eq_of_chip`; `Int.toNat` never appears
again. -/
def offsetFromSide (D : CFDiv (spec.scale N hN).graph) (W : Finset (Fin n))
    (e : Fin p) : ℕ :=
  (∑ i ∈ Finset.Ioo 0 N, (i : ℤ) * D (spec.sidePoint N hN e (spec.nearEndpoint W e) i)).toNat

/-- `s = sup_{e ∈ X} t_e`, the largest crossing offset.  Definitionally equal to
`(spec.stateBridgeData …).sMax`. -/
def sMax (D : CFDiv (spec.scale N hN).graph) (E : Finset (Fin p))
    (W : Finset (Fin n)) : ℕ :=
  (spec.crossing E W).sup (spec.offsetFromSide N hN D W)

/-- `X_max`: the crossing slots whose chip attains the maximal offset.  These are
exactly the slots whose chip *lands on a core vertex* at the end of the move, so
`|X_max| ≥ 2` would put two chips on the core. -/
def crossingMax (D : CFDiv (spec.scale N hN).graph) (E : Finset (Fin p))
    (W : Finset (Fin n)) : Finset (Fin p) :=
  (spec.crossing E W).filter fun e => spec.offsetFromSide N hN D W e = spec.sMax N hN D E W

/-- The crossing-data condition of clause (b) of a hub system
(`GenusSixOddDescent/HubSystem.lean`): exactly one crossing slot attains the
maximal offset, `|X_max| = 1`.  `dichotomy` in `GenusSixOddDescent/Swap.lean`
proves it for every bridge move under non-selection. -/
def CrossingValid (D : CFDiv (spec.scale N hN).graph) (E : Finset (Fin p))
    (W : Finset (Fin n)) : Prop :=
  (spec.crossingMax N hN D E W).card = 1

/-- `τ* = N − s`, the number of firings the move takes.  Definitionally equal to
`(spec.stateBridgeData …).tauStar`. -/
def tauStar (D : CFDiv (spec.scale N hN).graph) (E : Finset (Fin p))
    (W : Finset (Fin n)) : ℕ :=
  N - spec.sMax N hN D E W

/-- **Reading `offsetFromSide` off a chip.**  On a slot of chip count one, an
interior offset carrying the chip *is* the value of `offsetFromSide`.  Every use
of `offsetFromSide` downstream goes through this lemma, so the `Int.toNat` in the
definition is never unfolded again. -/
theorem offsetFromSide_eq_of_chip (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D) {e : Fin p}
    (hchip : spec.edgeChipCount N hN D e = 1) (W : Finset (Fin n)) {t : ℕ}
    (ht0 : 0 < t) (htN : t < N)
    (hDt : D (spec.sidePoint N hN e (spec.nearEndpoint W e) t) = 1) :
    spec.offsetFromSide N hN D W e = t := by
  obtain ⟨c, hc0, hcN, -, hcrest⟩ :=
    spec.exists_chip_offset_side N hN hunit hDeff (spec.nearEndpoint W e) hchip
  have htc : t = c := by
    by_contra hne
    have hz := hcrest t ht0 htN hne
    omega
  have hrest : ∀ k, 0 < k → k < N → k ≠ t →
      D (spec.sidePoint N hN e (spec.nearEndpoint W e) k) = 0 :=
    fun k hk0 hkN hkt => hcrest k hk0 hkN (by omega)
  unfold offsetFromSide
  have hsum : (∑ i ∈ Finset.Ioo 0 N,
      (i : ℤ) * D (spec.sidePoint N hN e (spec.nearEndpoint W e) i)) = (t : ℤ) := by
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_Ioo.mpr ⟨ht0, htN⟩)]
    · rw [hDt]; ring
    · intro i hi hine
      obtain ⟨hi0, hiN⟩ := Finset.mem_Ioo.mp hi
      rw [hrest i hi0 hiN hine]
      ring
  rw [hsum]
  simp

/-- The full data of `offsetFromSide` on a chip slot: it is an interior offset,
it carries the chip, and no other interior offset does. -/
theorem offsetFromSide_spec (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D) {e : Fin p}
    (hchip : spec.edgeChipCount N hN D e = 1) (W : Finset (Fin n)) :
    0 < spec.offsetFromSide N hN D W e ∧ spec.offsetFromSide N hN D W e < N ∧
      D (spec.sidePoint N hN e (spec.nearEndpoint W e)
          (spec.offsetFromSide N hN D W e)) = 1 ∧
      ∀ k, 0 < k → k < N → k ≠ spec.offsetFromSide N hN D W e →
        D (spec.sidePoint N hN e (spec.nearEndpoint W e) k) = 0 := by
  obtain ⟨c, hc0, hcN, hc1, hcrest⟩ :=
    spec.exists_chip_offset_side N hN hunit hDeff (spec.nearEndpoint W e) hchip
  have hval : spec.offsetFromSide N hN D W e = c :=
    spec.offsetFromSide_eq_of_chip N hN hunit hDeff hchip W hc0 hcN hc1
  rw [hval]
  exact ⟨hc0, hcN, hc1, hcrest⟩

/-- The chip of a chip slot really sits at `offsetFromSide`. -/
theorem offsetFromSide_chip (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D) {e : Fin p}
    (hchip : spec.edgeChipCount N hN D e = 1) (W : Finset (Fin n)) :
    D (spec.sidePoint N hN e (spec.nearEndpoint W e)
        (spec.offsetFromSide N hN D W e)) = 1 :=
  (spec.offsetFromSide_spec N hN hunit hDeff hchip W).2.2.1

/-- … and nowhere else in the interior. -/
theorem eq_zero_of_ne_offsetFromSide (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D) {e : Fin p}
    (hchip : spec.edgeChipCount N hN D e = 1) (W : Finset (Fin n)) {k : ℕ}
    (hk0 : 0 < k) (hkN : k < N) (hne : k ≠ spec.offsetFromSide N hN D W e) :
    D (spec.sidePoint N hN e (spec.nearEndpoint W e) k) = 0 :=
  (spec.offsetFromSide_spec N hN hunit hDeff hchip W).2.2.2 k hk0 hkN hne

/-- **The chip is interior**: offset at least one from the near side. -/
theorem one_le_offsetFromSide (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D) {e : Fin p}
    (hchip : spec.edgeChipCount N hN D e = 1) (W : Finset (Fin n)) :
    1 ≤ spec.offsetFromSide N hN D W e :=
  (spec.offsetFromSide_spec N hN hunit hDeff hchip W).1

/-- … and at most `N − 1`. -/
theorem offsetFromSide_lt (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D) {e : Fin p}
    (hchip : spec.edgeChipCount N hN D e = 1) (W : Finset (Fin n)) :
    spec.offsetFromSide N hN D W e < N :=
  (spec.offsetFromSide_spec N hN hunit hDeff hchip W).2.1

/-- The chip point of a chip slot, read from the **tail** as a `slotPoint` at an
interior offset.  This is what tells the crossing chips of a bridge move apart
from the chips of the other slots. -/
theorem exists_front_offset (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D) {e : Fin p}
    (hchip : spec.edgeChipCount N hN D e = 1) (W : Finset (Fin n)) :
    ∃ c : ℕ, 0 < c ∧ c < N ∧
      spec.sidePoint N hN e (spec.nearEndpoint W e) (spec.offsetFromSide N hN D W e)
        = spec.slotPoint N hN e c :=
  ⟨spec.sideOffset N e (spec.nearEndpoint W e) (spec.offsetFromSide N hN D W e),
    spec.sideOffset_pos N e _ (spec.one_le_offsetFromSide N hN hunit hDeff hchip W)
      (spec.offsetFromSide_lt N hN hunit hDeff hchip W),
    spec.sideOffset_lt N e _ (spec.one_le_offsetFromSide N hN hunit hDeff hchip W)
      (spec.offsetFromSide_lt N hN hunit hDeff hchip W),
    spec.sidePoint_eq_slotPoint N hN e _ _⟩

/-- **A chip slot carries exactly one chip, at `offsetFromSide`.**  Pointwise, in
tail coordinates: this is the form the rest divisor of the adapter below is
computed in. -/
theorem apply_slotPoint_eq_one_chip (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D) {e : Fin p}
    (hchip : spec.edgeChipCount N hN D e = 1) (W : Finset (Fin n)) {j : ℕ}
    (hj0 : 0 < j) (hjN : j < N) :
    D (spec.slotPoint N hN e j)
      = (one_chip (spec.sidePoint N hN e (spec.nearEndpoint W e)
          (spec.offsetFromSide N hN D W e)) : CFDiv (spec.scale N hN).graph)
          (spec.slotPoint N hN e j) := by
  set z := spec.nearEndpoint W e with hz
  set s := spec.offsetFromSide N hN D W e with hs
  have hs0 : 0 < s := spec.one_le_offsetFromSide N hN hunit hDeff hchip W
  have hsN : s < N := spec.offsetFromSide_lt N hN hunit hDeff hchip W
  set k := spec.sideOffset N e z j with hk
  have hk0 : 0 < k := spec.sideOffset_pos N e z hj0 hjN
  have hkN : k < N := spec.sideOffset_lt N e z hj0 hjN
  have hpt : spec.sidePoint N hN e z k = spec.slotPoint N hN e j := by
    rw [spec.sidePoint_eq_slotPoint N hN e z k, hk,
      spec.sideOffset_sideOffset N e z (le_of_lt hjN)]
  by_cases hks : k = s
  · have hfront : spec.sidePoint N hN e z s = spec.slotPoint N hN e j := by
      rw [← hks]; exact hpt
    rw [hfront, one_chip_apply_v, ← hfront]
    exact spec.offsetFromSide_chip N hN hunit hDeff hchip W
  · have hzero : D (spec.slotPoint N hN e j) = 0 := by
      rw [← hpt]
      exact spec.eq_zero_of_ne_offsetFromSide N hN hunit hDeff hchip W hk0 hkN hks
    have hne : spec.sideOffset N e z s ≠ j := by
      intro h
      refine hks ?_
      have h2 : spec.sideOffset N e z (spec.sideOffset N e z s) = spec.sideOffset N e z j := by
        rw [h]
      rw [spec.sideOffset_sideOffset N e z (le_of_lt hsN)] at h2
      exact h2.symm
    rw [hzero, spec.sidePoint_eq_slotPoint N hN e z s]
    exact (one_chip_apply_other' _ _
      (spec.slotPoint_ne N hN hunit e (le_of_lt hjN)
        (spec.sideOffset_le N e z (le_of_lt hsN)) (Ne.symm hne))).symm

/-! ## The adapter: a state and a bridge give a `BridgeData`

The rest divisor `R` is the state minus its core chip and
minus the chips on the crossing slots — i.e. **exactly the non-crossing chips**
`∑_{e ∈ E ∖ X} x_e`. -/

/-- **The bridge move at a state, as `BridgeData`.**  The crossing slots are
`crossing E W`, their near endpoints `nearEndpoint W`, their offsets
`offsetFromSide D W`, and the rest divisor is what is left of `D` after the core
chip at `v` and the crossing chips are removed.

`hbridgeless` is used only for the field `supPos` (via `crossing_nonempty`), and
`hconn` only for the field `farF` (via `crosses_of_isNearSide`). -/
noncomputable def stateBridgeData (hunit : spec.IsUnit)
    (hbridgeless : spec.core.Bridgeless)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    {f : Fin p} (hinc : spec.core.Incident f v)
    (hbridge : spec.core.IsBridgeOff E f) {W : Finset (Fin n)}
    (hW : spec.core.IsNearSide E f v W) : spec.BridgeData N hN where
  W := W
  v := v
  f := f
  X := spec.crossing E W
  z := spec.nearEndpoint W
  t := spec.offsetFromSide N hN D W
  R := D - one_chip ((spec.scale N hN).coreVertex v)
        - ∑ e ∈ spec.crossing E W, one_chip (spec.sidePoint N hN e
            (spec.nearEndpoint W e) (spec.offsetFromSide N hN D W e))
  memW := hW.1
  incF := hinc
  farF := spec.core.otherEnd_not_mem_of_crosses hinc hW.1
    (spec.crosses_of_isNearSide hconn hW)
  notMemF := fun hmem => hbridge.1 (spec.crossing_subset E W hmem)
  crossX := fun _ he => (Finset.mem_filter.mp he).2
  incX := fun e _ => spec.nearEndpoint_incident W e
  memX := fun _ he => spec.nearEndpoint_mem (Finset.mem_filter.mp he).2
  cutSub := fun g hg => by
    by_cases hgf : g = f
    · exact Or.inr hgf
    · exact Or.inl (Finset.mem_filter.mpr
        ⟨by
          by_contra hgE
          exact hW.2.2 g (fun hmem => (Finset.mem_insert.mp hmem).elim hgf hgE) hg, hg⟩)
  onePos := fun e he => spec.one_le_offsetFromSide N hN hunit hD.1
    (by rw [hD.2.2.2.2 e, if_pos (spec.crossing_subset E W he)]) W
  offLt := fun e he => by
    have := spec.offsetFromSide_lt N hN hunit hD.1
      (show spec.edgeChipCount N hN D e = 1 by
        rw [hD.2.2.2.2 e, if_pos (spec.crossing_subset E W he)]) W
    omega
  supPos := by
    obtain ⟨e, he⟩ := spec.crossing_nonempty hbridgeless hbridge hW
    exact le_trans
      (spec.one_le_offsetFromSide N hN hunit hD.1
        (by rw [hD.2.2.2.2 e, if_pos (spec.crossing_subset E W he)]) W)
      (Finset.le_sup he)

/-- `sMax` of the adapter is `Spec.sMax`, by definition. -/
theorem stateBridgeData_sMax (hunit : spec.IsUnit)
    (hbridgeless : spec.core.Bridgeless)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    {f : Fin p} (hinc : spec.core.Incident f v)
    (hbridge : spec.core.IsBridgeOff E f) {W : Finset (Fin n)}
    (hW : spec.core.IsNearSide E f v W) :
    (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).sMax
      = spec.sMax N hN D E W := rfl

/-- `τ*` of the adapter is `Spec.tauStar`, by definition. -/
theorem stateBridgeData_tauStar (hunit : spec.IsUnit)
    (hbridgeless : spec.core.Bridgeless)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    {f : Fin p} (hinc : spec.core.Incident f v)
    (hbridge : spec.core.IsBridgeOff E f) {W : Finset (Fin n)}
    (hW : spec.core.IsNearSide E f v W) :
    (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).tauStar
      = spec.tauStar N hN D E W := rfl

/-- **The chain starts at the state.**  `sidePoint f v 0 = coreVertex v`
(`sidePoint_zero`) puts the `f`-front on the core chip, `offsetFromSide_eq_of_chip`
puts each crossing front on that slot's chip, and the rest is the abstract
identity `chip_rest_cancel`. -/
theorem stateBridgeData_bridgeDiv_zero (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W) :
    (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv 0
      = D := by
  rw [BridgeData.bridgeDiv_zero _ hunit]
  exact chip_rest_cancel D _ _

/-- **The rest divisor of the adapter.**  It is effective, chipless on the core,
chipless off `E`, chipless on every crossing slot (in particular on `f` and on
every `e ∈ X`, whose chips are the fronts of the chain), and carries exactly one
chip on each `g ∈ E ∖ crossing E W` and none elsewhere.

The five clauses are exactly what `BridgeData.Confined` asks for. -/
theorem stateBridgeData_R (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W) :
    effective
        (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).R ∧
      (∀ u : Fin n,
        (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).R
          ((spec.scale N hN).coreVertex u) = 0) ∧
      (∀ g : Fin p, g ∉ E → ∀ j : ℕ, 0 < j → j < N →
        (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).R
          (spec.slotPoint N hN g j) = 0) ∧
      (∀ g : Fin p, spec.core.Crosses W g → ∀ j : ℕ, 0 < j → j < N →
        (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).R
          (spec.slotPoint N hN g j) = 0) ∧
      (∀ g : Fin p, ∑ j ∈ Finset.Ioo 0 N,
          (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).R
            (spec.slotPoint N hN g j)
        = if g ∈ E ∧ ¬ spec.core.Crosses W g then 1 else 0) := by
  classical
  have hDeff : effective D := hD.1
  have hDcore : ∀ u : Fin n,
      D ((spec.scale N hN).coreVertex u) = if u = v then 1 else 0 := hD.2.2.1
  have hDedge : ∀ e : Fin p,
      spec.edgeChipCount N hN D e = if e ∈ E then 1 else 0 := hD.2.2.2.2
  have hchipX : ∀ e ∈ spec.crossing E W, spec.edgeChipCount N hN D e = 1 := fun e he => by
    rw [hDedge e, if_pos (spec.crossing_subset E W he)]
  set Rd := (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).R
    with hRd
  have hRval : Rd = D - one_chip ((spec.scale N hN).coreVertex v)
      - ∑ e ∈ spec.crossing E W, one_chip (spec.sidePoint N hN e
          (spec.nearEndpoint W e) (spec.offsetFromSide N hN D W e)) := by
    rw [hRd]; rfl
  -- A crossing chip sits in the interior of **its own** slot, so it is invisible
  -- both at the core and on every other slot.
  have hfront : ∀ e ∈ spec.crossing E W, ∀ (g : Fin p) (j : ℕ), 0 < j → j < N → e ≠ g →
      (one_chip (spec.sidePoint N hN e (spec.nearEndpoint W e)
          (spec.offsetFromSide N hN D W e)) : CFDiv (spec.scale N hN).graph)
        (spec.slotPoint N hN g j) = 0 := by
    intro e he g j hj0 hjN hne
    obtain ⟨c, hc0, hcN, hceq⟩ := spec.exists_front_offset N hN hunit hDeff (hchipX e he) W
    rw [hceq]
    exact one_chip_apply_other' _ _ (fun h =>
      hne (spec.slot_eq_of_slotPoint_eq N hN hunit hj0 hjN hc0 hcN h).symm)
  have hfrontcore : ∀ e ∈ spec.crossing E W, ∀ u : Fin n,
      (one_chip (spec.sidePoint N hN e (spec.nearEndpoint W e)
          (spec.offsetFromSide N hN D W e)) : CFDiv (spec.scale N hN).graph)
        ((spec.scale N hN).coreVertex u) = 0 := by
    intro e he u
    obtain ⟨c, hc0, hcN, hceq⟩ := spec.exists_front_offset N hN hunit hDeff (hchipX e he) W
    rw [hceq]
    exact one_chip_apply_other' _ _ (spec.coreVertex_ne_slotPoint N hN hunit u e hc0 hcN)
  -- **The rest divisor at a core vertex.**  `D` has its single core chip at `v`,
  -- and that is exactly what was subtracted.
  have hA : ∀ u : Fin n, Rd ((spec.scale N hN).coreVertex u) = 0 := by
    intro u
    rw [hRval]
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [Finset.sum_eq_zero (fun e he => hfrontcore e he u), hDcore u]
    by_cases huv : u = v
    · rw [if_pos huv, huv, one_chip_apply_v]; ring
    · rw [if_neg huv, one_chip_apply_other' _ _
        (fun h => huv (coreVertex_inj (spec.scale N hN) h))]; ring
  -- **The rest divisor on a slot.**  A crossing slot is emptied exactly; every
  -- other slot keeps whatever `D` put there.
  have hB : ∀ (g : Fin p) (j : ℕ), 0 < j → j < N →
      Rd (spec.slotPoint N hN g j)
        = if g ∈ spec.crossing E W then 0 else D (spec.slotPoint N hN g j) := by
    intro g j hj0 hjN
    rw [hRval]
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [one_chip_apply_other' _ _
      (Ne.symm (spec.coreVertex_ne_slotPoint N hN hunit v g hj0 hjN))]
    by_cases hgX : g ∈ spec.crossing E W
    · rw [if_pos hgX,
        Finset.sum_eq_single_of_mem g hgX (fun e he hne => hfront e he g j hj0 hjN hne),
        ← spec.apply_slotPoint_eq_one_chip N hN hunit hDeff (hchipX g hgX) W hj0 hjN]
      ring
    · rw [if_neg hgX, Finset.sum_eq_zero
        (fun e he => hfront e he g j hj0 hjN (fun h => hgX (h ▸ he)))]
      ring
  -- A slot outside `E` is chipless for `D`, hence for the rest divisor.
  have hoff : ∀ g : Fin p, g ∉ E → ∀ j : ℕ, 0 < j → j < N →
      Rd (spec.slotPoint N hN g j) = 0 := by
    intro g hgE j hj0 hjN
    rw [hB g j hj0 hjN, if_neg (fun h => hgE (spec.crossing_subset E W h))]
    exact spec.slotPoint_eq_zero_of_edgeChipCount_zero N hN hunit hDeff
      (by rw [hDedge g, if_neg hgE]) j (Finset.mem_Ioo.mpr ⟨hj0, hjN⟩)
  refine ⟨?_, hA, hoff, ?_, ?_⟩
  · -- effectivity
    intro x
    rcases x with u | ⟨g, j⟩
    · show Rd ((spec.scale N hN).coreVertex u) ≥ 0
      exact ge_of_eq (hA u)
    · have hL := spec.length_scale N hN hunit g
      have hj0 : 0 < j.val + 1 := by omega
      have hjN : j.val + 1 < N := by have := j.isLt; omega
      show Rd ((spec.scale N hN).interiorVertex g j) ≥ 0
      rw [spec.interiorVertex_eq_slotPoint N hN hunit g j, hB g (j.val + 1) hj0 hjN]
      split_ifs
      · exact le_refl 0
      · exact hDeff _
  · -- chipless on every crossing slot
    intro g hgcross j hj0 hjN
    by_cases hgE : g ∈ E
    · have hgX : g ∈ spec.crossing E W := spec.mem_crossing.mpr ⟨hgE, hgcross⟩
      rw [hB g j hj0 hjN, if_pos hgX]
    · exact hoff g hgE j hj0 hjN
  · -- one chip on each non-crossing chip slot, none elsewhere
    intro g
    by_cases hgX : g ∈ spec.crossing E W
    · obtain ⟨hgE, hgcross⟩ := spec.mem_crossing.mp hgX
      have hzero : (∑ j ∈ Finset.Ioo 0 N, Rd (spec.slotPoint N hN g j)) = 0 :=
        Finset.sum_eq_zero fun j hj => by
          obtain ⟨hj0, hjN⟩ := Finset.mem_Ioo.mp hj
          rw [hB g j hj0 hjN, if_pos hgX]
      have hnot : ¬ (g ∈ E ∧ ¬ spec.core.Crosses W g) := fun h => h.2 hgcross
      rw [hzero, if_neg hnot]
    · have hcong : (∑ j ∈ Finset.Ioo 0 N, Rd (spec.slotPoint N hN g j))
          = ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) :=
        Finset.sum_congr rfl fun j hj => by
          obtain ⟨hj0, hjN⟩ := Finset.mem_Ioo.mp hj
          rw [hB g j hj0 hjN, if_neg hgX]
      rw [hcong, ← spec.edgeChipCount_eq_sum_slotPoint N hN hunit D g, hDedge g]
      by_cases hgE : g ∈ E
      · have hyes : g ∈ E ∧ ¬ spec.core.Crosses W g :=
          ⟨hgE, fun hc => hgX (spec.mem_crossing.mpr ⟨hgE, hc⟩)⟩
        rw [if_pos hgE, if_pos hyes]
      · have hno : ¬ (g ∈ E ∧ ¬ spec.core.Crosses W g) := fun h => hgE h.1
        rw [if_neg hgE, if_neg hno]

/-! ## The move theorems

`moves_classified` and `bridgeSet_forced` are proved here; the bridge-move
theorems `exists_legal_bridge_move`, `dichotomy` and `swap` are in
`GenusSixOddDescent/Swap.lean`. -/

/-! ### Private helpers

The generic facts about legal sets are `Gonality.num_edges_le_outdeg_S` and
`Gonality.mem_of_apply_le_zero` (`Utilities/Gonality/LegalFiringChain.lean`),
and the slot geometry is `vertex_cases`.

The propagation helpers below are the forms
`Utilities/Subdivision/SlotPropagation.lean` does not package, because the pivot
vertex `v` of a state **carries a chip** and therefore fails every
`D (coreVertex w) = 0` hypothesis there.  Propagation out of `v` has to start at
the offset-one point instead (`propagate_from`), and the hole gap in
`moves_classified` is closed by running *down* a slot rather than up it
(`propagate_down`): a chipless member of a legal set drags **both** of its fine
neighbours in, and the downward direction is the one that reaches back to the
offset-one point at `v`. -/

/-- A tail-relative offset read from the endpoint `z`. -/
private theorem slotPoint_eq_sidePoint (g : Fin p) (z : Fin n) {i : ℕ}
    (hi : i ≤ N) :
    spec.slotPoint N hN g i = spec.sidePoint N hN g z (spec.sideOffset N g z i) := by
  rw [spec.sidePoint_eq_slotPoint N hN g z (spec.sideOffset N g z i),
    spec.sideOffset_sideOffset N g z hi]

/-- **Propagation up a slot from a member at an arbitrary offset.**  The base
case of the helper `propagate_run` of `GenusSixOddDescent/Chain.lean` is a core
vertex of vanishing outdegree, and that of `propagate_chipless`
(`Utilities/Subdivision/SlotPropagation.lean`) a chipless core vertex; here it is
simply a member of `T` at offset `m`, which is what the pivot's *escape*
analysis produces (the offset-one point of every non-escaping slot at `v`). -/
private theorem propagate_from (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph}
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T) (g : Fin p) (z : Fin n)
    {m c : ℕ} (hcN : c ≤ N) (hmT : spec.sidePoint N hN g z m ∈ T)
    (hzero : ∀ k, m ≤ k → k < c → D (spec.sidePoint N hN g z k) = 0) :
    ∀ i, m + i ≤ c → spec.sidePoint N hN g z (m + i) ∈ T := by
  intro i
  induction i with
  | zero => intro _; simpa using hmT
  | succ i ih =>
      intro hle
      exact Gonality.mem_of_apply_le_zero hT (ih (by omega))
        (le_of_eq (hzero (m + i) (by omega) (by omega)))
        (spec.num_edges_sidePoint_succ_pos N hN hunit g z (k := m + i) (by omega))

/-- **Propagation down a slot from a chipless member.**  If the offsets
`1, …, c` of `g` are chipless and offset `c` lies in `T`, then so does every
offset below it — legality gives a chipless member vanishing outdegree, and the
lower neighbour is one of its two fine neighbours. -/
private theorem propagate_down (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph}
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T) (g : Fin p) (z : Fin n)
    {c : ℕ} (hcN : c ≤ N) (hcT : spec.sidePoint N hN g z c ∈ T)
    (hzero : ∀ k, 0 < k → k ≤ c → D (spec.sidePoint N hN g z k) = 0) :
    ∀ k, k ≤ c → spec.sidePoint N hN g z k ∈ T := by
  have hstep : ∀ i, i ≤ c → spec.sidePoint N hN g z (c - i) ∈ T := by
    intro i
    induction i with
    | zero => intro _; simpa using hcT
    | succ i ih =>
        intro hi
        have hadj : 0 < num_edges (spec.scale N hN).graph
            (spec.sidePoint N hN g z (c - i))
            (spec.sidePoint N hN g z (c - (i + 1))) := by
          have h := spec.num_edges_sidePoint_succ_pos N hN hunit g z
            (k := c - (i + 1)) (by omega)
          rw [show c - (i + 1) + 1 = c - i by omega, num_edges_symmetric] at h
          exact h
        exact Gonality.mem_of_apply_le_zero hT (ih (by omega))
          (le_of_eq (hzero (c - i) (by omega) (by omega))) hadj
  intro k hk
  have h := hstep (c - k) (by omega)
  rwa [show c - (c - k) = k by omega] at h

/-- **`2 ≤ N` at a state.**  `E` is non-empty (`E.card = 3`) and its slots carry
their chip at an interior offset, which needs an interior vertex. -/
private theorem two_le_scale_of_typeI (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) : 2 ≤ N := by
  obtain ⟨e, he⟩ : E.Nonempty := Finset.card_pos.mp (by rw [hD.2.2.2.1]; norm_num)
  obtain ⟨c, hc0, hcN, -, -⟩ := spec.exists_chip_offset N hN hunit hD.1
    (show spec.edgeChipCount N hN D e = 1 by rw [hD.2.2.2.2 e, if_pos he])
  omega

/-- **The unique escaping slot at the pivot.**  With `outdeg_S T (coreVertex v)
= 1` exactly one slot at `v` fails to have its offset-one point in `T`; every
other slot at `v` is entered.  This is `outdeg_coreVertex_eq` read through
`Finset.card_eq_one`. -/
private theorem exists_escape_slot (hunit : spec.IsUnit) (h2N : 2 ≤ N)
    {T : Finset (spec.scale N hN).graph.V} {v : Fin n}
    (hout : outdeg_S (spec.scale N hN).graph T
      ((spec.scale N hN).coreVertex v) = 1) :
    ∃ f : Fin p, spec.core.Incident f v ∧ spec.sidePoint N hN f v 1 ∉ T ∧
      ∀ g : Fin p, spec.core.Incident g v → g ≠ f →
        spec.sidePoint N hN g v 1 ∈ T := by
  classical
  set A : Finset (Fin p) := Finset.univ.filter
    (fun g => spec.core.Incident g v ∧ spec.sidePoint N hN g v 1 ∉ T) with hAdef
  have hAmem : ∀ g : Fin p, g ∈ A ↔
      (spec.core.Incident g v ∧ spec.sidePoint N hN g v 1 ∉ T) := by
    intro g; simp [hAdef]
  have hcard : (A.card : ℤ) = 1 := by
    rw [← spec.outdeg_coreVertex_eq N hN hunit h2N T v A hAmem]; exact hout
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp (by exact_mod_cast hcard)
  have hfA : f ∈ A := by rw [hf]; exact Finset.mem_singleton_self f
  obtain ⟨hfinc, hfout⟩ := (hAmem f).mp hfA
  refine ⟨f, hfinc, hfout, fun g hginc hgf => ?_⟩
  by_contra hgT
  exact hgf (Finset.mem_singleton.mp (hf ▸ (hAmem g).mpr ⟨hginc, hgT⟩))

/-- **Filling a slot at the pivot.**  `g` is a slot at `v` carrying at most one
interior chip, entered from `v` at offset one, and whose far endpoint is a
chipless member of `T`.  Then all of `g` lies in `T`: on a chipless slot one run
from the far end suffices, and on a one-chip slot the far run reaches down to the
chip while the run out of `v` reaches up to it. -/
private theorem fill_slot_at_pivot (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} (hDeff : effective D)
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T) (g : Fin p) {v : Fin n}
    (hinc : spec.core.Incident g v)
    (hvT : (spec.scale N hN).coreVertex v ∈ T)
    (hone : spec.sidePoint N hN g v 1 ∈ T)
    (hfarT : (spec.scale N hN).coreVertex (spec.core.otherEnd g v) ∈ T)
    (hfarD : D ((spec.scale N hN).coreVertex (spec.core.otherEnd g v)) = 0)
    (hchip : ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1) :
    ∀ k, k ≤ N → spec.sidePoint N hN g v k ∈ T := by
  classical
  have hwinc : spec.core.Incident g (spec.core.otherEnd g v) :=
    spec.core.incident_otherEnd g v
  have hwv : spec.core.otherEnd g v ≠ v :=
    spec.core.otherEnd_ne hinc (spec.core_loopless g)
  have hswap : ∀ k, k ≤ N →
      spec.sidePoint N hN g (spec.core.otherEnd g v) k
        = spec.sidePoint N hN g v (N - k) :=
    fun k hk => spec.sidePoint_swap N hN hinc hwinc (Ne.symm hwv) hk
  by_cases hfree : ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0
  · intro k hk
    have h := spec.propagate_chipless N hN hunit hT g hwinc hfarT hfarD hfree
      (N - k) (by omega)
    rwa [hswap (N - k) (by omega), show N - (N - k) = k by omega] at h
  · push Not at hfree
    obtain ⟨c, hcIoo, hcne⟩ := hfree
    obtain ⟨hc0, hcN⟩ := Finset.mem_Ioo.mp hcIoo
    have hDc : 1 ≤ D (spec.slotPoint N hN g c) := by
      have := hDeff (spec.slotPoint N hN g c); omega
    -- The chip, read from `v`.
    set cv := spec.sideOffset N g v c with hcvdef
    have hcv0 : 0 < cv := spec.sideOffset_pos N g v hc0 hcN
    have hcvN : cv < N := spec.sideOffset_lt N g v hc0 hcN
    have hpt : spec.sidePoint N hN g v cv = spec.slotPoint N hN g c := by
      rw [hcvdef, spec.sidePoint_eq_slotPoint N hN g v,
        spec.sideOffset_sideOffset N g v (le_of_lt hcN)]
    have hDcv : 1 ≤ D (spec.sidePoint N hN g v cv) := by rw [hpt]; exact hDc
    have hgap : ∀ k, 0 < k → k < N → k ≠ cv →
        D (spec.sidePoint N hN g v k) = 0 := fun k hk0 hkN hkc =>
      spec.sidePoint_apply_eq_zero_of_chip N hN hDeff g v hchip hcv0 hcvN hDcv
        hk0 hkN hkc
    -- The chip, read from the far end.
    have hDfar : 1 ≤ D (spec.sidePoint N hN g (spec.core.otherEnd g v) (N - cv)) := by
      rw [hswap (N - cv) (by omega), show N - (N - cv) = cv by omega]; exact hDcv
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [spec.sidePoint_zero N hN hunit g hinc]; exact hvT
    · by_cases hkc : k ≤ cv
      · have h := spec.propagate_from N hN hunit hT g v (m := 1) (c := cv)
          (le_of_lt hcvN) hone
          (fun j hj1 hjc => hgap j (by omega) (by omega) (by omega)) (k - 1) (by omega)
        rwa [show 1 + (k - 1) = k by omega] at h
      · have h := spec.propagate_upto_chip N hN hunit hDeff hT g hwinc hfarT hfarD
          hchip (t := N - cv) (by omega) (by omega) hDfar (N - k) (by omega)
        rwa [hswap (N - k) (by omega), show N - (N - k) = k by omega] at h

/-- **The moves at a state are classified.**  Every proper non-empty legal set
for a state is either a *hole* forward set on a chip slot at `v` (carrying
`holeDiv f t R j` to `holeDiv f t R (j+1)`), or a *bridge* set whose core part is
the near side of a bridge of `G − E` at `v`.

`pivot` gives `coreVertex v ∈ T` with `outdeg_S T = 1`, so exactly one fine
neighbour of `v` is outside `T`, and `exists_slot_of_coreVertex_adj` names its
slot `f`.  If `f ∈ E` the exception is on a chip slot, `core_closure` sweeps the
connected `G − E` and the argument of `hole_legal_sets` forces
`T = fwdSet f t j`; if `f ∉ E` then `{u : coreVertex u ∈ T}` is closed under
every slot but `f`, so `f` is a bridge with that near side. -/
theorem moves_classified (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless)
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T) (hne : T.Nonempty)
    (hproper : T ≠ Finset.univ) :
    (∃ (f : Fin p) (t j : ℕ) (R : CFDiv (spec.scale N hN).graph), f ∈ E ∧
        spec.core.Incident f v ∧ 2 * (j + 1) ≤ t ∧ t - (j + 1) < N ∧
        D = spec.holeDiv N hN f t R j ∧
        T = spec.fwdSet N hN f t j ∧
        set_firing (spec.scale N hN).graph D T = spec.holeDiv N hN f t R (j + 1)) ∨
      (∃ (f : Fin p) (W : Finset (Fin n)), f ∉ E ∧ spec.core.Incident f v ∧
        spec.core.IsBridgeOff E f ∧ spec.core.IsNearSide E f v W ∧
        ∀ u : Fin n, ((spec.scale N hN).coreVertex u ∈ T ↔ u ∈ W)) := by
  -- The English proof is the docstring above.  Two features of the formal proof
  -- are forced by the pivot carrying a chip.
  -- (a) `hole_legal_sets` is *not* invoked: its `1 ≤ j` excludes the state,
  --     which sits at `j = 0`.  Step 3 of H4 is re-run here in the
  --     `sidePoint`-from-`v` coordinates, where the gap `[1, c-1]` is closed by
  --     `propagate_down` from any member instead of by a maximal-run argument.
  -- (b) `core_closure` is used only away from `v`; at `v` the run starts at the
  --     offset-one point (`propagate_from`), which the escape analysis has just
  --     put inside `T`.
  -- The hole disjunct uses the sharp interiority hypothesis `t - (j + 1) < N` of
  -- `legal_fwdSet'`/`setFiring_fwdSet'`: at a head-hub state `t - j = N`.
  --
  -- `hbridgeless` is *not* used: bridgelessness of `G` is what makes a bridge
  -- move non-empty (`crossing_nonempty`, the field `supPos` of the adapter), not
  -- what classifies the moves.  It stays in the signature because
  -- `GenusSixOddDescent/Swap.lean` and `GenusSixOddDescent/HubSystem.lean` pass it
  -- straight on to `stateBridgeData`.
  have _ := hbridgeless
  classical
  have hDeff : effective D := hD.1
  have hDcore : ∀ u : Fin n,
      D ((spec.scale N hN).coreVertex u) = if u = v then 1 else 0 := hD.2.2.1
  have hDedge : ∀ e : Fin p,
      spec.edgeChipCount N hN D e = if e ∈ E then 1 else 0 := hD.2.2.2.2
  have h2N : 2 ≤ N := spec.two_le_scale_of_typeI N hN hunit hD
  have hchip : ∀ g : Fin p,
      ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1 := by
    intro g
    refine spec.sum_interior_le_one_of_edgeChipCount_le_one N hN hunit ?_
    rw [hDedge g]; split <;> omega
  have hfree : ∀ g : Fin p, g ∉ E →
      ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0 := fun g hg =>
    spec.slotPoint_eq_zero_of_edgeChipCount_zero N hN hunit hDeff
      (by rw [hDedge g, if_neg hg])
  -- **The pivot and its escaping slot.**
  obtain ⟨hvT, hout⟩ := spec.pivot N hN hunit hD hconn hT hne hproper
  obtain ⟨f, hfinc, hf1, hentered⟩ := spec.exists_escape_slot N hN hunit h2N hout
  -- **The core part of `T`,** and its closure in `G − E − f`.
  set U : Finset (Fin n) :=
    Finset.univ.filter (fun u => (spec.scale N hN).coreVertex u ∈ T) with hUdef
  have hUmem : ∀ u : Fin n, u ∈ U ↔ (spec.scale N hN).coreVertex u ∈ T := by
    intro u; simp [hUdef]
  have hvU : v ∈ U := (hUmem v).mpr hvT
  have hclosed : spec.core.ClosedOff (insert f E) U := by
    intro g hg hcross
    have hgE : g ∉ E := fun h => hg (Finset.mem_insert_of_mem h)
    have hgf : g ≠ f := fun h => hg (by rw [h]; exact Finset.mem_insert_self f E)
    have hgfree := hfree g hgE
    have hboth : ∀ z : Fin n, spec.core.Incident g z → z ∈ U →
        spec.core.tail g ∈ U ∧ spec.core.head g ∈ U := by
      intro z hzinc hzU
      have hfarT : spec.sidePoint N hN g z N ∈ T := by
        by_cases hzv : z = v
        · have hzvinc : spec.core.Incident g v := by rw [← hzv]; exact hzinc
          have hone : spec.sidePoint N hN g z 1 ∈ T := by
            rw [hzv]; exact hentered g hzvinc hgf
          have h := spec.propagate_from N hN hunit hT g z (m := 1) (c := N) le_rfl
            hone
            (fun k hk1 hkN => spec.sidePoint_apply_eq_zero_of_chipless N hN g z
              hgfree (by omega) hkN)
            (N - 1) (by omega)
          rwa [show 1 + (N - 1) = N by omega] at h
        · exact spec.propagate_chipless N hN hunit hT g hzinc ((hUmem z).mp hzU)
            (by rw [hDcore z, if_neg hzv]) hgfree N le_rfl
      by_cases hc : spec.core.tail g = z
      · rw [spec.sidePoint_last_of_tail N hN hunit g hc] at hfarT
        exact ⟨hc ▸ hzU, (hUmem _).mpr hfarT⟩
      · rw [spec.sidePoint_last_of_ne N hN g hc] at hfarT
        exact ⟨(hUmem _).mpr hfarT, (hzinc.resolve_left hc) ▸ hzU⟩
    rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hboth _ (Or.inl rfl) h1).2
    · exact h2 (hboth _ (Or.inr rfl) h1).1
  by_cases hfE : f ∈ E
  · -- **The hole branch.**  `U` is closed in `G − E`, hence everything.
    left
    have hallT : ∀ u : Fin n, (spec.scale N hN).coreVertex u ∈ T := by
      intro u
      refine (hUmem u).mp ?_
      by_contra hu
      obtain ⟨e, heE, hecross⟩ := hconn U ⟨v, u, hvU, hu⟩
      have hef : e ≠ f := fun h => heE (by rw [h]; exact hfE)
      exact hclosed e (fun hmem => (Finset.mem_insert.mp hmem).elim hef heE) hecross
    -- Every slot but `f` is swallowed whole.
    have hfill : ∀ g : Fin p, g ≠ f → ∀ k, k ≤ N →
        spec.slotPoint N hN g k ∈ T := by
      intro g hgf k hk
      by_cases hvinc : spec.core.Incident g v
      · have hwv : spec.core.otherEnd g v ≠ v :=
          spec.core.otherEnd_ne hvinc (spec.core_loopless g)
        have hfl := spec.fill_slot_at_pivot N hN hunit hDeff hT g hvinc hvT
          (hentered g hvinc hgf) (hallT _) (by rw [hDcore _, if_neg hwv]) (hchip g)
          (spec.sideOffset N g v k) (spec.sideOffset_le N g v hk)
        rwa [← spec.slotPoint_eq_sidePoint N hN g v hk] at hfl
      · have htv : spec.core.tail g ≠ v := fun h => hvinc (Or.inl h)
        have hhv : spec.core.head g ≠ v := fun h => hvinc (Or.inr h)
        exact spec.propagate_both_ends N hN hunit hDeff hT g (hallT _)
          (by rw [hDcore _, if_neg htv]) (hallT _)
          (by rw [hDcore _, if_neg hhv]) (hchip g) hk
    -- **The hole on `f`**, read from `v`: filled from the chip outwards, empty
    -- between `v` and the chip.
    have hchipf : spec.edgeChipCount N hN D f = 1 := by rw [hDedge f, if_pos hfE]
    obtain ⟨c, hc0, hcN, hDc, hcrest⟩ :=
      spec.exists_chip_offset_side N hN hunit hDeff v hchipf
    have hwv : spec.core.otherEnd f v ≠ v :=
      spec.core.otherEnd_ne hfinc (spec.core_loopless f)
    have hswap : ∀ k, k ≤ N →
        spec.sidePoint N hN f (spec.core.otherEnd f v) k
          = spec.sidePoint N hN f v (N - k) := fun k hk =>
      spec.sidePoint_swap N hN hfinc (spec.core.incident_otherEnd f v)
        (Ne.symm hwv) hk
    have hDfar : 1 ≤ D (spec.sidePoint N hN f (spec.core.otherEnd f v) (N - c)) := by
      rw [hswap (N - c) (by omega), show N - (N - c) = c by omega, hDc]
    have habove : ∀ k, c ≤ k → k ≤ N → spec.sidePoint N hN f v k ∈ T := by
      intro k hck hkN
      have h := spec.propagate_upto_chip N hN hunit hDeff hT f
        (spec.core.incident_otherEnd f v) (hallT _)
        (by rw [hDcore _, if_neg hwv]) (hchip f) (t := N - c) (by omega) (by omega)
        hDfar (N - k) (by omega)
      rwa [hswap (N - k) (by omega), show N - (N - k) = k by omega] at h
    have hbelow : ∀ k, 0 < k → k < c → spec.sidePoint N hN f v k ∉ T := by
      intro k hk0 hkc hmem
      exact hf1 (spec.propagate_down N hN hunit hT f v (c := k) (by omega) hmem
        (fun j hj0 hjk => hcrest j hj0 (by omega) (by omega)) 1 hk0)
    have hc2 : 2 ≤ c := by
      by_contra hcon
      exact hf1 (habove 1 (by omega) (by omega))
    -- The set is the complement of the gap, whatever the orientation of `f`.
    have hTeq_gen : ∀ s e : ℕ, 1 ≤ s → e < N →
        (∀ i, 0 < i → i < N →
          (spec.slotPoint N hN f i ∈ T ↔ ¬ (s ≤ i ∧ i ≤ e))) →
        T = (spec.slotInterval N hN f s e)ᶜ := by
      intro s e hs1 heN hfchar
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_compl]
      rcases spec.vertex_cases N hN hunit x with ⟨u, rfl⟩ | ⟨g, i, hi0, hiN, rfl⟩
      · refine ⟨fun _ hmem => ?_, fun _ => hallT u⟩
        obtain ⟨k, hk1, hk2, hk3⟩ := (spec.mem_slotInterval_iff N hN f s e _).mp hmem
        exact spec.coreVertex_ne_slotPoint N hN hunit u f (t := k) (by omega)
          (by omega) hk3.symm
      · by_cases hgf : g = f
        · rw [hgf, spec.slotPoint_mem_slotInterval_iff N hN hunit f (s := s) (t := e)
            (j := i) (by omega) (by omega)]
          exact hfchar i hi0 hiN
        · refine ⟨fun _ hmem => ?_, fun _ => hfill g hgf i (le_of_lt hiN)⟩
          obtain ⟨k, hk1, hk2, hk3⟩ := (spec.mem_slotInterval_iff N hN f s e _).mp hmem
          exact hgf (spec.slot_eq_of_slotPoint_eq N hN hunit (a := k) (b := i)
            (by omega) (by omega) hi0 hiN hk3).symm
    obtain ⟨t, j, hjt, htj, hTeq⟩ :
        ∃ t j : ℕ, 2 * (j + 1) ≤ t ∧ t - (j + 1) < N ∧
          T = spec.fwdSet N hN f t j := by
      by_cases hc1 : spec.core.tail f = v
      · refine ⟨c, 0, by omega, by omega, ?_⟩
        have hfchar : ∀ i, 0 < i → i < N →
            (spec.slotPoint N hN f i ∈ T ↔ ¬ (1 ≤ i ∧ i ≤ c - 1)) := by
          intro i hi0 hiN
          rw [← spec.sidePoint_of_tail N hN f hc1 i]
          refine ⟨fun hmem hcon => hbelow i hi0 (by omega) hmem, fun hcon => ?_⟩
          exact habove i (by omega) (le_of_lt hiN)
        have h := hTeq_gen 1 (c - 1) le_rfl (by omega) hfchar
        simp only [fwdSet, backSet, Nat.zero_add]
        exact h
      · refine ⟨2 * N - c, N - c, by omega, by omega, ?_⟩
        have hfchar : ∀ i, 0 < i → i < N →
            (spec.slotPoint N hN f i ∈ T ↔ ¬ (N - c + 1 ≤ i ∧ i ≤ N - 1)) := by
          intro i hi0 hiN
          have hpt : spec.slotPoint N hN f i = spec.sidePoint N hN f v (N - i) := by
            rw [spec.sidePoint_of_ne N hN f hc1 (N - i),
              show N - (N - i) = i by omega]
          rw [hpt]
          refine ⟨fun hmem hcon => hbelow (N - i) (by omega) (by omega) hmem,
            fun hcon => habove (N - i) (by omega) (by omega)⟩
        have h := hTeq_gen (N - c + 1) (N - 1) (by omega) (by omega) hfchar
        simp only [fwdSet, backSet]
        rw [show 2 * N - c - (N - c + 1) = N - 1 by omega]
        exact h
    obtain ⟨R, hRdef⟩ : ∃ R : CFDiv (spec.scale N hN).graph,
        R = D - one_chip (spec.slotPoint N hN f j)
          - one_chip (spec.slotPoint N hN f (t - j)) := ⟨_, rfl⟩
    have hDeq : D = spec.holeDiv N hN f t R j := by
      rw [hRdef]
      simp only [holeDiv]
      exact (chip_rest_cancel D _ _).symm
    refine ⟨f, t, j, R, hfE, hfinc, hjt, htj, hDeq, hTeq, ?_⟩
    rw [hDeq, hTeq]
    exact spec.setFiring_fwdSet' N hN hunit f hjt htj R
  · -- **The bridge branch.**  `U` is a proper closed set of `G − E − f`.
    right
    have hUproper : U ≠ Finset.univ := by
      intro hcon
      have hwT : (spec.scale N hN).coreVertex (spec.core.otherEnd f v) ∈ T :=
        (hUmem _).mp (by rw [hcon]; exact Finset.mem_univ _)
      have hwv : spec.core.otherEnd f v ≠ v :=
        spec.core.otherEnd_ne hfinc (spec.core_loopless f)
      have h := spec.propagate_chipless N hN hunit hT f
        (spec.core.incident_otherEnd f v) hwT (by rw [hDcore _, if_neg hwv])
        (hfree f hfE) (N - 1) (by omega)
      rw [spec.sidePoint_swap N hN hfinc (spec.core.incident_otherEnd f v)
          (Ne.symm hwv) (show N - 1 ≤ N by omega),
        show N - (N - 1) = 1 by omega] at h
      exact hf1 h
    refine ⟨f, U, hfE, hfinc, ⟨hfE, hconn, ?_⟩, ⟨hvU, hUproper, hclosed⟩,
      fun u => (hUmem u).symm⟩
    intro hconn'
    obtain ⟨u, hu⟩ : ∃ u : Fin n, u ∉ U := by
      by_contra hc
      push Not at hc
      exact hUproper (Finset.eq_univ_iff_forall.mpr hc)
    obtain ⟨e, heE, hecross⟩ := hconn' U ⟨v, u, hvU, hu⟩
    exact hclosed e heE hecross

/-- **The bridge branch of `moves_classified` is the bridge chain at `k = 0`.**  A
legal set whose core part is the near side `W` is *exactly* `bridgeSet 0`, so
`bridgeSet_step` at `k = 0` names its landing divisor `bridgeDiv 1`.  This
upgrades the "core part" form of the bridge branch in `moves_classified` to an
identification of the set itself. -/
theorem bridgeSet_forced (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W)
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph D T)
    (hTcore : ∀ u : Fin n, ((spec.scale N hN).coreVertex u ∈ T ↔ u ∈ W)) :
    T = (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeSet 0 := by
  -- `propagate_upto_chip`/`not_mem_beyond_chip` pin `T` slot by slot against the
  -- four `mem_bridgeSet_*` rules of `GenusSixOddDescent/BridgeChain.lean`.  The
  -- one new ingredient is that the pivot `v` carries a chip, so the runs that
  -- start there start at offset one (`fill_slot_at_pivot`, `propagate_from`)
  -- rather than at `v`.
  classical
  set d := spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW
    with hddef
  have hDeff : effective D := hD.1
  have hDcore : ∀ u : Fin n,
      D ((spec.scale N hN).coreVertex u) = if u = v then 1 else 0 := hD.2.2.1
  have hDedge : ∀ e : Fin p,
      spec.edgeChipCount N hN D e = if e ∈ E then 1 else 0 := hD.2.2.2.2
  have h2N : 2 ≤ N := spec.two_le_scale_of_typeI N hN hunit hD
  have hchip : ∀ g : Fin p,
      ∑ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) ≤ 1 := by
    intro g
    refine spec.sum_interior_le_one_of_edgeChipCount_le_one N hN hunit ?_
    rw [hDedge g]; split <;> omega
  have hfree : ∀ g : Fin p, g ∉ E →
      ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN g j) = 0 := fun g hg =>
    spec.slotPoint_eq_zero_of_edgeChipCount_zero N hN hunit hDeff
      (by rw [hDedge g, if_neg hg])
  have hvW : v ∈ W := hW.1
  have hvT : (spec.scale N hN).coreVertex v ∈ T := (hTcore v).mpr hvW
  -- `T` is non-empty and proper, so `pivot` applies.
  have hTne : T.Nonempty := ⟨_, hvT⟩
  have hTproper : T ≠ Finset.univ := by
    obtain ⟨u, hu⟩ : ∃ u : Fin n, u ∉ W := by
      by_contra hc
      push Not at hc
      exact hW.2.1 (Finset.eq_univ_iff_forall.mpr hc)
    intro hcon
    exact hu ((hTcore u).mp (by rw [hcon]; exact Finset.mem_univ _))
  obtain ⟨-, hout⟩ := spec.pivot N hN hunit hD hconn hT hTne hTproper
  -- The bridge slot is chipless, and its far endpoint leaves `W`.
  have hfE : f ∉ E := hbridge.1
  have hffree : ∀ j ∈ Finset.Ioo 0 N, D (spec.slotPoint N hN f j) = 0 := hfree f hfE
  have hfar : spec.core.otherEnd f v ∉ W :=
    spec.core.otherEnd_not_mem_of_crosses hinc hvW
      (spec.crosses_of_isNearSide hconn hW)
  have hfarT : (spec.scale N hN).coreVertex (spec.core.otherEnd f v) ∉ T :=
    fun hc => hfar ((hTcore _).mp hc)
  -- **The escape is on `f`.**  Otherwise a chipless run along `f` from offset one
  -- reaches the far endpoint, which is outside `T`.
  have hf1 : spec.sidePoint N hN f v 1 ∉ T := by
    intro hc
    have h := spec.propagate_from N hN hunit hT f v (m := 1) (c := N) le_rfl hc
      (fun k hk1 hkN =>
        spec.sidePoint_apply_eq_zero_of_chipless N hN f v hffree (by omega) hkN)
      (N - 1) (by omega)
    rw [show 1 + (N - 1) = N by omega, spec.sidePoint_last N hN hunit f v] at h
    exact hfarT h
  obtain ⟨f', hf'inc, hf'out, hf'in⟩ := spec.exists_escape_slot N hN hunit h2N hout
  have hfeq : f' = f := by
    by_contra hne'
    exact hf1 (hf'in f hinc (Ne.symm hne'))
  have hentered : ∀ g : Fin p, spec.core.Incident g v → g ≠ f →
      spec.sidePoint N hN g v 1 ∈ T := fun g hginc hgf =>
    hf'in g hginc (by rw [hfeq]; exact hgf)
  -- **Slots inside `W`** are swallowed whole.
  have hinside : ∀ g : Fin p, spec.core.tail g ∈ W → spec.core.head g ∈ W →
      ∀ k, k ≤ N → spec.slotPoint N hN g k ∈ T := by
    intro g htW hhW k hk
    have hnotcross : ¬ spec.core.Crosses W g := by
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h hhW
      · exact h htW
    by_cases hvinc : spec.core.Incident g v
    · have hw : spec.core.otherEnd g v ∈ W :=
        spec.core.otherEnd_mem_of_not_crosses hvinc hvW hnotcross
      have hwv : spec.core.otherEnd g v ≠ v :=
        spec.core.otherEnd_ne hvinc (spec.core_loopless g)
      have hgf : g ≠ f := by
        intro hgf'
        exact hfar (by rw [← hgf']; exact hw)
      have hfill := spec.fill_slot_at_pivot N hN hunit hDeff hT g hvinc hvT
        (hentered g hvinc hgf) ((hTcore _).mpr hw)
        (by rw [hDcore _, if_neg hwv]) (hchip g)
        (spec.sideOffset N g v k) (spec.sideOffset_le N g v hk)
      rwa [← spec.slotPoint_eq_sidePoint N hN g v hk] at hfill
    · have htv : spec.core.tail g ≠ v := fun h => hvinc (Or.inl h)
      have hhv : spec.core.head g ≠ v := fun h => hvinc (Or.inr h)
      exact spec.propagate_both_ends N hN hunit hDeff hT g ((hTcore _).mpr htW)
        (by rw [hDcore _, if_neg htv]) ((hTcore _).mpr hhW)
        (by rw [hDcore _, if_neg hhv]) (hchip g) hk
  -- **Slots outside `W`** are untouched (`slotInterior_disjoint_of_chip_le_one`).
  have houtside : ∀ g : Fin p, spec.core.tail g ∉ W → spec.core.head g ∉ W →
      ∀ i, 0 < i → i < N → spec.slotPoint N hN g i ∉ T := fun g htW hhW i hi0 hiN =>
    spec.slotInterior_disjoint_of_chip_le_one N hN hunit hDeff hT g (hchip g)
      (fun hc => htW ((hTcore _).mp hc)) (fun hc => hhW ((hTcore _).mp hc)) hi0 hiN
  -- **The bridge slot** is entered nowhere beyond `v` itself.
  have hfslot : ∀ k, 0 < k → k ≤ N → spec.sidePoint N hN f v k ∉ T := by
    intro k hk0 hkN hc
    by_cases hkeq : k = N
    · rw [hkeq, spec.sidePoint_last N hN hunit f v] at hc; exact hfarT hc
    · exact hf1 (spec.propagate_down N hN hunit hT f v (c := k) hkN hc
        (fun j hj0 hjk =>
          spec.sidePoint_apply_eq_zero_of_chipless N hN f v hffree hj0 (by omega))
        1 hk0)
  -- **A crossing chip slot** is swallowed exactly up to its chip.
  have hXslot : ∀ e ∈ spec.crossing E W, ∀ k, k ≤ N →
      (spec.sidePoint N hN e (spec.nearEndpoint W e) k ∈ T ↔
        k ≤ spec.offsetFromSide N hN D W e) := by
    intro e he k hk
    obtain ⟨heE, hecross⟩ := spec.mem_crossing.mp he
    have hchipe : spec.edgeChipCount N hN D e = 1 := by rw [hDedge e, if_pos heE]
    set z := spec.nearEndpoint W e with hzdef
    set c := spec.offsetFromSide N hN D W e with hcdef
    have hzW : z ∈ W := spec.nearEndpoint_mem hecross
    have hzinc : spec.core.Incident e z := spec.nearEndpoint_incident W e
    have hc0 : 0 < c := spec.one_le_offsetFromSide N hN hunit hDeff hchipe W
    have hcN : c < N := spec.offsetFromSide_lt N hN hunit hDeff hchipe W
    have hDc : D (spec.sidePoint N hN e z c) = 1 :=
      spec.offsetFromSide_chip N hN hunit hDeff hchipe W
    have hDc1 : 1 ≤ D (spec.sidePoint N hN e z c) := le_of_eq hDc.symm
    have hzT : (spec.scale N hN).coreVertex z ∈ T := (hTcore z).mpr hzW
    have hfarz : spec.core.otherEnd e z ∉ W :=
      spec.core.otherEnd_not_mem_of_crosses hzinc hzW hecross
    have hfarzT : spec.sidePoint N hN e z N ∉ T := by
      rw [spec.sidePoint_last N hN hunit e z]
      exact fun hcon => hfarz ((hTcore _).mp hcon)
    have hup : ∀ m, m ≤ c → spec.sidePoint N hN e z m ∈ T := by
      by_cases hzv : z = v
      · intro m hm
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · rw [spec.sidePoint_zero N hN hunit e hzinc]; exact hzT
        · have hef : e ≠ f := fun h => hfE (h ▸ heE)
          have hzvinc : spec.core.Incident e v := by rw [← hzv]; exact hzinc
          have hone : spec.sidePoint N hN e z 1 ∈ T := by
            rw [hzv]; exact hentered e hzvinc hef
          have h := spec.propagate_from N hN hunit hT e z (m := 1) (c := c)
            (le_of_lt hcN) hone
            (fun j hj1 hjc => spec.sidePoint_apply_eq_zero_of_chip N hN hDeff e z
              (hchip e) hc0 hcN hDc1 (by omega) (by omega) (by omega))
            (m - 1) (by omega)
          rwa [show 1 + (m - 1) = m by omega] at h
      · intro m hm
        exact spec.propagate_upto_chip N hN hunit hDeff hT e hzinc hzT
          (by rw [hDcore z, if_neg hzv]) (hchip e) hc0 hcN hDc1 m hm
    have hdown : ∀ m, c < m → m ≤ N → spec.sidePoint N hN e z m ∉ T := by
      intro m hcm hmN
      by_cases hmeq : m = N
      · rw [hmeq]; exact hfarzT
      · exact spec.not_mem_beyond_chip N hN hunit hDeff hT e (w := z) (hchip e)
          hc0 hcN hDc1 hfarzT hcm (by omega)
    exact ⟨fun hmem => by
        by_contra hcon
        exact hdown k (by omega) hk hmem, fun hle => hup k hle⟩
  -- **A crossing slot** is either a crossing chip slot or the bridge itself
  -- (the cut condition of the adapter).
  have hslotcross : ∀ g : Fin p, spec.core.Crosses W g → ∀ i, 0 < i → i < N →
      (spec.slotPoint N hN g i ∈ T ↔ spec.slotPoint N hN g i ∈ d.bridgeSet 0) := by
    intro g hcross i hi0 hiN
    have hcut : g ∈ spec.crossing E W ∨ g = f := d.cutSub g hcross
    rcases hcut with hgX | hgf
    · have hchipe : spec.edgeChipCount N hN D g = 1 := by
        rw [hDedge g, if_pos (spec.crossing_subset E W hgX)]
      have hcN : spec.offsetFromSide N hN D W g < N :=
        spec.offsetFromSide_lt N hN hunit hDeff hchipe W
      have hcle : spec.sideOffset N g (spec.nearEndpoint W g) i ≤ N :=
        spec.sideOffset_le N g _ (le_of_lt hiN)
      rw [spec.slotPoint_eq_sidePoint N hN g (spec.nearEndpoint W g) (le_of_lt hiN)]
      refine (hXslot g hgX _ hcle).trans ?_
      exact (d.mem_bridgeSet_frontX_iff hunit hgX
        (show spec.offsetFromSide N hN D W g + 0 < N by omega) hcle).symm
    · rw [hgf]
      have hcle : spec.sideOffset N f v i ≤ N :=
        spec.sideOffset_le N f v (le_of_lt hiN)
      have hc0 : 0 < spec.sideOffset N f v i := spec.sideOffset_pos N f v hi0 hiN
      rw [spec.slotPoint_eq_sidePoint N hN f v (le_of_lt hiN)]
      refine ⟨fun hmem => absurd hmem (hfslot _ hc0 hcle), fun hmem => ?_⟩
      have hle := (d.mem_bridgeSet_frontF_iff hunit (k := 0) hN hcle).mp hmem
      omega
  -- **The four classes of slot, against the four membership rules.**
  refine Finset.ext fun x => ?_
  rcases spec.vertex_cases N hN hunit x with ⟨u, rfl⟩ | ⟨g, i, hi0, hiN, rfl⟩
  · have hbs : ((spec.scale N hN).coreVertex u ∈ d.bridgeSet 0) ↔ u ∈ W :=
      d.coreVertex_mem_bridgeSet_iff 0 u
    rw [hbs]; exact hTcore u
  · by_cases htW : spec.core.tail g ∈ W <;> by_cases hhW : spec.core.head g ∈ W
    · exact ⟨fun _ => d.mem_bridgeSet_of_inside hunit 0 htW hhW (le_of_lt hiN),
        fun _ => hinside g htW hhW i (le_of_lt hiN)⟩
    · have hcross : spec.core.Crosses W g := Or.inl ⟨htW, hhW⟩
      exact hslotcross g hcross i hi0 hiN
    · have hcross : spec.core.Crosses W g := Or.inr ⟨hhW, htW⟩
      exact hslotcross g hcross i hi0 hiN
    · have hgf : g ≠ f := by
        intro hgf'
        rcases hinc with h | h
        · exact htW (by rw [hgf', h]; exact hvW)
        · exact hhW (by rw [hgf', h]; exact hvW)
      have hgX : g ∉ spec.crossing E W := by
        intro hmem
        rcases (spec.mem_crossing.mp hmem).2 with ⟨h, -⟩ | ⟨h, -⟩
        · exact htW h
        · exact hhW h
      exact ⟨fun hmem => absurd hmem (houtside g htW hhW i hi0 hiN),
        fun hmem => absurd hmem (d.not_mem_bridgeSet_of_outside hunit 0 htW hhW
          hgf hgX (le_of_lt hiN))⟩

end Spec

end SubdivisionGraph

end Utilities.Certificate
