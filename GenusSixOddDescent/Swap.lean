module

public import GenusSixOddDescent.Moves

@[expose] public section

/-!
# Bridge moves and swaps of states

`exists_legal_bridge_move` initiates the bridge chain from a state.
`dichotomy` shows that exactly one crossing slot attains the maximal chip
offset: two maxima would produce two core chips, contrary to nonselection.
`swap` identifies the landing divisor as the state at the far end of that
slot, with the corresponding exchange of chip slots.
-/

namespace Utilities.Certificate

namespace SubdivisionGraph

namespace Spec

open Utilities Utilities.Gonality

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-- **The bridge move exists and is legal.**  `bridgeSet_legal` at `k = 0`,
transported along the adapter; the legal set is named explicitly as
`bridgeSet 0` of `stateBridgeData`. -/
theorem exists_legal_bridge_move (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W) :
    legal_set (spec.scale N hN).graph D
        ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeSet 0) ∧
      ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeSet 0).Nonempty ∧
      (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeSet 0
        ≠ Finset.univ ∧
      (∀ u : Fin n, (spec.scale N hN).coreVertex u ∈
        (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeSet 0
          ↔ u ∈ W) := by
  -- `bridgeSet_legal` at `k = 0` (whose `hR : effective d.R` is
  -- `stateBridgeData_R.1`), plus `coreVertex_mem_bridgeSet_iff`; properness is
  -- the far endpoint of `f`, which `farF` puts outside `W`.
  classical
  set d := spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW
  have hR : effective d.R :=
    (spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).1
  have hzero : d.bridgeDiv 0 = D :=
    spec.stateBridgeData_bridgeDiv_zero N hN hunit hD hconn hbridgeless hinc hbridge hW
  have hlegal : legal_set (spec.scale N hN).graph D (d.bridgeSet 0) := by
    have h := d.bridgeSet_legal hunit hR (k := 0) d.one_le_tauStar
    rwa [hzero] at h
  refine ⟨hlegal, ⟨(spec.scale N hN).coreVertex v, ?_⟩, ?_, fun u =>
    d.coreVertex_mem_bridgeSet_iff 0 u⟩
  · exact (d.coreVertex_mem_bridgeSet_iff 0 v).mpr hW.1
  · intro hcon
    have hmem : (spec.scale N hN).coreVertex (spec.core.otherEnd f v) ∈ d.bridgeSet 0 := by
      rw [hcon]; exact Finset.mem_univ _
    exact d.farF ((d.coreVertex_mem_bridgeSet_iff 0 _).mp hmem)

/-! ## Private helpers: the landing divisor of the chain

The same three facts about `D_{τ*}` are used twice — once to *count* the
maximal crossing slots (`dichotomy`) and once to *name* the swap (`swap`) — so
they are factored out here.  Everything is at the abstract `Spec`. -/

/-- Membership in `crossingMax`, unfolded once (the counterpart of
`mem_crossing`). -/
private theorem mem_crossingMax {D : CFDiv (spec.scale N hN).graph}
    {E : Finset (Fin p)} {W : Finset (Fin n)} {e : Fin p} :
    e ∈ spec.crossingMax N hN D E W ↔
      e ∈ spec.crossing E W ∧
        spec.offsetFromSide N hN D W e = spec.sMax N hN D E W :=
  Finset.mem_filter

/-! ### `edgeChipCount` is additive, and sees a single chip only on its own slot

`edgeChipCount` (`GenusSixOddDescent/Cost.lean`) is a plain sum of evaluations,
so it commutes with `+` and with `∑`; on `one_chip x` it is the indicator of
"`x` is interior to this slot".  Those four facts turn the chain
`D_k = a_k(f) + Σ_e a_{t e + k}(e) + R` into a slot-by-slot chip count with no
divisor algebra at all. -/

private theorem edgeChipCount_add (D₁ D₂ : CFDiv (spec.scale N hN).graph) (g : Fin p) :
    spec.edgeChipCount N hN (D₁ + D₂) g
      = spec.edgeChipCount N hN D₁ g + spec.edgeChipCount N hN D₂ g := by
  unfold edgeChipCount
  simp only [Pi.add_apply]
  exact Finset.sum_add_distrib

private theorem edgeChipCount_sum {ι : Type*} (s : Finset ι)
    (F : ι → CFDiv (spec.scale N hN).graph) (g : Fin p) :
    spec.edgeChipCount N hN (∑ i ∈ s, F i) g
      = ∑ i ∈ s, spec.edgeChipCount N hN (F i) g := by
  unfold edgeChipCount
  simp only [Finset.sum_apply]
  exact Finset.sum_comm

/-- A chip interior to the slot `g` is counted by `g`'s chip count and by no
other slot's. -/
private theorem edgeChipCount_one_chip_slotPoint (hunit : spec.IsUnit) {g : Fin p} {o : ℕ}
    (h0 : 0 < o) (hoN : o < N) (g' : Fin p) :
    spec.edgeChipCount N hN
        (one_chip (spec.slotPoint N hN g o) : CFDiv (spec.scale N hN).graph) g'
      = if g' = g then (1 : ℤ) else 0 := by
  classical
  rw [spec.edgeChipCount_eq_sum_slotPoint N hN hunit]
  by_cases hgg : g' = g
  · have hsingle : ∀ b ∈ Finset.Ioo 0 N, b ≠ o →
        (one_chip (spec.slotPoint N hN g o) : CFDiv (spec.scale N hN).graph)
          (spec.slotPoint N hN g b) = 0 := by
      intro b hb hbo
      obtain ⟨hb0, hbN⟩ := Finset.mem_Ioo.mp hb
      exact one_chip_apply_other' _ _
        (spec.slotPoint_ne N hN hunit g (le_of_lt hbN) (le_of_lt hoN) hbo)
    rw [ite_eq_left hgg, hgg,
      Finset.sum_eq_single_of_mem o (Finset.mem_Ioo.mpr ⟨h0, hoN⟩) hsingle,
      one_chip_apply_v]
  · rw [ite_eq_right hgg]
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨hj0, hjN⟩ := Finset.mem_Ioo.mp hj
    exact one_chip_apply_other' _ _ fun h =>
      hgg (spec.slot_eq_of_slotPoint_eq N hN hunit hj0 hjN h0 hoN h)

/-- A chip that has landed on the core is counted by no slot. -/
private theorem edgeChipCount_one_chip_coreVertex (hunit : spec.IsUnit) (u : Fin n)
    (g' : Fin p) :
    spec.edgeChipCount N hN
        (one_chip ((spec.scale N hN).coreVertex u) : CFDiv (spec.scale N hN).graph) g'
      = 0 := by
  rw [spec.edgeChipCount_eq_sum_slotPoint N hN hunit]
  refine Finset.sum_eq_zero fun j hj => ?_
  obtain ⟨hj0, hjN⟩ := Finset.mem_Ioo.mp hj
  exact one_chip_apply_other' _ _
    (Ne.symm (spec.coreVertex_ne_slotPoint N hN hunit u g' hj0 hjN))

/-- **The landing divisor is an effective degree-four representative of the
class.**  Degree is read off `deg_bridgeDiv`, which does not depend on `k`, and
the equivalence off `bridgeDiv_linear_equiv` at `k = τ*`. -/
private theorem landing_data (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W) :
    effective
        ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv
          (spec.tauStar N hN D E W)) ∧
      deg ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv
          (spec.tauStar N hN D E W)) = 4 ∧
      linear_equiv (spec.scale N hN).graph D
        ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv
          (spec.tauStar N hN D E W)) := by
  classical
  set d := spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW
  have hR : effective d.R :=
    (spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).1
  have hzero : d.bridgeDiv 0 = D :=
    spec.stateBridgeData_bridgeDiv_zero N hN hunit hD hconn hbridgeless hinc hbridge hW
  have htau : d.tauStar = spec.tauStar N hN D E W :=
    spec.stateBridgeData_tauStar N hN hunit hbridgeless hD hconn hinc hbridge hW
  refine ⟨d.effective_bridgeDiv hR _, ?_, ?_⟩
  · rw [d.deg_bridgeDiv, ← d.deg_bridgeDiv 0, hzero]
    exact hD.2.1
  · have h := d.bridgeDiv_linear_equiv hunit (le_refl d.tauStar)
    rw [hzero, htau] at h
    exact h

/-- **The landing divisor at a core vertex.**  `bridgeDiv_tauStar_apply_coreVertex`
counts the maximal crossing slots landing at `u`; the rest divisor is chipless on
the core (`stateBridgeData_R`), so nothing else contributes. -/
private theorem landing_coreVertex (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W) (u : Fin n) :
    (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv
        (spec.tauStar N hN D E W) ((spec.scale N hN).coreVertex u)
      = (((spec.crossingMax N hN D E W).filter
          fun e => spec.core.otherEnd e (spec.nearEndpoint W e) = u).card : ℤ) := by
  classical
  set d := spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW
  have hRcore : ∀ w : Fin n, d.R ((spec.scale N hN).coreVertex w) = 0 :=
    (spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).2.1
  have hfib : d.X.filter (fun e => d.t e = d.sMax ∧ spec.core.otherEnd e (d.z e) = u)
      = (spec.crossingMax N hN D E W).filter
          fun e => spec.core.otherEnd e (spec.nearEndpoint W e) = u := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgX, hgt, hgo⟩ := Finset.mem_filter.mp hg
      exact Finset.mem_filter.mpr ⟨spec.mem_crossingMax N hN |>.mpr ⟨hgX, hgt⟩, hgo⟩
    · intro hg
      obtain ⟨hg1, hgo⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgX, hgt⟩ := spec.mem_crossingMax N hN |>.mp hg1
      exact Finset.mem_filter.mpr ⟨hgX, hgt, hgo⟩
  have htau : d.tauStar = spec.tauStar N hN D E W :=
    spec.stateBridgeData_tauStar N hN hunit hbridgeless hD hconn hinc hbridge hW
  rw [← htau, d.bridgeDiv_tauStar_apply_coreVertex hunit u, hRcore u, add_zero, hfib]

/-- **The core chip count of the landing divisor is `|X_max|`.**  Summing
`landing_coreVertex` over the core is a fibre count of `crossingMax` by landing
vertex, so the landings are counted *with multiplicity*: two maximal slots
landing at the same core vertex contribute two chips there. -/
private theorem coreChipCount_landing (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W) :
    spec.coreChipCount N hN
        ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv
          (spec.tauStar N hN D E W))
      = ((spec.crossingMax N hN D E W).card : ℤ) := by
  classical
  unfold coreChipCount
  rw [Finset.sum_congr rfl fun u _ =>
      spec.landing_coreVertex N hN hunit hD hconn hbridgeless hinc hbridge hW u,
    ← Nat.cast_sum]
  congr 1
  exact (Finset.card_eq_sum_card_fiberwise fun a _ => Finset.mem_univ
    (spec.core.otherEnd a (spec.nearEndpoint W a))).symm

/-- **The landing divisor, slot by slot.**  Three chips survive in the interior
of the fine graph: the bridge chip, now at offset `τ*` along `f`; one chip on
each crossing slot of *non-maximal* offset (the maximal ones have landed on the
core); and the rest divisor's chip on each non-crossing chip slot. -/
private theorem landing_edgeChipCount (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W) (g : Fin p) :
    spec.edgeChipCount N hN
        ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv
          (spec.tauStar N hN D E W)) g
      = (if g = f then (1 : ℤ) else 0)
        + (if g ∈ spec.crossing E W ∧ g ∉ spec.crossingMax N hN D E W then (1 : ℤ) else 0)
        + (if g ∈ E ∧ ¬ spec.core.Crosses W g then (1 : ℤ) else 0) := by
  classical
  set d := spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW
  have hRsum :=
    (spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).2.2.2.2
  have h2N : 2 ≤ N := d.two_le_scale
  have htau0 : 0 < d.tauStar := d.one_le_tauStar
  have htauN : d.tauStar < N := d.tauStar_lt
  have htaudef : d.tauStar = N - d.sMax := rfl
  have hsm : d.sMax ≤ N - 1 := d.sMax_le
  have hchain : d.bridgeDiv (spec.tauStar N hN D E W)
      = one_chip (d.frontF d.tauStar) + (∑ e ∈ d.X, one_chip (d.frontX e d.tauStar))
        + d.R := rfl
  -- the bridge chip, still interior at offset `τ*`
  have hF : spec.edgeChipCount N hN (one_chip (d.frontF d.tauStar)) g
      = if g = f then (1 : ℤ) else 0 := by
    have hpt : d.frontF d.tauStar
        = spec.slotPoint N hN f (spec.sideOffset N f v d.tauStar) :=
      spec.sidePoint_eq_slotPoint N hN d.f d.v d.tauStar
    rw [hpt, spec.edgeChipCount_one_chip_slotPoint N hN hunit
      (spec.sideOffset_pos N f v htau0 htauN) (spec.sideOffset_lt N f v htau0 htauN) g]
  -- each crossing chip: on the core if maximal, still interior otherwise
  have hterm : ∀ e ∈ d.X, spec.edgeChipCount N hN (one_chip (d.frontX e d.tauStar)) g
      = if g = e then (if d.t e = d.sMax then (0 : ℤ) else 1) else 0 := by
    intro e he
    have hone := d.onePos e he
    have hle := d.le_sMax he
    by_cases hmax : d.t e = d.sMax
    · have hlast : d.t e + d.tauStar = N := by omega
      have hpt : d.frontX e d.tauStar
          = (spec.scale N hN).coreVertex (spec.core.otherEnd e (d.z e)) := by
        show spec.sidePoint N hN e (d.z e) (d.t e + d.tauStar) = _
        rw [hlast, spec.sidePoint_last N hN hunit e (d.z e)]
      rw [hpt, spec.edgeChipCount_one_chip_coreVertex N hN hunit, ite_eq_left hmax]
      split_ifs <;> rfl
    · have hlt : d.t e < d.sMax := by omega
      have hc0 : 0 < d.t e + d.tauStar := by omega
      have hcN : d.t e + d.tauStar < N := by omega
      have hpt : d.frontX e d.tauStar
          = spec.slotPoint N hN e (spec.sideOffset N e (d.z e) (d.t e + d.tauStar)) :=
        spec.sidePoint_eq_slotPoint N hN e (d.z e) (d.t e + d.tauStar)
      rw [hpt, spec.edgeChipCount_one_chip_slotPoint N hN hunit
        (spec.sideOffset_pos N e (d.z e) hc0 hcN)
        (spec.sideOffset_lt N e (d.z e) hc0 hcN) g, ite_eq_right hmax]
  -- the middle indicator, rewritten in `crossingMax` terms
  have hmid : (if g ∈ d.X then (if d.t g = d.sMax then (0 : ℤ) else 1) else 0)
      = if g ∈ spec.crossing E W ∧ g ∉ spec.crossingMax N hN D E W then (1 : ℤ) else 0 := by
    by_cases hgX : g ∈ spec.crossing E W
    · rw [ite_eq_left (show g ∈ d.X from hgX)]
      by_cases hgm : spec.offsetFromSide N hN D W g = spec.sMax N hN D E W
      · rw [ite_eq_left (show d.t g = d.sMax from hgm),
          ite_eq_right fun h => h.2 ((spec.mem_crossingMax N hN).mpr ⟨hgX, hgm⟩)]
      · rw [ite_eq_right (show ¬ d.t g = d.sMax from hgm),
          ite_eq_left ⟨hgX, fun h => hgm ((spec.mem_crossingMax N hN).mp h).2⟩]
    · rw [ite_eq_right (show ¬ g ∈ d.X from hgX), ite_eq_right fun h => hgX h.1]
  rw [hchain, spec.edgeChipCount_add, spec.edgeChipCount_add, spec.edgeChipCount_sum,
    hF, Finset.sum_congr rfl hterm, Finset.sum_ite_eq, hmid,
    spec.edgeChipCount_eq_sum_slotPoint N hN hunit, hRsum g]

/-- **The dichotomy: exactly one crossing slot attains the maximal offset**
(`CrossingValid`).  `crossingMax` is non-empty because `crossing` is and a
`Finset.sup` is attained; two distinct slots of maximal offset would both land a
chip on the core at step `τ*` (`sidePoint_last`), and
`bridgeDiv_tauStar_apply_coreVertex` sums the landings *with multiplicity*
against `coreChipCount_le_one_of_notSelected`.  This is the sole consumer of
`hodd`/`h3N` in the module. -/
theorem dichotomy (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hDA : linear_equiv (spec.scale N hN).graph A D)
    (hodd : Odd N) (h3N : 3 ≤ N) :
    spec.CrossingValid N hN D E W := by
  -- As in the docstring: `Finset.exists_mem_eq_sup` on the non-empty
  -- `crossing E W` gives `|X_max| ≥ 1`; two maximal slots both land on the core
  -- at step `τ*` (`sidePoint_last`), and `bridgeDiv_tauStar_apply_coreVertex`
  -- counts the landings against `coreChipCount_le_one_of_notSelected` — the only
  -- use of `hodd`/`h3N`.
  classical
  show (spec.crossingMax N hN D E W).card = 1
  -- `|X_max| ≥ 1`: a `Finset.sup` over a non-empty finset is attained.
  have hXne : (spec.crossing E W).Nonempty :=
    spec.crossing_nonempty hbridgeless hbridge hW
  obtain ⟨e₁, he₁, he₁sup⟩ :=
    Finset.exists_mem_eq_sup (spec.crossing E W) hXne (spec.offsetFromSide N hN D W)
  have hone : 1 ≤ (spec.crossingMax N hN D E W).card :=
    Finset.card_pos.mpr ⟨e₁, Finset.mem_filter.mpr ⟨he₁, he₁sup.symm⟩⟩
  -- `|X_max| ≤ 1`: it *is* the core chip count of the landing divisor.
  have hle : (spec.crossingMax N hN D E W).card ≤ 1 := by
    obtain ⟨hLeff, hLdeg, hLA⟩ :=
      spec.landing_data N hN hunit hD hconn hbridgeless hinc hbridge hW
    have hcc := spec.coreChipCount_le_one_of_notSelected N hN hodd h3N hNS hLeff hLdeg
      (hDA.trans hLA)
    rw [spec.coreChipCount_landing N hN hunit hD hconn hbridgeless hinc hbridge hW] at hcc
    exact_mod_cast hcc
  omega

/-- **The swap.**  The unique maximal crossing slot `e₀` names the landing vertex
`w = otherEnd e₀ (nearEndpoint W e₀)`, and the landing divisor
`bridgeDiv τ*` is the state at `w` with chip slots `insert f (E.erase e₀)`.
`ConnectedOff` of the new chip-slot set comes from `lemmaQ` at the landing state,
which is where `hcore` enters. -/
theorem swap (hunit : spec.IsUnit)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    (hbridgeless : spec.core.Bridgeless) {f : Fin p}
    (hinc : spec.core.Incident f v) (hbridge : spec.core.IsBridgeOff E f)
    {W : Finset (Fin n)} (hW : spec.core.IsNearSide E f v W)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hDA : linear_equiv (spec.scale N hN).graph A D)
    (hodd : Odd N) (h3N : 3 ≤ N) (hcore : spec.core.Connected) :
    ∃ (w : Fin n) (e₀ : Fin p), spec.crossingMax N hN D E W = {e₀} ∧ w ∉ W ∧ w ≠ v ∧
      w = spec.core.otherEnd e₀ (spec.nearEndpoint W e₀) ∧ spec.core.Incident e₀ w ∧
      e₀ ∈ E ∧
      linear_equiv (spec.scale N hN).graph D
        ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv
          (spec.tauStar N hN D E W)) ∧
      spec.TypeI N hN
        ((spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).bridgeDiv
          (spec.tauStar N hN D E W)) w (insert f (E.erase e₀)) ∧
      spec.core.ConnectedOff (insert f (E.erase e₀)) := by
  -- After `dichotomy`, `crossingMax = {e₀}` by `Finset.card_eq_one`;
  -- `landing_data` gives the equivalence and the degree, `landing_coreVertex`
  -- and `landing_edgeChipCount` the `TypeI` data at `w`, and `lemmaQ` at the
  -- landing state the `ConnectedOff` (this is where `hcore` enters).
  classical
  set d := spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW
  -- **The unique maximal crossing slot.**
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : Fin p, spec.crossingMax N hN D E W = {e₀} :=
    Finset.card_eq_one.mp
      (spec.dichotomy N hN hunit hD hconn hbridgeless hinc hbridge hW hNS hDA hodd h3N)
  have hmax_iff : ∀ x : Fin p, x ∈ spec.crossingMax N hN D E W ↔ x = e₀ := fun x => by
    rw [he₀]; exact Finset.mem_singleton
  have he₀X : e₀ ∈ spec.crossing E W :=
    ((spec.mem_crossingMax N hN).mp ((hmax_iff e₀).mpr rfl)).1
  obtain ⟨he₀E, he₀cross⟩ := spec.mem_crossing.mp he₀X
  -- **The landing vertex.**
  have hzW : spec.nearEndpoint W e₀ ∈ W := spec.nearEndpoint_mem he₀cross
  have hwW : spec.core.otherEnd e₀ (spec.nearEndpoint W e₀) ∉ W :=
    spec.core.otherEnd_not_mem_of_crosses (spec.nearEndpoint_incident W e₀) hzW he₀cross
  have hwv : spec.core.otherEnd e₀ (spec.nearEndpoint W e₀) ≠ v := fun h => hwW (by
    rw [h]; exact hW.1)
  -- **The landing divisor.**
  obtain ⟨hLeff, hLdeg, hLA⟩ :=
    spec.landing_data N hN hunit hD hconn hbridgeless hinc hbridge hW
  have hLcore : ∀ u : Fin n,
      d.bridgeDiv (spec.tauStar N hN D E W) ((spec.scale N hN).coreVertex u)
        = if u = spec.core.otherEnd e₀ (spec.nearEndpoint W e₀) then 1 else 0 := by
    intro u
    rw [spec.landing_coreVertex N hN hunit hD hconn hbridgeless hinc hbridge hW u, he₀,
      Finset.filter_singleton]
    by_cases hu : u = spec.core.otherEnd e₀ (spec.nearEndpoint W e₀)
    · rw [ite_eq_left (show spec.core.otherEnd e₀ (spec.nearEndpoint W e₀) = u from hu.symm),
        ite_eq_left hu, Finset.card_singleton]
      norm_num
    · rw [ite_eq_right (show ¬ spec.core.otherEnd e₀ (spec.nearEndpoint W e₀) = u from
          fun h => hu h.symm), ite_eq_right hu, Finset.card_empty]
      norm_num
  -- **The landing divisor is the state at `w` with the swapped slot set.**
  have hLtype : spec.TypeI N hN (d.bridgeDiv (spec.tauStar N hN D E W))
      (spec.core.otherEnd e₀ (spec.nearEndpoint W e₀)) (insert f (E.erase e₀)) := by
    refine ⟨hLeff, hLdeg, hLcore, ?_, ?_⟩
    · have hfer : f ∉ E.erase e₀ := fun h => hbridge.1 (Finset.mem_of_mem_erase h)
      rw [Finset.card_insert_of_notMem hfer, Finset.card_erase_of_mem he₀E, hD.2.2.2.1]
    · intro g
      rw [spec.landing_edgeChipCount N hN hunit hD hconn hbridgeless hinc hbridge hW g]
      by_cases hgf : g = f
      · subst hgf
        rw [ite_eq_left (rfl : g = g),
          ite_eq_right (show ¬ (g ∈ spec.crossing E W ∧
              g ∉ spec.crossingMax N hN D E W) from
            fun h => hbridge.1 (spec.crossing_subset E W h.1)),
          ite_eq_right (show ¬ (g ∈ E ∧ ¬ spec.core.Crosses W g) from
            fun h => hbridge.1 h.1),
          ite_eq_left (Finset.mem_insert_self g (E.erase e₀))]
        norm_num
      · rw [ite_eq_right hgf]
        by_cases hgX : g ∈ spec.crossing E W
        · obtain ⟨hgE, hgcross⟩ := spec.mem_crossing.mp hgX
          rw [ite_eq_right (show ¬ (g ∈ E ∧ ¬ spec.core.Crosses W g) from
            fun h => h.2 hgcross)]
          by_cases hge : g = e₀
          · rw [ite_eq_right (show ¬ (g ∈ spec.crossing E W ∧
                g ∉ spec.crossingMax N hN D E W) from
                fun h => h.2 ((hmax_iff g).mpr hge)),
              ite_eq_right (show g ∉ insert f (E.erase e₀) from fun h => by
                rcases Finset.mem_insert.mp h with h1 | h1
                · exact hgf h1
                · exact (Finset.mem_erase.mp h1).1 hge)]
            norm_num
          · rw [ite_eq_left (show g ∈ spec.crossing E W ∧
                g ∉ spec.crossingMax N hN D E W from
                ⟨hgX, fun h => hge ((hmax_iff g).mp h)⟩),
              ite_eq_left (Finset.mem_insert.mpr
                (Or.inr (Finset.mem_erase.mpr ⟨hge, hgE⟩)))]
            norm_num
        · rw [ite_eq_right (show ¬ (g ∈ spec.crossing E W ∧
            g ∉ spec.crossingMax N hN D E W) from fun h => hgX h.1)]
          have hncross : ¬ spec.core.Crosses W g := fun hc =>
            (d.cutSub g hc).elim hgX hgf
          have hge : g ≠ e₀ := fun h => hgX (by rw [h]; exact he₀X)
          by_cases hgE : g ∈ E
          · rw [ite_eq_left (show g ∈ E ∧ ¬ spec.core.Crosses W g from ⟨hgE, hncross⟩),
              ite_eq_left (Finset.mem_insert.mpr
                (Or.inr (Finset.mem_erase.mpr ⟨hge, hgE⟩)))]
            norm_num
          · rw [ite_eq_right (show ¬ (g ∈ E ∧ ¬ spec.core.Crosses W g) from fun h => hgE h.1),
              ite_eq_right (show g ∉ insert f (E.erase e₀) from fun h => by
                rcases Finset.mem_insert.mp h with h1 | h1
                · exact hgf h1
                · exact hgE (Finset.mem_of_mem_erase h1))]
            norm_num
  -- **`lemmaQ` at the landing state.**
  have hconnW : spec.core.ConnectedOff (insert f (E.erase e₀)) :=
    spec.lemmaQ N hN hunit hcore hodd h3N hNS hLeff (hDA.trans hLA) hLtype
  exact ⟨spec.core.otherEnd e₀ (spec.nearEndpoint W e₀), e₀, he₀, hwW, hwv, rfl,
    spec.core.incident_otherEnd e₀ (spec.nearEndpoint W e₀), he₀E, hLA, hLtype, hconnW⟩

end Spec

end SubdivisionGraph

end Utilities.Certificate
