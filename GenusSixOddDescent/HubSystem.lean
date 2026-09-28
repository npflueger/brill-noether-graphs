import GenusSixOddDescent.Swap

/-!
# Hub systems, visibility along firing chains and confinement

A `HubSystem` records state representatives, their connected slot complements,
bridge moves and swaps. `hub_system` constructs this data from a nonselected
rank-one degree-four class; these properties are proved, not assumed inputs to
the final selection theorem.

At a general scale, several non-state divisors can occur between two states.
`StateVisible` therefore uses a legal firing chain whose intermediate nodes
are non-states. `states_swapAdj` follows this chain using a walk invariant: a
hole branch stays tethered to its state, while a bridge branch carries
confinement data. It supplies connectivity of the state move graph
(`swap_connected`).

Confinement then makes the cographic flat constant along moves. The
`separation` lemma uses reduced-divisor uniqueness and a maximum principle.
The resulting component constraints contradict the genus count in
`no_hub_system`. Together with `hub_system`, this contradiction proves selection.

All arguments use an abstract `Spec`; the genus-six restriction is explicit
where the component count needs it.
-/

namespace Utilities.Certificate

open Finset

namespace SubdivisionGraph

namespace Spec

variable {n p : ℕ}

/-! ## The hub system -/

/-- A **hub system** on the core of `spec`, at a general scale `N`.  It assigns
to every core vertex `v` a state `(E_v, ξ_v)` — recorded here as the three chip
slots `edges v` together with the `TypeI` divisor `divisor v = D_v` that carries
the offsets — such that

* (a) `G − E_v` is connected;
* (b) some slot `f ∋ v` outside `E_v` is a bridge of `G − E_v`, and every such
  `f` has valid crossing data (`CrossingValid`: exactly one crossing slot
  attains the maximal chip offset, `|X_max| = 1`);
* (c) every such `f` swaps: `E_w = (E_v ∖ {e₀}) ∪ {f}` for the landing vertex
  `w = target v f` and pivot slot `e₀ = pivot v f`;
* (d) the move graph on `V(G)` is connected.

The extra clause `divisor_equiv` records that a move is a *firing*, so all the
`D_v` lie in one linear equivalence class; this is what the separation lemma
consumes. -/
structure HubSystem (spec : Spec n p) (N : ℕ) (hN : 0 < N) where
  /-- The three chip slots of the state at `v`. -/
  edges : Fin n → Finset (Fin p)
  /-- The state divisor `D_v = v + Σ_{e ∈ E_v} ξ_v(e)`. -/
  divisor : Fin n → CFDiv (spec.scale N hN).graph
  /-- `D_v` really is a state at `v` with chip slots `E_v`. -/
  typeI : ∀ v : Fin n, spec.TypeI N hN (divisor v) v (edges v)
  /-- Clause (a). -/
  connected : ∀ v : Fin n, spec.core.ConnectedOff (edges v)
  /-- The landing vertex of the move at `v` along `f`. -/
  target : Fin n → Fin p → Fin n
  /-- The crossing slot that leaves `E_v` in the swap. -/
  pivot : Fin n → Fin p → Fin p
  /-- Clause (b), existence. -/
  exists_bridge : ∀ v : Fin n, ∃ f : Fin p,
    spec.core.Incident f v ∧ spec.core.IsBridgeOff (edges v) f
  /-- Clause (b), validity of the crossing data of every move. -/
  crossing_valid : ∀ (v : Fin n) (f : Fin p), spec.core.Incident f v →
    spec.core.IsBridgeOff (edges v) f → ∀ W : Finset (Fin n),
      spec.core.IsNearSide (edges v) f v W →
        spec.CrossingValid N hN (divisor v) (edges v) W
  /-- Clause (c), the swap rule. -/
  swap_rule : ∀ (v : Fin n) (f : Fin p), spec.core.Incident f v →
    spec.core.IsBridgeOff (edges v) f →
      pivot v f ∈ edges v ∧ target v f ≠ v ∧
        spec.core.Incident (pivot v f) (target v f) ∧
        edges (target v f) = insert f ((edges v).erase (pivot v f))
  /-- A move is a firing, so consecutive states are linearly equivalent. -/
  divisor_equiv : ∀ (v : Fin n) (f : Fin p), spec.core.Incident f v →
    spec.core.IsBridgeOff (edges v) f →
      linear_equiv (spec.scale N hN).graph (divisor v) (divisor (target v f))
  /-- Clause (d): the move graph on `V(G)` is connected, in cut form.  The move
  leaving `S` is exported with its own landing data `(w, e₀)` rather than through
  `target`: the two consumers of this clause (`flatOff_eq` and
  `divisor_linear_equiv`) only need *some* bridge move out of `S`, and
  `swap_connected` produces one without having to match it against the chosen
  `target`. -/
  moves_connected : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ∃ v ∈ S, ∃ (w : Fin n) (f e₀ : Fin p), w ∉ S ∧ spec.core.Incident f v ∧
      spec.core.IsBridgeOff (edges v) f ∧ e₀ ∈ edges v ∧
      edges w = insert f ((edges v).erase e₀) ∧
      linear_equiv (spec.scale N hN).graph (divisor v) (divisor w)

variable (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ### Private: the state family

The results of `GenusSixOddDescent/Chain.lean` on states, packaged in the shape
`hub_system` consumes.  A `TypeI` divisor knows both its hub vertex and its chip
slots (`typeI_vertex_eq`, `typeI_slots_eq`) and, in a class satisfying `(¬S)`
with `rank ≥ 1`, each core vertex carries exactly one state (`exists_state`,
`state_unique`), by `corR_unique_rep` together with `corR_dichotomy`. -/

/-- The chip slots of a `TypeI` divisor are determined by the divisor: `e` is a
chip slot exactly when `D` puts a chip on `e`. -/
private theorem typeI_slots_eq {D : CFDiv (spec.scale N hN).graph} {v v' : Fin n}
    {E E' : Finset (Fin p)} (hD : spec.TypeI N hN D v E)
    (hD' : spec.TypeI N hN D v' E') : E = E' := by
  ext e
  have h := hD.2.2.2.2 e
  have h' := hD'.2.2.2.2 e
  constructor
  · intro he
    by_contra he'
    rw [if_pos he] at h
    rw [if_neg he'] at h'
    omega
  · intro he'
    by_contra he
    rw [if_neg he] at h
    rw [if_pos he'] at h'
    omega

/-- The hub vertex of a `TypeI` divisor is determined by the divisor: it is the
one core vertex carrying a chip. -/
private theorem typeI_vertex_eq {D : CFDiv (spec.scale N hN).graph} {v v' : Fin n}
    {E E' : Finset (Fin p)} (hD : spec.TypeI N hN D v E)
    (hD' : spec.TypeI N hN D v' E') : v = v' := by
  have h := hD.2.2.1 v'
  have h' : D ((spec.scale N hN).coreVertex v') = 1 := by
    rw [hD'.2.2.1 v', if_pos rfl]
  rw [h'] at h
  by_contra hne
  rw [if_neg fun hc : v' = v => hne hc.symm] at h
  omega

/-- A `TypeI` divisor carries a chip at its hub vertex. -/
private theorem typeI_pos {D : CFDiv (spec.scale N hN).graph} {v : Fin n}
    {E : Finset (Fin p)} (hD : spec.TypeI N hN D v E) :
    0 < D ((spec.scale N hN).coreVertex v) := by
  have h := hD.2.2.1 v
  rw [if_pos rfl] at h
  omega

/-- **Existence of the state at `v`.**  Under `(¬S)` and `rank A ≥ 1` every core
vertex carries a state, with the connectivity of `lemmaQ`.

The proof combines `corR_unique_rep` with `corR_dichotomy`, which is where
`hodd` and `h3N` enter: the non-state branch is the single clause
`∀ u, D (coreVertex u) = 0`. -/
private theorem exists_state (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4) (hrank : rank (spec.scale N hN).graph A ≥ 1) (v : Fin n) :
    ∃ (D : CFDiv (spec.scale N hN).graph) (E : Finset (Fin p)),
      spec.TypeI N hN D v E ∧ spec.core.ConnectedOff E ∧
        linear_equiv (spec.scale N hN).graph A D := by
  obtain ⟨D, ⟨hDeff, hDlin, hDpos⟩, -⟩ :=
    spec.corR_unique_rep N hN hunit hcore hodd h3N hNS hdeg hrank v
  have hDdeg : deg D = 4 := by
    rw [← linear_equiv_preserves_deg _ A D hDlin]; exact hdeg
  rcases spec.corR_dichotomy N hN hunit hcore hodd h3N hNS hDeff hDdeg hDlin with
    ⟨u, E, hI, hconnE⟩ | hnon
  · have hchip := hI.2.2.1 v
    have hvu : v = u := by
      by_contra hne
      rw [if_neg hne] at hchip
      omega
    exact ⟨D, E, by rw [hvu]; exact hI, hconnE, hDlin⟩
  · exact absurd (hnon v) (by omega)

/-- **Uniqueness of the state at `v`.**  The state at `v` is the `v`-reduced
representative of its class. -/
private theorem state_unique (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4) (hrank : rank (spec.scale N hN).graph A ≥ 1)
    {D D' : CFDiv (spec.scale N hN).graph} {v : Fin n} {E E' : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hDA : linear_equiv (spec.scale N hN).graph A D)
    (hD' : spec.TypeI N hN D' v E')
    (hD'A : linear_equiv (spec.scale N hN).graph A D') : D = D' := by
  obtain ⟨D₀, -, huniq⟩ :=
    spec.corR_unique_rep N hN hunit hcore hodd h3N hNS hdeg hrank v
  rw [huniq D ⟨hD.1, hDA, spec.typeI_pos N hN hD⟩,
    huniq D' ⟨hD'.1, hD'A, spec.typeI_pos N hN hD'⟩]

/-! ### Private: small firing-graph facts -/

/-- Firing the empty set does nothing. -/
private theorem firing_empty {G : CFGraph} (D : CFDiv G) :
    set_firing G D (∅ : Finset G.V) = D := by
  funext w
  rw [set_firing_apply_of_not_mem G D (Finset.notMem_empty w)]
  have hzero : outdeg_S G (∅ : Finset G.V)ᶜ w = 0 := by
    unfold outdeg_S
    simp
  rw [hzero, add_zero]

/-- Firing everything does nothing. -/
private theorem firing_univ {G : CFGraph} (D : CFDiv G) :
    set_firing G D (Finset.univ : Finset G.V) = D := by
  funext w
  rw [set_firing_apply_of_mem G D (Finset.mem_univ w)]
  have hzero : outdeg_S G (Finset.univ : Finset G.V) w = 0 := by
    unfold outdeg_S
    simp
  rw [hzero, sub_zero]

/-- **Reversibility of a bridge move, on slot sets.**  If `f` is a bridge of
`G − E_z` and `E_u = (E_z ∖ {e₀}) ∪ {f}` has connected complement, then `e₀` is a
bridge of `G − E_u` and `E_z = (E_u ∖ {f}) ∪ {e₀}`: the move runs backwards with
the roles of `f` and `e₀` exchanged.  Pure cut combinatorics; no scale is
involved. -/
private theorem swapAdj_symm {Eu Ez : Finset (Fin p)} {f e₀ : Fin p}
    (hbr : spec.core.IsBridgeOff Ez f) (he₀ : e₀ ∈ Ez)
    (hEu : Eu = insert f (Ez.erase e₀))
    (hconnEu : spec.core.ConnectedOff Eu) :
    spec.core.IsBridgeOff Eu e₀ ∧ f ∈ Eu ∧ Ez = insert e₀ (Eu.erase f) := by
  classical
  obtain ⟨hfEz, -, hnot⟩ := hbr
  have hne : e₀ ≠ f := fun hc => hfEz (by rw [← hc]; exact he₀)
  have hfnot : f ∉ Ez.erase e₀ := fun hm => hfEz (Finset.mem_of_mem_erase hm)
  refine ⟨⟨?_, hconnEu, ?_⟩, ?_, ?_⟩
  · rw [hEu]
    intro hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact hne h
    · exact (Finset.notMem_erase e₀ Ez) h
  · rw [hEu, Finset.insert_comm, Finset.insert_erase he₀]
    exact hnot
  · rw [hEu]
    exact Finset.mem_insert_self f _
  · rw [hEu, Finset.erase_insert hfnot, Finset.insert_erase he₀]

/-! ## Visibility through non-states: `StateVisible` and `states_swapAdj`

`StateVisible M Dz` says `Dz` is reachable from `M` by a legal fire chain whose
*interior* nodes — everything strictly between the two ends — are non-states.
For chains of length `k ≤ 1` it says `Dz = M ∨ ∃ T, legal_set M T ∧
set_firing M T = Dz`.  `states_swapAdj` shows that a state visible in this sense
from another state sits at the same core vertex or differs from it by a single
bridge move. -/

/-- **`Dz` is visible from `M` through non-states.**  A legal fire chain
`M = M_0 → ⋯ → M_k = Dz` all of whose interior nodes `M_1, …, M_{k−1}` fail to
be states.  The case `k ≤ 1` says that `Dz` is `M` or one legal firing away
from it. -/
def StateVisible (M Dz : CFDiv (spec.scale N hN).graph) : Prop :=
  ∃ (k : ℕ) (U : ℕ → Finset (spec.scale N hN).graph.V),
    (∀ i, i < k → legal_set (spec.scale N hN).graph
        (Utilities.Gonality.fireChain (spec.scale N hN).graph M U i) (U i)) ∧
      Utilities.Gonality.fireChain (spec.scale N hN).graph M U k = Dz ∧
      ∀ i, 0 < i → i < k → ∀ (y : Fin n) (Ey : Finset (Fin p)),
        ¬ spec.TypeI N hN
          (Utilities.Gonality.fireChain (spec.scale N hN).graph M U i) y Ey

/-- The empty chain: every divisor is visible from itself. -/
theorem stateVisible_refl (M : CFDiv (spec.scale N hN).graph) :
    spec.StateVisible N hN M M :=
  ⟨0, fun _ => ∅, fun _ hi => absurd hi (by omega), rfl,
    fun _ _ hi => absurd hi (by omega)⟩

/-- One legal firing makes its target visible: the chain `M → Dz` has no interior
node, so the non-state condition is vacuous.  This is the case `k = 1`. -/
private theorem stateVisible_step {M Dz : CFDiv (spec.scale N hN).graph}
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph M T)
    (hfire : set_firing (spec.scale N hN).graph M T = Dz) :
    spec.StateVisible N hN M Dz := by
  refine ⟨1, fun _ => T, ?_, ?_, fun _ hi0 hi1 => absurd hi1 (by omega)⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [Utilities.Gonality.fireChain_zero]
    exact hT
  · rw [Utilities.Gonality.fireChain_succ, Utilities.Gonality.fireChain_zero]
    exact hfire

/-- **Prepending a step through a non-state.**  If `M` fires legally to `M'`,
`M'` is *not* a state and `Dz` is visible from `M'`, then `Dz` is visible from
`M`: `M'` becomes an interior node of the longer chain, which is exactly why the
non-state hypothesis `hns` is needed. -/
theorem stateVisible_cons {M M' Dz : CFDiv (spec.scale N hN).graph}
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph M T)
    (hfire : set_firing (spec.scale N hN).graph M T = M')
    (hvis : spec.StateVisible N hN M' Dz)
    (hns : ∀ (y : Fin n) (Ey : Finset (Fin p)), ¬ spec.TypeI N hN M' y Ey) :
    spec.StateVisible N hN M Dz := by
  classical
  obtain ⟨k, U, hlegal, hend, hmid⟩ := hvis
  obtain ⟨U', hU'0, hU'succ⟩ : ∃ U' : ℕ → Finset (spec.scale N hN).graph.V,
      U' 0 = T ∧ ∀ i, U' (i + 1) = U i :=
    ⟨fun i => if i = 0 then T else U (i - 1), by simp, by intro i; simp⟩
  have hstep : ∀ i,
      Utilities.Gonality.fireChain (spec.scale N hN).graph M U' (i + 1)
        = Utilities.Gonality.fireChain (spec.scale N hN).graph M' U i := by
    intro i
    induction i with
    | zero =>
      rw [Utilities.Gonality.fireChain_succ, Utilities.Gonality.fireChain_zero, hU'0,
        hfire, Utilities.Gonality.fireChain_zero]
    | succ i ih =>
      rw [Utilities.Gonality.fireChain_succ, ih, hU'succ]
      exact (Utilities.Gonality.fireChain_succ M' U i).symm
  refine ⟨k + 1, U', ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero => rw [Utilities.Gonality.fireChain_zero, hU'0]; exact hT
    | succ j => rw [hstep j, hU'succ]; exact hlegal j (by omega)
  · rw [hstep k]; exact hend
  · intro i hi0 hik
    cases i with
    | zero => exact absurd hi0 (by omega)
    | succ j =>
      rw [hstep j]
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [Utilities.Gonality.fireChain_zero]; exact hns
      · exact hmid j hj (by omega)

/-! ### Private: propagating the swap-closure of `S` along a firing chain -/

/-- `S` is **closed under the swap relation**: the negation of the conclusion of
`swap_connected` for the set `S`. -/
private def SwapClosed (A : CFDiv (spec.scale N hN).graph) (S : Finset (Fin n)) :
    Prop :=
  ∀ v ∈ S, ∀ (w : Fin n) (Dv Dw : CFDiv (spec.scale N hN).graph)
    (Ev : Finset (Fin p)) (f e₀ : Fin p),
    spec.TypeI N hN Dv v Ev → linear_equiv (spec.scale N hN).graph A Dv →
      spec.core.Incident f v → spec.core.IsBridgeOff Ev f → e₀ ∈ Ev →
        spec.TypeI N hN Dw w (insert f (Ev.erase e₀)) →
          linear_equiv (spec.scale N hN).graph A Dw → w ∈ S

/-- `M` is **tethered to `S`**: every state of the class visible from `M`
through non-states (`StateVisible M Dz`) sits at a vertex of `S`.  It is true
at a state of `S`, it is preserved by every legal firing once `S` is
swap-closed, and at a state it says exactly that the state's vertex lies in
`S`. -/
private def Tethered (A : CFDiv (spec.scale N hN).graph) (S : Finset (Fin n))
    (M : CFDiv (spec.scale N hN).graph) : Prop :=
  ∀ (z : Fin n) (Ez : Finset (Fin p)) (Dz : CFDiv (spec.scale N hN).graph),
    spec.TypeI N hN Dz z Ez → linear_equiv (spec.scale N hN).graph A Dz →
      spec.StateVisible N hN M Dz → z ∈ S

/-! ### Private: the three ingredients of `states_swapAdj`

Facts the walk of `states_swapAdj` consumes that no imported module states in
the shape it needs: offsets past the far end of a slot are clamped
(`slotPoint_clamp`, `sum_slotPoint_indicator`); the two sides of a bridge are the
*only* closed sets of `G − (E ∪ {f})` (`closedOff_of_nearSide`, which is the
connectivity input `G − (E ∪ {f}) = W ⊔ W'`, and the one clause of `Confined`
that `stateBridgeData_R` does not supply); and the rest divisor of a hole branch
through a state satisfies the chip hypotheses of `hole_legal_sets`
(`holeRest_props`). -/

/-- Offsets past the far end of a slot are clamped to the head
(`slotPos` takes a `min`). -/
private theorem slotPoint_clamp (hunit : spec.IsUnit) (g : Fin p) {i : ℕ}
    (hi : N ≤ i) : spec.slotPoint N hN g i = spec.slotPoint N hN g N := by
  have h : spec.slotPos N hN g i = spec.slotPos N hN g N := by
    apply Fin.ext
    show min i (N * spec.length g) = min N (N * spec.length g)
    rw [hunit g]
    omega
  show (spec.scale N hN).pathVertex g (spec.slotPos N hN g i)
      = (spec.scale N hN).pathVertex g (spec.slotPos N hN g N)
  rw [h]

/-- A single chip at offset `c` of the slot `g` is seen by the interior sum of
`g` exactly when `c` is an interior offset. -/
private theorem sum_slotPoint_indicator (hunit : spec.IsUnit) (g : Fin p) {c : ℕ}
    (hc : c ≤ N) :
    (∑ i ∈ Finset.Ioo 0 N, (if spec.slotPoint N hN g i = spec.slotPoint N hN g c
        then (1 : ℤ) else 0))
      = if 0 < c ∧ c < N then 1 else 0 := by
  classical
  by_cases hcin : 0 < c ∧ c < N
  · rw [if_pos hcin, Finset.sum_eq_single_of_mem c (Finset.mem_Ioo.mpr hcin)
      (fun i hi hne => if_neg (spec.slotPoint_ne N hN hunit g
        (le_of_lt (Finset.mem_Ioo.mp hi).2) hc hne))]
    exact if_pos rfl
  · rw [if_neg hcin]
    refine Finset.sum_eq_zero fun i hi => if_neg ?_
    obtain ⟨hi0, hiN⟩ := Finset.mem_Ioo.mp hi
    exact spec.slotPoint_ne N hN hunit g (le_of_lt hiN) hc (by omega)

/-- **The two sides of a bridge are the only closed sets.**  If `f` is a bridge
of the connected `G − E` with near side `W` at `v`, then `W` and `Wᶜ` are the two
components of `G − (E ∪ {f})`, so every set closed there is one of `∅`, `W`,
`Wᶜ`, `V(G)`.  This is the `closedOff` field of `Confined`
(`GenusSixOddDescent/BridgeChain.lean`). -/
private theorem closedOff_of_nearSide {E : Finset (Fin p)} {f : Fin p} {v : Fin n}
    {W : Finset (Fin n)} (hbridge : spec.core.IsBridgeOff E f)
    (hW : spec.core.IsNearSide E f v W) (U : Finset (Fin n))
    (hU : spec.core.ClosedOff (insert f E) U) :
    U = ∅ ∨ U = W ∨ U = Wᶜ ∨ U = Finset.univ := by
  classical
  obtain ⟨W₀, hW₀near, hcomp, hcompc, -, -⟩ := spec.core.exists_isNearSide hbridge v
  have hWW₀ : W = W₀ := spec.core.nearSide_unique hbridge hW hW₀near
  rw [hWW₀]
  obtain ⟨-, hW₀closed, hWmin⟩ := hcomp
  obtain ⟨-, -, hWcmin⟩ := hcompc
  have hinter : ∀ S T : Finset (Fin n), spec.core.ClosedOff (insert f E) S →
      spec.core.ClosedOff (insert f E) T →
        spec.core.ClosedOff (insert f E) (S ∩ T) := by
    intro S T hS hT e he hcross
    have h1 := hS e he
    have h2 := hT e he
    simp only [ExplicitPotential.Core.Crosses, Finset.mem_inter] at hcross h1 h2
    tauto
  have hcompl : ∀ S : Finset (Fin n), spec.core.ClosedOff (insert f E) S →
      spec.core.ClosedOff (insert f E) Sᶜ := by
    intro S hS e he hcross
    refine hS e he ?_
    simp only [ExplicitPotential.Core.Crosses, Finset.mem_compl] at hcross ⊢
    tauto
  have hstepW : (W₀ ∩ U).Nonempty → W₀ ⊆ U := by
    intro hne x hx
    have h := hWmin (W₀ ∩ U) Finset.inter_subset_left hne (hinter W₀ U hW₀closed hU)
    rw [← h] at hx
    exact Finset.mem_of_mem_inter_right hx
  have hstepWc : ((W₀ᶜ : Finset (Fin n)) ∩ U).Nonempty → (W₀ᶜ : Finset (Fin n)) ⊆ U := by
    intro hne x hx
    have h := hWcmin (W₀ᶜ ∩ U) Finset.inter_subset_left hne
      (hinter W₀ᶜ U (hcompl W₀ hW₀closed) hU)
    rw [← h] at hx
    exact Finset.mem_of_mem_inter_right hx
  by_cases hin : (W₀ ∩ U).Nonempty
  · by_cases hout : ((W₀ᶜ : Finset (Fin n)) ∩ U).Nonempty
    · refine Or.inr (Or.inr (Or.inr (Finset.eq_univ_iff_forall.mpr fun y => ?_)))
      by_cases hy : y ∈ W₀
      · exact hstepW hin hy
      · exact hstepWc hout (Finset.mem_compl.mpr hy)
    · refine Or.inr (Or.inl (Finset.Subset.antisymm (fun x hx => ?_) (hstepW hin)))
      by_contra hxW
      exact hout ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hxW, hx⟩⟩
  · by_cases hout : ((W₀ᶜ : Finset (Fin n)) ∩ U).Nonempty
    · refine Or.inr (Or.inr (Or.inl
        (Finset.Subset.antisymm (fun x hx => ?_) (hstepWc hout))))
      by_contra hxW
      exact hin ⟨x, Finset.mem_inter.mpr ⟨by simpa using hxW, hx⟩⟩
    · refine Or.inl (Finset.eq_empty_of_forall_notMem fun x hx => ?_)
      by_cases hxW : x ∈ W₀
      · exact hin ⟨x, Finset.mem_inter.mpr ⟨hxW, hx⟩⟩
      · exact hout ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hxW, hx⟩⟩

/-- **The rest divisor of a hole branch through a state.**
`moves_classified` presents the state as `D_u = holeDiv f t R j` without saying
anything about `R`; these are the five chip hypotheses `hole_legal_sets` asks of
it, read off the `TypeI` data of `D_u`.

The four offsets `j < j+1 ≤ t−j−1 < t−j` are distinct points of the closed slot
`[0, N]`, so `R` agrees with `D_u` away from `{a_j, a_{t−j}}` and with the next
node of the branch away from `{a_{j+1}, a_{t−j−1}}`; that gives effectivity.
`D_u` then has one core chip and one chip on each slot of `E`, and `R` is what is
left after removing the hole pair, so the pair cannot be two interior points of
`f` (the slot would owe a chip) nor two core vertices (the core would), and is
therefore one core endpoint of `f` — necessarily `u` — together with the single
chip of the slot `f`. -/
private theorem holeRest_props (hunit : spec.IsUnit)
    {Du : CFDiv (spec.scale N hN).graph} {u : Fin n} {E : Finset (Fin p)}
    (hDu : spec.TypeI N hN Du u E) {f : Fin p} (hfE : f ∈ E) {t j : ℕ}
    {R : CFDiv (spec.scale N hN).graph}
    (hjt : 2 * (j + 1) ≤ t) (htj : t - (j + 1) < N)
    (hDeq : Du = spec.holeDiv N hN f t R j)
    (hnext : effective (spec.holeDiv N hN f t R (j + 1))) :
    effective R ∧ (∀ w : Fin n, R ((spec.scale N hN).coreVertex w) = 0) ∧
      (∀ i : ℕ, R (spec.slotPoint N hN f i) = 0) ∧
      (∀ g : Fin p, ∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN g i) ≤ 1) ∧
      (∀ g : Fin p, g ∉ E → ∀ i ∈ Finset.Ioo 0 N,
        R (spec.slotPoint N hN g i) = 0) := by
  classical
  have hjN : j + 1 < N := by omega
  have hBle : t - j ≤ N := by omega
  have hAB : j < t - j := by omega
  -- `R` is `D_u` minus the hole pair, and also the next node minus *its* pair.
  have hDx : ∀ x : (spec.scale N hN).graph.V, R x = Du x
      - (if x = spec.slotPoint N hN f j then (1 : ℤ) else 0)
      - (if x = spec.slotPoint N hN f (t - j) then (1 : ℤ) else 0) := by
    intro x
    rw [hDeq]
    simp only [Spec.holeDiv, Pi.add_apply, one_chip]
    ring
  have hNx : ∀ x : (spec.scale N hN).graph.V,
      R x = spec.holeDiv N hN f t R (j + 1) x
      - (if x = spec.slotPoint N hN f (j + 1) then (1 : ℤ) else 0)
      - (if x = spec.slotPoint N hN f (t - (j + 1)) then (1 : ℤ) else 0) := by
    intro x
    simp only [Spec.holeDiv, Pi.add_apply, one_chip]
    ring
  -- **Effectivity.**  The two pairs are disjoint, so every vertex is covered.
  have hReff : effective R := by
    intro x
    by_cases h1 : x = spec.slotPoint N hN f j
    · have hne1 : x ≠ spec.slotPoint N hN f (j + 1) := by
        rw [h1]; exact spec.slotPoint_ne N hN hunit f (by omega) (by omega) (by omega)
      have hne2 : x ≠ spec.slotPoint N hN f (t - (j + 1)) := by
        rw [h1]; exact spec.slotPoint_ne N hN hunit f (by omega) (by omega) (by omega)
      have h := hnext x
      rw [hNx x, if_neg hne1, if_neg hne2]
      omega
    · by_cases h2 : x = spec.slotPoint N hN f (t - j)
      · have hne1 : x ≠ spec.slotPoint N hN f (j + 1) := by
          rw [h2]; exact spec.slotPoint_ne N hN hunit f (by omega) (by omega) (by omega)
        have hne2 : x ≠ spec.slotPoint N hN f (t - (j + 1)) := by
          rw [h2]; exact spec.slotPoint_ne N hN hunit f (by omega) (by omega) (by omega)
        have h := hnext x
        rw [hNx x, if_neg hne1, if_neg hne2]
        omega
      · have h := hDu.1 x
        rw [hDx x, if_neg h1, if_neg h2]
        omega
  have hRle : ∀ x : (spec.scale N hN).graph.V, R x ≤ Du x := by
    intro x
    rw [hDx x]
    split_ifs <;> omega
  -- **The two ends of the slot.**
  have hcore0 : spec.slotPoint N hN f 0
      = (spec.scale N hN).coreVertex (spec.core.tail f) := spec.slotPoint_zero N hN f
  have hcoreN : spec.slotPoint N hN f N
      = (spec.scale N hN).coreVertex (spec.core.head f) :=
    spec.slotPoint_last N hN hunit f
  -- **The interior sum on the slot `f`.**
  have hfsum : (∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN f i))
      = 1 - (if 0 < j ∧ j < N then (1 : ℤ) else 0)
          - (if 0 < t - j ∧ t - j < N then (1 : ℤ) else 0) := by
    have hEC : (∑ i ∈ Finset.Ioo 0 N, Du (spec.slotPoint N hN f i)) = 1 := by
      rw [← spec.edgeChipCount_eq_sum_slotPoint N hN hunit Du f, hDu.2.2.2.2 f,
        if_pos hfE]
    rw [Finset.sum_congr rfl (fun i _ => hDx (spec.slotPoint N hN f i))]
    simp only [Finset.sum_sub_distrib]
    rw [hEC, spec.sum_slotPoint_indicator N hN hunit f (show j ≤ N by omega),
      spec.sum_slotPoint_indicator N hN hunit f hBle]
  have hfsumnn : 0 ≤ ∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN f i) :=
    Finset.sum_nonneg fun i _ => hReff _
  -- The hole pair is not two interior points …
  have hnotboth : ¬ (0 < j ∧ t - j < N) := by
    rintro ⟨hj0, hBN⟩
    rw [if_pos ⟨hj0, by omega⟩, if_pos ⟨by omega, hBN⟩] at hfsum
    omega
  -- … nor two core vertices.
  have hnotcore : ¬ (j = 0 ∧ t - j = N) := by
    rintro ⟨hj0, hBN⟩
    have hne : (spec.scale N hN).coreVertex (spec.core.tail f)
        ≠ (spec.scale N hN).coreVertex (spec.core.head f) := by
      rw [← hcore0, ← hcoreN]
      exact spec.slotPoint_ne N hN hunit f (by omega) (by omega) (by omega)
    have e1 := hDx ((spec.scale N hN).coreVertex (spec.core.tail f))
    have e2 := hDx ((spec.scale N hN).coreVertex (spec.core.head f))
    rw [hBN, hj0, hcore0, hcoreN, if_pos rfl, if_neg hne] at e1
    rw [hBN, hj0, hcore0, hcoreN, if_neg (Ne.symm hne), if_pos rfl] at e2
    have h1 := hDu.2.2.1 (spec.core.tail f)
    have h2 := hDu.2.2.1 (spec.core.head f)
    have n1 := hReff ((spec.scale N hN).coreVertex (spec.core.tail f))
    have n2 := hReff ((spec.scale N hN).coreVertex (spec.core.head f))
    have htu : spec.core.tail f = u := by
      by_cases hc : spec.core.tail f = u
      · exact hc
      · rw [if_neg hc] at h1; omega
    have hhu : spec.core.head f = u := by
      by_cases hc : spec.core.head f = u
      · exact hc
      · rw [if_neg hc] at h2; omega
    exact hne (by rw [htu, hhu])
  -- **Core-freeness**, from whichever end of the slot carries the core chip.
  have hgen : ∀ (c : Fin n) (o : ℕ), 0 < o → o < N →
      (∀ x : (spec.scale N hN).graph.V, R x = Du x
        - (if x = (spec.scale N hN).coreVertex c then (1 : ℤ) else 0)
        - (if x = spec.slotPoint N hN f o then (1 : ℤ) else 0)) →
      ∀ w : Fin n, R ((spec.scale N hN).coreVertex w) = 0 := by
    intro c o ho0 hoN hR
    have hcw : ∀ y : Fin n,
        (spec.scale N hN).coreVertex y ≠ spec.slotPoint N hN f o :=
      fun y => spec.coreVertex_ne_slotPoint N hN hunit y f ho0 hoN
    have hcu : c = u ∧ R ((spec.scale N hN).coreVertex c) = 0 := by
      have h := hR ((spec.scale N hN).coreVertex c)
      rw [if_neg (hcw c), if_pos rfl] at h
      have hd := hDu.2.2.1 c
      have hnn := hReff ((spec.scale N hN).coreVertex c)
      by_cases hcu : c = u
      · rw [if_pos hcu] at hd
        exact ⟨hcu, by omega⟩
      · exfalso; rw [if_neg hcu] at hd; omega
    intro w
    have h := hR ((spec.scale N hN).coreVertex w)
    rw [if_neg (hcw w)] at h
    by_cases hwc : (spec.scale N hN).coreVertex w = (spec.scale N hN).coreVertex c
    · rw [hwc]; exact hcu.2
    · rw [if_neg hwc] at h
      have hd := hDu.2.2.1 w
      by_cases hwu : w = u
      · exact absurd (by rw [hwu, hcu.1] : (spec.scale N hN).coreVertex w
          = (spec.scale N hN).coreVertex c) hwc
      · rw [if_neg hwu] at hd; omega
  have hmain : (∀ w : Fin n, R ((spec.scale N hN).coreVertex w) = 0)
      ∧ (∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN f i)) = 0 := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · have hBN : t - j < N := by
        by_contra hc
        exact hnotcore ⟨hj0, by omega⟩
      have hR : ∀ x : (spec.scale N hN).graph.V, R x = Du x
          - (if x = (spec.scale N hN).coreVertex (spec.core.tail f) then (1 : ℤ) else 0)
          - (if x = spec.slotPoint N hN f (t - j) then (1 : ℤ) else 0) := by
        have hswap : spec.slotPoint N hN f j
            = (spec.scale N hN).coreVertex (spec.core.tail f) := by
          rw [hj0]; exact hcore0
        intro x; rw [hDx x, hswap]
      refine ⟨hgen (spec.core.tail f) (t - j) (by omega) hBN hR, ?_⟩
      rw [if_neg (by omega : ¬ (0 < j ∧ j < N)),
        if_pos (show 0 < t - j ∧ t - j < N from ⟨by omega, hBN⟩)] at hfsum
      omega
    · have hBN : t - j = N := by
        by_contra hc
        exact hnotboth ⟨hjpos, by omega⟩
      have hR : ∀ x : (spec.scale N hN).graph.V, R x = Du x
          - (if x = (spec.scale N hN).coreVertex (spec.core.head f) then (1 : ℤ) else 0)
          - (if x = spec.slotPoint N hN f j then (1 : ℤ) else 0) := by
        have hswap : spec.slotPoint N hN f (t - j)
            = (spec.scale N hN).coreVertex (spec.core.head f) := by
          rw [hBN]; exact hcoreN
        intro x; rw [hDx x, hswap]; ring
      refine ⟨hgen (spec.core.head f) j hjpos (by omega) hR, ?_⟩
      rw [if_pos (show 0 < j ∧ j < N from ⟨hjpos, by omega⟩),
        if_neg (by omega : ¬ (0 < t - j ∧ t - j < N))] at hfsum
      omega
  obtain ⟨hRcore, hsum0⟩ := hmain
  have hzero : ∀ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN f i) = 0 :=
    fun i hi => (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hReff _)).mp hsum0 i hi
  refine ⟨hReff, hRcore, ?_, ?_, ?_⟩
  · intro i
    by_cases hi0 : i = 0
    · rw [hi0, hcore0]; exact hRcore _
    · by_cases hiN : i < N
      · exact hzero i (Finset.mem_Ioo.mpr ⟨by omega, hiN⟩)
      · rw [spec.slotPoint_clamp N hN hunit f (by omega), hcoreN]; exact hRcore _
  · intro g
    calc (∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN g i))
        ≤ ∑ i ∈ Finset.Ioo 0 N, Du (spec.slotPoint N hN g i) :=
          Finset.sum_le_sum fun i _ => hRle _
      _ = spec.edgeChipCount N hN Du g :=
          (spec.edgeChipCount_eq_sum_slotPoint N hN hunit Du g).symm
      _ ≤ 1 := by rw [hDu.2.2.2.2 g]; split_ifs <;> omega
  · intro g hgE i hi
    have h1 : Du (spec.slotPoint N hN g i) = 0 :=
      spec.slotPoint_eq_zero_of_edgeChipCount_zero N hN hunit hDu.1
        (by rw [hDu.2.2.2.2 g, if_neg hgE]) i hi
    have h2 := hRle (spec.slotPoint N hN g i)
    have h3 := hReff (spec.slotPoint N hN g i)
    omega

/-- **The bridge chain of a state is confined.**  The `Confined` data
(`GenusSixOddDescent/BridgeChain.lean`) that `Confined.legal_set_unique` runs on,
with `chipSlots = E ∪ {f}`: the five chip clauses are `stateBridgeData_R` and the
connectivity clause is `closedOff_of_nearSide`. -/
private def stateConfined (hunit : spec.IsUnit)
    (hbridgeless : spec.core.Bridgeless)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hconn : spec.core.ConnectedOff E)
    {f : Fin p} (hinc : spec.core.Incident f v)
    (hbridge : spec.core.IsBridgeOff E f) {W : Finset (Fin n)}
    (hW : spec.core.IsNearSide E f v W) :
    (spec.stateBridgeData N hN hunit hbridgeless hD hconn hinc hbridge hW).Confined where
  chipSlots := insert f E
  memF := Finset.mem_insert_self f E
  subX := fun _ he => Finset.mem_insert_of_mem (spec.crossing_subset E W he)
  eff := (spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).1
  coreFree := (spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).2.1
  slotFree := fun g hg =>
    (spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).2.2.1 g
      (fun hm => hg (Finset.mem_insert_of_mem hm))
  crossFree :=
    (spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).2.2.2.1
  oneChip := fun g => by
    rw [(spec.stateBridgeData_R N hN hunit hD hconn hbridgeless hinc hbridge hW).2.2.2.2 g]
    split_ifs <;> omega
  closedOff := spec.closedOff_of_nearSide hbridge hW

/-! ### Private: the walk invariant of `states_swapAdj`

`WalkInv Du M u Eu` is a three-way invariant: the node `M` of the walk is the
anchoring state `D_u` itself (the case that absorbs the stuttering firings
`T ∈ {∅, univ}`), or a strictly later node of a hole branch anchored at `D_u`,
or a node `1 ≤ m ≤ τ*` of a bridge chain anchored at `D_u`.

The statement of `moves_classified` forces two things on the shape of the hole
disjunct.  First, the branch index at the *state* need not be zero — a head-hub
state is `holeDiv f (2N−t) R (N−t)` (see `GenusSixOddDescent/Hole.lean`) — so
the anchor index `j₀` is carried and the invariant reads `j₀ < j`, its
`j₀ = j − 1` back step landing on `D_u` itself.  Second, `t − j < N` is *not*
preserved by the back step, so the anchor's `t − (j₀+1) < N` is carried instead
and the interiority at `j` is recovered from `j₀ < j`.

The bridge disjunct carries the landing state as data rather than re-deriving
it from `swap` at the end of the walk: that keeps the `stateBridgeData` term —
which depends on proofs — out of the invariant. -/
private def WalkInv (Du M : CFDiv (spec.scale N hN).graph) (u : Fin n)
    (Eu : Finset (Fin p)) : Prop :=
  M = Du
  ∨ (∃ (f : Fin p) (t j₀ j : ℕ) (R : CFDiv (spec.scale N hN).graph),
      f ∈ Eu ∧ effective R ∧
        (∀ w : Fin n, R ((spec.scale N hN).coreVertex w) = 0) ∧
        (∀ i : ℕ, R (spec.slotPoint N hN f i) = 0) ∧
        (∀ g : Fin p, ∑ i ∈ Finset.Ioo 0 N, R (spec.slotPoint N hN g i) ≤ 1) ∧
        (∀ g : Fin p, g ∉ Eu → ∀ i ∈ Finset.Ioo 0 N,
          R (spec.slotPoint N hN g i) = 0) ∧
        Du = spec.holeDiv N hN f t R j₀ ∧ t - (j₀ + 1) < N ∧ j₀ < j ∧ 2 * j ≤ t ∧
        M = spec.holeDiv N hN f t R j)
  ∨ (∃ (d : spec.BridgeData N hN) (_ : d.Confined) (m : ℕ) (f e₀ : Fin p)
        (w : Fin n),
      d.bridgeDiv 0 = Du ∧ 1 ≤ m ∧ m ≤ d.tauStar ∧ M = d.bridgeDiv m ∧
        spec.core.Incident f u ∧ spec.core.IsBridgeOff Eu f ∧ e₀ ∈ Eu ∧
        spec.TypeI N hN (d.bridgeDiv d.tauStar) w (insert f (Eu.erase e₀)))

/-- **One step of the walk out of the anchoring state.**  `moves_classified`
classifies the move: `T ∈ {∅, univ}` stutters, a hole forward set enters a hole
branch (its rest divisor satisfying `holeRest_props`), and a bridge set is
`(stateBridgeData …).bridgeSet 0` by `bridgeSet_forced`, landing on
`bridgeDiv 1` by `bridgeSet_step`.  `swap` supplies the landing state of the
chain, which the invariant carries along. -/
private theorem walkInv_from_state (hunit : spec.IsUnit)
    (hcore : spec.core.Connected) (hbridgeless : spec.core.Bridgeless)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    {Du : CFDiv (spec.scale N hN).graph} {u : Fin n} {Eu : Finset (Fin p)}
    (hDu : spec.TypeI N hN Du u Eu)
    (hDuA : linear_equiv (spec.scale N hN).graph A Du)
    (hconnu : spec.core.ConnectedOff Eu)
    {M' : CFDiv (spec.scale N hN).graph} {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph Du T)
    (hfire : set_firing (spec.scale N hN).graph Du T = M') :
    spec.WalkInv N hN Du M' u Eu := by
  classical
  by_cases hTe : T = ∅
  · exact Or.inl (by rw [← hfire, hTe, firing_empty])
  by_cases hTu : T = Finset.univ
  · exact Or.inl (by rw [← hfire, hTu, firing_univ])
  rcases spec.moves_classified N hN hunit hDu hconnu hbridgeless hT
    (Finset.nonempty_iff_ne_empty.mpr hTe) hTu with
    ⟨f, t, j, R, hfE, hincf, hjt, htj, hDeq, hTeq, hland⟩
    | ⟨f, W, hfE, hincf, hbridge, hW, hTcore⟩
  · -- **A hole branch.**
    obtain ⟨hReff, hRcore, hRf, hRchip, hRout⟩ :=
      spec.holeRest_props N hN hunit hDu hfE hjt htj hDeq
        (by rw [← hland]; exact effective_set_firing_of_legal_set _ hDu.1 hT)
    exact Or.inr (Or.inl ⟨f, t, j, j + 1, R, hfE, hReff, hRcore, hRf, hRchip,
      hRout, hDeq, htj, by omega, hjt, by rw [← hfire, hland]⟩)
  · -- **A bridge chain.**
    obtain ⟨w, e₀, -, -, -, -, -, he₀E, -, hDtype, -⟩ :=
      spec.swap N hN hunit hDu hconnu hbridgeless hincf hbridge hW hNS hDuA hodd h3N
        hcore
    have hzero := spec.stateBridgeData_bridgeDiv_zero N hN hunit hDu hconnu
      hbridgeless hincf hbridge hW
    have hstep := (spec.stateBridgeData N hN hunit hbridgeless hDu hconnu hincf
      hbridge hW).bridgeSet_step hunit
      (show 0 < (spec.stateBridgeData N hN hunit hbridgeless hDu hconnu hincf hbridge
        hW).tauStar from (spec.stateBridgeData N hN hunit hbridgeless hDu hconnu hincf
        hbridge hW).one_le_tauStar)
    refine Or.inr (Or.inr ⟨_, spec.stateConfined N hN hunit hbridgeless hDu hconnu
      hincf hbridge hW, 1, f, e₀, w, hzero, le_rfl,
      (spec.stateBridgeData N hN hunit hbridgeless hDu hconnu hincf hbridge
        hW).one_le_tauStar, ?_, hincf, hbridge, he₀E, ?_⟩)
    · rw [← hfire, spec.bridgeSet_forced N hN hunit hDu hconnu hbridgeless hincf
        hbridge hW hT hTcore, ← hstep, hzero]
    · rw [spec.stateBridgeData_tauStar N hN hunit hbridgeless hDu hconnu hincf
        hbridge hW]
      exact hDtype

/-- **One step of the walk.**  From the anchoring state this is
`walkInv_from_state`; from a hole branch `hole_legal_sets` forces `j ↦ j ± 1`
(or a stutter), the back step at `j₀ + 1` returning to `D_u`; from a bridge
chain `Confined.legal_set_unique` forces `m ↦ m ± 1`, the back step at `m = 1`
returning to `D_u`.  At `m = τ*` the node *is* a state, so the
hypothesis `hMok` — every node of the walk is `D_u` or a non-state — closes that
branch. -/
private theorem walkInv_step (hunit : spec.IsUnit)
    (hcore : spec.core.Connected) (hbridgeless : spec.core.Bridgeless)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    {Du : CFDiv (spec.scale N hN).graph} {u : Fin n} {Eu : Finset (Fin p)}
    (hDu : spec.TypeI N hN Du u Eu)
    (hDuA : linear_equiv (spec.scale N hN).graph A Du)
    (hconnu : spec.core.ConnectedOff Eu)
    {M M' : CFDiv (spec.scale N hN).graph} {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph M T)
    (hfire : set_firing (spec.scale N hN).graph M T = M')
    (hMok : M = Du ∨ ∀ (y : Fin n) (Ey : Finset (Fin p)),
      ¬ spec.TypeI N hN M y Ey)
    (hinv : spec.WalkInv N hN Du M u Eu) :
    spec.WalkInv N hN Du M' u Eu := by
  classical
  rcases hMok with rfl | hns
  · exact spec.walkInv_from_state N hN hunit hcore hbridgeless hodd h3N hNS hDu hDuA
      hconnu hT hfire
  rcases hinv with rfl | hb | hc
  · exact spec.walkInv_from_state N hN hunit hcore hbridgeless hodd h3N hNS hDu hDuA
      hconnu hT hfire
  · -- **On a hole branch.**
    obtain ⟨f, t, j₀, j, R, hfE, hReff, hRcore, hRf, hRchip, hRout, hDeq, htj₀,
      hj₀j, hjt, hMeq⟩ := hb
    have hj1 : 1 ≤ j := by omega
    have htjN : t - j < N := by omega
    by_cases hTe : T = ∅
    · exact Or.inr (Or.inl ⟨f, t, j₀, j, R, hfE, hReff, hRcore, hRf, hRchip, hRout,
        hDeq, htj₀, hj₀j, hjt, by rw [← hfire, hTe, firing_empty, hMeq]⟩)
    by_cases hTu : T = Finset.univ
    · exact Or.inr (Or.inl ⟨f, t, j₀, j, R, hfE, hReff, hRcore, hRf, hRchip, hRout,
        hDeq, htj₀, hj₀j, hjt, by rw [← hfire, hTu, firing_univ, hMeq]⟩)
    rw [hMeq] at hT
    rcases spec.hole_legal_sets N hN hunit f hj1 hjt htjN hReff hRcore hRf hRchip
      hfE hRout hconnu hT hTe hTu with hback | ⟨hfwd, hfwdeq⟩
    · -- back step
      have hM' : M' = spec.holeDiv N hN f t R (j - 1) := by
        rw [← hfire, hMeq, hback]
        exact spec.setFiring_backSet N hN hunit f hj1 hjt htjN R
      rcases Nat.eq_or_lt_of_le (show j₀ ≤ j - 1 by omega) with heq | hlt
      · exact Or.inl (by rw [hM', ← heq, ← hDeq])
      · exact Or.inr (Or.inl ⟨f, t, j₀, j - 1, R, hfE, hReff, hRcore, hRf, hRchip,
          hRout, hDeq, htj₀, hlt, by omega, hM'⟩)
    · -- forward step
      have hM' : M' = spec.holeDiv N hN f t R (j + 1) := by
        rw [← hfire, hMeq, hfwdeq]
        exact spec.setFiring_fwdSet' N hN hunit f hfwd (by omega) R
      exact Or.inr (Or.inl ⟨f, t, j₀, j + 1, R, hfE, hReff, hRcore, hRf, hRchip,
        hRout, hDeq, htj₀, by omega, hfwd, hM'⟩)
  · -- **On a bridge chain.**
    obtain ⟨d, c, m, f, e₀, w, hzero, hm1, hmt, hMeq, hincf, hbr, he₀, hstate⟩ := hc
    by_cases hmeq : m = d.tauStar
    · exact absurd (by rw [hMeq, hmeq]; exact hstate) (hns w (insert f (Eu.erase e₀)))
    have hmlt : m < d.tauStar := by omega
    by_cases hTe : T = ∅
    · exact Or.inr (Or.inr ⟨d, c, m, f, e₀, w, hzero, hm1, hmt,
        by rw [← hfire, hTe, firing_empty, hMeq], hincf, hbr, he₀, hstate⟩)
    by_cases hTu : T = Finset.univ
    · exact Or.inr (Or.inr ⟨d, c, m, f, e₀, w, hzero, hm1, hmt,
        by rw [← hfire, hTu, firing_univ, hMeq], hincf, hbr, he₀, hstate⟩)
    rw [hMeq] at hT
    rcases c.legal_set_unique hunit hm1 hmlt hT hTe hTu with hfwd | hback
    · -- forward step
      exact Or.inr (Or.inr ⟨d, c, m + 1, f, e₀, w, hzero, by omega, by omega,
        by rw [← hfire, hMeq, hfwd]; exact d.bridgeSet_step hunit hmlt,
        hincf, hbr, he₀, hstate⟩)
    · -- back step
      have hM' : M' = d.bridgeDiv (m - 1) := by
        rw [← hfire, hMeq, hback]
        have h := d.setFiring_bridgeSet_compl hunit (show m - 1 < d.tauStar by omega)
        rw [show m - 1 + 1 = m from by omega] at h
        exact h
      rcases Nat.eq_zero_or_pos (m - 1) with hz | hpos
      · exact Or.inl (by rw [hM', hz, hzero])
      · exact Or.inr (Or.inr ⟨d, c, m - 1, f, e₀, w, hzero, hpos, by omega, hM',
          hincf, hbr, he₀, hstate⟩)

/-- **Visible states differ by at most one bridge move.**  Under `(¬S)`, if
`D_u` and `D_z` are states of the class and `D_z` is `StateVisible` from `D_u`,
then `u = z` or the two differ by a bridge move: some slot `f ∋ u` outside `E_u`
is a bridge of `G − E_u` and `E_z = (E_u ∖ {e₀}) ∪ {f}` for some `e₀ ∈ E_u`.

*Proof.*  Walk `M_0 = D_u → ⋯ → M_k = D_z`, carrying `WalkInv` — `M_i` is `D_u`,
or a strictly later node `holeDiv f t R j` (`j₀ < j`) of a hole branch anchored
at `D_u`, or a node `d.bridgeDiv m` (`1 ≤ m ≤ τ*`) of a bridge chain anchored at
`D_u` — together with the *anchoring* state's `ConnectedOff E_u` (`lemmaQ` at
`D_u`: `G − E_u` connected comes from the anchor, never from `M_i`).
`walkInv_from_state` opens a branch out of `D_u` (`moves_classified` and
`bridgeSet_forced`, with `holeRest_props` supplying the chip data of `R`), and
`walkInv_step` moves along one: `hole_legal_sets` resp.
`Confined.legal_set_unique` force `j ↦ j ± 1` resp. `m ↦ m ± 1`, the `±0`
covering the stuttering firings `T ∈ {∅, univ}` (`firing_empty`,
`firing_univ`).

As recorded in `WalkInv`'s docstring, the branch index at the anchoring state
is a general `j₀`, not `0` (a head-hub state is `holeDiv f (2N−t) R (N−t)`), and
the interiority `t − j < N` is carried in the anchored form `t − (j₀+1) < N`,
since the back step does not preserve it.

Every node of a branch other than the anchor is core-chip-free
(`holeDiv_coreVertex`, `Confined.bridgeDiv_coreVertex`) and so is not a state;
the sole exception is `d.bridgeDiv τ*`, which the non-state hypothesis on
`M_1, …, M_{k−1}` confines to `i = k`.  So `M_k = D_z` is `D_u`, giving `u = z`
by `typeI_vertex_eq`, or `d.bridgeDiv τ*`, where the landing state carried by the
invariant (from `swap`) supplies `(f, e₀)` and, through `typeI_slots_eq`, the
identity `E_z = insert f (E_u.erase e₀)`. -/
theorem states_swapAdj (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hbridgeless : spec.core.Bridgeless) (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4) (hrank : rank (spec.scale N hN).graph A ≥ 1)
    {Du Dz : CFDiv (spec.scale N hN).graph} {u z : Fin n}
    {Eu Ez : Finset (Fin p)}
    (hDu : spec.TypeI N hN Du u Eu)
    (hDuA : linear_equiv (spec.scale N hN).graph A Du)
    (hDz : spec.TypeI N hN Dz z Ez)
    (hDzA : linear_equiv (spec.scale N hN).graph A Dz)
    (hvis : spec.StateVisible N hN Du Dz) :
    u = z ∨ ∃ f e₀ : Fin p, spec.core.Incident f u ∧
      spec.core.IsBridgeOff Eu f ∧ e₀ ∈ Eu ∧ Ez = insert f (Eu.erase e₀) := by
  classical
  -- `hdeg`, `hrank` and `hDzA` are not consumed: the walk runs on the local data
  -- of the two states, `(¬S)` entering only through `lemmaQ` and `swap`.  They
  -- are kept so that the statement describes two states of one rank-one class.
  have _hdeg : deg A = 4 := hdeg
  have _hrank : rank (spec.scale N hN).graph A ≥ 1 := hrank
  have _hDzA : linear_equiv (spec.scale N hN).graph A Dz := hDzA
  -- `G − E_u` connected comes from the *anchoring* state, never from an
  -- intermediate node of the walk.
  have hconnu : spec.core.ConnectedOff Eu :=
    spec.lemmaQ N hN hunit hcore hodd h3N hNS hDu.1 hDuA hDu
  obtain ⟨k, U, hlegal, hend, hmid⟩ := hvis
  -- The invariant, along the whole chain.
  have hinv : ∀ i, i ≤ k → spec.WalkInv N hN Du
      (Utilities.Gonality.fireChain (spec.scale N hN).graph Du U i) u Eu := by
    intro i
    induction i with
    | zero => intro _; exact Or.inl rfl
    | succ i ih =>
      intro hik
      refine spec.walkInv_step N hN hunit hcore hbridgeless hodd h3N hNS hDu hDuA
        hconnu (hlegal i (by omega)) rfl ?_ (ih (by omega))
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact Or.inl rfl
      · exact Or.inr (hmid i hi0 (by omega))
  -- Read the invariant off at the end of the chain, where the node is a state.
  have hz := hinv k le_rfl
  rw [hend] at hz
  rcases hz with hDzeq | hb | hc
  · exact Or.inl (spec.typeI_vertex_eq N hN hDu (hDzeq ▸ hDz))
  · -- A hole node of a branch is core-chip-free, so it cannot be the state `D_z`.
    exfalso
    obtain ⟨f, t, j₀, j, R, -, -, hRcore, -, -, -, -, htj₀, hj₀j, hjt, hMeq⟩ := hb
    have hpos := spec.typeI_pos N hN hDz
    have hval := spec.holeDiv_coreVertex N hN hunit f (show 1 ≤ j by omega) hjt
      (show t - j < N by omega) R z
    rw [← hMeq, hRcore z] at hval
    omega
  · obtain ⟨d, c, m, f, e₀, w, -, hm1, hmt, hMeq, hincf, hbr, he₀, hstate⟩ := hc
    by_cases hmeq : m = d.tauStar
    · -- The landing state of the bridge chain: the slot identity of `swap`.
      have hDzstate : spec.TypeI N hN Dz w (insert f (Eu.erase e₀)) := by
        rw [hMeq, hmeq]; exact hstate
      exact Or.inr ⟨f, e₀, hincf, hbr, he₀, spec.typeI_slots_eq N hN hDz hDzstate⟩
    · -- An intermediate node of the chain is core-chip-free.
      exfalso
      have hpos := spec.typeI_pos N hN hDz
      have hval := c.bridgeDiv_coreVertex hunit hm1 (by omega) z
      rw [← hMeq] at hval
      omega

/-- **One legal firing between two states is a bridge move.**  The case `k = 1`
of `states_swapAdj`.  The conclusion is *directional*: it does not record
`Incident e₀ z` or `ConnectedOff Ez`, which would be needed only to run the move
backwards through `swapAdj_symm`. -/
private theorem state_step (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hbridgeless : spec.core.Bridgeless) (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4) (hrank : rank (spec.scale N hN).graph A ≥ 1)
    {Du Dz : CFDiv (spec.scale N hN).graph} {u z : Fin n}
    {Eu Ez : Finset (Fin p)}
    (hDu : spec.TypeI N hN Du u Eu)
    (hDuA : linear_equiv (spec.scale N hN).graph A Du)
    (hDz : spec.TypeI N hN Dz z Ez)
    (hDzA : linear_equiv (spec.scale N hN).graph A Dz)
    {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph Du T)
    (hfire : set_firing (spec.scale N hN).graph Du T = Dz) :
    u = z ∨ ∃ f e₀ : Fin p, spec.core.Incident f u ∧
      spec.core.IsBridgeOff Eu f ∧ e₀ ∈ Eu ∧ Ez = insert f (Eu.erase e₀) :=
  spec.states_swapAdj N hN hunit hcore hbridgeless hodd h3N hNS hdeg hrank hDu hDuA
    hDz hDzA (spec.stateVisible_step N hN hT hfire)

/-- The states of `S` are tethered to `S`: they are their own hub vertex, and
every state visible from one of them is a swap partner, hence again in `S`.
`states_swapAdj` covers every chain length at once, the case `Dz = M` being its
`k = 0` case (`stateVisible_refl`). -/
private theorem tethered_state (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hbridgeless : spec.core.Bridgeless) (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4)
    (hrank : rank (spec.scale N hN).graph A ≥ 1) {S : Finset (Fin n)}
    (hclosed : spec.SwapClosed N hN A S) {Dv : CFDiv (spec.scale N hN).graph}
    {v : Fin n} {Ev : Finset (Fin p)} (hDv : spec.TypeI N hN Dv v Ev)
    (hDvA : linear_equiv (spec.scale N hN).graph A Dv) (hvS : v ∈ S) :
    spec.Tethered N hN A S Dv := by
  intro z Ez Dz hDz hDzA hvis
  rcases spec.states_swapAdj N hN hunit hcore hbridgeless hodd h3N hNS hdeg hrank
    hDv hDvA hDz hDzA hvis with hvz | ⟨f, e₀, hinc, hbridge, he₀, hEz⟩
  · rw [← hvz]; exact hvS
  · exact hclosed v hvS z Dv Dz Ev f e₀ hDv hDvA hinc hbridge he₀
      (by rw [← hEz]; exact hDz) hDzA

/-- **Tethering survives a legal firing.**  Two cases: if the fired divisor `M'`
is a state, its vertex is in `S` by `Tethered M` at `k = 1`
(`stateVisible_step`), and `states_swapAdj` applied at `M'` together with
swap-closure puts `z` in `S`; if `M'` is a non-state, prepend the step with
`stateVisible_cons` and use `Tethered M` directly. -/
private theorem tethered_setFiring (hunit : spec.IsUnit)
    (hcore : spec.core.Connected) (hbridgeless : spec.core.Bridgeless)
    (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph}
    (hNS : spec.NotSelected N hN A) (hdeg : deg A = 4)
    (hrank : rank (spec.scale N hN).graph A ≥ 1) {S : Finset (Fin n)}
    (hclosed : spec.SwapClosed N hN A S) {M : CFDiv (spec.scale N hN).graph}
    (_hM : effective M) (hMA : linear_equiv (spec.scale N hN).graph A M)
    (hMt : spec.Tethered N hN A S M) {T : Finset (spec.scale N hN).graph.V}
    (hT : legal_set (spec.scale N hN).graph M T) :
    spec.Tethered N hN A S (set_firing (spec.scale N hN).graph M T) := by
  classical
  intro z Ez Dz hDz hDzA hvis
  have hM'A : linear_equiv (spec.scale N hN).graph A
      (set_firing (spec.scale N hN).graph M T) :=
    hMA.trans (linear_equiv_set_firing M T)
  by_cases hM'state : ∃ (y : Fin n) (Ey : Finset (Fin p)),
      spec.TypeI N hN (set_firing (spec.scale N hN).graph M T) y Ey
  · -- The fired divisor is a state, and its vertex is in `S`.
    obtain ⟨y, Ey, hM'I⟩ := hM'state
    have hyS : y ∈ S :=
      hMt y Ey (set_firing (spec.scale N hN).graph M T) hM'I hM'A
        (spec.stateVisible_step N hN hT rfl)
    rcases spec.states_swapAdj N hN hunit hcore hbridgeless hodd h3N hNS hdeg hrank
      hM'I hM'A hDz hDzA hvis with hyz | ⟨f, e₀, hinc, hbridge, he₀, hEz⟩
    · rw [← hyz]; exact hyS
    · exact hclosed y hyS z _ Dz Ey f e₀ hM'I hM'A hinc hbridge he₀
        (by rw [← hEz]; exact hDz) hDzA
  · -- The fired divisor is a non-state: prepend the step.
    push Not at hM'state
    exact hMt z Ez Dz hDz hDzA
      (spec.stateVisible_cons N hN hT rfl hvis hM'state)

/-! ## The swap graph is connected -/

/-- **The swap graph is connected.**  Under `(¬S)` the swap multigraph on
`V(G)` — one edge `v — w` for each bridge move at the state `D_v` — is
connected, in the cut formulation: every non-trivial vertex set has a bridge
move leaving it.

This does not follow from connectivity of the firing graph of the class alone:
states are joined through non-states, and deleting a node of degree `> 2` from a
connected graph can disconnect it.  The non-states are *not* enumerated (their
variety grows with `N`).  Instead the whole chain of `exists_legal_fireChain` is
walked with the `Tethered` invariant, which by `tethered_setFiring` survives
every step regardless of what the intermediate divisors look like; the content
is in `states_swapAdj`. -/
theorem swap_connected (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hbridgeless : spec.core.Bridgeless) (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4) (hrank : rank (spec.scale N hN).graph A ≥ 1) (hn : 2 ≤ n)
    (S : Finset (Fin n)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ v ∈ S, ∃ (w : Fin n) (Dv Dw : CFDiv (spec.scale N hN).graph)
      (Ev : Finset (Fin p)) (f e₀ : Fin p),
      w ∉ S ∧ spec.TypeI N hN Dv v Ev ∧
        linear_equiv (spec.scale N hN).graph A Dv ∧
        spec.core.Incident f v ∧ spec.core.IsBridgeOff Ev f ∧ e₀ ∈ Ev ∧
        spec.TypeI N hN Dw w (insert f (Ev.erase e₀)) ∧
        linear_equiv (spec.scale N hN).graph A Dw := by
  classical
  -- `hn` is not consumed: for `n ≤ 1` no set is both non-empty and proper, so
  -- the statement is vacuous there; it is kept to match the hypotheses of
  -- `bridge_move_exists` and `hub_system`.
  have _hn : 2 ≤ n := hn
  by_contra hcon
  -- The negation says exactly that `S` is closed under the swap relation.
  have hclosed : spec.SwapClosed N hN A S := by
    intro v hv w Dv Dw Ev f e₀ hDv hDvA hinc hbridge he₀ hDw hDwA
    by_contra hw
    exact hcon ⟨v, hv, w, Dv, Dw, Ev, f, e₀, hw, hDv, hDvA, hinc, hbridge, he₀,
      hDw, hDwA⟩
  -- The two states the firing chain has to join.
  obtain ⟨v, hvS⟩ := hne
  obtain ⟨w, hwS⟩ : ∃ w : Fin n, w ∉ S := by
    by_contra hall
    push Not at hall
    exact hproper (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨Dv, Ev, hDv, -, hDvA⟩ :=
    spec.exists_state N hN hunit hcore hodd h3N hNS hdeg hrank v
  obtain ⟨Dw, Ew, hDw, -, hDwA⟩ :=
    spec.exists_state N hN hunit hcore hodd h3N hNS hdeg hrank w
  obtain ⟨k, U, hlegal, hend⟩ :=
    Utilities.Gonality.exists_legal_fireChain hDv.1 hDw.1 (hDvA.symm.trans hDwA)
  -- Tethering to `S` holds at `D_v` and survives every step of the chain.
  have hchain : ∀ i, i ≤ k →
      spec.Tethered N hN A S
        (Utilities.Gonality.fireChain (spec.scale N hN).graph Dv U i) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact spec.tethered_state N hN hunit hcore hbridgeless hodd h3N hNS hdeg hrank
        hclosed hDv hDvA hvS
    | succ i ih =>
      intro hik
      have hi : i ≤ k := by omega
      exact spec.tethered_setFiring N hN hunit hcore hbridgeless hodd h3N hNS hdeg
        hrank hclosed
        (Utilities.Gonality.fireChain_effective hDv.1 hlegal i hi)
        (hDvA.trans (Utilities.Gonality.fireChain_linear_equiv Dv U i)) (ih hi)
        (hlegal i (by omega))
  -- But the last divisor of the chain is the state at `w ∉ S`, visible from
  -- itself (`stateVisible_refl`, the `k = 0` witness).
  refine hwS (hchain k le_rfl w Ew Dw hDw hDwA ?_)
  rw [hend]
  exact spec.stateVisible_refl N hN Dw

/-! ## A bridge move always exists -/

/-- **A bridge move always exists.**  Under `(¬S)`, `rank A ≥ 1` and
`|V(G)| ≥ 2`, every state `D_v` admits a bridge move.

The proof is `swap_connected` applied to the **singleton cut** `S = {v}`.
`swap_connected` walks the chain of `exists_legal_fireChain` from the state at
`v` to the state at some `w ∉ S` with the `Tethered` invariant, whose
preservation (`tethered_setFiring`) is exactly `states_swapAdj` turning each
state met into a bridge move at the previous one; the move it reports as leaving
`{v}` is therefore a bridge `f ∋ v` of `G − E_v`.  `hn` makes `{v}` proper,
`rank A ≥ 1` and `hdeg` feed `exists_state` inside `swap_connected`, and
`typeI_unique` (with `lemmaQ` for the connectivity of the reported slot set)
identifies the state it found at `v` with `D`, hence its slots with `E`.

This is why the declaration lives here rather than in
`GenusSixOddDescent/Moves.lean`: its proof rests on `states_swapAdj`.
Truncating the chain by hand at the first state after `D_v` would re-derive the
induction of `swap_connected`; nothing is circular, since `swap_connected` does
not consume `bridge_move_exists`. -/
theorem bridge_move_exists (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hbridgeless : spec.core.Bridgeless) (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4) (hrank : rank (spec.scale N hN).graph A ≥ 1) (hn : 2 ≤ n)
    {D : CFDiv (spec.scale N hN).graph} {v : Fin n} {E : Finset (Fin p)}
    (hD : spec.TypeI N hN D v E) (hDA : linear_equiv (spec.scale N hN).graph A D)
    (hconn : spec.core.ConnectedOff E) :
    ∃ f : Fin p, spec.core.Incident f v ∧ spec.core.IsBridgeOff E f := by
  classical
  -- `swap_connected` at the singleton cut `S = {v}` *is* the truncation argument
  -- of the docstring, already run: it walks a chain of `exists_legal_fireChain`
  -- with the `Tethered` invariant, and `Tethered` is preserved only because
  -- `states_swapAdj` turns each state met into a bridge move at the previous
  -- one.  So the move leaving `{v}` is a bridge at `v`.
  have hproper : ({v} : Finset (Fin n)) ≠ Finset.univ := by
    intro hc
    have h1 : ({v} : Finset (Fin n)).card = (Finset.univ : Finset (Fin n)).card := by
      rw [hc]
    rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨v', hv'S, -, Dv, -, Ev, f, -, -, hDv, hDvA, hinc, hbridge, -, -, -⟩ :=
    spec.swap_connected N hN hunit hcore hbridgeless hodd h3N hNS hdeg hrank hn
      ({v} : Finset (Fin n)) ⟨v, Finset.mem_singleton_self v⟩ hproper
  have hvv : v' = v := Finset.mem_singleton.mp hv'S
  subst hvv
  -- The state at `v'` in the class is unique, so it is `D` and its slots are `E`.
  have hconnv : spec.core.ConnectedOff Ev :=
    spec.lemmaQ N hN hunit hcore hodd h3N hNS hDv.1 hDvA hDv
  have hDeq : Dv = D :=
    spec.typeI_unique N hN hunit hDv hD hconnv hconn (hDvA.symm.trans hDA)
  have hEeq : Ev = E := spec.typeI_slots_eq N hN hDv (hDeq ▸ hD)
  exact ⟨f, hinc, hEeq ▸ hbridge⟩

/-! ## Non-selection gives a hub system -/

/-- **Non-selection gives a hub system.**  Under `(¬S)`, the graph `G` carries a
hub system.

The state at `v` is the `v`-reduced representative `D_v` of `corR_unique_rep`,
whose chip-slot complement is connected by `lemmaQ`; clause (b) is
`bridge_move_exists` (existence) with `dichotomy` (validity of the crossing
data); clause (c) is `swap`; clause (d) is `swap_connected`; and
`divisor_equiv` holds because all the `D_v` are representatives of the one
class `A`.

`exists_legal_bridge_move` is *not* needed here: `swap` takes the bridge and the
near side directly and produces the landing divisor `bridgeDiv τ*` itself,
rather than a divisor obtained by firing a set the caller supplies. -/
theorem hub_system (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hbridgeless : spec.core.Bridgeless) (hodd : Odd N) (h3N : 3 ≤ N)
    {A : CFDiv (spec.scale N hN).graph} (hNS : spec.NotSelected N hN A)
    (hdeg : deg A = 4) (hrank : rank (spec.scale N hN).graph A ≥ 1) (hn : 2 ≤ n) :
    Nonempty (spec.HubSystem N hN) := by
  classical
  -- The state family.
  choose divisor edges htypeI hconnE hlinA using
    fun v => spec.exists_state N hN hunit hcore hodd h3N hNS hdeg hrank v
  -- Any state of the class is *the* state at its hub vertex, so both its divisor
  -- and its slot set are the chosen ones.
  have hstate : ∀ (v : Fin n) (D : CFDiv (spec.scale N hN).graph)
      (E : Finset (Fin p)), spec.TypeI N hN D v E →
        linear_equiv (spec.scale N hN).graph A D → D = divisor v ∧ E = edges v := by
    intro v D E hD hDA
    have hDeq : D = divisor v :=
      spec.state_unique N hN hunit hcore hodd h3N hNS hdeg hrank hD hDA (htypeI v)
        (hlinA v)
    subst hDeq
    exact ⟨rfl, spec.typeI_slots_eq N hN hD (htypeI v)⟩
  -- Clause (c): `swap` lands every bridge move on another state, and the state
  -- there is the chosen one, so its slots are `(E_v ∖ {e₀}) ∪ {f}`.
  have hswapdata : ∀ (v : Fin n) (f : Fin p), ∃ (w : Fin n) (e₀ : Fin p),
      spec.core.Incident f v → spec.core.IsBridgeOff (edges v) f →
        e₀ ∈ edges v ∧ w ≠ v ∧ spec.core.Incident e₀ w ∧
          edges w = insert f ((edges v).erase e₀) := by
    intro v f
    by_cases hcase : spec.core.Incident f v ∧ spec.core.IsBridgeOff (edges v) f
    · obtain ⟨hinc, hbridge⟩ := hcase
      obtain ⟨W, hW, -, -, -, -⟩ := spec.core.exists_isNearSide hbridge v
      obtain ⟨w, e₀, -, -, hwv, -, hincw, he₀E, hlinD, hD'type, -⟩ :=
        spec.swap N hN hunit (htypeI v) (hconnE v) hbridgeless hinc hbridge hW hNS
          (hlinA v) hodd h3N hcore
      exact ⟨w, e₀, fun _ _ => ⟨he₀E, hwv, hincw,
        ((hstate w _ _ hD'type ((hlinA v).trans hlinD)).2).symm⟩⟩
    · exact ⟨v, f, fun h1 h2 => absurd ⟨h1, h2⟩ hcase⟩
  choose target pivot hswaprule using hswapdata
  refine ⟨{ edges := edges, divisor := divisor, typeI := htypeI, connected := hconnE
            target := target, pivot := pivot, swap_rule := hswaprule
            exists_bridge := fun v => spec.bridge_move_exists N hN hunit hcore
              hbridgeless hodd h3N hNS hdeg hrank hn (htypeI v) (hlinA v) (hconnE v)
            crossing_valid := fun v f hinc hbridge W hW =>
              spec.dichotomy N hN hunit (htypeI v) (hconnE v) hbridgeless hinc
                hbridge hW hNS (hlinA v) hodd h3N
            divisor_equiv := fun v f _ _ => (hlinA v).symm.trans (hlinA (target v f))
            moves_connected := ?_ }⟩
  -- Clause (d) is `swap_connected`: the swap edge it produces leaves `S`, and its
  -- landing data `(w, e₀)` is exactly what the clause reports.
  intro S hne hproper
  obtain ⟨v, hvS, w, Dv, Dw, Ev, f, e₀, hwS, hDv, hDvA, hinc, hbridge, he₀, hDw,
    hDwA⟩ := spec.swap_connected N hN hunit hcore hbridgeless hodd h3N hNS hdeg
      hrank hn S hne hproper
  have hEv : Ev = edges v := (hstate v Dv Ev hDv hDvA).2
  subst hEv
  obtain ⟨hDweq, hEw⟩ := hstate w Dw _ hDw hDwA
  refine ⟨v, hvS, w, f, e₀, hwS, hinc, hbridge, he₀, hEw.symm, ?_⟩
  rw [← (hstate v Dv _ hDv hDvA).1, ← hDweq]
  exact hDvA.symm.trans hDwA

/-! ### Private: the fine geometry the separation lemma runs on

Two small facts about the `N`-fold refinement of a slot, isolated so that the
separation argument itself stays at the level of the script `F`:
`interiorVertex_eq_zero` says a slot carrying no chip carries none at any of its
interior fine vertices, and `slot_boundary` is the crossing step of a slot. -/

/-- On the argmax set of a firing script, each edge to a strictly lower vertex
costs one unit of the principal divisor.  No scale is involved. -/
private theorem prin_le_of_argmax {G : CFGraph} (F : firing_script G) {x : G.V}
    (hmax : ∀ u : G.V, F u ≤ F x) (T : Finset G.V) (hT : ∀ y ∈ T, F y < F x) :
    prin G F x ≤ - ∑ y ∈ T, (num_edges G x y : ℤ) := by
  classical
  rw [prin_apply]
  calc ∑ u : G.V, (F u - F x) * (num_edges G x u : ℤ)
      ≤ ∑ u ∈ T, (F u - F x) * (num_edges G x u : ℤ) := by
        have hneg : ∑ u ∈ T, -((F u - F x) * (num_edges G x u : ℤ))
            ≤ ∑ u : G.V, -((F u - F x) * (num_edges G x u : ℤ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) ?_
          intro u _ _
          have h1 : F u - F x ≤ 0 := by have := hmax u; omega
          have h2 : (0 : ℤ) ≤ (num_edges G x u : ℤ) := Int.natCast_nonneg _
          nlinarith
        rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib] at hneg
        omega
    _ ≤ ∑ u ∈ T, (-1) * (num_edges G x u : ℤ) := by
        refine Finset.sum_le_sum fun u hu => ?_
        refine mul_le_mul_of_nonneg_right ?_ (Int.natCast_nonneg _)
        have := hT u hu
        omega
    _ = - ∑ y ∈ T, (num_edges G x y : ℤ) := by
        rw [← Finset.mul_sum, neg_one_mul]

/-- A slot carrying no chip carries none at any of its interior fine vertices. -/
private theorem interiorVertex_eq_zero {D : CFDiv (spec.scale N hN).graph}
    (hD : effective D) {e : Fin p} (he : spec.edgeChipCount N hN D e = 0)
    (j : Fin ((spec.scale N hN).length e - 1)) :
    D ((spec.scale N hN).interiorVertex e j) = 0 := by
  have hsum : ∑ k : Fin ((spec.scale N hN).length e - 1),
      D ((spec.scale N hN).interiorVertex e k) = 0 := he
  have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin ((spec.scale N hN).length e - 1))),
      0 ≤ D ((spec.scale N hN).interiorVertex e k) := fun k _ => hD _
  exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j (Finset.mem_univ j)

/-- **The crossing step of a slot.**  Let `A` be a set of fine vertices which
absorbs the neighbours of every fine vertex of the slot `e` other than
`coreVertex v`.  If the two core endpoints of `e` sit on opposite sides of `A`,
then `v` is an endpoint of `e` and the interior fine neighbour of `v` along `e`
lies outside `A`.

The proof is a **propagation** along the slot.  Say `a_0 = coreVertex (tail e) ∈ A` and
`a_N = coreVertex (head e) ∉ A`, and let `k` be the least offset with
`a_k ∉ A`.  Then `1 ≤ k ≤ N` and `a_{k−1} ∈ A`, so `a_{k−1}` fails to absorb its
neighbour `a_k` and must therefore be `coreVertex v`; but every `a_m` with
`0 < m < N` is an *interior* fine vertex, so `k − 1 = 0`.  Hence
`coreVertex (tail e) = coreVertex v` and `a_1 ∉ A` is the required neighbour.
The other orientation is the mirror image, run from the largest offset outside
`A`.  `2 ≤ N` is what makes `a_1` interior (at `N = 1` a slot has no interior
vertex at all and the statement is false). -/
private theorem slot_boundary (hunit : spec.IsUnit) (h2N : 2 ≤ N) {e : Fin p}
    {v : Fin n} {A : Finset (spec.scale N hN).graph.V}
    (habs : ∀ x : (spec.scale N hN).graph.V, x ∈ A →
      x ≠ (spec.scale N hN).coreVertex v →
      (x = (spec.scale N hN).coreVertex (spec.core.tail e) ∨
        x = (spec.scale N hN).coreVertex (spec.core.head e) ∨
        ∃ j, x = (spec.scale N hN).interiorVertex e j) →
      ∀ y : (spec.scale N hN).graph.V,
        0 < num_edges (spec.scale N hN).graph x y → y ∈ A)
    (hcross : ¬ ((spec.scale N hN).coreVertex (spec.core.tail e) ∈ A ↔
      (spec.scale N hN).coreVertex (spec.core.head e) ∈ A)) :
    ∃ j : Fin ((spec.scale N hN).length e - 1),
      (spec.scale N hN).interiorVertex e j ∉ A ∧
      0 < num_edges (spec.scale N hN).graph ((spec.scale N hN).coreVertex v)
        ((spec.scale N hN).interiorVertex e j) := by
  classical
  -- Offsets along the slot, from the tail.
  have h0 : spec.slotPoint N hN e 0
      = (spec.scale N hN).coreVertex (spec.core.tail e) := spec.slotPoint_zero N hN e
  have hlast : spec.slotPoint N hN e N
      = (spec.scale N hN).coreVertex (spec.core.head e) :=
    spec.slotPoint_last N hN hunit e
  -- Every offset in `[0, N]` is one of the three shapes `habs` recognises.
  have hshape : ∀ m, m ≤ N →
      (spec.slotPoint N hN e m = (spec.scale N hN).coreVertex (spec.core.tail e) ∨
        spec.slotPoint N hN e m
            = (spec.scale N hN).coreVertex (spec.core.head e) ∨
        ∃ j, spec.slotPoint N hN e m = (spec.scale N hN).interiorVertex e j) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact Or.inl h0
    · rcases Nat.eq_or_lt_of_le hm with rfl | hmN
      · exact Or.inr (Or.inl hlast)
      · obtain ⟨j, hj⟩ :=
          spec.exists_interiorVertex_eq_slotPoint N hN hunit e hm0 hmN
        exact Or.inr (Or.inr ⟨j, hj⟩)
  -- An interior offset is not `coreVertex v`.
  have hint : ∀ m, 0 < m → m < N →
      spec.slotPoint N hN e m ≠ (spec.scale N hN).coreVertex v := fun m hm0 hmN =>
    (spec.coreVertex_ne_slotPoint N hN hunit v e hm0 hmN).symm
  by_cases htail : (spec.scale N hN).coreVertex (spec.core.tail e) ∈ A
  · have hhead : (spec.scale N hN).coreVertex (spec.core.head e) ∉ A := fun hmem =>
      hcross ⟨fun _ => hmem, fun _ => htail⟩
    -- The least offset outside `A`.
    set C : Finset ℕ := (Finset.range (N + 1)).filter
      (fun m => spec.slotPoint N hN e m ∉ A) with hCdef
    have hNC : N ∈ C := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [hlast]; exact hhead
    have hCne : C.Nonempty := ⟨N, hNC⟩
    set k := C.min' hCne with hkdef
    have hkC : k ∈ C := C.min'_mem hCne
    have hkrange : k ≤ N := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hkC).1; omega
    have hkA : spec.slotPoint N hN e k ∉ A := (Finset.mem_filter.mp hkC).2
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hz | hpos
      · exact absurd (by rw [hz, h0]; exact htail) hkA
      · exact hpos
    have hprevA : spec.slotPoint N hN e (k - 1) ∈ A := by
      by_contra hc
      have hmem : k - 1 ∈ C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩
      have := C.min'_le _ hmem
      omega
    -- The predecessor fails to absorb, hence it is `coreVertex v`.
    have hadj : 0 < num_edges (spec.scale N hN).graph
        (spec.slotPoint N hN e (k - 1)) (spec.slotPoint N hN e (k - 1 + 1)) :=
      spec.num_edges_slotPoint_succ_pos N hN hunit e (by omega)
    rw [show k - 1 + 1 = k by omega] at hadj
    have hprev_v : spec.slotPoint N hN e (k - 1) = (spec.scale N hN).coreVertex v := by
      by_contra hne
      exact hkA (habs _ hprevA hne (hshape (k - 1) (by omega)) _ hadj)
    -- Only the two endpoints can be a core vertex, and `k - 1 < N`.
    have hk1 : k = 1 := by
      by_contra hne
      exact hint (k - 1) (by omega) (by omega) hprev_v
    rw [hk1] at hkA hadj hprev_v
    obtain ⟨j, hj⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit e
      (t := 1) (by omega) (by omega)
    refine ⟨j, by rw [← hj]; exact hkA, ?_⟩
    rw [← hj, ← hprev_v]
    simpa using hadj
  · have hhead : (spec.scale N hN).coreVertex (spec.core.head e) ∈ A := by
      by_contra hmem
      exact hcross ⟨fun h => absurd h htail, fun h => absurd h hmem⟩
    -- The largest offset outside `A`.
    set C : Finset ℕ := (Finset.range (N + 1)).filter
      (fun m => spec.slotPoint N hN e m ∉ A) with hCdef
    have h0C : 0 ∈ C := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [h0]; exact htail
    have hCne : C.Nonempty := ⟨0, h0C⟩
    set k := C.max' hCne with hkdef
    have hkC : k ∈ C := C.max'_mem hCne
    have hkrange : k ≤ N := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hkC).1; omega
    have hkA : spec.slotPoint N hN e k ∉ A := (Finset.mem_filter.mp hkC).2
    have hkN : k < N := by
      rcases Nat.eq_or_lt_of_le hkrange with hz | hlt
      · exact absurd (by rw [hz, hlast]; exact hhead) hkA
      · exact hlt
    have hnextA : spec.slotPoint N hN e (k + 1) ∈ A := by
      by_contra hc
      have hmem : k + 1 ∈ C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩
      have := C.le_max' _ hmem
      omega
    have hadj : 0 < num_edges (spec.scale N hN).graph
        (spec.slotPoint N hN e (k + 1)) (spec.slotPoint N hN e k) := by
      rw [num_edges_symmetric]
      exact spec.num_edges_slotPoint_succ_pos N hN hunit e hkN
    have hnext_v : spec.slotPoint N hN e (k + 1)
        = (spec.scale N hN).coreVertex v := by
      by_contra hne
      exact hkA (habs _ hnextA hne (hshape (k + 1) (by omega)) _ hadj)
    have hkeq : k + 1 = N := by
      by_contra hne
      exact hint (k + 1) (by omega) (by omega) hnext_v
    obtain ⟨j, hj⟩ := spec.exists_interiorVertex_eq_slotPoint N hN hunit e
      (t := k) (by omega) hkN
    refine ⟨j, by rw [← hj]; exact hkA, ?_⟩
    rw [← hj, ← hnext_v]
    exact hadj

/-! ## Confinement -/

namespace HubSystem

variable {spec} {N} {hN} (hs : spec.HubSystem N hN)

include hs in
/-- A hub system forces `2 ≤ N`: each of the three chip slots of a state carries
one interior chip, and at `N = 1` a slot has no interior vertex. -/
theorem two_le_scale (hunit : spec.IsUnit) : 2 ≤ N := by
  classical
  by_contra hcon
  let v₀ : Fin n := ⟨0, spec.core_nonempty⟩
  have hcard : (hs.edges v₀).card = 3 := (hs.typeI v₀).2.2.2.1
  obtain ⟨e, he⟩ : (hs.edges v₀).Nonempty := Finset.card_pos.mp (by omega)
  have hchip := (hs.typeI v₀).2.2.2.2 e
  rw [if_pos he] at hchip
  have hL : (spec.scale N hN).length e = N := spec.length_scale N hN hunit e
  have hzero : spec.edgeChipCount N hN (hs.divisor v₀) e = 0 := by
    show ∑ j : Fin ((spec.scale N hN).length e - 1),
      (hs.divisor v₀) ((spec.scale N hN).interiorVertex e j) = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    exact absurd j.isLt (by omega)
  omega

/-- **Confinement, the single move.**  A move does not change the flat: the
closure `cl(E_v)` of the chip slots in the cographic matroid of the core
(`flatOff`).

Proof: set `F := E_v ∪ {f}`.  `E_v` is independent (clause (a)) so `r*(E_v) = 3`;
`F` is dependent, since `f` is a bridge of `G − E_v`, and `|F| = 4`, so
`r*(F) = 3` and `cl(F) = cl(E_v)`.  By the swap rule
`E_w = (E_v ∖ {e₀}) ∪ {f} ⊆ F` is independent of size three, hence a basis of
`F`, so `cl(E_w) = cl(F) = cl(E_v)`.  Pure cut combinatorics on the core; no
scale is involved. -/
theorem flatOff_move_eq (v w : Fin n) (f e₀ : Fin p)
    (hbridge : spec.core.IsBridgeOff (hs.edges v) f) (he₀ : e₀ ∈ hs.edges v)
    (hedges : hs.edges w = insert f ((hs.edges v).erase e₀)) :
    spec.core.flatOff (hs.edges w) = spec.core.flatOff (hs.edges v) := by
  obtain ⟨W₀, -, -, -, hsub₀, hfW₀⟩ := spec.core.exists_isNearSide hbridge v
  exact spec.core.flatOff_swap_eq
    (spec.core.connected_of_connectedOff (hs.connected v))
    (hs.connected v) (hs.connected w) he₀ hbridge.1 hedges hfW₀ hsub₀

/-- The same statement for the chosen `target` of the swap rule. -/
theorem flatOff_target_eq (v : Fin n) (f : Fin p) (hinc : spec.core.Incident f v)
    (hbridge : spec.core.IsBridgeOff (hs.edges v) f) :
    spec.core.flatOff (hs.edges (hs.target v f)) =
      spec.core.flatOff (hs.edges v) := by
  obtain ⟨hpivot, -, -, hedges⟩ := hs.swap_rule v f hinc hbridge
  exact hs.flatOff_move_eq v _ f _ hbridge hpivot hedges

/-- **Confinement.**  The flat `Φ = cl(E_v)` does not depend on the state:
`flatOff_move_eq` makes it constant along every move, and clause (d) makes the
move graph connected on `V(G)`. -/
theorem flatOff_eq (v w : Fin n) :
    spec.core.flatOff (hs.edges v) = spec.core.flatOff (hs.edges w) := by
  classical
  set S : Finset (Fin n) :=
    Finset.univ.filter fun u =>
      spec.core.flatOff (hs.edges u) = spec.core.flatOff (hs.edges v) with hSdef
  have hmem : ∀ u : Fin n,
      u ∈ S ↔ spec.core.flatOff (hs.edges u) = spec.core.flatOff (hs.edges v) := by
    intro u; rw [hSdef]; simp
  have hvS : v ∈ S := (hmem v).mpr rfl
  have huniv : S = Finset.univ := by
    by_contra hne
    obtain ⟨u, huS, w', f, e₀, hw'S, -, hbridge, he₀, hedges, -⟩ :=
      hs.moves_connected S ⟨v, hvS⟩ hne
    exact hw'S ((hmem _).mpr
      ((hs.flatOff_move_eq u w' f e₀ hbridge he₀ hedges).trans ((hmem u).mp huS)))
  exact ((hmem w).mp (huniv ▸ Finset.mem_univ w)).symm

/-- The flat of a hub system.  By `flatOff_eq` any state computes it. -/
def flat : Finset (Fin p) :=
  spec.core.flatOff (hs.edges ⟨0, spec.core_nonempty⟩)

theorem flat_eq_flatOff (v : Fin n) : hs.flat = spec.core.flatOff (hs.edges v) :=
  hs.flatOff_eq _ v

theorem edges_subset_flat (v : Fin n) : hs.edges v ⊆ hs.flat := by
  rw [hs.flat_eq_flatOff v]
  exact spec.core.subset_flatOff _

/-- **The moves are the slots of `Φ`.**  Inside `Φ` the moves are unobstructed:
a slot outside `E_v` is a bridge of `G − E_v` exactly when it lies in `Φ`. -/
theorem isBridgeOff_iff_mem_flat (v : Fin n) {f : Fin p} (hf : f ∉ hs.edges v) :
    spec.core.IsBridgeOff (hs.edges v) f ↔ f ∈ hs.flat := by
  rw [hs.flat_eq_flatOff v, spec.core.mem_flatOff_iff]
  exact (or_iff_right hf).symm

/-- **Every vertex touches `Φ`.**  Clause (b) gives every vertex `v` a bridge of
`G − E_v` at `v`, so every vertex of `G` is an endpoint of an edge of `Φ`. -/
theorem exists_incident_mem_flat (v : Fin n) :
    ∃ f ∈ hs.flat, spec.core.Incident f v := by
  obtain ⟨f, hinc, hbridge⟩ := hs.exists_bridge v
  exact ⟨f, (hs.isBridgeOff_iff_mem_flat v hbridge.1).mp hbridge, hinc⟩

/-- **The rank of the flat.**  `r*(Φ) = |Φ| − c(G − Φ) + 1 = 3`, i.e.
`c(G − Φ) = |Φ| − 2`. -/
theorem componentCount_flat : spec.core.componentCount hs.flat + 2 = hs.flat.card := by
  classical
  let v₀ : Fin n := ⟨0, spec.core_nonempty⟩
  have hflat : hs.flat = spec.core.flatOff (hs.edges v₀) := hs.flat_eq_flatOff v₀
  have hcard : (hs.edges v₀).card = 3 := (hs.typeI v₀).2.2.2.1
  have hmain := spec.core.componentCount_flatOff
    (spec.core.connected_of_connectedOff (hs.connected v₀)) spec.core_nonempty
    (hs.connected v₀)
  rw [← hflat, hcard] at hmain
  omega

/-- **The components of `G − Φ` are bridgeless.**  `Φ` is a flat exactly when no
slot outside `Φ` is a bridge of `G − Φ`, i.e. when every component of `G − Φ` is
bridgeless. -/
theorem bridgelessOff_flat {K : Finset (Fin n)}
    (hK : spec.core.IsComponentOff hs.flat K) :
    spec.core.BridgelessOff hs.flat K := by
  classical
  intro S hSK hSne hSKne
  by_contra hlt
  push Not at hlt
  have hstep : ∀ x ∈ spec.core.cut S, x ∉ hs.flat →
      x ∈ (spec.core.edgesInside hs.flat K).filter (spec.core.Crosses S) := by
    intro x hx hxΦ
    have hcross : spec.core.Crosses S x := spec.core.mem_cut.mp hx
    have hKclosed : ¬ spec.core.Crosses K x := hK.2.1 x hxΦ
    have h2 : spec.core.tail x ∈ S → spec.core.tail x ∈ K := fun h => hSK h
    have h3 : spec.core.head x ∈ S → spec.core.head x ∈ K := fun h => hSK h
    have hboth : spec.core.tail x ∈ K ∧ spec.core.head x ∈ K := by
      simp only [ExplicitPotential.Core.Crosses] at hcross hKclosed
      tauto
    refine Finset.mem_filter.mpr ⟨?_, hcross⟩
    simp only [ExplicitPotential.Core.edgesInside, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hxΦ, hboth.1, hboth.2⟩
  by_cases hcutsub : spec.core.cut S ⊆ hs.flat
  · exact hSKne (hK.2.2 S hSK hSne (spec.core.closedOff_iff.mpr hcutsub))
  · obtain ⟨f, hfS, hfΦ⟩ := Finset.not_subset.mp hcutsub
    have hfmem := hstep f hfS hfΦ
    have hsingle :
        (spec.core.edgesInside hs.flat K).filter (spec.core.Crosses S) = {f} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hfmem, fun x hx => ?_⟩
      by_contra hxf
      have h2card := Finset.one_lt_card.mpr ⟨f, hfmem, x, hx, fun h => hxf h.symm⟩
      omega
    have hsub : spec.core.cut S ⊆ insert f hs.flat := by
      intro x hx
      by_cases hxΦ : x ∈ hs.flat
      · exact Finset.mem_insert_of_mem hxΦ
      · have hx' := hstep x hx hxΦ
        rw [hsingle, Finset.mem_singleton] at hx'
        exact hx' ▸ Finset.mem_insert_self _ _
    let v₀ : Fin n := ⟨0, spec.core_nonempty⟩
    have hflat : hs.flat = spec.core.flatOff (hs.edges v₀) := hs.flat_eq_flatOff v₀
    refine spec.core.no_cut_subset_flatOff
      (spec.core.connected_of_connectedOff (hs.connected v₀)) (hs.connected v₀)
      (by rw [← hflat]; exact hfΦ) hfS ?_
    rw [← hflat]; exact hsub

/-- **The genus bookkeeping.**  The components of `G − Φ` carry a total genus of
`g − 3`, which is `3` at genus six. -/
theorem sum_genusOff_flat (hgenus : (p : ℤ) = (n : ℤ) + 5) :
    ∑ K ∈ spec.core.componentsOff hs.flat, spec.core.genusOff hs.flat K = 3 := by
  classical
  have hverts := spec.core.sum_card_componentsOff hs.flat
  have hedges := spec.core.sum_card_edgesInside hs.flat
  have hcc : (spec.core.componentsOff hs.flat).card + 2 = hs.flat.card :=
    hs.componentCount_flat
  have hexpand : ∑ K ∈ spec.core.componentsOff hs.flat, spec.core.genusOff hs.flat K
      = ((∑ K ∈ spec.core.componentsOff hs.flat,
            (spec.core.edgesInside hs.flat K).card : ℕ) : ℤ)
        - ((∑ K ∈ spec.core.componentsOff hs.flat, K.card : ℕ) : ℤ)
        + ((spec.core.componentsOff hs.flat).card : ℤ) := by
    rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    rw [show ((spec.core.componentsOff hs.flat).card : ℤ)
        = ∑ _K ∈ spec.core.componentsOff hs.flat, (1 : ℤ) by simp]
    rw [← Finset.sum_add_distrib]
    rfl
  rw [hexpand, hverts]
  omega

/-- A connected bridgeless graph of genus zero is a single vertex; so a component
of `G − Φ` of positive genus, being loopless, has at least two vertices. -/
theorem two_le_card_of_genusOff_pos {K : Finset (Fin n)}
    (hK : spec.core.IsComponentOff hs.flat K)
    (hgK : 0 < spec.core.genusOff hs.flat K) : 2 ≤ K.card := by
  classical
  by_contra hcard
  push Not at hcard
  obtain ⟨u, hu⟩ := hK.1
  have hcard1 : K.card = 1 := le_antisymm (by omega) (Finset.card_pos.mpr ⟨u, hu⟩)
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
  have hempty : spec.core.edgesInside hs.flat K = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun e he => ?_
    simp only [ExplicitPotential.Core.edgesInside, Finset.mem_filter, Finset.mem_univ,
      true_and, hx, Finset.mem_singleton] at he
    exact spec.core_loopless e (he.2.1.trans he.2.2.symm)
  rw [ExplicitPotential.Core.genusOff, hempty, hcard1] at hgK
  norm_num at hgK

/-- All the states of a hub system lie in a single linear equivalence class: the
`divisor_equiv` clause propagated along the connected move graph.  This is the
input the separation lemma consumes. -/
theorem divisor_linear_equiv (v w : Fin n) :
    linear_equiv (spec.scale N hN).graph (hs.divisor v) (hs.divisor w) := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter fun u =>
    linear_equiv (spec.scale N hN).graph (hs.divisor v) (hs.divisor u) with hSdef
  have hmem : ∀ u : Fin n,
      u ∈ S ↔ linear_equiv (spec.scale N hN).graph (hs.divisor v) (hs.divisor u) := by
    intro u; rw [hSdef]; simp
  have hvS : v ∈ S := (hmem v).mpr (linear_equiv.refl _ _)
  have huniv : S = Finset.univ := by
    by_contra hne
    obtain ⟨u, huS, w', -, -, hw'S, -, -, -, -, hlin⟩ :=
      hs.moves_connected S ⟨v, hvS⟩ hne
    exact hw'S ((hmem _).mpr (((hmem u).mp huS).trans hlin))
  exact (hmem w).mp (huniv ▸ Finset.mem_univ w)

/-- **Separation.**  A hub system has at most one hub vertex in each component of
`G − Φ`.

Proof: let `v ≠ w` both lie in `K`.  Since `E_v, E_w ⊆ Φ` and `E(K) ∩ Φ = ∅`,
neither `D_v` nor `D_w` has an interior chip inside `K`, so `D_v|_K = v` and
`D_w|_K = w`.  Write `D_w = D_v + prin F` (the `divisor_equiv` clause).  Both
`D_v` and `D_w` are reduced at their own vertices (`typeI_qReduced`),
so the max principle `Utilities.Gonality.le_apply_of_qReduced` gives
`F(v) = max F` and `F(w) = min F`, with `max F > min F`.  Every fine vertex over
`K` other than `v` carries no chip of `D_v`, so if it lies in the argmax `A` it
absorbs all of its neighbours.  Hence every slot of `K` whose two endpoints
straddle `A` — and `bridgelessOff_flat` supplies **two** of them — contributes an
interior fine neighbour of `v` outside `A` (`slot_boundary`); two such
neighbours force `prin F (v) ≤ -2`, while `D_v(v) = 1` and effectivity of `D_w`
give `prin F (v) ≥ -1`.

The only place the scale enters is `slot_boundary`. -/
theorem separation (hunit : spec.IsUnit) {K : Finset (Fin n)}
    (hK : spec.core.IsComponentOff hs.flat K) {v w : Fin n} (hv : v ∈ K)
    (hw : w ∈ K) : v = w := by
  classical
  by_contra hvw
  have h2N : 2 ≤ N := hs.two_le_scale hunit
  have hDv := hs.typeI v
  have hDw := hs.typeI w
  -- The script carrying the state at `v` to the state at `w`.
  obtain ⟨F, hF⟩ :=
    (principal_iff_eq_prin (spec.scale N hN).graph _).mp (hs.divisor_linear_equiv v w)
  have hFadd : ∀ x : (spec.scale N hN).graph.V,
      hs.divisor w x = hs.divisor v x + prin (spec.scale N hN).graph F x := by
    intro x
    have hx := congrFun hF x
    simp only [Pi.sub_apply] at hx
    omega
  have hDweq : hs.divisor w = hs.divisor v + prin (spec.scale N hN).graph F := by
    funext x
    simp only [Pi.add_apply]
    exact hFadd x
  -- Both states are reduced at their own core vertex.
  have hmax : ∀ x, F x ≤ F ((spec.scale N hN).coreVertex v) :=
    Utilities.Gonality.le_apply_of_qReduced
      (spec.typeI_qReduced N hN hunit hDv (hs.connected v))
      (by rw [← hDweq]; exact hDw.1)
  have hmin : ∀ x, F ((spec.scale N hN).coreVertex w) ≤ F x :=
    Utilities.Gonality.apply_le_of_qReduced
      (spec.typeI_qReduced N hN hunit hDw (hs.connected w)) hDv.1 hDweq
  -- The chip pattern of the two states at the two core vertices.
  have hDvv : hs.divisor v ((spec.scale N hN).coreVertex v) = 1 := by
    have h := hDv.2.2.1 v
    rwa [if_pos rfl] at h
  have hDww : hs.divisor w ((spec.scale N hN).coreVertex w) = 1 := by
    have h := hDw.2.2.1 w
    rwa [if_pos rfl] at h
  have hDvw : hs.divisor v ((spec.scale N hN).coreVertex w) = 0 := by
    have h := hDv.2.2.1 w
    rwa [if_neg fun hEq => hvw hEq.symm] at h
  -- The script is not constant: it strictly drops from `v` to `w`.
  have hstrict : F ((spec.scale N hN).coreVertex w)
      < F ((spec.scale N hN).coreVertex v) := by
    rcases lt_or_eq_of_le (hmax ((spec.scale N hN).coreVertex w)) with hlt | heq
    · exact hlt
    · exfalso
      have hconst : ∀ x, F x = F ((spec.scale N hN).coreVertex w) := by
        intro x
        have h1 := hmax x
        have h2 := hmin x
        omega
      have hprin :
          prin (spec.scale N hN).graph F ((spec.scale N hN).coreVertex w) = 0 := by
        rw [prin_apply]
        refine Finset.sum_eq_zero fun u _ => ?_
        rw [hconst u, hconst ((spec.scale N hN).coreVertex w), sub_self, zero_mul]
      have h := hFadd ((spec.scale N hN).coreVertex w)
      omega
  -- The argmax set of the script and its trace on the core.
  set A : Finset (spec.scale N hN).graph.V :=
    Finset.univ.filter (fun x => F x = F ((spec.scale N hN).coreVertex v)) with hAdef
  have hmemA : ∀ x, x ∈ A ↔ F x = F ((spec.scale N hN).coreVertex v) := by
    intro x; rw [hAdef]; simp
  have hvA : (spec.scale N hN).coreVertex v ∈ A := (hmemA _).mpr rfl
  have hwA : (spec.scale N hN).coreVertex w ∉ A := by
    rw [hmemA]; omega
  -- A vertex of the argmax carrying no chip of `D_v` keeps its neighbours inside.
  have habsorb : ∀ x, x ∈ A → hs.divisor v x = 0 →
      ∀ y, 0 < num_edges (spec.scale N hN).graph x y → y ∈ A := by
    intro x hxA hx0 y hy
    by_contra hyA
    have hFx : F x = F ((spec.scale N hN).coreVertex v) := (hmemA x).mp hxA
    have hFy : F y ≠ F ((spec.scale N hN).coreVertex v) := fun h => hyA ((hmemA y).mpr h)
    have hmaxx : ∀ u, F u ≤ F x := by intro u; rw [hFx]; exact hmax u
    have hle := prin_le_of_argmax F hmaxx {y} (by
      intro z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      have := hmax z
      omega)
    rw [Finset.sum_singleton] at hle
    have h1 : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph x y : ℤ) := by
      exact_mod_cast hy
    have hwx := hDw.1 x
    have hadd := hFadd x
    omega
  -- Inside `K` the state `D_v` has no chip except the one at `v`.
  have hzero_core : ∀ u : Fin n, u ≠ v →
      hs.divisor v ((spec.scale N hN).coreVertex u) = 0 := by
    intro u hu
    have h := hDv.2.2.1 u
    rwa [if_neg hu] at h
  have hzero_int : ∀ e : Fin p, e ∉ hs.flat →
      ∀ j : Fin ((spec.scale N hN).length e - 1),
        hs.divisor v ((spec.scale N hN).interiorVertex e j) = 0 := by
    intro e he j
    refine spec.interiorVertex_eq_zero N hN hDv.1 ?_ j
    have h := hDv.2.2.2.2 e
    rwa [if_neg fun hmem => he (hs.edges_subset_flat v hmem)] at h
  -- `S` is a proper non-empty subset of the component `K`, so `K` has at least
  -- two internal slots crossing it (`bridgelessOff_flat`).
  set S : Finset (Fin n) :=
    K.filter (fun u => (spec.scale N hN).coreVertex u ∈ A) with hSdef
  have hmemS : ∀ u, u ∈ S ↔ (u ∈ K ∧ (spec.scale N hN).coreVertex u ∈ A) := by
    intro u; rw [hSdef]; simp
  have hvS : v ∈ S := (hmemS v).mpr ⟨hv, hvA⟩
  have hSK : S ≠ K := by
    intro hEq
    have hwS : w ∈ S := by rw [hEq]; exact hw
    exact hwA ((hmemS w).mp hwS).2
  have hbl := hs.bridgelessOff_flat hK S (Finset.filter_subset _ _) ⟨v, hvS⟩ hSK
  -- Each such slot contributes an interior fine neighbour of `v` outside `A`.
  have hslot : ∀ e ∈ (spec.core.edgesInside hs.flat K).filter (spec.core.Crosses S),
      ∃ j : Fin ((spec.scale N hN).length e - 1),
        (spec.scale N hN).interiorVertex e j ∉ A ∧
        0 < num_edges (spec.scale N hN).graph ((spec.scale N hN).coreVertex v)
          ((spec.scale N hN).interiorVertex e j) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heIn, hecross⟩ := he
    have heIn' : e ∉ hs.flat ∧ spec.core.tail e ∈ K ∧ spec.core.head e ∈ K := by
      simpa [ExplicitPotential.Core.edgesInside] using heIn
    refine spec.slot_boundary N hN hunit h2N (fun x hxA hxv hxloc y hy => ?_) ?_
    · refine habsorb x hxA ?_ y hy
      rcases hxloc with rfl | rfl | ⟨j, rfl⟩
      · exact hzero_core _ fun hEq => hxv (by rw [hEq])
      · exact hzero_core _ fun hEq => hxv (by rw [hEq])
      · exact hzero_int e heIn'.1 j
    · intro hiff
      have h1 : spec.core.tail e ∈ S ↔ spec.core.head e ∈ S := by
        rw [hmemS, hmemS]
        exact ⟨fun h => ⟨heIn'.2.2, hiff.mp h.2⟩, fun h => ⟨heIn'.2.1, hiff.mpr h.2⟩⟩
      rcases hecross with ⟨ht, hh⟩ | ⟨hh, ht⟩
      · exact hh (h1.mp ht)
      · exact ht (h1.mpr hh)
  obtain ⟨e₁, he₁, e₂, he₂, hne12⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le one_lt_two hbl)
  obtain ⟨j₁, hj₁A, hj₁adj⟩ := hslot e₁ he₁
  obtain ⟨j₂, hj₂A, hj₂adj⟩ := hslot e₂ he₂
  have hyne : (spec.scale N hN).interiorVertex e₁ j₁
      ≠ (spec.scale N hN).interiorVertex e₂ j₂ := by
    intro hEq
    simp only [SubdivisionGraph.Spec.interiorVertex, Sum.inr.injEq] at hEq
    exact hne12 (congrArg Sigma.fst hEq)
  -- Two edges of the argmax boundary at `coreVertex v`, but `D_v` has one chip.
  have hT : ∀ z ∈ ({(spec.scale N hN).interiorVertex e₁ j₁,
      (spec.scale N hN).interiorVertex e₂ j₂} : Finset (spec.scale N hN).graph.V),
      F z < F ((spec.scale N hN).coreVertex v) := by
    intro z hz
    have hzA : z ∉ A := by
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hj₁A
      · rw [Finset.mem_singleton] at hz'
        subst hz'
        exact hj₂A
    have h1 := hmax z
    have h2 : F z ≠ F ((spec.scale N hN).coreVertex v) := fun h => hzA ((hmemA z).mpr h)
    omega
  have hle := prin_le_of_argmax F hmax _ hT
  rw [Finset.sum_pair hyne] at hle
  have h1 : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
      ((spec.scale N hN).coreVertex v)
      ((spec.scale N hN).interiorVertex e₁ j₁) : ℤ) := by exact_mod_cast hj₁adj
  have h2 : (1 : ℤ) ≤ (num_edges (spec.scale N hN).graph
      ((spec.scale N hN).coreVertex v)
      ((spec.scale N hN).interiorVertex e₂ j₂) : ℤ) := by exact_mod_cast hj₂adj
  have hwv := hDw.1 ((spec.scale N hN).coreVertex v)
  have haddv := hFadd ((spec.scale N hN).coreVertex v)
  omega

end HubSystem

/-! ## No hub system -/

/-- **No hub system in genus six.**  No connected loopless multigraph with
`|E| = |V| + 5` carries a hub system, at any scale `N`.

Clause (d) makes the system cover `V(G)`, so `separation` gives
`|V| ≤ c(G − Φ)`.
But `Σ genus(K_i) = g − 3 = 3 > 0`, so some component has positive genus and
hence at least two vertices, whence `c(G − Φ) ≤ |V| − 1`.  Contradiction.

No minimum-degree or cut-vertex hypothesis and no bound on `|V|` is used, and
the same proof works in every genus `g ≥ 4`, where `g − 3 > 0`. -/
theorem no_hub_system (hunit : spec.IsUnit) (hcore : spec.core.Connected)
    (hgenus : (p : ℤ) = (n : ℤ) + 5) : IsEmpty (spec.HubSystem N hN) := by
  classical
  refine ⟨fun hs => ?_⟩
  -- `hcore` is not consumed below: clause (a) of the hub system already forces
  -- `G` to be connected (`connected_of_connectedOff`).
  have _hcore : spec.core.Connected := hcore
  -- Separation makes every component of `G − Φ` a single vertex.
  have hsingleton : ∀ K ∈ spec.core.componentsOff hs.flat, K.card = 1 := by
    intro K hK
    have hKcomp := spec.core.mem_componentsOff.mp hK
    obtain ⟨u, hu⟩ := hKcomp.1
    have hKu : K = {u} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hu, fun x hx => hs.separation hunit hKcomp hx hu⟩
    rw [hKu, Finset.card_singleton]
  -- But the genera of the components sum to three, so one of them is positive.
  have hsum := hs.sum_genusOff_flat hgenus
  obtain ⟨K, hK, hgK⟩ : ∃ K ∈ spec.core.componentsOff hs.flat,
      0 < spec.core.genusOff hs.flat K := by
    by_contra hall
    push Not at hall
    have hle : ∑ K ∈ spec.core.componentsOff hs.flat,
        spec.core.genusOff hs.flat K ≤ 0 := Finset.sum_nonpos hall
    omega
  -- A component of positive genus is loopless with at least two vertices.
  have h2 := hs.two_le_card_of_genusOff_pos (spec.core.mem_componentsOff.mp hK) hgK
  have h1 := hsingleton K hK
  omega

end Spec

end SubdivisionGraph

end Utilities.Certificate
