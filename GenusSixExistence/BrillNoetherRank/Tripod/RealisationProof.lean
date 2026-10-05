module

public import GenusSixExistence.BrillNoetherRank.Tripod.TripodModelDefs
public import GenusSixExistence.BrillNoetherRank.Tripod.ClawDefs
public import DraismaVargasCount.DegenerateBigDivisor
public import DraismaVargasCount.ExpansionSeriesMoment
public import DraismaVargasCount.RowHairpinPosition
public import Utilities.Subdivision.ZeroBudgetRounding
public import GenusSixExistence.BrillNoetherRank.Tripod.ChainSeparator
public import DraismaVargasCount.PencilTransportProducer
public import GenusSixExistence.BrillNoetherRank.Tripod.ClawShape

@[expose] public section

/-!
# The realisation of a closed odd claw member, link by link

Proof of `Realisation.witness_of_closed_oddClaw`, under the same binders and conclusion
(`RealisationProof.witness_of_closed_oddClaw`). Prose proof:
`Research/genus-six-brill-noether-rank.md`, §7.1 (The repaired morphism), §7.2 (Fibres and
retraction), §7.3 (The witness divisor E + F), §7.4 (Odd multiplicity gives an odd scale) and
§7.5 (Rounding with E fixed), with §8.2 (Where the Lean proof differs from the prose); section
and statement numbers in this file refer to that note.

## The construction (links (1)–(4))

Let `k = memberScale mem`. The member lives over `tripodCore G̃ s` at the actual request, which
is `degenerateLength` on the G-slots and the legs on the leg slots (`legRequest`). As in the
unmarked endgame (`DegenerateBigDivisor`), it is placed by `DegeneratePlacement` on a
specification `tripodSpec M k` of the tripod core that only partly fills its slots: a G-slot gets
the length `M.expansion.bigSpec (M.small.scale k)` gives it (`1` on a contracted slot), a leg the
length `k ℓ_j`. The placed fibre over `φ(c)` is `placed`. The **`G′`-part** of the fibre
(`gFibre`) keeps the source vertices whose retraction is off the tripod (`OnTripod`: the centre and
the leg rows are `Y`); it is placed (`placedG`), lands on G-positions only (`placedG_support`), is
restricted along the inclusion `gEmbed` of the expanded marked core into the tripod specification
(`gPart`), and is pushed along the expansion's contraction to the divisor `clawDivisor` on
`M.small.scale k`. This is `F_k` of Proposition 7.4, with `s_k = 1`: the `G′`-part of the
fibre over `φ(c)` retracted to `G`. The split is made on the source, not on positions,
because at the closed point a point of `Y′` may be placed at a mark; on the interior of a G-slot
the two agree (`placedG_interior`).

## Contents

* `round_completion` (links (5)–(6), §7.5): interior firing on `F` alone
  (`InteriorFiring.exists_onGrid`), the scale composition (`scaleScaleLaplacianEquiv`), and
  zero-budget nearest rounding with the coarse part fixed (`Spec.rank_ge_of_rank_scale_ge_nearest`
  with `D₀` the embedded marks and two chips).
* `transport_completion` (§7.5): `M.transport u` and `LaplacianEquiv.rank_mapDiv_ge_iff` move
  the result to the `u`-fold subdivision of `G`, the marks going to `E`.
* `clawDivisor_effective`, and `clawDivisor_moment` (links (1) and (4), §7.4): every slot moment
  of `clawDivisor` on `M.small.scale (2^a u)` is divisible by `2^a`.
* **The rank-determining set** (`rankDetermining_gReach`, §7.4): the points of `G` over target
  vertices are rank-determining on `M.small.scale k`.
  * `rankDetermining_of_fib_loopDoubles` — the graph half, `ChainSeparator.rank_ge_one_of_fib_loopDoubles`:
    the strong-separator lemma applied to the reached set, with cells that are maximal unreached
    intervals of the slots and of the `double` chains through their bivalent markers (no marker
    move or merge).
  * `loopDouble_reach` — the member half: the row over a loop `double` has an interior address
    strictly inside the chain (`loopRow_interior`, the argument of
    `PencilTransportProducer.doubleRowInterior_of_loopDoubles` on the G-rows, with the label
    potential `labelPot` constant on the fibres of the expansion), realised in `gReach`
    (`address_mem_gReach`).
* **The slid fibres** (`exists_slidPencil`, §7.4 and §8.2), from the slid fibres
  `slidFibre x = slidBase x + Σ_j markCoeff x j · markChip j` (`s_j·1[x ∈ H_j]` chips at the
  marks, read through the leg edge `germ` and `TreeMetricPotential.cutValue`):
  * `slidFibre_transport` — **any two slid fibres are linearly equivalent**, by the descended
    G-row script of the tree potential with incidence `anchor − root`. The small side
    (`slidBase_sub_eq_rows`, `gRealize_gRow`, `gRealize_legRow`), the big side (`gScript`,
    `gCompat`, `gScript_eq_pullScript`, `gPushDiv_prin_script`, `gSlot_sum`) and the leg edges
    at the marks (`legRow_sum`, `germ_unique`, `markCoeff_eq_germ`, `tree_flow_eq`,
    `germ_balance`) combine to this: it is the argument of `PencilTransportProducer` §5–§7 on
    the G-rows, plus the boundary term of Lemma 7.3.
  * `slidFibre_effective`, `slidBase_le_slidFibre`, `slidFibre_centre` (from `markCoeff_centre`).
* `jump_rule` (Lemma 4.1 on `G′`): `δ_G(x) + Σ_j markCoeff x j` is constant, from the degree
  of the linear system; `sum_gFibre` from it, `claw_kZero` and `markCoeff_centre`, and
  `deg_clawDivisor` from `sum_gFibre`.
* `centreTarget_not_leaf`, `exists_slidBase_pos`, `rank_clawDivisor`, `fib_mem_gReach`,
  `small_scale_connected`, and `witness_of_closed_oddClaw`, the assembly, with `N = u` the odd
  part of `memberScale mem`.
* **The claw classification** (Theorem 4.7(b), Lemma 4.8, Corollary 4.10), from `ClawShape`,
  where it is proved for every claw frame over a connected core:
  * `markCoeff_centre` — the leg edge at each mark has index one (`ClawShape.firstEdge_index`,
    Lemma 4.8) and its target edge separates `φ(c)` from the mark image
    (`ClawShape.firstEdge_separates`, Theorem 4.7(b), Corollary 4.3);
  * `claw_kZero` — `k₀ = 0`, at `x = φ(c)`: `δ_G(φ(c)) = 2` (`sum_gFibre_centre`, from
    `ClawShape.sum_yCore_centre`, the branch census of the tripod part of the fibre) and three mark
    coefficients one. `onTripod_iff_yCore` reads `OnTripod` as the frame predicate
    `ClawShape.YCore`.

  Neither uses closedness or long legs.
-/

namespace GenusSixExistence.Tripod.RealisationProof

open DraismaVargas.Count
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open DraismaVargas.Count.RowRealizedPosition (memberScale memberScale_pos)
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.SurvivingSlotMap
  (InteriorAddress addressVertex addressVertex_valency addressVertex_injective)
open DraismaVargas.Count.CanonicalSurvivor (representative representative_eq_iff)
open Gadget Classification Closure

/-! ## 0.  Generic helpers -/

section Generic

/-- Adding a fixed divisor respects linear equivalence (stated on an abstract graph, so that no
concrete vertex type is unfolded). -/
theorem linear_equiv_add_left {H : CFGraph} (A : CFDiv H) {F F' : CFDiv H}
    (h : linear_equiv H F F') : linear_equiv H (A + F) (A + F') := by
  unfold linear_equiv at h ⊢
  have hEq : A + F' - (A + F) = F' - F := by abel
  rw [hEq]
  exact h

/-- An effective divisor positive at `x`, linearly equivalent to `Dv`, makes `Dv - x`
winnable. -/
theorem winnable_sub_one_chip_of_linear_equiv {H : CFGraph} {Dv P : CFDiv H}
    (hP : effective P) (hEquiv : linear_equiv H Dv P) {x : H.V} (hx : 0 < P x) :
    winnable H (Dv - one_chip x) := by
  rw [winnable_iff_exists_effective]
  refine ⟨P - one_chip x, ?_, ?_⟩
  · intro b
    by_cases hb : b = x
    · subst hb
      simp only [Pi.sub_apply, one_chip_apply_v]
      omega
    · simp only [Pi.sub_apply, one_chip, ite_eq_right hb, sub_zero]
      exact hP b
  · unfold linear_equiv at hEquiv ⊢
    have hEq : (P - one_chip x) - (Dv - one_chip x) = P - Dv := by abel
    rw [hEq]
    exact hEquiv

/-- `LaplacianEquiv.mapDiv` commutes with finite sums. -/
theorem mapDiv_sum {H K : CFGraph} (L : LaplacianEquiv H K) {ι : Type*} (s : Finset ι)
    (f : ι → CFDiv H) : L.mapDiv (∑ i ∈ s, f i) = ∑ i ∈ s, L.mapDiv (f i) := by
  funext y
  simp only [LaplacianEquiv.mapDiv_apply, Finset.sum_apply]

/-- **Re-requesting a member.** A member over `y₁` is a member over any `y₂ = y₁`, with the same
target, datum, presentation, identification and coordinates, so its frame, scale and multiplicity
are unchanged by definition. -/
def reRequest {n p degree : ℕ} {core : Core n p} {y₁ y₂ : Fin p → ℚ} (h : y₁ = y₂)
    (mem : FibreMember core y₁ degree) : FibreMember core y₂ degree where
  target := mem.target
  data := mem.data
  fullDim := mem.fullDim
  ident := mem.ident
  coords := mem.coords
  realizes := by subst h; exact mem.realizes

end Generic

/-! ## 1.  Links (5)–(6): interior firing on `F` and zero-budget rounding with `E` fixed -/

section Rounding

variable {n p : ℕ}

/-- The divisor of a family of core vertices of a specification. -/
noncomputable def coreChips (S : Spec n p) {ι : Type*} [Fintype ι] (v : ι → Fin n) :
    CFDiv S.graph :=
  ∑ i, one_chip (S.coreVertex (v i))

theorem embed_finset_sum (S : Spec n p) (N : ℕ) (hN : 0 < N) {ι : Type*} (s : Finset ι)
    (D : ι → CFDiv S.graph) : S.embed N hN (∑ i ∈ s, D i) = ∑ i ∈ s, S.embed N hN (D i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using S.embed_zero N hN
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, S.embed_add N hN, ih]

/-- Embedding into a regular subdivision keeps chips at core vertices. -/
theorem embed_coreChips (S : Spec n p) (N : ℕ) (hN : 0 < N) {ι : Type*} [Fintype ι]
    (v : ι → Fin n) : S.embed N hN (coreChips S v) = coreChips (S.scale N hN) v := by
  unfold coreChips
  rw [embed_finset_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [S.embed_one_chip N hN, Spec.fineOf_coreVertex]

/-- The composition relabelling fixes core vertices. -/
theorem scaleScale_symm_coreVertex (S : Spec n p) (u M : ℕ) (hu : 0 < u) (hM : 0 < M)
    (v : Fin n) :
    (ScaleComposition.scaleScaleLaplacianEquiv S u M hu hM).symm
        ((S.scale (M * u) (Nat.mul_pos hM hu)).coreVertex v) =
      ((S.scale u hu).scale M hM).coreVertex v := by
  show (ScaleComposition.scaleScaleLaplacianEquiv S u M hu hM).toEquiv.symm _ = _
  rw [Equiv.symm_apply_eq, ScaleComposition.scaleScaleLaplacianEquiv_toEquiv,
    Spec.vertexEquiv_coreVertex]
  rfl

theorem scaleScale_symm_coreChips (S : Spec n p) (u M : ℕ) (hu : 0 < u) (hM : 0 < M)
    {ι : Type*} [Fintype ι] (v : ι → Fin n) :
    (ScaleComposition.scaleScaleLaplacianEquiv S u M hu hM).symm.mapDiv
        (coreChips (S.scale (M * u) (Nat.mul_pos hM hu)) v) =
      coreChips ((S.scale u hu).scale M hM) v := by
  unfold coreChips
  rw [mapDiv_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LaplacianEquiv.mapDiv_one_chip, scaleScale_symm_coreVertex]

/-- **Links (5)–(6), §7.5.** An effective `F` of degree two on `S.scale (2^a u)` whose slot
moments are divisible by `2^a`, completing the embedded core chips `D₀` to rank at least one,
descends to an effective `F'` of degree two on `S.scale u` with the same property.

Interior firing is applied to `F` alone (§7.5), so nothing is needed about the chips
of `D₀` surviving it; the nearest rounding then has budget zero, every chip being on the
`2^a`-grid (§7.5, as `BrillNoetherRank.coarse_completion` with the zero budget of
`ZeroBudgetRounding`). -/
theorem round_completion (S : Spec n p) {ι : Type*} [Fintype ι] (v : ι → Fin n)
    (u a : ℕ) (hu : 0 < u) (hk : 0 < 2 ^ a * u)
    (F : CFDiv (S.scale (2 ^ a * u) hk).graph) (hF : effective F) (hdeg : deg F = 2)
    (hmom : ∀ j, ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment (S.scale (2 ^ a * u) hk) F j)
    (hrank : rank (S.scale (2 ^ a * u) hk).graph
      (S.embed (2 ^ a * u) hk (coreChips S v) + F) ≥ 1) :
    ∃ F' : CFDiv (S.scale u hu).graph, effective F' ∧ deg F' = 2 ∧
      rank (S.scale u hu).graph (S.embed u hu (coreChips S v) + F') ≥ 1 := by
  classical
  have hM : 0 < 2 ^ a := Nat.two_pow_pos a
  -- interior firing on `F` alone
  obtain ⟨F₁, hlin, hF₁, hdeg₁, hgrid₁⟩ :=
    InteriorFiring.exists_onGrid (S.scale (2 ^ a * u) hk) (2 ^ a)
      (fun e ↦ by
        rw [Spec.scale_length]
        exact Dvd.dvd.mul_right (Dvd.intro u rfl) _)
      F hF hmom
  have hrank₁ : rank (S.scale (2 ^ a * u) hk).graph
      (S.embed (2 ^ a * u) hk (coreChips S v) + F₁) ≥ 1 := by
    rw [← Utilities.rank_eq_of_linear_equiv _ (linear_equiv_add_left _ hlin)]
    exact hrank
  -- the composition relabelling
  set L := ScaleComposition.scaleScaleLaplacianEquiv S u (2 ^ a) hu hM with hL
  set F₂ : CFDiv ((S.scale u hu).scale (2 ^ a) hM).graph := L.symm.mapDiv F₁ with hF₂def
  have hF₂ : effective F₂ := (L.symm.effective_mapDiv_iff F₁).mpr hF₁
  have hdeg₂ : deg F₂ = 2 := by
    rw [hF₂def, L.symm.deg_mapDiv, hdeg₁, hdeg]
  have hgrid₂ : ∀ y, F₂ y ≠ 0 → SlotGrid.OnGrid ((S.scale u hu).scale (2 ^ a) hM) (2 ^ a) y := by
    intro y hy
    have hy' : F₁ (L.toEquiv y) ≠ 0 := hy
    have h := hgrid₁ (L.toEquiv y) hy'
    rw [hL, ScaleComposition.scaleScaleLaplacianEquiv_toEquiv] at h
    exact (ScaleComposition.onGrid_vertexEquiv_iff S u (2 ^ a) hu hM (2 ^ a) y).mp h
  have hrank₂ : rank ((S.scale u hu).scale (2 ^ a) hM).graph
      ((S.scale u hu).embed (2 ^ a) hM (S.embed u hu (coreChips S v)) + F₂) ≥ 1 := by
    have hmap : L.symm.mapDiv (S.embed (2 ^ a * u) hk (coreChips S v) + F₁) =
        (S.scale u hu).embed (2 ^ a) hM (S.embed u hu (coreChips S v)) + F₂ := by
      rw [LaplacianEquiv.mapDiv_add, embed_coreChips, embed_coreChips, embed_coreChips]
      congr 1
      exact scaleScale_symm_coreChips S u (2 ^ a) hu hM v
    rw [← hmap]
    exact (L.symm.rank_mapDiv_ge_iff _ 1).mpr hrank₁
  -- two chips on the grid, rounded at zero budget
  obtain ⟨y₁, y₂, hy⟩ := exists_chip_pair_of_effective_deg_two _ F₂ hF₂ hdeg₂
  have hpos₁ : F₂ y₁ ≠ 0 := by
    rw [hy]
    have h₂ := eff_one_chip (G := ((S.scale u hu).scale (2 ^ a) hM).graph) y₂ y₁
    simp only [Pi.add_apply, one_chip_apply_v]
    omega
  have hpos₂ : F₂ y₂ ≠ 0 := by
    rw [hy]
    have h₁ := eff_one_chip (G := ((S.scale u hu).scale (2 ^ a) hM).graph) y₁ y₂
    simp only [Pi.add_apply, one_chip_apply_v]
    omega
  have hd₁ := SlotGrid.roundDist_eq_zero_of_onGrid (S.scale u hu) (2 ^ a) hM (hgrid₂ y₁ hpos₁)
  have hd₂ := SlotGrid.roundDist_eq_zero_of_onGrid (S.scale u hu) (2 ^ a) hM (hgrid₂ y₂ hpos₂)
  have hbudget : (∑ i : Fin 2, ((S.scale u hu).roundDist (2 ^ a) hM (![y₁, y₂] i) : ℤ)) <
      (2 ^ a : ℕ) := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hd₁, hd₂]
    exact_mod_cast hM
  have hrank2 : rank ((S.scale u hu).scale (2 ^ a) hM).graph
      ((S.scale u hu).embed (2 ^ a) hM (S.embed u hu (coreChips S v)) +
        ∑ i : Fin 2, one_chip (![y₁, y₂] i)) ≥ 1 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hy]
    exact hrank₂
  have hcoarse := (S.scale u hu).rank_ge_of_rank_scale_ge_nearest (2 ^ a) hM ![y₁, y₂]
    (S.embed u hu (coreChips S v)) 1 hbudget hrank2
  rw [Fin.sum_univ_two] at hcoarse
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcoarse
  have heff : effective (one_chip ((S.scale u hu).nearest (2 ^ a) hM y₁) +
      one_chip ((S.scale u hu).nearest (2 ^ a) hM y₂) : CFDiv (S.scale u hu).graph) := by
    intro w
    exact add_nonneg (eff_one_chip _ w) (eff_one_chip _ w)
  have hdegB : deg (one_chip ((S.scale u hu).nearest (2 ^ a) hM y₁) +
      one_chip ((S.scale u hu).nearest (2 ^ a) hM y₂) : CFDiv (S.scale u hu).graph) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  exact ⟨_, heff, hdegB, hcoarse⟩

end Rounding

/-! ## 2.  §7.5: transport to `G`, the marks going to `E` -/

section Transport

variable {G : CFGraph.{0}} {E : CFDiv (UnitSubdivisionPresentation.spec G).graph}

/-- The three marks of a tripod model, as a divisor on its small specification. -/
noncomputable def marksDiv (M : TripodModel G E) : CFDiv M.small.graph :=
  coreChips M.small M.smallMark

/-- **Transport to `G`** (§7.5). A completion of the marks on `M.small.scale u` is a completion
of `E` on the `u`-fold subdivision of `G`. -/
theorem transport_completion (M : TripodModel G E) (u : ℕ) (hu : 0 < u)
    (F : CFDiv (M.small.scale u hu).graph) (hF : effective F) (hdeg : deg F = 2)
    (hrank : rank (M.small.scale u hu).graph (M.small.embed u hu (marksDiv M) + F) ≥ 1) :
    ∃ F' : CFDiv ((UnitSubdivisionPresentation.spec G).scale u hu).graph,
      effective F' ∧ deg F' = 2 ∧
        rank ((UnitSubdivisionPresentation.spec G).scale u hu).graph
          ((UnitSubdivisionPresentation.spec G).embed u hu E + F') ≥ 1 := by
  obtain ⟨eqv, heqv⟩ := M.transport u hu
  refine ⟨eqv.mapDiv F, (eqv.effective_mapDiv_iff F).mpr hF, by rw [eqv.deg_mapDiv, hdeg], ?_⟩
  rw [← heqv, ← LaplacianEquiv.mapDiv_add]
  exact (eqv.rank_mapDiv_ge_iff _ 1).mpr hrank

end Transport

/-! ## 3.  A rank-determining set for a subdivision carrying markers (the graph half) -/

section RankDetermining

/-- **The rank-determining set, graph-theoretic half** (§7.4, "a rank-determining set"; Luo's
criterion). On a subdivision `T` of the small core of an expansion datum, a set `R` of vertices
that contains every `D.fib` image and a vertex strictly inside the chain of every `double` slot
that displays a loop is rank-determining for the rank-one test.

Proved in `ChainSeparator.rank_ge_one_of_fib_loopDoubles`, by the strong-separator lemma applied
directly to the reached set: every slot of `T`, and the chain of every `double` slot through its
bivalent marker, is a bivalent path, and a maximal unreached interval of one with distinct reached
ends is a strong-separator cell. No marker move or merge is needed. -/
theorem rankDetermining_of_fib_loopDoubles {n p N Q : ℕ} (D : ExpansionData n p N Q)
    (T : Spec n p) (hCond : D.Conditions T.core) (hConn : graph_connected T.graph)
    (R : Set T.Vertex) (hFib : ∀ a : Fin N, T.coreVertex (D.fib a) ∈ R)
    (hLoop : ∀ (e : Fin Q) (j₁ j₂ : Fin p), D.kind e = SlotKind.double j₁ j₂ →
      T.core.tail j₁ = T.core.head j₂ →
      ∃ t, 0 < t ∧ t < T.length j₁ + T.length j₂ ∧
        kindVertex T (T.core.tail j₁) (SlotKind.double j₁ j₂) t ∈ R)
    (Dv : CFDiv T.graph) (hReach : ∀ w ∈ R, winnable T.graph (Dv - one_chip w)) :
    rank T.graph Dv ≥ 1 :=
  ChainSeparator.rank_ge_one_of_fib_loopDoubles D T hCond hConn R hFib hLoop Dv hReach

end RankDetermining

/-! ## 4.  Links (1)–(4): the placed fibre over `φ(c)` and its G-part -/

section Construction

variable {G : CFGraph.{0}} {E : CFDiv (UnitSubdivisionPresentation.spec G).graph}
variable (M : TripodModel G E)

/-- The actual request of `M`, in natural numbers. -/
def legRequest : Fin (15 + 1 + 1 + 1 + 3) → ℕ :=
  Fin.addCases (fun i ↦ degenerateLength M.expansion M.small i) M.legs

theorem request_eq : M.request = fun e ↦ ((legRequest M e : ℕ) : ℚ) := by
  funext e
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) e
  · simp [TripodModel.request, legRequest]
  · simp [TripodModel.request, legRequest]

theorem expansion_loopless :
    ∀ e, M.expansion.bigCore.tail e ≠ M.expansion.bigCore.head e :=
  ExpansionData.loopless_of_conditions M.conditions

theorem markedCore_loopless' :
    ∀ i, (markedCore M.core M.slots).tail i ≠ (markedCore M.core M.slots).head i := by
  rw [← M.bigCore_eq]
  exact expansion_loopless M

theorem tripodCore_loopless' :
    ∀ e, (tripodCore M.core M.slots).tail e ≠ (tripodCore M.core M.slots).head e :=
  attachTripod_loopless _ _ (markedCore_loopless' M)

theorem legs_pos (j : Fin 3) : 0 < M.legs j :=
  lt_of_le_of_lt (Nat.zero_le _) (M.long j)

variable (k : ℕ) (hk : 0 < k)

/-- The expanded marked core at scale `k`: the target the unmarked endgame places on. -/
abbrev bigSpecAt : Spec (10 + 1 + 1 + 1) (15 + 1 + 1 + 1) :=
  M.expansion.bigSpec (M.small.scale k hk) (by norm_num) (expansion_loopless M)

/-- Slot lengths of the tripod specification: the expanded lengths on the G-slots, `k ℓ_j` on the
legs. -/
def tripodLength : Fin (15 + 1 + 1 + 1 + 3) → ℕ :=
  Fin.addCases (fun i ↦ (bigSpecAt M k hk).length i) fun j ↦ k * M.legs j

theorem tripodLength_pos : ∀ e, 0 < tripodLength M k hk e := by
  intro e
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) e
  · simp only [tripodLength, Fin.addCases_left]
    exact (bigSpecAt M k hk).length_pos i
  · simp only [tripodLength, Fin.addCases_right]
    exact Nat.mul_pos hk (legs_pos M j)

/-- **The tripod specification at scale `k`**: the target on which the member is placed. It is
reducible, so that its core is literally `tripodCore M.core M.slots`. -/
abbrev tripodSpec : Spec (10 + 1 + 1 + 1 + 1) (15 + 1 + 1 + 1 + 3) where
  core := tripodCore M.core M.slots
  length := tripodLength M k hk
  core_nonempty := by norm_num
  core_loopless := tripodCore_loopless' M
  length_pos := tripodLength_pos M k hk

theorem tripodSpec_length_castAdd (i : Fin (15 + 1 + 1 + 1)) :
    (tripodSpec M k hk).length (Fin.castAdd 3 i) = (bigSpecAt M k hk).length i := by
  show tripodLength M k hk (Fin.castAdd 3 i) = _
  simp only [tripodLength, Fin.addCases_left]

theorem tripodLength_castAdd (i : Fin (15 + 1 + 1 + 1)) :
    tripodLength M k hk (Fin.castAdd 3 i) = (bigSpecAt M k hk).length i := by
  simp only [tripodLength, Fin.addCases_left]

theorem tripodSpec_length_natAdd (j : Fin 3) :
    (tripodSpec M k hk).length (Fin.natAdd (15 + 1 + 1 + 1) j) = k * M.legs j := by
  show tripodLength M k hk (Fin.natAdd _ j) = _
  simp only [tripodLength, Fin.addCases_right]

/-- **The inclusion of the G-part.** A core vertex of the expanded marked core is the same vertex
of the tripod core, and an interior vertex of a G-slot is the same interior vertex there. -/
def gEmbed : (bigSpecAt M k hk).Vertex → (tripodSpec M k hk).Vertex
  | Sum.inl v => Sum.inl v.castSucc
  | Sum.inr x => Sum.inr ⟨Fin.castAdd 3 x.1,
      Fin.cast (congrArg (· - 1) (tripodSpec_length_castAdd M k hk x.1).symm) x.2⟩

/-- **The G-part** of a divisor on the tripod specification: its restriction to the expanded
marked core. -/
def gPart (Bv : CFDiv (tripodSpec M k hk).graph) : CFDiv (bigSpecAt M k hk).graph :=
  fun w ↦ Bv (gEmbed M k hk w)

theorem gPart_effective {Bv : CFDiv (tripodSpec M k hk).graph} (h : effective Bv) :
    effective (gPart M k hk Bv) :=
  fun _ ↦ h _

/-- A path position of a G-slot of the tripod specification is a G-position. -/
theorem pathVertex_castAdd_mem_range (e : Fin (15 + 1 + 1 + 1))
    (q : (tripodSpec M k hk).PathPosition (Fin.castAdd 3 e)) :
    ∃ w, (tripodSpec M k hk).pathVertex (Fin.castAdd 3 e) q = gEmbed M k hk w := by
  unfold Spec.pathVertex
  split_ifs with h0 hL
  · refine ⟨Sum.inl ((markedCore M.core M.slots).tail e), ?_⟩
    show Sum.inl ((tripodCore M.core M.slots).tail (Fin.castAdd 3 e)) = _
    rw [tripodCore, attachTripod_tail_castAdd]
    rfl
  · refine ⟨Sum.inl ((markedCore M.core M.slots).head e), ?_⟩
    show Sum.inl ((tripodCore M.core M.slots).head (Fin.castAdd 3 e)) = _
    rw [tripodCore, attachTripod_head_castAdd]
    rfl
  · exact ⟨Sum.inr ⟨e, Fin.cast (congrArg (· - 1) (tripodSpec_length_castAdd M k hk e))
      ⟨q.val - 1, by have := q.isLt; omega⟩⟩, rfl⟩

theorem gEmbed_injective : Function.Injective (gEmbed M k hk) := by
  rintro (v | ⟨i, o⟩) (v' | ⟨i', o'⟩) h
  · exact congrArg Sum.inl (Fin.castSucc_injective _ (Sum.inl.inj h))
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · have hσ := Sum.inr.inj h
    have hi : i = i' := Fin.castAdd_injective _ _ (congrArg Sigma.fst hσ)
    subst hi
    have ho : o.val = o'.val :=
      congrArg (fun x : (tripodSpec M k hk).Interior ↦ x.2.val) hσ
    exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Fin.ext ho)))

/-- A divisor supported on the G-positions keeps its degree when restricted to them. -/
theorem deg_gPart_of_support (Bv : CFDiv (tripodSpec M k hk).graph)
    (h : ∀ v, Bv v ≠ 0 → ∃ w, v = gEmbed M k hk w) : deg (gPart M k hk Bv) = deg Bv := by
  show (∑ w : (bigSpecAt M k hk).Vertex, Bv (gEmbed M k hk w)) =
    ∑ v : (tripodSpec M k hk).Vertex, Bv v
  refine Fintype.sum_of_injective (gEmbed M k hk) (gEmbed_injective M k hk) _ _ ?_ fun _ ↦ rfl
  intro v hv
  by_contra hne
  obtain ⟨w, rfl⟩ := h v hne
  exact hv ⟨w, rfl⟩

variable {M}

/-- The member at the request `legRequest`: the same frame and coordinates. -/
noncomputable def reMember (mem : FibreMember (tripodCore M.core M.slots) M.request (3 + 2)) :
    FibreMember (tripodCore M.core M.slots) (fun e ↦ ((legRequest M e : ℕ) : ℚ)) (3 + 2) :=
  reRequest (request_eq M) mem

theorem degen_fit {n p N Q : ℕ} (D : ExpansionData n p N Q) (small : Spec n p) (k : ℕ)
    (hk : 0 < k) (e : Fin Q) :
    k * degenerateLength D small e ≤ kindLength (small.scale k hk) (D.kind e) := by
  by_cases h : D.kind e = SlotKind.contracted
  · rw [DegenerateBigDivisor.degenerateLength_contracted D small h, Nat.mul_zero]
    exact Nat.zero_le _
  · rw [DegenerateBigDivisor.degenerateLength_of_ne D small h,
      DegenerateBigDivisor.kindLength_scale_of_ne_contracted small k hk h]

theorem degen_exact {n p N Q : ℕ} (D : ExpansionData n p N Q) (small : Spec n p) (k : ℕ)
    (hk : 0 < k) (e : Fin Q) (hTwo : 1 < kindLength (small.scale k hk) (D.kind e)) :
    k * degenerateLength D small e = kindLength (small.scale k hk) (D.kind e) := by
  by_cases h : D.kind e = SlotKind.contracted
  · rw [h] at hTwo
    exact absurd hTwo (by simp [kindLength])
  · rw [DegenerateBigDivisor.degenerateLength_of_ne D small h,
      DegenerateBigDivisor.kindLength_scale_of_ne_contracted small k hk h]

variable (mem : FibreMember (tripodCore M.core M.slots) (fun e ↦ ((legRequest M e : ℕ) : ℚ)) (3 + 2))

/-- **The fit** (Proposition 7.4): the member never overruns the room `tripodSpec` gives it. -/
theorem tripod_fit (hScale : memberScale mem = k) :
    ∀ e, memberScale mem * legRequest M e ≤ (tripodSpec M k hk).length e := by
  intro e
  rw [hScale]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) e
  · rw [tripodSpec_length_castAdd]
    simp only [legRequest, Fin.addCases_left]
    exact degen_fit M.expansion M.small k hk i
  · rw [tripodSpec_length_natAdd]
    simp only [legRequest, Fin.addCases_right, le_refl]

/-- **The exactness, where it is used**: a slot with an interior vertex is filled exactly. -/
theorem tripod_exact (hScale : memberScale mem = k) :
    ∀ e, 1 < (tripodSpec M k hk).length e →
      memberScale mem * legRequest M e = (tripodSpec M k hk).length e := by
  intro e
  rw [hScale]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) e
  · intro hTwo
    rw [tripodSpec_length_castAdd] at hTwo ⊢
    simp only [legRequest, Fin.addCases_left]
    exact degen_exact M.expansion M.small k hk i hTwo
  · intro _
    rw [tripodSpec_length_natAdd]
    simp only [legRequest, Fin.addCases_right]

/-! ### The split `G′ / Y′` of the source, and the fibre over `φ(c)` -/

/-- The member has a surviving source vertex (its centre); the base point of the retraction. -/
theorem survivor_exists : ∃ v : mem.data.SourceVertex, 0 < nonDanglingValency mem.data v :=
  ⟨(mem.ident.vertex.symm (centre 10)).1, by
    have := (mem.ident.vertex.symm (centre 10)).2
    omega⟩

/-- **A surviving source vertex on the tripod `Y`**: the centre, or an interior vertex of a leg
row. A source vertex lies on `Y′` (§4.1) when its retraction does; the trees
grafted at the marks retract to the marks, which are branch vertices of `G`, so they lie on `G′`. -/
def OnTripod (s : {v : mem.data.SourceVertex // 0 < nonDanglingValency mem.data v}) : Prop :=
  (∃ h : 3 ≤ nonDanglingValency mem.data s.1, mem.ident.vertex ⟨s.1, h⟩ = centre 10) ∨
    ∃ a : InteriorAddress mem.fullDim, s.1 = addressVertex mem.fullDim a ∧
      ¬ IsGSlot (mem.ident.row a.1)

open Classical in
/-- **The `G′`-part of the fibre over a target vertex `root`**: the source vertices over `root`
whose retraction is not on the tripod, with their indices. (It does not depend on `k`; the
specification only types `DegeneratePlacement.fibre`.) -/
noncomputable def gFibre (root : mem.target.V) : CFDiv mem.data.sourceGraph := fun raw ↦
  if OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw) then 0
  else DegeneratePlacement.fibre (tripodSpec M k hk) (legRequest M) mem root raw

theorem gFibre_effective (root : mem.target.V) : effective (gFibre k hk mem root) := by
  intro raw
  unfold gFibre
  split_ifs
  · exact le_rfl
  · unfold DegeneratePlacement.fibre
    split_ifs <;> positivity

variable (hClosed : mem.Closed)

/-- **The placed fibre over `root`** (Proposition 7.4): the member's own pullback
fibre, placed on the tripod specification. At `root = φ(c)` it is the claw witness before the
repair. -/
noncomputable def placed (hScale : memberScale mem = k) (root : mem.target.V) :
    CFDiv (tripodSpec M k hk).graph :=
  DegeneratePlacement.divisor (tripodSpec M k hk) (legRequest M) mem hClosed
    (tripod_fit k hk mem hScale) root

/-- **The placed `G′`-part** of the fibre over `root`. -/
noncomputable def placedG (hScale : memberScale mem = k) (root : mem.target.V) :
    CFDiv (tripodSpec M k hk).graph :=
  PendantDivisorTransport.push (G := mem.data.sourceGraph) (H := (tripodSpec M k hk).graph)
    (DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale))
    (gFibre k hk mem root)

/-- **The `G′`-part of the fibre over `root`, on `G_k`**: `ρ_*(G′-part of D_root)`, placed and
pushed along the expansion's contraction to `M.small.scale k`. The slid fibre over `root`
(§7.4) is this plus marks. -/
noncomputable def slidBase (hScale : memberScale mem = k) (root : mem.target.V) :
    CFDiv (M.small.scale k hk).graph :=
  ExpansionSeriesMoment.pushDivisor M.expansion (M.small.scale k hk) (by norm_num)
    (expansion_loopless M) (gPart M k hk (placedG k hk mem hClosed hScale root))

/-- **`F_k`, the claw divisor** (Proposition 7.4, with `s_k = 1`): the `G′`-part of
the fibre over `φ(c)`, placed and pushed along the expansion's contraction to `M.small.scale k`.
This is `ρ_*(G′-part of D_{φ(c)})`. -/
noncomputable def clawDivisor (hScale : memberScale mem = k) : CFDiv (M.small.scale k hk).graph :=
  slidBase k hk mem hClosed hScale (TripodFrame.centreTarget (Frame.of mem))

theorem slidBase_effective (hScale : memberScale mem = k) (root : mem.target.V) :
    effective (slidBase k hk mem hClosed hScale root) :=
  ExpansionSeriesMoment.effective_pushDivisor _
    (gPart_effective M k hk
      (PendantDivisorTransport.push_effective _ (gFibre_effective k hk mem root)))

theorem clawDivisor_effective (hScale : memberScale mem = k) :
    effective (clawDivisor k hk mem hClosed hScale) :=
  slidBase_effective k hk mem hClosed hScale _

/-- **On a G-slot interior vertex, only `G′` is placed.** Whatever is placed at an interior vertex
of a G-slot retracts to an interior vertex of that G-row (`sourcePoint_eq_interior_iff`), which is
not on the tripod. So there the `G′`-part and the whole fibre agree. -/
theorem placedG_interior (hScale : memberScale mem = k) (root : mem.target.V)
    (e : Fin (15 + 1 + 1 + 1)) (o : Fin ((tripodSpec M k hk).length (Fin.castAdd 3 e) - 1)) :
    placedG k hk mem hClosed hScale root
        ((tripodSpec M k hk).interiorVertex (Fin.castAdd 3 e) o) =
      placed k hk mem hClosed hScale root
        ((tripodSpec M k hk).interiorVertex (Fin.castAdd 3 e) o) := by
  classical
  show (∑ raw : mem.data.SourceVertex,
      if DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
          (tripod_fit k hk mem hScale) raw =
        (tripodSpec M k hk).interiorVertex (Fin.castAdd 3 e) o then
        gFibre k hk mem root raw else 0) =
    ∑ raw : mem.data.SourceVertex,
      if DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
          (tripod_fit k hk mem hScale) raw =
        (tripodSpec M k hk).interiorVertex (Fin.castAdd 3 e) o then
        DegeneratePlacement.fibre (tripodSpec M k hk) (legRequest M) mem root raw else 0
  refine Finset.sum_congr rfl fun raw _ ↦ ?_
  by_cases hHit : DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) raw =
      (tripodSpec M k hk).interiorVertex (Fin.castAdd 3 e) o
  · rw [ite_eq_left hHit, ite_eq_left hHit]
    obtain ⟨i, hClass, -⟩ := (DegeneratePlacement.sourcePoint_eq_interior_iff
      (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) (Fin.castAdd 3 e) o raw).mp hHit
    let a₀ : InteriorAddress mem.fullDim := ⟨mem.ident.row.symm (Fin.castAdd 3 e), i⟩
    have hv₀ := addressVertex_valency mem.fullDim a₀
    have hRep : representative mem.fullDim.connected (survivor_exists mem) raw =
        ⟨addressVertex mem.fullDim a₀, by omega⟩ :=
      (representative_eq_iff _ _ raw _).mpr hClass
    have hNot : ¬ OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw) := by
      rw [hRep]
      rintro (⟨h, -⟩ | ⟨a, ha, hG⟩)
      · simp only at h
        omega
      · have ha' := addressVertex_injective mem.fullDim ha
        subst ha'
        apply hG
        show (mem.ident.row (mem.ident.row.symm (Fin.castAdd 3 e))).val < 15 + 1 + 1 + 1
        rw [Equiv.apply_symm_apply]
        simp
    simp only [gFibre, ite_eq_right hNot]
  · rw [ite_eq_right hHit, ite_eq_right hHit]

/-- **The placement of `G′` lands on G-positions.** A surviving vertex off the tripod is a branch
vertex with a label of the marked core, or an interior vertex of a G-row; both are placed in the
image of `gEmbed`. -/
theorem survivingPoint_mem_range (hScale : memberScale mem = k)
    (s : {v : mem.data.SourceVertex // 0 < nonDanglingValency mem.data v})
    (hs : ¬ OnTripod mem s) :
    ∃ w, DegeneratePlacement.survivingPoint (tripodSpec M k hk) (legRequest M) mem
      hClosed (tripod_fit k hk mem hScale) s = gEmbed M k hk w := by
  rcases DegeneratePlacement.survivor_cases (tripodSpec M k hk) (legRequest M) mem s with
    ⟨b, hb⟩ | ⟨a, ha⟩
  · have hEq : s = ⟨b.1, lt_of_lt_of_le (by norm_num) b.2⟩ := Subtype.ext hb
    subst hEq
    rw [DegeneratePlacement.survivingPoint_branch]
    have hne : mem.ident.vertex b ≠ centre 10 := fun h ↦ hs (Or.inl ⟨b.2, h⟩)
    rcases (mem.ident.vertex b).eq_castSucc_or_eq_last with ⟨c, hc⟩ | hc
    · refine ⟨Sum.inl c, ?_⟩
      show Sum.inl (mem.ident.vertex b) = Sum.inl c.castSucc
      rw [hc]
    · exact absurd hc hne
  · have hEq : s = ⟨addressVertex mem.fullDim a, by rw [addressVertex_valency]; norm_num⟩ :=
      Subtype.ext ha
    subst hEq
    rw [DegeneratePlacement.survivingPoint_address]
    have hG : IsGSlot (mem.ident.row a.1) := by
      by_contra h
      exact hs (Or.inr ⟨a, rfl, h⟩)
    have he : mem.ident.row a.1 = Fin.castAdd 3 ⟨(mem.ident.row a.1).val, hG⟩ := Fin.ext rfl
    show ∃ w, (tripodSpec M k hk).pathVertex (mem.ident.row a.1) _ = _
    generalize DegeneratePlacement.position (tripodSpec M k hk) (legRequest M) mem
      hClosed (tripod_fit k hk mem hScale) (mem.ident.row a.1) (a.2.val + 1) = q
    revert q
    rw [he]
    exact pathVertex_castAdd_mem_range M k hk _

/-- **`G′` is placed on G-positions only.** -/
theorem placedG_support (hScale : memberScale mem = k) (root : mem.target.V)
    (v : (tripodSpec M k hk).Vertex) (hv : placedG k hk mem hClosed hScale root v ≠ 0) :
    ∃ w, v = gEmbed M k hk w := by
  classical
  have hv' : (∑ raw : mem.data.SourceVertex,
      if DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
          (tripod_fit k hk mem hScale) raw = v then gFibre k hk mem root raw else 0) ≠ 0 := hv
  obtain ⟨raw, -, hraw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv'
  by_cases hHit : DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) raw = v
  · rw [ite_eq_left hHit] at hraw
    have hNot : ¬ OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw) := by
      intro hOn
      apply hraw
      simp only [gFibre, ite_eq_left hOn]
    obtain ⟨w, hw⟩ := survivingPoint_mem_range k hk mem hClosed hScale _ hNot
    exact ⟨w, hHit.symm.trans hw⟩
  · rw [ite_eq_right hHit] at hraw
    exact absurd rfl hraw

/-- **`φ(c)` is internal.** The centre is a branch vertex of the member, and a branch vertex never
lies over a leaf of the target (`RowHairpinPosition.surviving_leaf_data`: a surviving source
vertex over a leaf has non-dangling valency two). -/
theorem centreTarget_not_leaf :
    ¬ IsLeafVertex mem.target (TripodFrame.centreTarget (Frame.of mem)) := by
  intro hLeaf
  have hb := (mem.ident.vertex.symm (centre 10)).2
  have h := (RowHairpinPosition.surviving_leaf_data mem.fullDim
    (vertex := (mem.ident.vertex.symm (centre 10)).1) (by omega) hLeaf).1
  omega

/-- **Links (1) and (4), §7.4: the receipts for the G-part.** At scale `k = memberScale mem`
with `2^a ∣ k`, every slot moment of `F_k` is divisible by `2^a`. The per-position receipt is
`DegeneratePlacement.divisor_interior_mem` at the internal root `φ(c)` (odd denominators from odd
multiplicity, `OddDenominator`, and the row receipts of `RowHairpinPosition`), read on the G-slots,
where the `G′`-part is the whole fibre (`placedG_interior`);
`ExpansionSeriesMoment.dvd_slotMoment_of_bigDivisor` carries it across the expansion (chains of
any length). -/
theorem clawDivisor_moment (hScale : memberScale mem = k) (hOdd : mem.HasOddMult) (a : ℕ)
    (hka : 2 ^ a ∣ k) (j : Fin M.smallSlots) :
    ((2 ^ a : ℕ) : ℤ) ∣
      InteriorFiring.slotMoment (M.small.scale k hk) (clawDivisor k hk mem hClosed hScale) j := by
  refine ExpansionSeriesMoment.dvd_slotMoment_of_bigDivisor M.small M.conditions k a hk hka
    (gPart M k hk (placedG k hk mem hClosed hScale (TripodFrame.centreTarget (Frame.of mem))))
    (fun e o ↦ ?_) j
  have h := DegeneratePlacement.divisor_interior_mem (tripodSpec M k hk) (legRequest M)
    mem hClosed (tripod_fit k hk mem hScale) (tripod_exact k hk mem hScale)
    ((hasOddMult_iff_odd_oddMult mem).mp hOdd) (centreTarget_not_leaf mem) (Fin.castAdd 3 e)
    (Fin.cast (congrArg (· - 1) (tripodSpec_length_castAdd M k hk e).symm) o)
  rw [hScale] at h
  have hG := placedG_interior k hk mem hClosed hScale (TripodFrame.centreTarget (Frame.of mem)) e
    (Fin.cast (congrArg (· - 1) (tripodSpec_length_castAdd M k hk e).symm) o)
  show ((placedG k hk mem hClosed hScale (TripodFrame.centreTarget (Frame.of mem))
      ((tripodSpec M k hk).interiorVertex (Fin.castAdd 3 e)
        (Fin.cast (congrArg (· - 1) (tripodSpec_length_castAdd M k hk e).symm) o)) : ℤ) : ℚ) *
    (((o.val + 1 : ℕ) : ℚ) / (k : ℚ)) ∈ SlotMoment.oddDenominatorSubring
  rw [hG]
  exact h

/-! ### The points of `G` over target vertices -/

/-- **The points of `G` over target vertices** (§7.4, the set `R`): the realisations on
`M.small.scale k` of the surviving source vertices off the tripod. -/
def gReach (hScale : memberScale mem = k) : Set (M.small.scale k hk).Vertex :=
  {w | ∃ s : {v : mem.data.SourceVertex // 0 < nonDanglingValency mem.data v},
    ¬ OnTripod mem s ∧ ∃ v : (bigSpecAt M k hk).Vertex,
      DegeneratePlacement.survivingPoint (tripodSpec M k hk) (legRequest M) mem
          hClosed (tripod_fit k hk mem hScale) s = gEmbed M k hk v ∧
        ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
          (expansion_loopless M) v = w}

/-- The small subdivision is connected: it is the contraction of a subdivision of the connected
marked core (`GraphContractionCertificate.graphConnected`, `ExpansionData.certificate_valid`). -/
theorem small_scale_connected : graph_connected (M.small.scale k hk).graph := by
  have hBig : (bigSpecAt M k hk).core.Connected := by
    show M.expansion.bigCore.Connected
    rw [M.bigCore_eq]
    exact subdivide_connected _ _ (subdivide_connected _ _ (subdivide_connected _ _ M.connected))
  exact (ExpansionData.certificate M.expansion (M.small.scale k hk) (by norm_num)
    (expansion_loopless M)).graphConnected
    (ExpansionData.certificate_valid (D := M.expansion) (small := M.small.scale k hk)
      (hN := by norm_num) (hL := expansion_loopless M) M.conditions)
    ((bigSpecAt M k hk).graph_connected_of_coreConnected hBig)

/-- **Every `D.fib` image is a point of `G` over a target vertex**: the branch vertex labelled by a
vertex of the marked core is off the tripod and is placed at that label. -/
theorem fib_mem_gReach (hScale : memberScale mem = k) (a : Fin (10 + 1 + 1 + 1)) :
    (M.small.scale k hk).coreVertex (M.expansion.fib a) ∈ gReach k hk mem hClosed hScale := by
  set b := mem.ident.vertex.symm a.castSucc with hbdef
  refine ⟨⟨b.1, lt_of_lt_of_le (by norm_num) b.2⟩, ?_, Sum.inl a, ?_, rfl⟩
  · rintro (⟨h, hc⟩ | ⟨a', ha', -⟩)
    · have hb : mem.ident.vertex ⟨b.1, h⟩ = mem.ident.vertex b := rfl
      rw [hb, hbdef, Equiv.apply_symm_apply] at hc
      exact (Fin.castSucc_lt_last a).ne hc
    · have h1 := addressVertex_valency mem.fullDim a'
      have h2 := b.2
      simp only at ha'
      rw [ha'] at h2
      omega
  · rw [DegeneratePlacement.survivingPoint_branch]
    show Sum.inl (mem.ident.vertex b) = Sum.inl a.castSucc
    rw [hbdef, Equiv.apply_symm_apply]

/-! ### The member half: the row over a loop `double` reaches inside its chain

The argument of `PencilTransportProducer.doubleRowInterior_of_loopDoubles`, on the G-rows of the
tripod core (`PencilTransportProducer` §4 is stated for members over any core). A target potential
whose rises are integral multiples of the member's realized lengths (`RiseCompatible`) is constant
along every contracted G-row, whose occurrences have length zero (`rowLen_eq_zero_of_contracted`),
so it takes one value on the labels of each fibre of `M.expansion.fib` (`labelPot_eq_of_fib_eq`,
through the last clause of `ExpansionData.Conditions`). The two ends of the row over a loop
`double` lie in one fibre. If no row vertex lay strictly inside the chain, one occurrence would
carry the whole length, and the potential rising only along its target edge would separate the
two ends (`loopRow_interior`). An interior address of a G-row is a point of `G` over a target
vertex, placed at its chain vertex (`address_mem_gReach`). -/

theorem tripodCore_tail_castAdd (e : Fin (15 + 1 + 1 + 1)) :
    (tripodCore M.core M.slots).tail (Fin.castAdd 3 e) = (M.expansion.bigCore.tail e).castSucc := by
  rw [M.bigCore_eq, tripodCore, attachTripod_tail_castAdd]

theorem tripodCore_head_castAdd (e : Fin (15 + 1 + 1 + 1)) :
    (tripodCore M.core M.slots).head (Fin.castAdd 3 e) = (M.expansion.bigCore.head e).castSucc := by
  rw [M.bigCore_eq, tripodCore, attachTripod_head_castAdd]

/-- `gEmbed` carries the path of a G-slot of the expanded core to the path of the same slot of
the tripod specification. -/
theorem gEmbed_pathVertex (e : Fin (15 + 1 + 1 + 1)) (q : (bigSpecAt M k hk).PathPosition e) :
    gEmbed M k hk ((bigSpecAt M k hk).pathVertex e q) =
      (tripodSpec M k hk).pathVertex (Fin.castAdd 3 e)
        ⟨q.val, by rw [tripodSpec_length_castAdd]; exact q.isLt⟩ := by
  by_cases h0 : q.val = 0
  · rw [PathHelpers.pathVertex_of_zero (bigSpecAt M k hk) e q h0,
      PathHelpers.pathVertex_of_zero (tripodSpec M k hk) _ _ h0]
    show Sum.inl ((M.expansion.bigCore.tail e).castSucc) =
      Sum.inl ((tripodCore M.core M.slots).tail (Fin.castAdd 3 e))
    rw [tripodCore_tail_castAdd]
  · by_cases hL : q.val = (bigSpecAt M k hk).length e
    · rw [PathHelpers.pathVertex_of_last (bigSpecAt M k hk) e q h0 hL,
        PathHelpers.pathVertex_of_last (tripodSpec M k hk) _ _ h0
          (hL.trans (tripodSpec_length_castAdd M k hk e).symm)]
      show Sum.inl ((M.expansion.bigCore.head e).castSucc) =
        Sum.inl ((tripodCore M.core M.slots).head (Fin.castAdd 3 e))
      rw [tripodCore_head_castAdd]
    · rw [PathHelpers.pathVertex_of_interior (bigSpecAt M k hk) e q h0 hL,
        PathHelpers.pathVertex_of_interior (tripodSpec M k hk) _ _ h0
          (fun h ↦ hL (h.trans (tripodSpec_length_castAdd M k hk e)))]
      rfl

variable {k} in
/-- The full integral prefix of a G-row is `k` times the degenerate length of its slot. -/
theorem rowStart_full (hScale : memberScale mem = k) (e : Fin (15 + 1 + 1 + 1)) :
    PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e)
        (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length =
      k * degenerateLength M.expansion M.small e := by
  unfold PencilTransportProducer.rowStart
  rw [RowRealizedPosition.member_integralPrefix_full (legRequest M) mem hClosed (Fin.castAdd 3 e),
    hScale]
  simp [legRequest]

/-- The row over the G-slot `e` runs between the branch vertices labelled by the two ends of
`e`, in one of the two orders. -/
theorem row_ends (e : Fin (15 + 1 + 1 + 1)) :
    ((mem.ident.vertex.symm (M.expansion.bigCore.tail e).castSucc).1 =
        RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)) 0 ∧
      (mem.ident.vertex.symm (M.expansion.bigCore.head e).castSucc).1 =
        RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e))
          (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length) ∨
    ((mem.ident.vertex.symm (M.expansion.bigCore.head e).castSucc).1 =
        RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)) 0 ∧
      (mem.ident.vertex.symm (M.expansion.bigCore.tail e).castSucc).1 =
        RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e))
          (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length) := by
  rcases DegeneratePlacement.endpoints (tripodCore_loopless' M) mem (Fin.castAdd 3 e) with
    ⟨hS, hF⟩ | ⟨hS, hF⟩
  · rw [tripodCore_tail_castAdd] at hS
    rw [tripodCore_head_castAdd] at hF
    refine Or.inl ⟨?_, ?_⟩
    · rw [← hS, Equiv.symm_apply_apply]
      rfl
    · rw [← hF, Equiv.symm_apply_apply]
      rfl
  · rw [tripodCore_head_castAdd] at hS
    rw [tripodCore_tail_castAdd] at hF
    refine Or.inr ⟨?_, ?_⟩
    · rw [← hS, Equiv.symm_apply_apply]
      rfl
    · rw [← hF, Equiv.symm_apply_apply]
      rfl

variable {k} in
/-- The occurrences of a contracted G-row have length zero. -/
theorem rowLen_eq_zero_of_contracted (hScale : memberScale mem = k) (e : Fin (15 + 1 + 1 + 1))
    (hc : M.expansion.kind e = SlotKind.contracted)
    (i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length) :
    PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i = 0 := by
  have h := PencilTransportProducer.rowStart_add_rowLen_le mem hClosed (Fin.castAdd 3 e) i
  rw [rowStart_full mem hClosed hScale e, DegenerateBigDivisor.degenerateLength_contracted _ _ hc,
    Nat.mul_zero] at h
  omega

/-- The pulled-back potential at the branch vertex carrying a label of the marked core. -/
noncomputable def labelPot (P : mem.target.V → ℤ) (v : Fin (10 + 1 + 1 + 1)) : ℤ :=
  PencilTransportProducer.sourcePotential mem P (mem.ident.vertex.symm v.castSucc).1

variable {k} in
/-- **A rise-compatible potential is constant along a contracted G-row.** -/
theorem labelPot_contracted (hScale : memberScale mem = k) (s : mem.target.edges → ℤ)
    (P : mem.target.V → ℤ) (hRise : PencilTransportProducer.RiseCompatible mem hClosed s P)
    (e : Fin (15 + 1 + 1 + 1)) (hc : M.expansion.kind e = SlotKind.contracted) :
    labelPot mem P (M.expansion.bigCore.tail e) = labelPot mem P (M.expansion.bigCore.head e) := by
  have hTel := PencilTransportProducer.sum_rowSlope_mul_rowLen mem hClosed s P hRise
    (Fin.castAdd 3 e)
  rw [Finset.sum_eq_zero fun i _ ↦ by
    rw [rowLen_eq_zero_of_contracted mem hClosed hScale e hc i]; simp] at hTel
  unfold labelPot
  rcases row_ends mem e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    linarith
  · rw [h1, h2]
    linarith

variable {k} in
/-- **A rise-compatible potential is constant on the labels of a fibre of `M.expansion.fib`**:
the fibre is connected through contracted slots (the last clause of `ExpansionData.Conditions`). -/
theorem labelPot_eq_of_fib_eq (hScale : memberScale mem = k) (s : mem.target.edges → ℤ)
    (P : mem.target.V → ℤ) (hRise : PencilTransportProducer.RiseCompatible mem hClosed s P)
    {v w : Fin (10 + 1 + 1 + 1)} (h : M.expansion.fib v = M.expansion.fib w) :
    labelPot mem P v = labelPot mem P w := by
  classical
  by_contra hne
  obtain ⟨e, hc, -, hcross⟩ := ExpansionData.fibre_of_conditions M.conditions (M.expansion.fib v)
    (Finset.univ.filter fun u ↦ labelPot mem P u = labelPot mem P v)
    ⟨v, by simp, rfl⟩ ⟨w, by simpa using fun h' ↦ hne h'.symm, h.symm⟩
  have hEq := labelPot_contracted mem hClosed hScale s P hRise e hc
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 (hEq.symm.trans h1)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 (hEq.trans h1)

/-- `offsetVal`, in terms of `rowStart`. -/
theorem offsetVal_eq' (E : Fin (15 + 1 + 1 + 1 + 3)) (j : ℕ) :
    DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed E j =
      if DegeneratePlacement.reverse mem E then
        (tripodSpec M k hk).length E - PencilTransportProducer.rowStart mem hClosed E j
      else PencilTransportProducer.rowStart mem hClosed E j := rfl

/-- **The row over a loop `double` has an interior address strictly inside the chain** (as
`PencilTransportProducer.doubleRowInterior_of_loopDoubles`). -/
theorem loopRow_interior (hScale : memberScale mem = k) (e : Fin (15 + 1 + 1 + 1))
    {j₁ j₂ : Fin M.smallSlots} (hk2 : M.expansion.kind e = SlotKind.double j₁ j₂)
    (hLoop : (M.small.scale k hk).core.tail j₁ = (M.small.scale k hk).core.head j₂) :
    ∃ a : InteriorAddress mem.fullDim, mem.ident.row a.1 = Fin.castAdd 3 e ∧
      0 < DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
        (Fin.castAdd 3 e) (a.2.val + 1) ∧
      DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
        (Fin.castAdd 3 e) (a.2.val + 1) <
          (M.small.scale k hk).length j₁ + (M.small.scale k hk).length j₂ := by
  classical
  have hne : M.expansion.kind e ≠ SlotKind.contracted := by
    rw [hk2]
    exact fun h ↦ by cases h
  have hLenB : (tripodSpec M k hk).length (Fin.castAdd 3 e) =
      (M.small.scale k hk).length j₁ + (M.small.scale k hk).length j₂ := by
    rw [tripodSpec_length_castAdd]
    show kindLength (M.small.scale k hk) (M.expansion.kind e) = _
    rw [hk2]
    rfl
  have hFull : PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e)
      (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length =
      (tripodSpec M k hk).length (Fin.castAdd 3 e) := by
    rw [rowStart_full mem hClosed hScale e, tripodSpec_length_castAdd]
    show k * degenerateLength M.expansion M.small e =
      kindLength (M.small.scale k hk) (M.expansion.kind e)
    rw [DegenerateBigDivisor.degenerateLength_of_ne _ _ hne,
      DegenerateBigDivisor.kindLength_scale_of_ne_contracted _ k hk hne]
  have hLenPos := (tripodSpec M k hk).length_pos (Fin.castAdd 3 e)
  by_contra hNo
  -- every interior prefix is `0` or the full length
  have hInt : ∀ j, 0 < j →
      j < (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length →
      PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) j = 0 ∨
        PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) j =
          (tripodSpec M k hk).length (Fin.castAdd 3 e) := by
    intro j hj0 hjl
    have hle : PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) j ≤
        (tripodSpec M k hk).length (Fin.castAdd 3 e) :=
      (PencilTransportProducer.rowStart_le_full mem hClosed (Fin.castAdd 3 e) j).trans hFull.le
    by_contra hj
    apply hNo
    refine ⟨⟨mem.ident.row.symm (Fin.castAdd 3 e), ⟨j - 1, by omega⟩⟩,
      Equiv.apply_symm_apply _ _, ?_, ?_⟩
    · show 0 < DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
        (Fin.castAdd 3 e) (j - 1 + 1)
      rw [show j - 1 + 1 = j by omega, offsetVal_eq']
      split_ifs <;> omega
    · show DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
        (Fin.castAdd 3 e) (j - 1 + 1) < _
      rw [show j - 1 + 1 = j by omega, offsetVal_eq', ← hLenB]
      split_ifs <;> omega
  -- the first prefix to leave `0` jumps to the full length
  have hEx : ∃ j, 1 ≤ PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) j :=
    ⟨(RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length,
      by omega⟩
  have hJ : 1 ≤ PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) (Nat.find hEx) :=
    Nat.find_spec hEx
  have hJpos : 0 < Nat.find hEx := by
    by_contra h
    rw [show Nat.find hEx = 0 by omega, PencilTransportProducer.rowStart_zero] at hJ
    omega
  have hJle : Nat.find hEx ≤
      (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length :=
    Nat.find_min' hEx (by omega)
  have hJm : PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) (Nat.find hEx - 1) =
      0 := by
    have := Nat.find_min hEx (show Nat.find hEx - 1 < Nat.find hEx by omega)
    omega
  have hJv : PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) (Nat.find hEx) =
      (tripodSpec M k hk).length (Fin.castAdd 3 e) := by
    rcases Nat.lt_or_ge (Nat.find hEx)
        (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length
      with h | h
    · rcases hInt _ hJpos h with h' | h' <;> omega
    · rw [show Nat.find hEx = (RowWalk.orderedRow mem.fullDim.pathEnds
        (mem.ident.row.symm (Fin.castAdd 3 e))).length by omega, hFull]
  set i0 : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
      (mem.ident.row.symm (Fin.castAdd 3 e))).length := ⟨Nat.find hEx - 1, by omega⟩ with hi0
  have hL0 : PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i0 =
      (tripodSpec M k hk).length (Fin.castAdd 3 e) := by
    have h := PencilTransportProducer.rowStart_succ mem hClosed (Fin.castAdd 3 e) i0
    have h' : PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) (Nat.find hEx - 1 + 1) =
        PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) (Nat.find hEx - 1) +
          PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i0 := h
    rw [show Nat.find hEx - 1 + 1 = Nat.find hEx by omega] at h'
    omega
  have hOthers : ∀ i, i ≠ i0 → PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i = 0 := by
    intro i hi
    have hSum := PencilTransportProducer.sum_rowLen mem hClosed (Fin.castAdd 3 e)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hL0, hFull] at hSum
    have hz : (∑ x ∈ Finset.univ.erase i0,
        (PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) x : ℤ)) = 0 := by linarith
    have hnn : ∀ x ∈ Finset.univ.erase i0,
        (0 : ℤ) ≤ PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) x :=
      fun _ _ ↦ by positivity
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    exact_mod_cast this
  -- the separating potential
  set t := ((RowWalk.orderedRow mem.fullDim.pathEnds
    (mem.ident.row.symm (Fin.castAdd 3 e)))[i0]).1.1 with ht
  let s : mem.target.edges → ℤ := fun t' ↦ if t' = t then 1 else 0
  let P : mem.target.V → ℤ := TreeMetricPotential.integrate
    (fun t' ↦ s t' * ((RowRealizedPosition.memberRealization mem hClosed).targetLength t' : ℤ))
  have hRise : PencilTransportProducer.RiseCompatible mem hClosed s P := fun t' ↦
    TreeMetricPotential.integrate_rise mem.fullDim.targetConnected mem.fullDim.targetGenus _ t'
  have hFib : M.expansion.fib (M.expansion.bigCore.tail e) =
      M.expansion.fib (M.expansion.bigCore.head e) := by
    obtain ⟨h1, -, h3⟩ := (ExpansionData.compatible_of_conditions M.conditions e).2.2 j₁ j₂ hk2
    rw [h1, h3]
    exact hLoop
  have hCP := labelPot_eq_of_fib_eq mem hClosed hScale s P hRise hFib
  have hPsi : PencilTransportProducer.sourcePotential mem P
        (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e))
          (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length) =
      PencilTransportProducer.sourcePotential mem P
        (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)) 0) := by
    unfold labelPot at hCP
    rcases row_ends mem e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hCP
      exact hCP.symm
    · rw [h1, h2] at hCP
      exact hCP
  have hTel := PencilTransportProducer.sum_rowSlope_mul_rowLen mem hClosed s P hRise
    (Fin.castAdd 3 e)
  rw [hPsi, sub_self, Finset.sum_eq_single i0 (fun i _ hi ↦ by rw [hOthers i hi]; simp)
    (by simp), hL0] at hTel
  have hSlope : PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i0 ≠ 0 := by
    have hidx := GluingDatum.sourceEdgeIndex_pos mem.data
      (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e)))[i0]
    have hs : s t = 1 := ite_eq_left rfl
    unfold PencilTransportProducer.rowSlope PencilTransportProducer.edgeSlope
    rw [← ht, hs]
    split_ifs <;> omega
  rcases mul_eq_zero.mp hTel with h | h
  · exact hSlope h
  · exact absurd h (by exact_mod_cast hLenPos.ne')

/-- **An interior address of a G-row is a point of `G` over a target vertex**, realised on
`M.small.scale k` at the chain vertex of its own oriented offset. -/
theorem address_mem_gReach (hScale : memberScale mem = k) (e : Fin (15 + 1 + 1 + 1))
    (a : InteriorAddress mem.fullDim) (ha : mem.ident.row a.1 = Fin.castAdd 3 e) :
    kindVertex (M.small.scale k hk) (M.expansion.fib (M.expansion.bigCore.tail e))
        (M.expansion.kind e)
        (DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
          (Fin.castAdd 3 e) (a.2.val + 1)) ∈ gReach k hk mem hClosed hScale := by
  have hle := DegeneratePlacement.offsetVal_le (tripodSpec M k hk) (legRequest M) mem hClosed
    (tripod_fit k hk mem hScale) (Fin.castAdd 3 e) (a.2.val + 1)
  rw [tripodSpec_length_castAdd] at hle
  let q : (bigSpecAt M k hk).PathPosition e :=
    ⟨DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
      (Fin.castAdd 3 e) (a.2.val + 1), by omega⟩
  refine ⟨⟨addressVertex mem.fullDim a, by rw [addressVertex_valency]; norm_num⟩, ?_,
    (bigSpecAt M k hk).pathVertex e q, ?_, ?_⟩
  · rintro (⟨h, -⟩ | ⟨a', ha', hG⟩)
    · have hv := addressVertex_valency mem.fullDim a
      simp only at h
      omega
    · have hEq := addressVertex_injective mem.fullDim ha'
      subst hEq
      apply hG
      rw [ha]
      exact e.isLt
  · rw [DegeneratePlacement.survivingPoint_address, gEmbed_pathVertex]
    have key : ∀ E : Fin (15 + 1 + 1 + 1 + 3), E = Fin.castAdd 3 e →
        (tripodSpec M k hk).pathVertex E
            (DegeneratePlacement.position (tripodSpec M k hk) (legRequest M) mem hClosed
              (tripod_fit k hk mem hScale) E (a.2.val + 1)) =
          (tripodSpec M k hk).pathVertex (Fin.castAdd 3 e)
            ⟨q.val, by rw [tripodSpec_length_castAdd]; exact q.isLt⟩ := by
      intro E hE
      subst hE
      rfl
    exact key _ ha
  · exact ExpansionData.vertexMap_pathVertex (D := M.expansion) (small := M.small.scale k hk)
      (hN := by norm_num) (hL := expansion_loopless M) M.conditions e q

/-- **The member half: loops are reached inside** (§7.4). For
every `double` slot of the expansion that displays a loop, some point of `G` over a target vertex
lies strictly inside its chain on `M.small.scale k`: the interior address of `loopRow_interior`,
realised by `address_mem_gReach`. -/
theorem loopDouble_reach (hScale : memberScale mem = k) :
    ∀ (e : Fin (15 + 1 + 1 + 1)) (j₁ j₂ : Fin M.smallSlots),
      M.expansion.kind e = SlotKind.double j₁ j₂ →
      (M.small.scale k hk).core.tail j₁ = (M.small.scale k hk).core.head j₂ →
      ∃ t, 0 < t ∧ t < (M.small.scale k hk).length j₁ + (M.small.scale k hk).length j₂ ∧
        kindVertex (M.small.scale k hk) ((M.small.scale k hk).core.tail j₁)
          (SlotKind.double j₁ j₂) t ∈ gReach k hk mem hClosed hScale := by
  intro e j₁ j₂ hk2 hLoop
  obtain ⟨a, ha, h0, hL⟩ := loopRow_interior k hk mem hClosed hScale e hk2 hLoop
  refine ⟨_, h0, hL, ?_⟩
  have h := address_mem_gReach k hk mem hClosed hScale e a ha
  rw [hk2] at h
  exact h

/-- **Reach and markers** (§7.4, "a rank-determining set"): the
points of `G` over target vertices are rank-determining on `M.small.scale k`, from the graph half
`rankDetermining_of_fib_loopDoubles`, `fib_mem_gReach` and the member half `loopDouble_reach`. -/
theorem rankDetermining_gReach (hScale : memberScale mem = k)
    (Dv : CFDiv (M.small.scale k hk).graph)
    (hReach : ∀ w ∈ gReach k hk mem hClosed hScale,
      winnable (M.small.scale k hk).graph (Dv - one_chip w)) :
    rank (M.small.scale k hk).graph Dv ≥ 1 :=
  rankDetermining_of_fib_loopDoubles M.expansion (M.small.scale k hk) M.conditions
    (small_scale_connected (M := M) k hk) (gReach k hk mem hClosed hScale)
    (fib_mem_gReach k hk mem hClosed hScale) (loopDouble_reach k hk mem hClosed hScale) Dv hReach

/-- **Every point of `G` over a target vertex is in the `G′`-part of its own fibre.** A surviving
source vertex `s` off the tripod lies over `x = s.1.1.1` with index at least one, and is placed at
its own realisation (`sourcePoint_survivor`), so `slidBase x` is positive there. -/
theorem exists_slidBase_pos (hScale : memberScale mem = k) {w : (M.small.scale k hk).Vertex}
    (hw : w ∈ gReach k hk mem hClosed hScale) :
    ∃ x, 0 < slidBase k hk mem hClosed hScale x w := by
  classical
  obtain ⟨s, hs, v, hv, rfl⟩ := hw
  refine ⟨s.1.1.1, ?_⟩
  -- the term of the source vertex `s` itself
  have hFib : 1 ≤ gFibre k hk mem s.1.1.1 s.1 := by
    have hRep : representative mem.fullDim.connected (survivor_exists mem) s.1 = s :=
      CanonicalSurvivor.representative_fixes _ _ s
    show (1 : ℤ) ≤ if OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) s.1)
      then 0 else DegeneratePlacement.fibre (tripodSpec M k hk) (legRequest M) mem s.1.1.1 s.1
    rw [hRep, ite_eq_right hs]
    show (1 : ℤ) ≤ if s.1.1.1 = s.1.1.1 then
      ((mem.data.vertexPartition s.1.1.1).blockCard s.1.1.2 : ℤ) else 0
    rw [ite_eq_left rfl]
    exact_mod_cast (mem.data.vertexPartition s.1.1.1).blockCard_pos s.1.1.2
  have hPlace : DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) s.1 = gEmbed M k hk v :=
    (DegeneratePlacement.sourcePoint_survivor (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) s).trans hv
  -- positivity of the placed `G′`-part at `gEmbed v`
  have hG : 1 ≤ placedG k hk mem hClosed hScale s.1.1.1 (gEmbed M k hk v) := by
    show (1 : ℤ) ≤ ∑ raw : mem.data.SourceVertex,
      if DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
          (tripod_fit k hk mem hScale) raw = gEmbed M k hk v then
        gFibre k hk mem s.1.1.1 raw else 0
    refine le_trans ?_ (Finset.single_le_sum (f := fun raw ↦
      if DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
          (tripod_fit k hk mem hScale) raw = gEmbed M k hk v then
        gFibre k hk mem s.1.1.1 raw else 0) (fun raw _ ↦ ?_) (Finset.mem_univ s.1))
    · simp only [ite_eq_left hPlace]
      exact hFib
    · split_ifs
      · exact gFibre_effective k hk mem _ raw
      · exact le_rfl
  -- positivity of the pushforward at `vertexMap v`
  show 0 < ∑ v' : (bigSpecAt M k hk).Vertex,
    if ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M) v' =
      ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M) v then
      gPart M k hk (placedG k hk mem hClosed hScale s.1.1.1) v' else 0
  refine lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hG) (le_trans ?_ (Finset.single_le_sum
    (f := fun v' ↦ if ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M) v' =
      ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M) v then
      gPart M k hk (placedG k hk mem hClosed hScale s.1.1.1) v' else 0)
    (fun v' _ ↦ ?_) (Finset.mem_univ v)))
  · rw [ite_eq_left rfl]
    exact le_rfl
  · split_ifs
    · exact gPart_effective M k hk
        (PendantDivisorTransport.push_effective _ (gFibre_effective k hk mem _)) v'
    · exact le_rfl

/-! ### The slid fibres, in four pieces

The slid fibre over `x` (§7.4) is `slidFibre x = slidBase x + Σ_j markCoeff x j · markChip j`:
the `G′`-part of the fibre over `x`, retracted to `G` and pushed to `M.small.scale k`, plus
`s_j·1[x ∈ H_j]` chips at the mark `j`. Here `s_j` is the index of the leg edge at the mark `j`
and `H_j` the branch of the target at `φ(j)` containing its image (`markCoeff`, read through
`TreeMetricPotential.cutValue`: the target edge under the leg edge separates `x` from `φ(j)`).
This is the retracted fibre of the repaired morphism of Lemma 7.1, which grafts `s_j` copies
of `H̄_j` at the mark `j`: the copies over `x` retract to `s_j·1[x ∈ H_j]` chips at the mark
(Lemma 7.3). The repaired morphism is not built: its fibre family is written down
directly, and its linear system is proved through the pulled-back tree potential, as in the
unmarked endgame (§8.2).

* `slidFibre_effective`, `slidBase_le_slidFibre` — the correction is effective.
* `slidFibre_transport` — any two slid fibres are linearly equivalent (below, after the small
  side, the big side and the leg edges); `slidFibre_adjacent` and `slidFibre_linear_equiv` are
  its cases.
* `slidFibre_centre` — at `φ(c)` every mark coefficient is one (`markCoeff_centre`, from the
  claw classification of `ClawShape`). -/

/-- The chip at the mark `j` on `M.small.scale k`. -/
noncomputable def markChip (j : Fin 3) : CFDiv (M.small.scale k hk).graph :=
  one_chip ((M.small.scale k hk).coreVertex (M.smallMark j))

omit hClosed in
theorem embed_marksDiv : M.small.embed k hk (marksDiv M) = ∑ j, markChip k hk j := by
  unfold marksDiv
  rw [embed_coreChips]
  rfl

open Classical in
/-- **The mark coefficient `s_j·1[x ∈ H_j]`**: the total index of the source edges of the leg row
`j` at the mark `j` whose target edge separates `x` from `φ(j)`. There is exactly one such leg
edge at the mark (the mark is a branch vertex, met once by its leg), of index `s_j`, over the
target edge `h_j`, and `x ∈ H_j` iff `h_j` separates `x` from `φ(j)`. -/
noncomputable def markCoeff (x : mem.target.V) (j : Fin 3) : ℕ :=
  ∑ e : mem.data.SourceEdge,
    if RowWalk.OnRow mem.data (mem.ident.row.symm (legSlot 15 j)) e ∧
        Incident mem.data e (mem.ident.vertex.symm (tripodMark 10 j)).1 ∧
        TreeMetricPotential.cutValue e.1.1 x ≠
          TreeMetricPotential.cutValue e.1.1 (mem.ident.vertex.symm (tripodMark 10 j)).1.1.1
    then mem.data.sourceEdgeIndex e else 0

/-- **The slid fibre over `x`** (§7.4): the retracted `G′`-part plus the mark correction. -/
noncomputable def slidFibre (hScale : memberScale mem = k) (x : mem.target.V) :
    CFDiv (M.small.scale k hk).graph :=
  slidBase k hk mem hClosed hScale x + ∑ j, ((markCoeff mem x j : ℕ) : ℤ) • markChip k hk j

theorem markCorrection_nonneg (x : mem.target.V) (w : (M.small.scale k hk).Vertex) :
    0 ≤ (∑ j, ((markCoeff mem x j : ℕ) : ℤ) • markChip k hk j) w := by
  rw [Finset.sum_apply]
  exact Finset.sum_nonneg fun j _ ↦ by
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (Int.natCast_nonneg _) (eff_one_chip (G := (M.small.scale k hk).graph)
      ((M.small.scale k hk).coreVertex (M.smallMark j)) w)

theorem slidFibre_effective (hScale : memberScale mem = k) (x : mem.target.V) :
    effective (slidFibre k hk mem hClosed hScale x) := fun w ↦
  add_nonneg (slidBase_effective k hk mem hClosed hScale x w)
    (markCorrection_nonneg k hk mem x w)

theorem slidBase_le_slidFibre (hScale : memberScale mem = k) (x : mem.target.V)
    (w : (M.small.scale k hk).Vertex) :
    slidBase k hk mem hClosed hScale x w ≤ slidFibre k hk mem hClosed hScale x w :=
  le_add_of_nonneg_right (markCorrection_nonneg k hk mem x w)

/-! ### The transport of the slid fibres: the small side

The pushed `G′`-part of the fibre is the push of the whole fibre along `gRealize`, the
realisation of `G′` on `M.small.scale k` (`none` on `Y′`). So the difference of two slid bases is
the pushed pulled-back incidence (`PencilTransportProducer.sum_fibre_sub`), a sum over the rows
(`PencilTransportProducer.sum_edges_eq_sum_rows`; dangling edges are collapsed). -/

open Classical in
/-- **The realisation of `G′`** on `M.small.scale k`: a source vertex off the tripod goes to the
image under the contraction of its placement in the expanded core; one on the tripod to `none`. -/
noncomputable def gRealize (hScale : memberScale mem = k) (raw : mem.data.SourceVertex) :
    Option (M.small.scale k hk).Vertex :=
  if OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw) then none
  else if h : ∃ v, DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) raw = gEmbed M k hk v then
    some (ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
      (expansion_loopless M) h.choose)
  else none

theorem gRealize_of_onTripod (hScale : memberScale mem = k) {raw : mem.data.SourceVertex}
    (hOn : OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw)) :
    gRealize k hk mem hClosed hScale raw = none := by
  unfold gRealize
  rw [ite_eq_left hOn]

theorem gRealize_of_eq (hScale : memberScale mem = k) {raw : mem.data.SourceVertex}
    (hNot : ¬ OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw))
    {v : (bigSpecAt M k hk).Vertex}
    (hv : DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) raw = gEmbed M k hk v) :
    gRealize k hk mem hClosed hScale raw =
      some (ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M) v) := by
  have h : ∃ v, DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) raw = gEmbed M k hk v := ⟨v, hv⟩
  unfold gRealize
  rw [ite_eq_right hNot, dite_eq_left h]
  congr 2
  exact gEmbed_injective M k hk (h.choose_spec.symm.trans hv)

/-- **The slid base is the push of the fibre along `gRealize`.** -/
theorem slidBase_apply (hScale : memberScale mem = k) (x : mem.target.V)
    (b : (M.small.scale k hk).Vertex) :
    slidBase k hk mem hClosed hScale x b =
      ∑ raw, if gRealize k hk mem hClosed hScale raw = some b then
        DegeneratePlacement.fibre (tripodSpec M k hk) (legRequest M) mem x raw else 0 := by
  classical
  show (∑ v : (bigSpecAt M k hk).Vertex,
      if ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
          (expansion_loopless M) v = b then
        (∑ raw, if DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
            (tripod_fit k hk mem hScale) raw = gEmbed M k hk v then gFibre k hk mem x raw
          else 0)
      else 0) = _
  have hIn : ∀ v : (bigSpecAt M k hk).Vertex,
      (if ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
          (expansion_loopless M) v = b then
        (∑ raw, if DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
            (tripod_fit k hk mem hScale) raw = gEmbed M k hk v then gFibre k hk mem x raw
          else 0)
      else 0) =
        ∑ raw, if ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
            (expansion_loopless M) v = b then
          (if DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
            (tripod_fit k hk mem hScale) raw = gEmbed M k hk v then gFibre k hk mem x raw
          else 0) else 0 := fun v ↦ by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun v _ ↦ hIn v, Finset.sum_comm]
  refine Finset.sum_congr rfl fun raw _ ↦ ?_
  by_cases hOn : OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw)
  · have hz : gFibre k hk mem x raw = 0 := by
      unfold gFibre
      rw [ite_eq_left hOn]
    rw [gRealize_of_onTripod k hk mem hClosed hScale hOn, hz]
    simp
  · obtain ⟨w, hw⟩ := survivingPoint_mem_range k hk mem hClosed hScale _ hOn
    have hsp : DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
        (tripod_fit k hk mem hScale) raw = gEmbed M k hk w := hw
    have hg : gFibre k hk mem x raw =
        DegeneratePlacement.fibre (tripodSpec M k hk) (legRequest M) mem x raw := by
      unfold gFibre
      rw [ite_eq_right hOn]
    rw [gRealize_of_eq k hk mem hClosed hScale hOn hsp, hg, hsp]
    have hI : ∀ v, (gEmbed M k hk w = gEmbed M k hk v) ↔ (w = v) :=
      fun v ↦ (gEmbed_injective M k hk).eq_iff
    simp only [hI, Option.some.injEq]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      simp [Ne.symm hv]
    · simp

/-- `gRealize` factors through the retraction. -/
theorem gRealize_retract (hScale : memberScale mem = k) {first second : mem.data.SourceVertex}
    (hEq : PendantRetraction.retractVertex first = PendantRetraction.retractVertex second) :
    gRealize k hk mem hClosed hScale first = gRealize k hk mem hClosed hScale second := by
  have hRep : representative mem.fullDim.connected (survivor_exists mem) first =
      representative mem.fullDim.connected (survivor_exists mem) second :=
    (representative_eq_iff mem.fullDim.connected (survivor_exists mem) first _).mpr
      (hEq.trans (CanonicalSurvivor.representative_class mem.fullDim.connected
        (survivor_exists mem) second))
  have hsp := DegeneratePlacement.sourcePoint_of_retract (tripodSpec M k hk) (legRequest M) mem
    hClosed (tripod_fit k hk mem hScale) hEq
  unfold gRealize
  rw [hRep, hsp]

/-- A dangling edge is collapsed by `gRealize`. -/
theorem gRealize_dangling (hScale : memberScale mem = k) {edge : mem.data.SourceEdge}
    (hD : IsDangling mem.data edge) :
    gRealize k hk mem hClosed hScale (mem.data.sourceEnds edge).1 =
      gRealize k hk mem hClosed hScale (mem.data.sourceEnds edge).2 :=
  gRealize_retract k hk mem hClosed hScale
    (Quotient.sound (Relation.ReflTransGen.single ⟨edge, hD, Or.inl rfl⟩))

open Classical in
/-- **The small side, row by row.** The difference of the slid bases over `anchor` and `root` is
the sum, over the rows of the tripod core, of the row slopes times the difference of the
indicator of `b` under `gRealize` at the two ends of each occurrence. -/
theorem slidBase_sub_eq_rows (hScale : memberScale mem = k) (root anchor : mem.target.V)
    (b : (M.small.scale k hk).Vertex) :
    slidBase k hk mem hClosed hScale anchor b - slidBase k hk mem hClosed hScale root b =
      ∑ E : Fin (15 + 1 + 1 + 1 + 3), ∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm E)).length,
        PencilTransportProducer.rowSlope mem (PencilTransportProducer.chipSlope mem root anchor) E i *
          ((if gRealize k hk mem hClosed hScale
              (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm E) i) = some b then 1 else 0) -
            (if gRealize k hk mem hClosed hScale
              (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm E) (i.val + 1)) = some b
              then 1 else 0)) := by
  rw [slidBase_apply, slidBase_apply, ← Finset.sum_sub_distrib]
  have hStep := PencilTransportProducer.sum_fibre_sub mem root anchor
    (gRealize k hk mem hClosed hScale) (some b)
  rw [show (∑ raw, ((if gRealize k hk mem hClosed hScale raw = some b then
        DegeneratePlacement.fibre (tripodSpec M k hk) (legRequest M) mem anchor raw else 0) -
      (if gRealize k hk mem hClosed hScale raw = some b then
        DegeneratePlacement.fibre (tripodSpec M k hk) (legRequest M) mem root raw else 0))) =
      ∑ raw, if gRealize k hk mem hClosed hScale raw = some b then
        ((if raw.1.1 = anchor then ((mem.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ)
            else 0) -
          (if raw.1.1 = root then ((mem.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ)
            else 0)) else 0 from
    Finset.sum_congr rfl fun raw _ ↦ by
      unfold DegeneratePlacement.fibre
      split_ifs <;> simp]
  rw [hStep]
  rw [PencilTransportProducer.sum_edges_eq_sum_rows mem _ (fun edge hD ↦ by
    rw [gRealize_dangling k hk mem hClosed hScale hD]
    ring)]
  refine Finset.sum_congr rfl fun E _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← PencilTransportProducer.rowSlope_mul_sub mem _ E i (fun v ↦
    if gRealize k hk mem hClosed hScale v = some b then 1 else 0)]

/-! ### The realisation of the row vertices -/

theorem rep_branch (β : StableGraphIncidence.BranchVertex mem.data) :
    representative mem.fullDim.connected (survivor_exists mem) β.1 =
      ⟨β.1, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) β.2⟩ :=
  CanonicalSurvivor.representative_fixes _ _ ⟨β.1, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) β.2⟩

/-- A branch vertex is on the tripod exactly when it is the centre. -/
theorem branch_onTripod_iff (β : StableGraphIncidence.BranchVertex mem.data) :
    OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) β.1) ↔
      mem.ident.vertex β = centre 10 := by
  rw [rep_branch]
  constructor
  · rintro (⟨h, hc⟩ | ⟨a, ha, -⟩)
    · exact hc
    · exfalso
      have h1 := addressVertex_valency mem.fullDim a
      have h2 := β.2
      simp only at ha
      rw [ha] at h2
      omega
  · intro h
    exact Or.inl ⟨β.2, h⟩

theorem sourcePoint_branch' (hScale : memberScale mem = k) (β : StableGraphIncidence.BranchVertex mem.data) :
    DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
        (tripod_fit k hk mem hScale) β.1 =
      (tripodSpec M k hk).coreVertex (mem.ident.vertex β) :=
  (DegeneratePlacement.sourcePoint_survivor (tripodSpec M k hk) (legRequest M) mem hClosed
    (tripod_fit k hk mem hScale) ⟨β.1, by have := β.2; omega⟩).trans
    (DegeneratePlacement.survivingPoint_branch (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) β)

/-- A branch vertex labelled by a vertex `ℓ` of the marked core is realised at `fib ℓ`. -/
theorem gRealize_branch (hScale : memberScale mem = k) (β : StableGraphIncidence.BranchVertex mem.data)
    (ℓ : Fin (10 + 1 + 1 + 1)) (hβ : mem.ident.vertex β = ℓ.castSucc) :
    gRealize k hk mem hClosed hScale β.1 =
      some ((M.small.scale k hk).coreVertex (M.expansion.fib ℓ)) := by
  have hNot : ¬ OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) β.1) := by
    rw [branch_onTripod_iff, hβ]
    exact (Fin.castSucc_lt_last ℓ).ne
  have hsp : DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) β.1 = gEmbed M k hk (Sum.inl ℓ) := by
    rw [sourcePoint_branch' k hk mem hClosed hScale β, hβ]
    rfl
  rw [gRealize_of_eq k hk mem hClosed hScale hNot hsp]
  rfl

/-- The centre is not realised. -/
theorem gRealize_centre (hScale : memberScale mem = k) (β : StableGraphIncidence.BranchVertex mem.data)
    (hβ : mem.ident.vertex β = centre 10) : gRealize k hk mem hClosed hScale β.1 = none :=
  gRealize_of_onTripod k hk mem hClosed hScale ((branch_onTripod_iff mem β).mpr hβ)

theorem address_onTripod_iff (a : InteriorAddress mem.fullDim) :
    OnTripod mem (representative mem.fullDim.connected (survivor_exists mem)
        (addressVertex mem.fullDim a)) ↔ ¬ IsGSlot (mem.ident.row a.1) := by
  rw [CanonicalSurvivor.representative_fixes _ _
    ⟨addressVertex mem.fullDim a, by rw [addressVertex_valency]; norm_num⟩]
  constructor
  · rintro (⟨h, -⟩ | ⟨a', ha', hG⟩)
    · have hv := addressVertex_valency mem.fullDim a
      simp only at h
      omega
    · have hEq := addressVertex_injective mem.fullDim ha'
      subst hEq
      exact hG
  · intro hG
    exact Or.inr ⟨a, rfl, hG⟩

/-- An interior address of a G-row is realised at the chain vertex of its oriented offset. -/
theorem gRealize_address_gRow (hScale : memberScale mem = k) (e : Fin (15 + 1 + 1 + 1))
    (a : InteriorAddress mem.fullDim) (ha : mem.ident.row a.1 = Fin.castAdd 3 e) :
    gRealize k hk mem hClosed hScale (addressVertex mem.fullDim a) =
      some (kindVertex (M.small.scale k hk) (M.expansion.fib (M.expansion.bigCore.tail e))
        (M.expansion.kind e)
        (DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
          (Fin.castAdd 3 e) (a.2.val + 1))) := by
  have hle := DegeneratePlacement.offsetVal_le (tripodSpec M k hk) (legRequest M) mem hClosed
    (tripod_fit k hk mem hScale) (Fin.castAdd 3 e) (a.2.val + 1)
  rw [tripodSpec_length_castAdd] at hle
  let q : (bigSpecAt M k hk).PathPosition e :=
    ⟨DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
      (Fin.castAdd 3 e) (a.2.val + 1), by omega⟩
  have hNot : ¬ OnTripod mem (representative mem.fullDim.connected (survivor_exists mem)
      (addressVertex mem.fullDim a)) := by
    rw [address_onTripod_iff, ha, not_not]
    exact e.isLt
  have hsp : DegeneratePlacement.sourcePoint (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale) (addressVertex mem.fullDim a) =
        gEmbed M k hk ((bigSpecAt M k hk).pathVertex e q) := by
    rw [DegeneratePlacement.sourcePoint_survivor (tripodSpec M k hk) (legRequest M) mem hClosed
      (tripod_fit k hk mem hScale)
      ⟨addressVertex mem.fullDim a, by rw [addressVertex_valency]; norm_num⟩,
      DegeneratePlacement.survivingPoint_address, gEmbed_pathVertex]
    have key : ∀ E : Fin (15 + 1 + 1 + 1 + 3), E = Fin.castAdd 3 e →
        (tripodSpec M k hk).pathVertex E
            (DegeneratePlacement.position (tripodSpec M k hk) (legRequest M) mem hClosed
              (tripod_fit k hk mem hScale) E (a.2.val + 1)) =
          (tripodSpec M k hk).pathVertex (Fin.castAdd 3 e)
            ⟨q.val, by rw [tripodSpec_length_castAdd]; exact q.isLt⟩ := by
      intro E hE
      subst hE
      rfl
    exact key _ ha
  rw [gRealize_of_eq k hk mem hClosed hScale hNot hsp]
  exact congrArg some (ExpansionData.vertexMap_pathVertex (D := M.expansion)
    (small := M.small.scale k hk) (hN := by norm_num) (hL := expansion_loopless M) M.conditions e q)

variable {k} in
/-- The full prefix of a non-contracted G-row is the length of its slot. -/
theorem rowStart_full_of_ne (hScale : memberScale mem = k) (e : Fin (15 + 1 + 1 + 1))
    (hne : M.expansion.kind e ≠ SlotKind.contracted) :
    PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e)
        (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length =
      (bigSpecAt M k hk).length e := by
  rw [rowStart_full mem hClosed hScale e]
  show k * degenerateLength M.expansion M.small e =
    kindLength (M.small.scale k hk) (M.expansion.kind e)
  rw [DegenerateBigDivisor.degenerateLength_of_ne _ _ hne,
    DegenerateBigDivisor.kindLength_scale_of_ne_contracted _ k hk hne]

/-- **Every vertex of a G-row is realised at `kindVertex` of its oriented offset** (as
`PencilTransportProducer.realization_rowVertex`). -/
theorem gRealize_gRow (hScale : memberScale mem = k) (e : Fin (15 + 1 + 1 + 1)) (j : ℕ)
    (hj : j ≤ (RowWalk.orderedRow mem.fullDim.pathEnds
      (mem.ident.row.symm (Fin.castAdd 3 e))).length) :
    gRealize k hk mem hClosed hScale
        (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)) j) =
      some (kindVertex (M.small.scale k hk) (M.expansion.fib (M.expansion.bigCore.tail e))
        (M.expansion.kind e)
        (DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
          (Fin.castAdd 3 e) j)) := by
  have hEnds := DegeneratePlacement.reverse_endpoints (tripodCore_loopless' M) mem
    (Fin.castAdd 3 e)
  rw [tripodCore_tail_castAdd, tripodCore_head_castAdd] at hEnds
  have hLen := tripodSpec_length_castAdd M k hk e
  have hz := PencilTransportProducer.kindVertex_zero_eq M.expansion M.small (by norm_num)
    (expansion_loopless M) k hk M.conditions e
  have hl := PencilTransportProducer.kindVertex_length_eq M.expansion M.small (by norm_num)
    (expansion_loopless M) k hk M.conditions e
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have h := gRealize_branch k hk mem hClosed hScale
      (RowSlotOrientation.startBranch mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)))
      (if DegeneratePlacement.reverse mem (Fin.castAdd 3 e) then M.expansion.bigCore.head e
        else M.expansion.bigCore.tail e)
      (by rw [hEnds.1]; split_ifs <;> rfl)
    refine h.trans ?_
    rw [offsetVal_eq', PencilTransportProducer.rowStart_zero, Nat.sub_zero, hLen]
    split_ifs
    · rw [hl]
    · rw [hz]
  by_cases hjl : j = (RowWalk.orderedRow mem.fullDim.pathEnds
      (mem.ident.row.symm (Fin.castAdd 3 e))).length
  · subst hjl
    have h := gRealize_branch k hk mem hClosed hScale
      (RowSlotOrientation.finishBranch mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)))
      (if DegeneratePlacement.reverse mem (Fin.castAdd 3 e) then M.expansion.bigCore.tail e
        else M.expansion.bigCore.head e)
      (by rw [hEnds.2]; split_ifs <;> rfl)
    refine h.trans ?_
    rw [offsetVal_eq', hLen]
    by_cases hc : M.expansion.kind e = SlotKind.contracted
    · have hFib := (ExpansionData.compatible_of_conditions M.conditions e).1 hc
      rw [hc]
      show _ = some ((M.small.scale k hk).coreVertex _)
      split_ifs
      · rfl
      · rw [hFib]
    · rw [rowStart_full_of_ne hk mem hClosed hScale e hc]
      split_ifs
      · rw [Nat.sub_self, hz]
      · rw [hl]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact gRealize_address_gRow k hk mem hClosed hScale e
      ⟨mem.ident.row.symm (Fin.castAdd 3 e), ⟨i, by omega⟩⟩ (Equiv.apply_symm_apply _ _)

theorem tripodCore_tail_legSlot (j : Fin 3) :
    (tripodCore M.core M.slots).tail (legSlot 15 j) = centre 10 := by
  simp [tripodCore, legSlot, centre]

theorem tripodCore_head_legSlot (j : Fin 3) :
    (tripodCore M.core M.slots).head (legSlot 15 j) = tripodMark 10 j := by
  simp [tripodCore, legSlot, tripodMark]

/-- **A leg row is realised only at its mark end**, at the mark. -/
theorem gRealize_legRow (hScale : memberScale mem = k) (j : Fin 3) (i : ℕ)
    (hi : i ≤ (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j))).length) :
    gRealize k hk mem hClosed hScale
        (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) i) =
      if i = (if DegeneratePlacement.reverse mem (legSlot 15 j) then 0 else
          (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j))).length)
      then some ((M.small.scale k hk).coreVertex (M.smallMark j)) else none := by
  have hEnds := DegeneratePlacement.reverse_endpoints (tripodCore_loopless' M) mem (legSlot 15 j)
  rw [tripodCore_tail_legSlot, tripodCore_head_legSlot] at hEnds
  have hPos := RowSlotOrientation.orderedRow_length_pos mem.fullDim
    (mem.ident.row.symm (legSlot 15 j))
  have hMark : some ((M.small.scale k hk).coreVertex (M.expansion.fib (markVertex 10 j))) =
      some ((M.small.scale k hk).coreVertex (M.smallMark j)) := by
    rw [M.fib_mark j]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · by_cases hr : DegeneratePlacement.reverse mem (legSlot 15 j) = true
    · rw [ite_eq_left hr, ite_eq_left rfl]
      have h := gRealize_branch k hk mem hClosed hScale
        (RowSlotOrientation.startBranch mem.fullDim (mem.ident.row.symm (legSlot 15 j)))
        (markVertex 10 j) (by rw [hEnds.1, ite_eq_left hr]; rfl)
      exact h.trans hMark
    · rw [ite_eq_right hr, ite_eq_right (by omega)]
      exact gRealize_centre k hk mem hClosed hScale
        (RowSlotOrientation.startBranch mem.fullDim (mem.ident.row.symm (legSlot 15 j)))
        (by rw [hEnds.1, ite_eq_right hr])
  by_cases hil : i = (RowWalk.orderedRow mem.fullDim.pathEnds
      (mem.ident.row.symm (legSlot 15 j))).length
  · subst hil
    by_cases hr : DegeneratePlacement.reverse mem (legSlot 15 j) = true
    · rw [ite_eq_left hr, ite_eq_right (by omega)]
      exact gRealize_centre k hk mem hClosed hScale
        (RowSlotOrientation.finishBranch mem.fullDim (mem.ident.row.symm (legSlot 15 j)))
        (by rw [hEnds.2, ite_eq_left hr])
    · rw [ite_eq_right hr, ite_eq_left rfl]
      have h := gRealize_branch k hk mem hClosed hScale
        (RowSlotOrientation.finishBranch mem.fullDim (mem.ident.row.symm (legSlot 15 j)))
        (markVertex 10 j) (by rw [hEnds.2, ite_eq_right hr]; rfl)
      exact h.trans hMark
  · rw [ite_eq_right (by split_ifs <;> omega)]
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine gRealize_of_onTripod k hk mem hClosed hScale ?_
    have h := (address_onTripod_iff mem
      ⟨mem.ident.row.symm (legSlot 15 j), ⟨i', by omega⟩⟩).mpr (by
        show ¬ IsGSlot (mem.ident.row (mem.ident.row.symm (legSlot 15 j)))
        rw [Equiv.apply_symm_apply]
        exact legSlot_not_isGSlot j)
    exact h

/-! ### The transport of the slid fibres: the big side

The G-row script on the expanded core, as `PencilTransportProducer` §6–§7 builds it for members
over `D.bigCore`: the pulled-back potential read along every G-row (`gSlotValue`), with the label
potential `labelPot` at the core vertices. It is compatible at the slot ends (`gCompat`), constant
on the fibres of the contraction (`gScript_eq_of_vertexMap_eq`), and its pushed Laplacian is, slot
by slot, the row sum of the small side (`gPushDiv_prin_script`, `gSlot_sum`). -/

/-- The row position of offset `o` of the G-slot `e`, oriented by the row. -/
noncomputable def gSlotPos (e : Fin (15 + 1 + 1 + 1)) (o : ℕ) : ℤ :=
  if DegeneratePlacement.reverse mem (Fin.castAdd 3 e) then
    ((bigSpecAt M k hk).length e : ℤ) - o
  else o

/-- The script's value at offset `o` of the G-slot `e`: the row potential there. -/
noncomputable def gSlotValue (s : mem.target.edges → ℤ) (P : mem.target.V → ℤ)
    (e : Fin (15 + 1 + 1 + 1)) (o : ℕ) : ℤ :=
  PencilTransportProducer.rowValue mem hClosed s P (Fin.castAdd 3 e) (gSlotPos k hk mem e o)

/-- **The G-row script** on the expanded core. -/
noncomputable def gScript (s : mem.target.edges → ℤ) (P : mem.target.V → ℤ) :
    firing_script (bigSpecAt M k hk).graph :=
  (bigSpecAt M k hk).slotValueScript (labelPot mem P) (gSlotValue k hk mem hClosed s P)

/-- The start of the row over the G-slot `e` carries the label potential of its first end. -/
theorem labelPot_start (P : mem.target.V → ℤ) (e : Fin (15 + 1 + 1 + 1)) :
    labelPot mem P (if DegeneratePlacement.reverse mem (Fin.castAdd 3 e) then
        M.expansion.bigCore.head e else M.expansion.bigCore.tail e) =
      PencilTransportProducer.sourcePotential mem P
        (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)) 0) := by
  have hEnds := DegeneratePlacement.reverse_endpoints (tripodCore_loopless' M) mem
    (Fin.castAdd 3 e)
  rw [tripodCore_tail_castAdd, tripodCore_head_castAdd] at hEnds
  have h : mem.ident.vertex.symm (if DegeneratePlacement.reverse mem (Fin.castAdd 3 e) then
      M.expansion.bigCore.head e else M.expansion.bigCore.tail e).castSucc =
      RowSlotOrientation.startBranch mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)) := by
    rw [Equiv.symm_apply_eq, hEnds.1]
    split_ifs <;> rfl
  unfold labelPot
  rw [h]
  rfl

theorem labelPot_finish (P : mem.target.V → ℤ) (e : Fin (15 + 1 + 1 + 1)) :
    labelPot mem P (if DegeneratePlacement.reverse mem (Fin.castAdd 3 e) then
        M.expansion.bigCore.tail e else M.expansion.bigCore.head e) =
      PencilTransportProducer.sourcePotential mem P
        (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e))
          (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length) := by
  have hEnds := DegeneratePlacement.reverse_endpoints (tripodCore_loopless' M) mem
    (Fin.castAdd 3 e)
  rw [tripodCore_tail_castAdd, tripodCore_head_castAdd] at hEnds
  have h : mem.ident.vertex.symm (if DegeneratePlacement.reverse mem (Fin.castAdd 3 e) then
      M.expansion.bigCore.tail e else M.expansion.bigCore.head e).castSucc =
      RowSlotOrientation.finishBranch mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)) := by
    rw [Equiv.symm_apply_eq, hEnds.2]
    split_ifs <;> rfl
  unfold labelPot
  rw [h]
  rfl

variable {k} in
theorem rowStart_full_le (hScale : memberScale mem = k) (e : Fin (15 + 1 + 1 + 1)) :
    PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e)
        (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (Fin.castAdd 3 e))).length ≤
      (bigSpecAt M k hk).length e := by
  by_cases hc : M.expansion.kind e = SlotKind.contracted
  · rw [rowStart_full mem hClosed hScale e, DegenerateBigDivisor.degenerateLength_contracted _ _ hc,
      Nat.mul_zero]
    exact Nat.zero_le _
  · exact (rowStart_full_of_ne hk mem hClosed hScale e hc).le

/-- **The G-row script is compatible with the label potential at both ends of every slot.** -/
theorem gCompat (hScale : memberScale mem = k) (s : mem.target.edges → ℤ) (P : mem.target.V → ℤ)
    (hRise : PencilTransportProducer.RiseCompatible mem hClosed s P) :
    (bigSpecAt M k hk).SlotValueCompatible (labelPot mem P) (gSlotValue k hk mem hClosed s P) := by
  have hFull := rowStart_full_le hk mem hClosed hScale
  constructor
  · intro e
    change _ = labelPot mem P (M.expansion.bigCore.tail e)
    have hS := labelPot_start mem P e
    have hF := labelPot_finish mem P e
    unfold gSlotValue gSlotPos
    cases hr : DegeneratePlacement.reverse mem (Fin.castAdd 3 e)
    · simp only [hr, Bool.false_eq_true, ite_false] at hS ⊢
      rw [PencilTransportProducer.rowValue_of_nonpos _ _ _ _ _ (by simp), hS]
    · simp only [hr, ite_true] at hF ⊢
      rw [PencilTransportProducer.rowValue_of_ge _ _ _ _ hRise _ (by have := hFull e; omega), hF]
  · intro e
    change _ = labelPot mem P (M.expansion.bigCore.head e)
    have hS := labelPot_start mem P e
    have hF := labelPot_finish mem P e
    unfold gSlotValue gSlotPos
    cases hr : DegeneratePlacement.reverse mem (Fin.castAdd 3 e)
    · simp only [hr, Bool.false_eq_true, ite_false] at hF ⊢
      rw [PencilTransportProducer.rowValue_of_ge _ _ _ _ hRise _ (by have := hFull e; omega), hF]
    · simp only [hr, ite_true] at hS ⊢
      rw [PencilTransportProducer.rowValue_of_nonpos _ _ _ _ _ (by simp), hS]

/-- **The G-row script descends**: it is constant on the fibres of the contraction. -/
theorem gScript_eq_of_vertexMap_eq (hScale : memberScale mem = k) (s : mem.target.edges → ℤ)
    (P : mem.target.V → ℤ) (hRise : PencilTransportProducer.RiseCompatible mem hClosed s P)
    {x x' : (bigSpecAt M k hk).Vertex}
    (h : ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M) x =
      ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M) x') :
    gScript k hk mem hClosed s P x = gScript k hk mem hClosed s P x' := by
  have hCond' : M.expansion.Conditions (M.small.scale k hk).core := M.conditions
  rcases x with v | ⟨e, o⟩
  · rcases x' with w | ⟨e', o'⟩
    · have hfib : M.expansion.fib v = M.expansion.fib w := by
        have h' : (M.small.scale k hk).coreVertex (M.expansion.fib v) =
            (M.small.scale k hk).coreVertex (M.expansion.fib w) := h
        exact Sum.inl.inj h'
      exact labelPot_eq_of_fib_eq mem hClosed hScale s P hRise hfib
    · rw [ExpansionData.interior_fibre hCond' e' o' _ h]
      rfl
  · rw [ExpansionData.interior_fibre hCond' e o x' h.symm]
    rfl

/-- The descended G-row script on `M.small.scale k`. -/
noncomputable def gSmallScript (s : mem.target.edges → ℤ) (P : mem.target.V → ℤ) :
    firing_script (M.small.scale k hk).graph := fun b ↦
  gScript k hk mem hClosed s P
    (Classical.choose (ExpansionData.vertexMap_surjective (D := M.expansion)
      (small := M.small.scale k hk) (hN := by norm_num) (hL := expansion_loopless M)
      M.conditions b))

theorem gScript_eq_pullScript (hScale : memberScale mem = k) (s : mem.target.edges → ℤ)
    (P : mem.target.V → ℤ) (hRise : PencilTransportProducer.RiseCompatible mem hClosed s P) :
    gScript k hk mem hClosed s P =
      (ExpansionData.certificate M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M)).pullScript (gSmallScript k hk mem hClosed s P) := by
  funext x
  exact gScript_eq_of_vertexMap_eq k hk mem hClosed hScale s P hRise
    (Classical.choose_spec (ExpansionData.vertexMap_surjective (D := M.expansion)
      (small := M.small.scale k hk) (hN := by norm_num) (hL := expansion_loopless M)
      M.conditions (ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M) x))).symm

/-- **The pushed Laplacian of the G-row script**, as a sum over the unit steps of every slot of
the expanded core (as `PencilTransportProducer.pushDiv_prin_script`). -/
theorem gPushDiv_prin_script (hScale : memberScale mem = k) (s : mem.target.edges → ℤ)
    (P : mem.target.V → ℤ) (hRise : PencilTransportProducer.RiseCompatible mem hClosed s P)
    (b : (M.small.scale k hk).Vertex) :
    (ExpansionData.certificate M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M)).pushDiv
        (prin (bigSpecAt M k hk).graph (gScript k hk mem hClosed s P)) b =
      ∑ e : Fin (15 + 1 + 1 + 1), ∑ o : Fin ((bigSpecAt M k hk).length e),
        (gSlotValue k hk mem hClosed s P e (o.val + 1) - gSlotValue k hk mem hClosed s P e o.val) *
        (PencilTransportProducer.hit M.expansion M.small k hk e b o.val -
          PencilTransportProducer.hit M.expansion M.small k hk e b (o.val + 1)) := by
  classical
  have hCond' : M.expansion.Conditions (M.small.scale k hk).core := M.conditions
  set B := bigSpecAt M k hk
  have hSlope := B.isStepSlope_slotValueScript (gCompat k hk mem hClosed hScale s P hRise)
  unfold GraphContractionCertificate.pushDiv
  simp only [gScript]
  rw [Finset.sum_congr rfl fun x _ ↦ by rw [B.prin_eq_sum_slopes hSlope x]]
  have hSwap : ∀ x : B.Vertex,
      (if (ExpansionData.certificate M.expansion (M.small.scale k hk) (by norm_num)
          (expansion_loopless M)).vertexMap x = b then
        ∑ step : B.Step,
          ((if B.stepLeft step.1 step.2 = x then
              gSlotValue k hk mem hClosed s P step.1 (step.2.val + 1) -
                gSlotValue k hk mem hClosed s P step.1 step.2.val
            else 0) +
            (if B.stepRight step.1 step.2 = x then
              -(gSlotValue k hk mem hClosed s P step.1 (step.2.val + 1) -
                gSlotValue k hk mem hClosed s P step.1 step.2.val)
            else 0))
      else 0) =
        ∑ step : B.Step,
          ((if B.stepLeft step.1 step.2 = x then
              (if ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
                  (expansion_loopless M) x = b then
                gSlotValue k hk mem hClosed s P step.1 (step.2.val + 1) -
                  gSlotValue k hk mem hClosed s P step.1 step.2.val
                else 0)
            else 0) +
            (if B.stepRight step.1 step.2 = x then
              (if ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
                  (expansion_loopless M) x = b then
                -(gSlotValue k hk mem hClosed s P step.1 (step.2.val + 1) -
                  gSlotValue k hk mem hClosed s P step.1 step.2.val)
                else 0)
            else 0)) := by
    intro x
    by_cases hx : (ExpansionData.certificate M.expansion (M.small.scale k hk) (by norm_num)
        (expansion_loopless M)).vertexMap x = b
    · rw [ite_eq_left hx]
      refine Finset.sum_congr rfl fun step _ ↦ ?_
      have hx' : ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
          (expansion_loopless M) x = b := hx
      simp only [hx', ite_true]
    · rw [ite_eq_right hx]
      have hx' : ¬ ExpansionData.vertexMap M.expansion (M.small.scale k hk) (by norm_num)
          (expansion_loopless M) x = b := hx
      simp only [hx', ite_false, ite_self, add_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun x _ ↦ hSwap x, Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun o _ ↦ ?_
  rw [ExpansionData.vertexMap_stepLeft hCond' e o, ExpansionData.vertexMap_stepRight hCond' e o]
  unfold PencilTransportProducer.hit
  split_ifs <;> ring

/-- **The window computation, one G-slot at a time** (as `PencilTransportProducer.slot_sum`). -/
theorem gSlot_sum (hScale : memberScale mem = k) (s : mem.target.edges → ℤ)
    (P : mem.target.V → ℤ) (e : Fin (15 + 1 + 1 + 1)) (δ : ℕ → ℤ) :
    (∑ o : Fin ((bigSpecAt M k hk).length e),
      (gSlotValue k hk mem hClosed s P e (o.val + 1) - gSlotValue k hk mem hClosed s P e o.val) *
      (δ o.val - δ (o.val + 1))) =
      ∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (Fin.castAdd 3 e))).length,
        PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
          (δ (DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
              (Fin.castAdd 3 e) i) -
            δ (DegeneratePlacement.offsetVal (tripodSpec M k hk) (legRequest M) mem hClosed
              (Fin.castAdd 3 e) (i.val + 1))) := by
  have hFull := rowStart_full_le hk mem hClosed hScale e
  have hWin : ∀ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
      (mem.ident.row.symm (Fin.castAdd 3 e))).length,
      PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i +
          PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i ≤
        (bigSpecAt M k hk).length e :=
    fun i ↦ (PencilTransportProducer.rowStart_add_rowLen_le mem hClosed (Fin.castAdd 3 e) i).trans
      hFull
  simp only [offsetVal_eq', tripodLength_castAdd]
  unfold gSlotValue gSlotPos
  cases hr : DegeneratePlacement.reverse mem (Fin.castAdd 3 e)
  · simp only [Bool.false_eq_true, ite_false]
    have hDiff : ∀ o : ℕ,
        PencilTransportProducer.rowValue mem hClosed s P (Fin.castAdd 3 e) ((o + 1 : ℕ) : ℤ) -
            PencilTransportProducer.rowValue mem hClosed s P (Fin.castAdd 3 e) (o : ℤ) =
          ∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
              (mem.ident.row.symm (Fin.castAdd 3 e))).length,
            PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
              (if PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i ≤ o ∧
                  o < PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i +
                    PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i
                then (1 : ℤ) else 0) := by
      intro o
      unfold PencilTransportProducer.rowValue
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← mul_sub, show ((o + 1 : ℕ) : ℤ) = (o : ℤ) + 1 by push_cast; ring,
        PencilTransportProducer.ramp_succ_sub _ _ _ (by positivity)]
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun o _ ↦ by rw [hDiff o.val]]
    rw [Fin.sum_univ_eq_sum_range (fun o ↦ (∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
        (mem.ident.row.symm (Fin.castAdd 3 e))).length,
        PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
          (if PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i ≤ o ∧
              o < PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i +
                PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i
            then (1 : ℤ) else 0)) * (δ o - δ (o + 1)))]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [mul_assoc]
    rw [← Finset.mul_sum, PencilTransportProducer.sum_window δ _ _ _ (hWin i)]
    show _ = PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
      (δ (PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i) -
        δ (PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) (i.val + 1)))
    rw [PencilTransportProducer.rowStart_succ]
  · simp only [ite_true]
    have hDiff : ∀ o : ℕ, o < (bigSpecAt M k hk).length e →
        PencilTransportProducer.rowValue mem hClosed s P (Fin.castAdd 3 e)
            (((bigSpecAt M k hk).length e : ℤ) - ((o + 1 : ℕ) : ℤ)) -
          PencilTransportProducer.rowValue mem hClosed s P (Fin.castAdd 3 e)
            (((bigSpecAt M k hk).length e : ℤ) - (o : ℤ)) =
          ∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
              (mem.ident.row.symm (Fin.castAdd 3 e))).length,
            PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
              -(if (bigSpecAt M k hk).length e -
                    PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
                    PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i ≤ o ∧
                  o < (bigSpecAt M k hk).length e -
                    PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i
                then (1 : ℤ) else 0) := by
      intro o ho
      unfold PencilTransportProducer.rowValue
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hStep := PencilTransportProducer.ramp_succ_sub
        (((bigSpecAt M k hk).length e : ℤ) - ((o + 1 : ℕ) : ℤ))
        (PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i)
        (PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i) (by positivity)
      rw [show ((bigSpecAt M k hk).length e : ℤ) - ((o + 1 : ℕ) : ℤ) + 1 =
        ((bigSpecAt M k hk).length e : ℤ) - (o : ℤ) by push_cast; ring] at hStep
      rw [← mul_sub, ← neg_sub, hStep]
      have := hWin i
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun o _ ↦ by rw [hDiff o.val o.isLt]]
    rw [Fin.sum_univ_eq_sum_range (fun o ↦ (∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
        (mem.ident.row.symm (Fin.castAdd 3 e))).length,
        PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
          -(if (bigSpecAt M k hk).length e -
                PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
                PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i ≤ o ∧
              o < (bigSpecAt M k hk).length e -
                PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i
            then (1 : ℤ) else 0)) * (δ o - δ (o + 1)))]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hW := hWin i
    have hEq : ∀ o ∈ Finset.range ((bigSpecAt M k hk).length e),
        PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
            -(if (bigSpecAt M k hk).length e -
                  PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
                  PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i ≤ o ∧
                o < (bigSpecAt M k hk).length e -
                  PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i
              then (1 : ℤ) else 0) * (δ o - δ (o + 1)) =
          -PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
            ((if (bigSpecAt M k hk).length e -
                  PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
                  PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i ≤ o ∧
                o < (bigSpecAt M k hk).length e -
                  PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
                  PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i +
                    PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i
              then (1 : ℤ) else 0) * (δ o - δ (o + 1))) := by
      intro o _
      have hIff : (o < (bigSpecAt M k hk).length e -
          PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i) ↔
          (o < (bigSpecAt M k hk).length e -
            PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
            PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i +
              PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i) := by omega
      simp only [hIff]
      ring
    rw [Finset.sum_congr rfl hEq, ← Finset.mul_sum]
    have hSum' := PencilTransportProducer.sum_window δ ((bigSpecAt M k hk).length e)
      ((bigSpecAt M k hk).length e -
        PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
        PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i)
      (PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i) (by omega)
    rw [hSum']
    show _ = PencilTransportProducer.rowSlope mem s (Fin.castAdd 3 e) i *
      (δ ((bigSpecAt M k hk).length e -
          PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i) -
        δ ((bigSpecAt M k hk).length e -
          PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) (i.val + 1)))
    rw [PencilTransportProducer.rowStart_succ,
      show (bigSpecAt M k hk).length e -
        PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
        PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i +
          PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i =
        (bigSpecAt M k hk).length e -
          PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i by omega,
      show (bigSpecAt M k hk).length e -
        (PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i +
          PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i) =
        (bigSpecAt M k hk).length e -
          PencilTransportProducer.rowStart mem hClosed (Fin.castAdd 3 e) i -
          PencilTransportProducer.rowLen mem hClosed (Fin.castAdd 3 e) i by omega]
    ring

/-! ### The leg edges at the marks

A leg row is realised only at its mark (`gRealize_legRow`), so its row sum is the row slope of
the single occurrence at the mark, the leg edge (`germ`), times the indicator of the mark. The
leg edge is the only edge of the leg row at the mark (`germ_unique`), so `markCoeff` reads it
(`markCoeff_eq_germ`), and the tree flow with incidence `anchor − root` crosses its target edge
by the change of side (`tree_flow_eq`). The two contributions cancel (`germ_balance`). -/

/-- **On a tree, the flow with incidence `anchor − root` crosses each edge by the change of
side**, read through `TreeMetricPotential.cutValue`. -/
theorem tree_flow_eq {T : CFGraph} (hConn : graph_connected T) (hGenus : genus T = 0)
    (f : T.edges → ℤ) (root anchor : T.V)
    (hf : ∀ v, GluingDatum.targetEdgeIncidence f v =
      (if v = anchor then 1 else 0) - (if v = root then 1 else 0))
    (t : T.edges) :
    f t = TreeMetricPotential.cutValue t root - TreeMetricPotential.cutValue t anchor := by
  classical
  have key : ∑ v : T.V, TreeMetricPotential.cutValue t v * GluingDatum.targetEdgeIncidence f v =
      -f t := by
    unfold GluingDatum.targetEdgeIncidence
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single t]
    · simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      rw [TreeMetricPotential.cutValue_tail t, TreeMetricPotential.cutValue_head hConn hGenus t]
      ring
    · intro u _ hu
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      rw [TreeMetricPotential.cutValue_other hConn hGenus t u (Ne.symm hu)]
      ring
    · simp
  have key2 : ∑ v : T.V, TreeMetricPotential.cutValue t v * GluingDatum.targetEdgeIncidence f v =
      TreeMetricPotential.cutValue t anchor - TreeMetricPotential.cutValue t root := by
    simp only [hf, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  linarith

theorem cutValue_cases {T : CFGraph} (t : T.edges) (v : T.V) :
    TreeMetricPotential.cutValue t v = 0 ∨ TreeMetricPotential.cutValue t v = 1 := by
  unfold TreeMetricPotential.cutValue
  split_ifs <;> simp

/-- The index of the end of the leg row at the mark: `0` if the row starts there. -/
noncomputable def markIdx (j : Fin 3) : ℕ :=
  if DegeneratePlacement.reverse mem (legSlot 15 j) then 0 else
    (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j))).length

/-- The occurrence of the leg row at the mark. -/
noncomputable def germIdx (j : Fin 3) :
    Fin (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j))).length :=
  if DegeneratePlacement.reverse mem (legSlot 15 j) then
    ⟨0, RowSlotOrientation.orderedRow_length_pos mem.fullDim _⟩
  else
    ⟨(RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j))).length - 1,
      Nat.sub_lt (RowSlotOrientation.orderedRow_length_pos mem.fullDim _) Nat.one_pos⟩

/-- **The leg edge at the mark `j`.** -/
noncomputable def germ (j : Fin 3) : mem.data.SourceEdge :=
  (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j)))[(germIdx mem j).val]'
    (germIdx mem j).isLt

/-- The mark is the row vertex at `markIdx`, and the centre the one at the other end. -/
theorem leg_ends (j : Fin 3) :
    (mem.ident.vertex.symm (tripodMark 10 j)).1 =
        RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) (markIdx mem j) ∧
      (mem.ident.vertex.symm (centre 10)).1 =
        RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j))
          (if DegeneratePlacement.reverse mem (legSlot 15 j) then
            (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j))).length
          else 0) := by
  have hEnds := DegeneratePlacement.reverse_endpoints (tripodCore_loopless' M) mem (legSlot 15 j)
  rw [tripodCore_tail_legSlot, tripodCore_head_legSlot] at hEnds
  unfold markIdx
  by_cases hr : DegeneratePlacement.reverse mem (legSlot 15 j) = true
  · have h1 : mem.ident.vertex.symm (tripodMark 10 j) =
        RowSlotOrientation.startBranch mem.fullDim (mem.ident.row.symm (legSlot 15 j)) := by
      rw [Equiv.symm_apply_eq, hEnds.1, ite_eq_left hr]
    have h2 : mem.ident.vertex.symm (centre 10) =
        RowSlotOrientation.finishBranch mem.fullDim (mem.ident.row.symm (legSlot 15 j)) := by
      rw [Equiv.symm_apply_eq, hEnds.2, ite_eq_left hr]
    simp only [hr, ↓reduceIte]
    exact ⟨congrArg (fun b ↦ b.1) h1, congrArg (fun b ↦ b.1) h2⟩
  · have h1 : mem.ident.vertex.symm (tripodMark 10 j) =
        RowSlotOrientation.finishBranch mem.fullDim (mem.ident.row.symm (legSlot 15 j)) := by
      rw [Equiv.symm_apply_eq, hEnds.2, ite_eq_right hr]
    have h2 : mem.ident.vertex.symm (centre 10) =
        RowSlotOrientation.startBranch mem.fullDim (mem.ident.row.symm (legSlot 15 j)) := by
      rw [Equiv.symm_apply_eq, hEnds.1, ite_eq_right hr]
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    exact ⟨congrArg (fun b ↦ b.1) h1, congrArg (fun b ↦ b.1) h2⟩

/-- **The leg edge is the only edge of the leg row at the mark.** -/
theorem germ_unique (j : Fin 3) (e : mem.data.SourceEdge)
    (hOn : RowWalk.OnRow mem.data (mem.ident.row.symm (legSlot 15 j)) e)
    (hInc : Incident mem.data e (mem.ident.vertex.symm (tripodMark 10 j)).1) :
    e = germ mem j := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp
    ((RowWalk.mem_orderedRow_iff mem.fullDim.pathEnds _ e).mpr hOn)
  have hEnds := leg_ends mem j
  have hI := RowPosition.rowVertex_incident mem.fullDim (mem.ident.row.symm (legSlot 15 j)) hi
  have hSucc : RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) (i + 1) =
      W4StableSource.otherEnd mem.data
        (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j)))[i]
        (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) i) :=
    OrientedTraversal.walkVertex_succ _ _ hi
  -- the mark is the row vertex at `i` or `i + 1`
  have hm : ∃ m, (m = i ∨ m = i + 1) ∧ (mem.ident.vertex.symm (tripodMark 10 j)).1 =
      RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) m := by
    rcases eq_or_eq_otherEnd mem.data hI hInc with h | h
    · exact ⟨i, Or.inl rfl, h⟩
    · exact ⟨i + 1, Or.inr rfl, h.trans hSucc.symm⟩
  obtain ⟨m, hmi, hmEq⟩ := hm
  -- it is not an interior row vertex
  have hBranch := (mem.ident.vertex.symm (tripodMark 10 j)).2
  have hEnd : m = 0 ∨ m = (RowWalk.orderedRow mem.fullDim.pathEnds
      (mem.ident.row.symm (legSlot 15 j))).length := by
    by_contra hNo
    push Not at hNo
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hv := RowPosition.rowVertex_valency mem.fullDim (mem.ident.row.symm (legSlot 15 j))
      (j := m') (by omega)
    rw [← hmEq] at hv
    omega
  -- nor the centre
  have hNe : ∀ m₀, (mem.ident.vertex.symm (centre 10)).1 =
      RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) m₀ → m ≠ m₀ := by
    intro m₀ hm₀ hmm
    subst hmm
    have h := hmEq.trans hm₀.symm
    have h' : mem.ident.vertex.symm (tripodMark 10 j) = mem.ident.vertex.symm (centre 10) :=
      Subtype.ext h
    exact (Fin.castSucc_lt_last _).ne (mem.ident.vertex.symm.injective h')
  have hNeC := hNe _ hEnds.2
  have hLenPos := RowSlotOrientation.orderedRow_length_pos mem.fullDim
    (mem.ident.row.symm (legSlot 15 j))
  unfold germ germIdx
  by_cases hr : DegeneratePlacement.reverse mem (legSlot 15 j) = true
  · simp only [hr, ↓reduceIte] at hNeC ⊢
    have hi0 : i = 0 := by omega
    subst hi0
    rfl
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hNeC ⊢
    have hiL : i = (RowWalk.orderedRow mem.fullDim.pathEnds
        (mem.ident.row.symm (legSlot 15 j))).length - 1 := by omega
    subst hiL
    rfl

theorem germ_onRow (j : Fin 3) :
    RowWalk.OnRow mem.data (mem.ident.row.symm (legSlot 15 j)) (germ mem j) :=
  (RowWalk.mem_orderedRow_iff mem.fullDim.pathEnds _ _).mp (List.getElem_mem _)

/-- The mark is the start of the leg-edge occurrence if the row starts at the mark, and its other
end otherwise. -/
theorem germ_mark (j : Fin 3) :
    if DegeneratePlacement.reverse mem (legSlot 15 j) then
      (mem.ident.vertex.symm (tripodMark 10 j)).1 =
        RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) (germIdx mem j)
    else
      (mem.ident.vertex.symm (tripodMark 10 j)).1 =
        W4StableSource.otherEnd mem.data (germ mem j)
          (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j))
            (germIdx mem j)) := by
  have hSucc : RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j))
        ((germIdx mem j).val + 1) =
      W4StableSource.otherEnd mem.data (germ mem j)
        (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j))
          (germIdx mem j)) :=
    OrientedTraversal.walkVertex_succ _ _ (germIdx mem j).isLt
  have hMark := (leg_ends mem j).1
  have hLenPos := RowSlotOrientation.orderedRow_length_pos mem.fullDim
    (mem.ident.row.symm (legSlot 15 j))
  by_cases hr : DegeneratePlacement.reverse mem (legSlot 15 j) = true
  · rw [ite_eq_left hr, hMark]
    unfold markIdx germIdx
    simp only [hr, ↓reduceIte]
  · rw [ite_eq_right hr, hMark, ← hSucc]
    unfold markIdx germIdx
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    congr 1
    omega

theorem germ_incident (j : Fin 3) :
    Incident mem.data (germ mem j) (mem.ident.vertex.symm (tripodMark 10 j)).1 := by
  have h := germ_mark mem j
  split_ifs at h
  · rw [h]
    exact RowPosition.rowVertex_incident mem.fullDim _ (germIdx mem j).isLt
  · rw [h]
    exact incident_otherEnd mem.data _ _

open Classical in
/-- **`markCoeff` reads the leg edge.** -/
theorem markCoeff_eq_germ (x : mem.target.V) (j : Fin 3) :
    markCoeff mem x j =
      if TreeMetricPotential.cutValue (germ mem j).1.1 x ≠
          TreeMetricPotential.cutValue (germ mem j).1.1
            (mem.ident.vertex.symm (tripodMark 10 j)).1.1.1
      then mem.data.sourceEdgeIndex (germ mem j) else 0 := by
  unfold markCoeff
  rw [Finset.sum_eq_single (germ mem j)]
  · simp only [germ_onRow, germ_incident, true_and]
  · intro e _ he
    rw [ite_eq_right]
    rintro ⟨hOn, hInc, -⟩
    exact he (germ_unique mem j e hOn hInc)
  · simp

/-- The first edge of leg `j` in the claw-frame sense (`ClawShape.firstEdge`) is the leg edge
`germ mem j` at the mark. -/
theorem firstEdge_eq_germ (j : Fin 3) :
    (ClawShape.firstEdge (Frame.of mem) j).1 = germ mem j :=
  germ_unique mem j _
    ⟨(ClawShape.firstEdge (Frame.of mem) j).2,
      (Equiv.eq_symm_apply _).mpr (ClawShape.firstEdge_row (Frame.of mem) j)⟩
    (ClawShape.firstEdge_incident (Frame.of mem) j)

/-- **At `φ(c)` every mark coefficient is one** (Theorem 4.7(b), Lemma 4.8 and Corollary 4.3).

`markCoeff` reads the leg edge `germ mem j` at the mark (`markCoeff_eq_germ`). Its target edge
`h_j` separates `φ(c)` from `φ(j)` (`ClawShape.firstEdge_separates`, Theorem 4.7(b)), and
its index is `s_j = 1` (`ClawShape.firstEdge_index`, Lemma 4.8). Neither uses closedness or
long legs; the connectedness of `G̃` is `M.connected`. -/
theorem markCoeff_centre (hClaw : MemberIsClaw mem) (j : Fin 3) :
    markCoeff mem (TripodFrame.centreTarget (Frame.of mem)) j = 1 := by
  have h := markCoeff_eq_germ mem (TripodFrame.centreTarget (Frame.of mem)) j
  rw [← firstEdge_eq_germ mem j] at h
  rw [h]
  split_ifs with hc
  · exact ClawShape.firstEdge_index (Frame.of mem) M.connected hClaw j
  · exact absurd (ClawShape.firstEdge_separates (Frame.of mem) M.connected hClaw j) hc

theorem slidFibre_centre (hScale : memberScale mem = k) (hClaw : MemberIsClaw mem) :
    slidFibre k hk mem hClosed hScale (TripodFrame.centreTarget (Frame.of mem)) =
      M.small.embed k hk (marksDiv M) + clawDivisor k hk mem hClosed hScale := by
  unfold slidFibre clawDivisor
  rw [embed_marksDiv, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [markCoeff_centre mem hClaw j, Nat.cast_one, one_smul]

/-- **The leg-edge balance.** The row slope of the leg edge, read away from the mark, cancels the
change of the mark coefficient from `root` to `anchor`. -/
theorem germ_balance (root anchor : mem.target.V) (j : Fin 3) :
    (if DegeneratePlacement.reverse mem (legSlot 15 j) then
        PencilTransportProducer.rowSlope mem (PencilTransportProducer.chipSlope mem root anchor)
          (legSlot 15 j) (germIdx mem j)
      else -PencilTransportProducer.rowSlope mem
          (PencilTransportProducer.chipSlope mem root anchor) (legSlot 15 j) (germIdx mem j)) +
      ((markCoeff mem anchor j : ℕ) : ℤ) - ((markCoeff mem root j : ℕ) : ℤ) = 0 := by
  classical
  have hFlow := tree_flow_eq mem.fullDim.targetConnected mem.fullDim.targetGenus
    (PencilTransportProducer.chipSlope mem root anchor) root anchor
    (TreeMetricPotential.chipSlope_incidence mem.data mem.fullDim.targetConnected
      mem.fullDim.targetGenus root anchor) (germ mem j).1.1
  have hMark := germ_mark mem j
  have hInc := germ_incident mem j
  have hne := mem.data.sourceEnds_ne (germ mem j)
  rw [markCoeff_eq_germ, markCoeff_eq_germ]
  -- the row slope of the leg edge, read away from the mark
  have hc : (if DegeneratePlacement.reverse mem (legSlot 15 j) then
        PencilTransportProducer.rowSlope mem (PencilTransportProducer.chipSlope mem root anchor)
          (legSlot 15 j) (germIdx mem j)
      else -PencilTransportProducer.rowSlope mem
          (PencilTransportProducer.chipSlope mem root anchor) (legSlot 15 j) (germIdx mem j)) =
      if (mem.data.sourceEnds (germ mem j)).1 = (mem.ident.vertex.symm (tripodMark 10 j)).1 then
        PencilTransportProducer.edgeSlope mem (PencilTransportProducer.chipSlope mem root anchor)
          (germ mem j)
      else -PencilTransportProducer.edgeSlope mem
          (PencilTransportProducer.chipSlope mem root anchor) (germ mem j) := by
    unfold PencilTransportProducer.rowSlope
    change (if DegeneratePlacement.reverse mem (legSlot 15 j) then
        (if (mem.data.sourceEnds (germ mem j)).1 = RowPosition.rowVertex mem.fullDim
            (mem.ident.row.symm (legSlot 15 j)) (germIdx mem j) then
          PencilTransportProducer.edgeSlope mem
            (PencilTransportProducer.chipSlope mem root anchor) (germ mem j)
        else -PencilTransportProducer.edgeSlope mem
            (PencilTransportProducer.chipSlope mem root anchor) (germ mem j))
      else -(if (mem.data.sourceEnds (germ mem j)).1 = RowPosition.rowVertex mem.fullDim
            (mem.ident.row.symm (legSlot 15 j)) (germIdx mem j) then
          PencilTransportProducer.edgeSlope mem
            (PencilTransportProducer.chipSlope mem root anchor) (germ mem j)
        else -PencilTransportProducer.edgeSlope mem
            (PencilTransportProducer.chipSlope mem root anchor) (germ mem j))) = _
    by_cases hr : DegeneratePlacement.reverse mem (legSlot 15 j) = true
    · rw [ite_eq_left hr] at hMark ⊢
      rw [hMark]
    · rw [ite_eq_right hr] at hMark ⊢
      rw [hMark]
      unfold W4StableSource.otherEnd
      by_cases h1 : (mem.data.sourceEnds (germ mem j)).1 = RowPosition.rowVertex mem.fullDim
          (mem.ident.row.symm (legSlot 15 j)) (germIdx mem j)
      · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right hne]
      · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left rfl, neg_neg]
  -- the side of the mark on the target edge of the leg edge
  have hct : if (mem.data.sourceEnds (germ mem j)).1 = (mem.ident.vertex.symm (tripodMark 10 j)).1
      then TreeMetricPotential.cutValue (germ mem j).1.1
          (mem.ident.vertex.symm (tripodMark 10 j)).1.1.1 = 0
      else TreeMetricPotential.cutValue (germ mem j).1.1
          (mem.ident.vertex.symm (tripodMark 10 j)).1.1.1 = 1 := by
    split_ifs with h
    · rw [← h]
      exact TreeMetricPotential.cutValue_tail _
    · have h2 : (mem.data.sourceEnds (germ mem j)).2 = (mem.ident.vertex.symm (tripodMark 10 j)).1 :=
        hInc.resolve_left h
      rw [← h2]
      exact TreeMetricPotential.cutValue_head mem.fullDim.targetConnected mem.fullDim.targetGenus _
  rw [hc]
  unfold PencilTransportProducer.edgeSlope
  rw [hFlow]
  have hr₀ := cutValue_cases (germ mem j).1.1 root
  have ha₀ := cutValue_cases (germ mem j).1.1 anchor
  split_ifs at hct ⊢ <;> rcases hr₀ with hr₀ | hr₀ <;> rcases ha₀ with ha₀ | ha₀ <;>
    simp_all

/-- **The row sum of a leg row**: the row slope of the leg edge, read away from the mark, at the
mark. -/
theorem legRow_sum (hScale : memberScale mem = k) (root anchor : mem.target.V) (j : Fin 3)
    (b : (M.small.scale k hk).Vertex) :
    (∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds (mem.ident.row.symm (legSlot 15 j))).length,
      PencilTransportProducer.rowSlope mem (PencilTransportProducer.chipSlope mem root anchor)
          (legSlot 15 j) i *
        ((if gRealize k hk mem hClosed hScale
            (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) i) = some b
            then 1 else 0) -
          (if gRealize k hk mem hClosed hScale
            (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (legSlot 15 j)) (i.val + 1)) =
              some b then 1 else 0))) =
      (if DegeneratePlacement.reverse mem (legSlot 15 j) then
        PencilTransportProducer.rowSlope mem (PencilTransportProducer.chipSlope mem root anchor)
          (legSlot 15 j) (germIdx mem j)
      else -PencilTransportProducer.rowSlope mem
          (PencilTransportProducer.chipSlope mem root anchor) (legSlot 15 j) (germIdx mem j)) *
        (if (M.small.scale k hk).coreVertex (M.smallMark j) = b then 1 else 0) := by
  classical
  have hLenPos := RowSlotOrientation.orderedRow_length_pos mem.fullDim
    (mem.ident.row.symm (legSlot 15 j))
  rw [Finset.sum_congr rfl fun i _ ↦ by
    rw [gRealize_legRow k hk mem hClosed hScale j i (le_of_lt i.isLt),
      gRealize_legRow k hk mem hClosed hScale j (i.val + 1) i.isLt]]
  by_cases hr : DegeneratePlacement.reverse mem (legSlot 15 j) = true
  · simp only [hr, ↓reduceIte]
    rw [Finset.sum_eq_single (germIdx mem j)]
    · have h0 : (germIdx mem j).val = 0 := by
        unfold germIdx
        simp only [hr, ↓reduceIte]
      simp only [h0, Nat.zero_add, one_ne_zero, ↓reduceIte, Option.some.injEq]
      split_ifs <;> simp_all
    · intro i _ hi
      have h0 : (germIdx mem j).val = 0 := by
        unfold germIdx
        simp only [hr, ↓reduceIte]
      have hi0 : i.val ≠ 0 := fun h ↦ hi (Fin.ext (h.trans h0.symm))
      simp [hi0]
    · simp
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_eq_single (germIdx mem j)]
    · have hL : (germIdx mem j).val = (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (legSlot 15 j))).length - 1 := by
        unfold germIdx
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
      have h1 : (germIdx mem j).val ≠ (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (legSlot 15 j))).length := by omega
      have h2 : (germIdx mem j).val + 1 = (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (legSlot 15 j))).length := by omega
      simp only [h1, h2, ↓reduceIte, Option.some.injEq]
      split_ifs <;> simp_all
    · intro i _ hi
      have hL : (germIdx mem j).val = (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (legSlot 15 j))).length - 1 := by
        unfold germIdx
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
      have h1 : i.val ≠ (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (legSlot 15 j))).length := by have := i.isLt; omega
      have h2 : i.val + 1 ≠ (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (legSlot 15 j))).length := by
        intro h
        exact hi (Fin.ext (by omega))
      simp [h1, h2]
    · simp

/-- **The slid fibres form a linear system** (§7.4, Lemmas 7.2 and 7.3): the
difference of the slid fibres over `root` and `anchor` is the Laplacian of the descended G-row
script of the tree potential with incidence `anchor − root`. -/
theorem slidFibre_transport (hScale : memberScale mem = k) (root anchor : mem.target.V) :
    linear_equiv (M.small.scale k hk).graph (slidFibre k hk mem hClosed hScale root)
      (slidFibre k hk mem hClosed hScale anchor) := by
  classical
  have hCond' : M.expansion.Conditions (M.small.scale k hk).core := M.conditions
  have hRise := PencilTransportProducer.chip_riseCompatible mem hClosed root anchor
  unfold linear_equiv
  rw [principal_iff_eq_prin]
  refine ⟨gSmallScript k hk mem hClosed (PencilTransportProducer.chipSlope mem root anchor)
    (PencilTransportProducer.chipPotential mem hClosed root anchor), ?_⟩
  rw [← (ExpansionData.certificate M.expansion (M.small.scale k hk) (by norm_num)
      (expansion_loopless M)).pushDiv_prin_pullScript (ExpansionData.certificate_valid hCond'),
    ← gScript_eq_pullScript k hk mem hClosed hScale _ _ hRise]
  funext b
  rw [gPushDiv_prin_script k hk mem hClosed hScale _ _ hRise b]
  have hBase := slidBase_sub_eq_rows k hk mem hClosed hScale root anchor b
  rw [Fin.sum_univ_add] at hBase
  -- the G-rows are the slot sums of the script
  have hG : ∀ e : Fin (15 + 1 + 1 + 1),
      (∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (Fin.castAdd 3 e))).length,
        PencilTransportProducer.rowSlope mem (PencilTransportProducer.chipSlope mem root anchor)
            (Fin.castAdd 3 e) i *
          ((if gRealize k hk mem hClosed hScale
              (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e)) i) = some b
              then 1 else 0) -
            (if gRealize k hk mem hClosed hScale
              (RowPosition.rowVertex mem.fullDim (mem.ident.row.symm (Fin.castAdd 3 e))
                (i.val + 1)) = some b then 1 else 0))) =
        ∑ o : Fin ((bigSpecAt M k hk).length e),
          (gSlotValue k hk mem hClosed (PencilTransportProducer.chipSlope mem root anchor)
              (PencilTransportProducer.chipPotential mem hClosed root anchor) e (o.val + 1) -
            gSlotValue k hk mem hClosed (PencilTransportProducer.chipSlope mem root anchor)
              (PencilTransportProducer.chipPotential mem hClosed root anchor) e o.val) *
          (PencilTransportProducer.hit M.expansion M.small k hk e b o.val -
            PencilTransportProducer.hit M.expansion M.small k hk e b (o.val + 1)) := by
    intro e
    rw [gSlot_sum k hk mem hClosed hScale _ _ e (PencilTransportProducer.hit M.expansion M.small k hk e b)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [gRealize_gRow k hk mem hClosed hScale e i (le_of_lt i.isLt),
      gRealize_gRow k hk mem hClosed hScale e (i.val + 1) i.isLt]
    simp only [Option.some.injEq]
    rfl
  -- the leg rows cancel the mark correction
  have hL : ∀ j : Fin 3,
      (∑ i : Fin (RowWalk.orderedRow mem.fullDim.pathEnds
          (mem.ident.row.symm (Fin.natAdd (15 + 1 + 1 + 1) j))).length,
        PencilTransportProducer.rowSlope mem (PencilTransportProducer.chipSlope mem root anchor)
            (Fin.natAdd (15 + 1 + 1 + 1) j) i *
          ((if gRealize k hk mem hClosed hScale
              (RowPosition.rowVertex mem.fullDim
                (mem.ident.row.symm (Fin.natAdd (15 + 1 + 1 + 1) j)) i) = some b
              then 1 else 0) -
            (if gRealize k hk mem hClosed hScale
              (RowPosition.rowVertex mem.fullDim
                (mem.ident.row.symm (Fin.natAdd (15 + 1 + 1 + 1) j)) (i.val + 1)) = some b
              then 1 else 0))) +
        (((markCoeff mem anchor j : ℕ) : ℤ) - ((markCoeff mem root j : ℕ) : ℤ)) *
          markChip k hk j b = 0 := by
    intro j
    have h := legRow_sum k hk mem hClosed hScale root anchor j b
    have hB := germ_balance mem root anchor j
    refine (congrArg (· + (((markCoeff mem anchor j : ℕ) : ℤ) - ((markCoeff mem root j : ℕ) : ℤ)) *
      markChip k hk j b) h).trans ?_
    unfold markChip one_chip
    by_cases hb : b = (M.small.scale k hk).coreVertex (M.smallMark j)
    · rw [ite_eq_left hb.symm, ite_eq_left hb]
      linarith
    · rw [ite_eq_right (Ne.symm hb), ite_eq_right hb]
      ring
  have hCorr : ∀ x, (∑ j, ((markCoeff mem x j : ℕ) : ℤ) • markChip k hk j) b =
      ∑ j, ((markCoeff mem x j : ℕ) : ℤ) * markChip k hk j b := fun x ↦ by
    rw [Finset.sum_apply]
    rfl
  show slidFibre k hk mem hClosed hScale anchor b - slidFibre k hk mem hClosed hScale root b = _
  unfold slidFibre
  rw [Pi.add_apply, Pi.add_apply, hCorr, hCorr]
  have hSplit : slidBase k hk mem hClosed hScale anchor b +
        ∑ j, ((markCoeff mem anchor j : ℕ) : ℤ) * markChip k hk j b -
      (slidBase k hk mem hClosed hScale root b +
        ∑ j, ((markCoeff mem root j : ℕ) : ℤ) * markChip k hk j b) =
      (slidBase k hk mem hClosed hScale anchor b - slidBase k hk mem hClosed hScale root b) +
        ∑ j, (((markCoeff mem anchor j : ℕ) : ℤ) - ((markCoeff mem root j : ℕ) : ℤ)) *
          markChip k hk j b := by
    rw [Finset.sum_congr rfl (fun j _ ↦ sub_mul _ _ _), Finset.sum_sub_distrib]
    ring
  rw [hSplit, hBase, Finset.sum_congr rfl fun e _ ↦ hG e]
  have hLsum := Finset.sum_eq_zero (s := Finset.univ) fun j (_ : j ∈ Finset.univ) ↦ hL j
  rw [Finset.sum_add_distrib] at hLsum
  linarith

/-- **Linear equivalence along a target edge** (§7.4 and §8.2, Lemmas 7.2 and 7.3): a case of
`slidFibre_transport`. -/
theorem slidFibre_adjacent (hScale : memberScale mem = k) (r₁ r₂ : mem.target.V)
    (_h : 0 < num_edges mem.target r₁ r₂) :
    linear_equiv (M.small.scale k hk).graph (slidFibre k hk mem hClosed hScale r₁)
      (slidFibre k hk mem hClosed hScale r₂) :=
  slidFibre_transport k hk mem hClosed hScale r₁ r₂

/-- **The slid fibres form a linear system** (`slidFibre_transport`). -/
theorem slidFibre_linear_equiv (hScale : memberScale mem = k) (x x' : mem.target.V) :
    linear_equiv (M.small.scale k hk).graph (slidFibre k hk mem hClosed hScale x)
      (slidFibre k hk mem hClosed hScale x') :=
  slidFibre_transport k hk mem hClosed hScale x x'

/-- **The slid fibres** (§7.4: the discrete forms of Lemmas 7.2 and 7.3, and rank one on
`σ_{N₀}(G)`): the family `slidFibre`, assembled from `slidFibre_centre`,
`slidFibre_effective`, `slidFibre_linear_equiv` and `slidBase_le_slidFibre`. -/
theorem exists_slidPencil (hScale : memberScale mem = k) (_hOdd : mem.HasOddMult)
    (hClaw : MemberIsClaw mem) :
    ∃ Sl : mem.target.V → CFDiv (M.small.scale k hk).graph,
      Sl (TripodFrame.centreTarget (Frame.of mem)) =
          M.small.embed k hk (marksDiv M) + clawDivisor k hk mem hClosed hScale ∧
        (∀ x, effective (Sl x)) ∧
        (∀ x, linear_equiv (M.small.scale k hk).graph
          (Sl (TripodFrame.centreTarget (Frame.of mem))) (Sl x)) ∧
        ∀ x w, slidBase k hk mem hClosed hScale x w ≤ Sl x w :=
  ⟨slidFibre k hk mem hClosed hScale, slidFibre_centre k hk mem hClosed hScale hClaw,
    slidFibre_effective k hk mem hClosed hScale,
    slidFibre_linear_equiv k hk mem hClosed hScale _,
    slidBase_le_slidFibre k hk mem hClosed hScale⟩

/-! ### The degree of `F_k`: the jump rule and `k₀ = 0`

The slid fibres are linearly equivalent, so they have one degree: `δ_G(x) + Σ_j s_j·1[x ∈ H_j]`
is constant on the target (`jump_rule`). This is Lemma 4.1, `δ_Y(x) = k₀ + Σ_j s_j·1[x ∈ H_j]`,
read on `G′`, with `δ_G + δ_Y = 5`; its constant is `5 − k₀`, the degree of the repaired
morphism of Lemma 7.1. For a claw member `k₀ = 0` (`claw_kZero`), and at `φ(c)` the mark
coefficients add up to three (`markCoeff_centre`), so `δ_G(φ(c)) = 2` (`sum_gFibre`). -/

theorem deg_slidBase (hScale : memberScale mem = k) (x : mem.target.V) :
    deg (slidBase k hk mem hClosed hScale x) = ∑ raw, gFibre k hk mem x raw := by
  unfold slidBase
  rw [ExpansionSeriesMoment.deg_pushDivisor,
    deg_gPart_of_support M k hk _ (placedG_support k hk mem hClosed hScale x)]
  exact PendantDivisorTransport.push_degree (G := mem.data.sourceGraph)
    (H := (tripodSpec M k hk).graph) _ _

omit hClosed in
theorem deg_markCorrection (x : mem.target.V) :
    deg (∑ j, ((markCoeff mem x j : ℕ) : ℤ) • markChip k hk j :
      CFDiv (M.small.scale k hk).graph) = ∑ j, ((markCoeff mem x j : ℕ) : ℤ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, markChip, deg_one_chip, smul_eq_mul, mul_one]

include hClosed in
/-- **The jump rule** (Lemma 4.1, read on `G′`): the degree `δ_G(x)` of the `G′`-part of the
fibre over `x`, plus the mark coefficients `Σ_j s_j·1[x ∈ H_j]`, does not depend on `x`. It is
the constancy of the degree along the linear system of slid fibres (`slidFibre_transport`). -/
theorem jump_rule (hScale : memberScale mem = k) (x x' : mem.target.V) :
    ∑ raw, gFibre k hk mem x raw + ∑ j, ((markCoeff mem x j : ℕ) : ℤ) =
      ∑ raw, gFibre k hk mem x' raw + ∑ j, ((markCoeff mem x' j : ℕ) : ℤ) := by
  have h := linear_equiv_preserves_deg _ _ _ (slidFibre_transport k hk mem hClosed hScale x x')
  unfold slidFibre at h
  rw [deg.map_add, deg.map_add, deg_slidBase, deg_slidBase, deg_markCorrection,
    deg_markCorrection] at h
  exact h

/-- **`OnTripod` is the frame predicate `ClawShape.YCore`**: the centre, or a vertex of surviving
valency two on a leg row (an interior address of a leg row, `exists_interior_index`). -/
theorem onTripod_iff_yCore
    (s : {v : mem.data.SourceVertex // 0 < nonDanglingValency mem.data v}) :
    OnTripod mem s ↔ ClawShape.YCore (Frame.of mem) s.1 := by
  constructor
  · rintro (⟨h, hc⟩ | ⟨⟨L, i⟩, ha, hG⟩)
    · left
      show s.1 = (mem.ident.vertex.symm (centre 10)).1
      exact (congrArg Subtype.val ((Equiv.symm_apply_eq mem.ident.vertex).mpr hc.symm)).symm
    · right
      change ¬ IsGSlot (mem.ident.row L) at hG
      have hlt : i.val < (RowWalk.orderedRow mem.fullDim.pathEnds L).length := by
        have := i.isLt
        omega
      obtain ⟨hS, hPath⟩ := (RowWalk.mem_orderedRow_iff mem.fullDim.pathEnds L _).mp
        (List.getElem_mem hlt)
      refine ⟨ha ▸ addressVertex_valency mem.fullDim ⟨L, i⟩, ⟨_, hS⟩, ?_, ?_⟩
      · rw [ha]
        exact OrientedTraversal.walkVertex_succ_incident hlt
      · intro hG'
        apply hG
        rw [← hPath]
        exact hG'
  · rintro (hc | ⟨h2, e, he, hG⟩)
    · left
      have h3 : 3 ≤ nonDanglingValency mem.data s.1 := by
        rw [hc]
        exact (mem.ident.vertex.symm (centre 10)).2
      refine ⟨h3, ?_⟩
      have hb : (⟨s.1, h3⟩ : StableGraphIncidence.BranchVertex mem.data) =
          mem.ident.vertex.symm (centre 10) := Subtype.ext hc
      rw [hb, Equiv.apply_symm_apply]
    · right
      obtain ⟨i, hi⟩ := RowVertexEnumeration.exists_interior_index mem.fullDim e.stablePath h2
        ⟨e.2, rfl⟩ he
      exact ⟨⟨e.stablePath, i⟩, hi.symm, hG⟩

/-- `ClawShape.OverCentreY` on the member's own source vertices: a source vertex over `φ(c)` that
retracts onto the tripod. -/
def overCentreY (raw : mem.data.SourceVertex) : Prop :=
  ClawShape.OverCentreY (Frame.of mem) raw

/-- **`δ_G(φ(c)) = 2`** for a claw member (Corollary 4.10): the fibre over `φ(c)` has total index
five (`GluingDatum.sum_sourceVertex_localDegree_over`), and the part of it that retracts onto the
tripod has total index three (`ClawShape.sum_yCore_centre`). -/
theorem sum_gFibre_centre (hClaw : MemberIsClaw mem) :
    ∑ raw, gFibre k hk mem (TripodFrame.centreTarget (Frame.of mem)) raw = 2 := by
  classical
  set x : mem.target.V := TripodFrame.centreTarget (Frame.of mem) with hx
  have hTot : (∑ v : mem.data.SourceVertex,
      if v.1.1 = x then ((mem.data.vertexPartition v.1.1).blockCard v.1.2 : ℤ) else 0) = 5 := by
    convert GluingDatum.sum_sourceVertex_localDegree_over mem.data x
  have hY := ClawShape.sum_yCore_centre (Frame.of mem) M.connected hClaw
  change (∑ v : mem.data.SourceVertex, if overCentreY mem v then
    ((mem.data.vertexPartition v.1.1).blockCard v.1.2 : ℤ) else 0) = 3 at hY
  have hIff : ∀ raw : mem.data.SourceVertex,
      OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw) ↔
        ∃ w : mem.data.SourceVertex, 0 < nonDanglingValency mem.data w ∧
          ClawShape.YCore (Frame.of mem) w ∧
            PendantRetraction.retractVertex raw = PendantRetraction.retractVertex w := by
    intro raw
    rw [onTripod_iff_yCore]
    constructor
    · intro h
      exact ⟨_, (representative mem.fullDim.connected (survivor_exists mem) raw).2, h,
        CanonicalSurvivor.representative_class _ _ raw⟩
    · rintro ⟨w, hw, hYw, hR⟩
      rw [(representative_eq_iff mem.fullDim.connected (survivor_exists mem) raw ⟨w, hw⟩).mpr hR]
      exact hYw
  have hSplit : ∀ raw : mem.data.SourceVertex,
      (if raw.1.1 = x then ((mem.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0) =
        gFibre k hk mem x raw +
          (if overCentreY mem raw then
            ((mem.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0) := by
    intro raw
    have hOn := hIff raw
    unfold gFibre DegeneratePlacement.fibre
    by_cases h1 : raw.1.1 = x
    · by_cases h2 : OnTripod mem (representative mem.fullDim.connected (survivor_exists mem) raw)
      · have h3 : overCentreY mem raw := And.intro h1 (hOn.mp h2)
        simp only [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, zero_add]
      · have h3 : ¬ overCentreY mem raw := fun h ↦ h2 (hOn.mpr (And.right h))
        simp only [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3, add_zero]
    · have h3 : ¬ overCentreY mem raw := fun h ↦ h1 (And.left h)
      simp only [ite_eq_right h1, ite_eq_right h3, add_zero, ite_self]
  have hSum : (∑ raw : mem.data.SourceVertex,
      if raw.1.1 = x then ((mem.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0) =
      (∑ raw : mem.data.SourceVertex, gFibre k hk mem x raw) +
        ∑ raw : mem.data.SourceVertex, (if overCentreY mem raw then
          ((mem.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0) :=
    (Finset.sum_congr rfl fun raw _ ↦ hSplit raw).trans Finset.sum_add_distrib
  rw [hY, hTot] at hSum
  change (∑ raw : mem.data.SourceVertex, gFibre k hk mem x raw) = 2
  linarith

/-- **`k₀ = 0` for a claw member** (Corollary 4.10; Lemma 4.1 and Lemma 7.1), at `x = φ(c)`:
`δ_G(φ(c)) = 2` (`sum_gFibre_centre`) and the three mark coefficients there are one
(`markCoeff_centre`). Neither closedness nor long legs is used. -/
theorem claw_kZero (hClaw : MemberIsClaw mem) :
    ∃ x : mem.target.V,
      ∑ raw, gFibre k hk mem x raw + ∑ j, ((markCoeff mem x j : ℕ) : ℤ) = 3 + 2 := by
  refine ⟨TripodFrame.centreTarget (Frame.of mem), ?_⟩
  rw [sum_gFibre_centre k hk mem hClaw]
  simp only [markCoeff_centre mem hClaw, Nat.cast_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  norm_num

/-- **The degree of the `G′`-part over `φ(c)`** (Proposition 7.4, step 4): by
`jump_rule`, `claw_kZero` and `markCoeff_centre`, `δ_G(φ(c)) = 5 − 3 = m − 1 = 2`. (`gFibre`
does not depend on the scale, so the jump rule is read at `memberScale mem`.) -/
theorem sum_gFibre (hClosed₀ : mem.Closed) (hClaw : MemberIsClaw mem) :
    ∑ raw, gFibre k hk mem (TripodFrame.centreTarget (Frame.of mem)) raw = 2 := by
  obtain ⟨x₀, hx₀⟩ := claw_kZero (memberScale mem) (memberScale_pos mem) mem hClaw
  have hJ := jump_rule (memberScale mem) (memberScale_pos mem) mem hClosed₀ rfl x₀
    (TripodFrame.centreTarget (Frame.of mem))
  have hC : ∑ j, ((markCoeff mem (TripodFrame.centreTarget (Frame.of mem)) j : ℕ) : ℤ) = 3 := by
    simp only [markCoeff_centre mem hClaw, Nat.cast_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  have hk' : ∑ raw, gFibre k hk mem (TripodFrame.centreTarget (Frame.of mem)) raw =
      ∑ raw, gFibre (memberScale mem) (memberScale_pos mem) mem
        (TripodFrame.centreTarget (Frame.of mem)) raw := rfl
  rw [hk']
  push_cast at hx₀
  linarith

/-- **`deg F_k = 2`**, from `sum_gFibre`: `G′` is placed on G-positions (`placedG_support`), and
the restriction and the pushforwards keep degree. -/
theorem deg_clawDivisor (hScale : memberScale mem = k) (hClaw : MemberIsClaw mem) :
    deg (clawDivisor k hk mem hClosed hScale) = 2 := by
  unfold clawDivisor slidBase
  rw [ExpansionSeriesMoment.deg_pushDivisor,
    deg_gPart_of_support M k hk _
      (placedG_support k hk mem hClosed hScale (TripodFrame.centreTarget (Frame.of mem)))]
  exact (PendantDivisorTransport.push_degree (G := mem.data.sourceGraph)
    (H := (tripodSpec M k hk).graph) _ _).trans (sum_gFibre k hk mem hClosed hClaw)

/-- **Link (3): rank one on `M.small.scale k`**, from the slid fibres and the rank-determining
set: every point of `G` over a target vertex lies in the slid fibre over that vertex
(`exists_slidBase_pos` and the domination in `exists_slidPencil`), which is linearly equivalent to `embed (marks) + F_k`. -/
theorem rank_clawDivisor (hScale : memberScale mem = k) (hOdd : mem.HasOddMult)
    (hClaw : MemberIsClaw mem) :
    rank (M.small.scale k hk).graph
      (M.small.embed k hk (marksDiv M) + clawDivisor k hk mem hClosed hScale) ≥ 1 := by
  obtain ⟨Sl, h0, hEff, hLin, hDom⟩ := exists_slidPencil k hk mem hClosed hScale hOdd hClaw
  refine rankDetermining_gReach k hk mem hClosed hScale _ fun w hw ↦ ?_
  obtain ⟨x, hx⟩ := exists_slidBase_pos k hk mem hClosed hScale hw
  rw [← h0]
  exact winnable_sub_one_chip_of_linear_equiv (hEff x) (hLin x) (lt_of_lt_of_le hx (hDom x w))

end Construction

/-! ## 5.  The assembly -/

/-- **The realisation** (Proposition 7.4 and Theorem 7.5). A closed claw member of odd
multiplicity over the gadget, at the actual request of a tripod model of `(G, E)`, completes `E`
by two chips to a divisor of rank at least one on an odd regular subdivision of `G`; the scale is
the odd part `u` of `memberScale mem`. -/
theorem witness_of_closed_oddClaw {G : CFGraph.{0}}
    {E : CFDiv (UnitSubdivisionPresentation.spec G).graph} (M : TripodModel G E)
    (mem : FibreMember (tripodCore M.core M.slots) M.request (3 + 2))
    (hClosed : mem.Closed) (hOdd : mem.HasOddMult) (hClaw : MemberIsClaw mem) :
    ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
      ∃ F : CFDiv ((UnitSubdivisionPresentation.spec G).scale N hN).graph,
        effective F ∧ deg F = 2 ∧
          rank ((UnitSubdivisionPresentation.spec G).scale N hN).graph
            ((UnitSubdivisionPresentation.spec G).embed N hN E + F) ≥ 1 := by
  -- the same member, at the request in natural numbers
  set mem' := reMember mem with hmem'
  have hClosed' : mem'.Closed := hClosed
  have hOdd' : mem'.HasOddMult := hOdd
  have hClaw' : MemberIsClaw mem' := hClaw
  have hScaleEq : memberScale mem' = memberScale mem := rfl
  -- link (1)–(3): the odd part of the member's own scale
  obtain ⟨a, u, hOddU, hEq⟩ := Nat.exists_eq_two_pow_mul_odd (memberScale_pos mem').ne'
  have hu : 0 < u := hOddU.pos
  have hk : 0 < 2 ^ a * u := hEq ▸ memberScale_pos mem'
  -- links (5)–(6) on `M.small`, then the transport to `G`
  obtain ⟨F', hF', hdeg', hrank'⟩ := round_completion M.small M.smallMark u a hu hk
    (clawDivisor (2 ^ a * u) hk mem' hClosed' hEq)
    (clawDivisor_effective (2 ^ a * u) hk mem' hClosed' hEq)
    (deg_clawDivisor (2 ^ a * u) hk mem' hClosed' hEq hClaw')
    (fun j ↦ clawDivisor_moment (2 ^ a * u) hk mem' hClosed' hEq hOdd' a (Dvd.intro u rfl) j)
    (rank_clawDivisor (2 ^ a * u) hk mem' hClosed' hEq hOdd' hClaw')
  obtain ⟨F, hF, hdeg, hrank⟩ := transport_completion M u hu F' hF' hdeg' hrank'
  exact ⟨u, hu, hOddU, F, hF, hdeg, hrank⟩

end GenusSixExistence.Tripod.RealisationProof
