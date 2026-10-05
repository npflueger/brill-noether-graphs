module

public import DraismaVargasCount.W2M1kStarCensusProof
public import DraismaVargasCount.W2PStarExhaustionProof

@[expose] public section

/-!
# M-1k star exhaustion: the `w2M1k` clause with no hypothesis

Sources: Draisma–Vargas Part I, Case `{w2-r2-nd3-M-1k}`, Figure 33, Equation (7);
Vargas, Part II, the star of a wall.  The reduction completed here is
`W2M1kStarCensusProof.exhausts_of_transports` (Stage 2 reduced to decoupled transports);
the transport builder is `M11StarExhaustionProof.nonempty_transportFree_of_rel`.

## The result, in one paragraph

Every member of a `w2M1k` wall's star receives a `PositionTransport` onto a
**nonsingular** position of Equation (7) (`exists_receipt`), so the star is exhausted
(`exhausts`), and `FamilyStarParity … .w2M1k` holds **with no hypothesis**, at every
degree, core size and request (`familyStarParity_w2M1k_general`, `familyStarParity_w2M1k`).
A member `m` with limit isomorphism `ψ` gets the wall's W2 input, profile and M-1k `Shape`
pulled back along `ψ` (`input_pullback`, `W2PStarExhaustionProof.exists_profile_pullback`,
`shape_pullback`), with the pinned sheets carried by the two direction permutations
(`pin_map`).  Part I's census at `m` (`member_census`) says its normal form is Figure 33's
leaf, divided or joined member **of its own datum**; read through §2 each is a global
relation (`PairRel`, `Detach`, `Detach2`, or the wall partition).  The wall position of the
same kind receives it (`exists_transport`): over the limit along `ψ`, or, when that kind is
remote in the wall's orientation (a divided member at an aligned wall, a leaf member at a
separated one: alignment compares sheets of two different occurrences, so it depends on
the labelling and can differ across `ψ`), along `ψ` followed by the
branch swap, which moves the wall's pinned sheets onto the copy's
(`pinSheet_swapProfile`).  The builder applies with `τO = E₀`, `τF = E₁`, `τN = E₀`
followed by one transposition in the distinguished block (divided), or `τO = τN = E₀`
followed by a transposition, `τF = E₀` (leaf): the transposition absorbs the free choice of
`LeafPair`/`DividedData` on either side, so `Classical.choice` in `limitColumns` costs
nothing.  The member's own cover, lifted along the transport, presents the position, which
is therefore nonsingular (`nonsingular_of_transport`).

## What is proved

* §1 `Detach`, `Detach2`, `PairRel`; `pairBlock_rel_iff`, `detach_detachSheet_iff`,
  `detach_off`, `detach2_off`, `pairRel_off`, `rel_iff_of_block_eq`,
  `rel_iff_of_block_singleton`, `detachSheet_rel_iff`.
* §2 `leaf_left_rel`, `leaf_right_rel`, `leaf_new_rel`, `divided_left_rel`,
  `divided_right_rel`, `divided_new_rel`, `joined_shape` (at any datum).
* §3 `Agree`, `agree_edge`, `rel_of_agree`, `cross_rel`, `agree_swap`, `detach_refl`,
  `detach_rel`, `detach2_rel`, `detach_of`, `detach_transfer`, `detach2_transfer`,
  `side_star`, **`transport_divided`**, **`transport_leaf`** (along any datum isomorphism).
* §4 `shape_pullback`, `pin_map`.  §5 `member_census`.
* §6 `pinSheet_swapProfile`, `receipt_localLeaf`, `receipt_remoteLeaf`,
  `receipt_localDivided`, `receipt_remoteDivided`, `receipt_joined`.
* §7 `limitAnchor_aligned_iff`, `limitAnchor_separated_iff`, `exists_transport`,
  `nonsingular_of_fullDim`, `nonsingular_of_transport`, `exists_receipt`, `exhausts`;
  `w2M1kStarExhaustion`, `w2M1kStarCensus`, `familyStarParity_w2M1k_general`, and the
  headline **`familyStarParity_w2M1k`**.

## Scope

* Nothing is assumed: the headlines have no hypothesis beyond their binders.  `exhausts`
  does not use the `w2M1k` classification tag; it holds at every regrowth carrying a W2
  input, a W2R2 profile and an M-1k `Shape`.
* The strict transport `ResolutionExpansion.Transport` is not produced; the transports
  are decoupled `TransportFree`s, which is all `StarCensusEngine.cls_eq_of_transport`
  consumes.

## Consumers

`StarSupplyAssembly` takes the `w2M1k` clause `familyStarParity_w2M1k`, for the trivalent
wall step of `DraismaVargasCount.Assembly`.  `DraismaVargasCount.W2MkkStarExhaustionProof`
reuses the relations of §1 and the transport lemmas of §3.
-/

namespace DraismaVargas.Count.W2M1kStarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W2R1Target SecondEquation W4Assembly W2R2SourceProfile
open W2M1kSourceCandidates W2M1kLimitColumns W2M1kTransport
open ResolutionM11 (LocalResolution)
open W2M1kCommonBalance (LimitMember LimitColumns)
open M11StarExhaustionProof (blockPre blockPre_rel sourceVertexEquiv_blockPre blockCard_blockPre
  localRamification_blockPre nonDanglingValency_blockPre input_pullback wall_rel_iff
  wall_rel_iff_of_agree eq_edge_of_incident incident_of_edge nonempty_transportFree_of_rel
  nonempty_transportFree_joined JoinedShape)
open W3Nd2StarCensusProof (PlacementSpec memberResolution memberNorm)

/-! ## 1.  Three relations -/

section Relations

variable {d : ℕ}

/-- One sheet detached from its block. -/
def Detach (W : SheetPartition d) (s x y : Fin d) : Prop :=
  (x = s ∧ y = s) ∨ (x ≠ s ∧ y ≠ s ∧ W.Rel x y)

/-- Two sheets detached from their block. -/
def Detach2 (W : SheetPartition d) (s t x y : Fin d) : Prop :=
  (x = t ∧ y = t) ∨ (x ≠ t ∧ y ≠ t ∧ Detach W s x y)

/-- The discrete partition with one pair joined. -/
def PairRel (p q x y : Fin d) : Prop :=
  x = y ∨ (x = p ∧ y = q) ∨ (x = q ∧ y = p)

theorem rel_iff_of_block_eq {P Q : SheetPartition d} {x : Fin d}
    (h : P.block x = Q.block x) (y : Fin d) : P.Rel x y ↔ Q.Rel x y := by
  rw [← SheetPartition.mem_block_iff, h, SheetPartition.mem_block_iff]

theorem rel_iff_of_block_singleton {P : SheetPartition d} {x : Fin d}
    (h : P.block x = {x}) (y : Fin d) : P.Rel x y ↔ x = y := by
  rw [← SheetPartition.mem_block_iff, h, Finset.mem_singleton, eq_comm]

theorem detachSheet_rel_iff (W : SheetPartition d) (s r : Fin d) (hne : s ≠ r)
    (hTogether : W.Rel s r) (x y : Fin d) :
    (W.detachSheet s r hne hTogether).Rel x y ↔ Detach W s x y :=
  W2PStarExhaustionProof.detachSheet_rel_iff W s r hne hTogether x y

theorem pairBlock_rel_iff (W : SheetPartition d) (p q : Fin d) (hne : p ≠ q)
    (hpq : W.Rel p q) {x : Fin d} (hx : W.Rel p x) (y : Fin d) :
    (W.pairBlock p q hne).Rel x y ↔ PairRel p q x y := by
  classical
  have hr : ∀ z, W.Rel p z → (W.pairBlock p q hne).repr z = if z = q then p else z := by
    intro z hz
    by_cases hzq : z = q
    · subst hzq
      rw [ite_eq_left rfl]
      exact W.pairBlock_repr_second p z hne hpq
    · rw [ite_eq_right hzq]
      exact W.pairBlock_repr_of_rel_of_ne_second p q z hne hz hzq
  rw [SheetPartition.rel_iff]
  by_cases hy : W.Rel p y
  · rw [hr x hx, hr y hy]
    unfold PairRel
    by_cases hxq : x = q <;> by_cases hyq : y = q
    · rw [ite_eq_left hxq, ite_eq_left hyq]
      exact ⟨fun _ ↦ Or.inl (hxq.trans hyq.symm), fun _ ↦ rfl⟩
    · rw [ite_eq_left hxq, ite_eq_right hyq]
      constructor
      · intro h; exact Or.inr (Or.inr ⟨hxq, h.symm⟩)
      · rintro (h | ⟨-, h⟩ | ⟨-, h⟩)
        · exact absurd (h.symm.trans hxq) hyq
        · exact absurd h hyq
        · exact h.symm
    · rw [ite_eq_right hxq, ite_eq_left hyq]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨h, hyq⟩)
      · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
        · exact absurd (h.trans hyq) hxq
        · exact h
        · exact absurd h hxq
    · rw [ite_eq_right hxq, ite_eq_right hyq]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · exact absurd h hyq
        · exact absurd h hxq
  · rw [W.pairBlock_repr_of_not_rel p q y hne hy]
    have hNot : ¬ PairRel p q x y := by
      rintro (rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩)
      · exact hy hx
      · exact hy hpq
      · exact hy rfl
    refine ⟨fun h ↦ ?_, fun h ↦ (hNot h).elim⟩
    exfalso
    apply hy
    have hRx : W.Rel p ((W.pairBlock p q hne).repr x) := by
      rw [hr x hx]
      split_ifs
      · rfl
      · exact hx
    rw [h] at hRx
    exact hRx.trans (W.rel_repr_left y)

theorem detach_detachSheet_iff (W : SheetPartition d) (s t : Fin d) (hne : s ≠ t)
    (hT : W.Rel s t) (x y : Fin d) :
    Detach (W.detachSheet s t hne hT) t x y ↔ Detach2 W s t x y := by
  unfold Detach2
  constructor <;> rintro (h | ⟨h1, h2, h3⟩)
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, (detachSheet_rel_iff W s t hne hT x y).mp h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, (detachSheet_rel_iff W s t hne hT x y).mpr h3⟩

theorem detach_off {W : SheetPartition d} {A s x : Fin d} (hs : W.Rel A s)
    (hx : ¬ W.Rel A x) (y : Fin d) : Detach W s x y ↔ W.Rel x y := by
  have hxs : x ≠ s := fun h ↦ hx (h ▸ hs)
  constructor
  · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
    · exact (hxs h).elim
    · exact h
  · intro h
    exact Or.inr ⟨hxs, fun hys ↦ hx (hs.trans (hys ▸ h).symm), h⟩

theorem detach2_off {W : SheetPartition d} {A s t x : Fin d} (hs : W.Rel A s)
    (ht : W.Rel A t) (hx : ¬ W.Rel A x) (y : Fin d) : Detach2 W s t x y ↔ W.Rel x y := by
  have hxt : x ≠ t := fun h ↦ hx (h ▸ ht)
  unfold Detach2
  rw [detach_off hs hx]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
    · exact (hxt h).elim
    · exact h
  · intro h
    exact Or.inr ⟨hxt, fun hyt ↦ hx (ht.trans (hyt ▸ h).symm), h⟩

theorem pairRel_off {W : SheetPartition d} {A p q x : Fin d} (hp : W.Rel A p)
    (hq : W.Rel A q) (hx : ¬ W.Rel A x) (y : Fin d) : PairRel p q x y ↔ x = y := by
  have hxp : x ≠ p := fun h ↦ hx (h ▸ hp)
  have hxq : x ≠ q := fun h ↦ hx (h ▸ hq)
  constructor
  · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
    · exact h
    · exact (hxp h).elim
    · exact (hxq h).elim
  · exact Or.inl

end Relations

/-! ## 2.  Figure 33's pasted resolutions, as global relations

On `A₀` each member carries its selected local resolution, off `A₀` its background one
(`W2M1kIncomingMatching` §1); both halves read as one relation on all sheets. -/

section Pasted

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall} {profile : SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)

open M11StarCensusProof (pasted)

theorem leaf_left_rel (pair : LeafPair profile) (x y : Fin degree) :
    (pasted (LeafPair.candidate input shape pair)).left.Rel x y ↔
      PairRel (pinSheet profile 0) pair.second x y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · rw [rel_iff_of_block_eq (W2M1kIncomingMatching.leaf_pasted_left_selected input shape pair hx)]
    exact pairBlock_rel_iff _ _ _ pair.ne_second pair.rel_second
      ((pinSheet_rel 0).symm.trans hx) y
  · rw [rel_iff_of_block_singleton
      (W2M1kIncomingMatching.leaf_pasted_left_background input shape pair hx),
      pairRel_off (pinSheet_rel 0) ((pinSheet_rel 0).trans pair.rel_second) hx]

theorem leaf_right_rel (pair : LeafPair profile) (x y : Fin degree) :
    (pasted (LeafPair.candidate input shape pair)).right.Rel x y ↔
      Detach (data.vertexPartition wall) (pinSheet profile 0) x y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.leaf_pasted_right_selected input shape pair hx)]
    exact detachSheet_rel_iff _ _ _ pair.ne_second pair.rel_second x y
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.leaf_pasted_right_background input shape pair hx),
      detach_off (pinSheet_rel 0) hx]

theorem leaf_new_rel (pair : LeafPair profile) (x y : Fin degree) :
    (pasted (LeafPair.candidate input shape pair)).newEdge.Rel x y ↔ x = y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.leaf_pasted_newEdge_selected input shape pair hx)]
    exact rel_iff_of_block_singleton ((data.vertexPartition wall).splitBlock_block_of_rel _ x
      ((pinSheet_rel 0).symm.trans hx)) y
  · exact rel_iff_of_block_singleton
      (W2M1kIncomingMatching.leaf_pasted_newEdge_background input shape pair hx) y

theorem divided_left_rel (divided : DividedData profile) (x y : Fin degree) :
    (pasted (DividedData.candidate shape divided)).left.Rel x y ↔
      Detach (data.vertexPartition wall) (pinSheet profile 0) x y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.divided_pasted_left_selected shape divided hx)]
    exact detachSheet_rel_iff _ _ _ divided.pins_ne
      (W2M1kStableGraph.pin_rel_pin profile 0 1) x y
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.divided_pasted_left_background shape divided hx),
      detach_off (pinSheet_rel 0) hx]

theorem divided_right_rel (divided : DividedData profile) (x y : Fin degree) :
    (pasted (DividedData.candidate shape divided)).right.Rel x y ↔
      Detach (data.vertexPartition wall) (pinSheet profile 1) x y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.divided_pasted_right_selected shape divided hx)]
    exact detachSheet_rel_iff _ _ _ divided.pins_ne.symm
      (W2M1kStableGraph.pin_rel_pin profile 1 0) x y
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.divided_pasted_right_background shape divided hx),
      detach_off (pinSheet_rel 1) hx]

theorem divided_new_rel (divided : DividedData profile) (x y : Fin degree) :
    (pasted (DividedData.candidate shape divided)).newEdge.Rel x y ↔
      Detach2 (data.vertexPartition wall) (pinSheet profile 0) (pinSheet profile 1) x y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.divided_pasted_newEdge_selected shape divided hx)]
    exact (detachSheet_rel_iff _ _ _ divided.ne_second
      (ResolutionM1k.detachFirst_rel_second_third _ _ _ _
        (W2M1kStableGraph.pin_rel_pin profile 0 1) divided.rel_third divided.pins_ne
        divided.ne_first) x y).trans
      (detach_detachSheet_iff _ _ _ divided.pins_ne (W2M1kStableGraph.pin_rel_pin profile 0 1)
        x y)
  · rw [rel_iff_of_block_eq
      (W2M1kIncomingMatching.divided_pasted_newEdge_background shape divided hx),
      detach2_off (pinSheet_rel 0) (pinSheet_rel 1) hx]

theorem joined_shape (geometry : GlobalM1k.Geometry data wall) :
    JoinedShape (data.vertexPartition wall) (pasted (joinedCandidate star geometry)) where
  left x y := rel_iff_of_block_eq (W2M1kIncomingMatching.joined_pasted_left_block geometry x) y
  right x y := rel_iff_of_block_eq (W2M1kIncomingMatching.joined_pasted_right_block geometry x) y
  newEdge x y :=
    rel_iff_of_block_eq (W2M1kIncomingMatching.joined_pasted_newEdge_block geometry x) y

end Pasted

/-! ## 3.  Decoupled transports between two members of one kind

Along any datum isomorphism of two W2 walls carrying the two-stars onto each other, a
resolution of one Figure 33 kind is carried onto a resolution of the same kind as soon as
the pinned sheets correspond under the occurrence permutations `E₀`, `E₁` of the two wall
directions.  The builder `M11StarExhaustionProof.nonempty_transportFree_of_rel` applies
with `τO = E₀`, `τF = E₁` and `τN = E₀` followed by one transposition inside the
distinguished block (divided), or with `τO = τN = E₀` followed by a transposition and
`τF = E₀` (leaf). -/

section Transports

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (iso : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  (hWall : iso.targetVertex wall = wall')

/-- A permutation agrees with the wall permutation modulo the wall partition. -/
def Agree (τ : Equiv.Perm (Fin degree)) : Prop :=
  ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (τ s)) s

theorem agree_edge (star₁ : TwoStar target₁ wall) (label : Fin 2) :
    Agree iso (wall := wall) (iso.edgePerm (star₁.edge label)) :=
  fun s ↦ iso.compatible _ wall (incident_of_edge star₁ label) s

theorem rel_of_agree {τ σ : Equiv.Perm (Fin degree)} (hτ : Agree iso (wall := wall) τ)
    (hσ : Agree iso (wall := wall) σ) (s : Fin degree) :
    (first.vertexPartition wall).Rel (σ.symm (τ s)) s := by
  have h := hσ (σ.symm (τ s))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm.trans (hτ s)

include hWall in
theorem cross_rel {τ σ : Equiv.Perm (Fin degree)} (hτ : Agree iso (wall := wall) τ)
    (hσ : Agree iso (wall := wall) σ) (x y : Fin degree) :
    (second.vertexPartition wall').Rel (τ x) (σ y) ↔ (first.vertexPartition wall).Rel x y := by
  rw [wall_rel_iff iso hWall]
  exact ⟨fun h ↦ (hτ x).symm.trans (h.trans (hσ y)),
    fun h ↦ (hτ x).trans (h.trans (hσ y).symm)⟩

include hWall in
theorem agree_swap {τ : Equiv.Perm (Fin degree)} (hτ : Agree iso (wall := wall) τ)
    {u v : Fin degree} (huv : (second.vertexPartition wall').Rel u v) :
    Agree iso (wall := wall) (τ.trans (Equiv.swap u v)) := by
  intro s
  have hUV := (wall_rel_iff iso hWall u v).mp huv
  change (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (Equiv.swap u v (τ s))) s
  by_cases hu : τ s = u
  · rw [hu, Equiv.swap_apply_left]
    have h := hτ s
    rw [hu] at h
    exact hUV.symm.trans h
  · by_cases hv : τ s = v
    · rw [hv, Equiv.swap_apply_right]
      have h := hτ s
      rw [hv] at h
      exact hUV.trans h
    · rw [Equiv.swap_apply_of_ne_of_ne hu hv]
      exact hτ s

variable {d : ℕ}

theorem detach_refl (W : SheetPartition d) (p s : Fin d) : Detach W p s s := by
  by_cases h : s = p
  · exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, h, rfl⟩

theorem detach_rel {W : SheetPartition d} {p x y : Fin d} (h : Detach W p x y) : W.Rel x y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨-, -, h⟩
  · rfl
  · exact h

theorem detach2_rel {W : SheetPartition d} {p q x y : Fin d} (h : Detach2 W p q x y) :
    W.Rel x y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨-, -, h⟩
  · rfl
  · exact detach_rel h

theorem detach_of {W : SheetPartition d} {p t s : Fin d} (hts : W.Rel t s)
    (h : t = p ↔ s = p) : Detach W p t s := by
  by_cases hs : s = p
  · exact Or.inl ⟨h.mpr hs, hs⟩
  · exact Or.inr ⟨fun ht ↦ hs (h.mp ht), hs, hts⟩

include hWall in
theorem detach_transfer {τ : Equiv.Perm (Fin degree)} (hτ : Agree iso (wall := wall) τ)
    {p p' : Fin degree} (hp : τ p = p') (a b : Fin degree) :
    Detach (first.vertexPartition wall) p a b ↔
      Detach (second.vertexPartition wall') p' (τ a) (τ b) := by
  have hW := wall_rel_iff_of_agree iso hWall τ hτ a b
  subst hp
  unfold Detach
  rw [hW]
  simp only [ne_eq, τ.injective.eq_iff]

include hWall in
theorem detach2_transfer {τ : Equiv.Perm (Fin degree)} (hτ : Agree iso (wall := wall) τ)
    {p q p' q' : Fin degree} (hp : τ p = p') (hq : τ q = q') (a b : Fin degree) :
    Detach2 (first.vertexPartition wall) p q a b ↔
      Detach2 (second.vertexPartition wall') p' q' (τ a) (τ b) := by
  have hD := detach_transfer iso hWall hτ hp a b
  subst hq
  unfold Detach2
  rw [hD]
  simp only [ne_eq, τ.injective.eq_iff]

variable {star₁ : TwoStar target₁ wall} {star' : TwoStar target₂ wall'}
  (hStar : ∀ label, iso.targetEdge (star₁.edge label) = star'.edge label)

include hStar in
theorem side_star (edge : target₁.edges) :
    star'.right (iso.targetEdge edge) = star₁.right edge := by
  unfold TwoStar.right
  rw [← hStar 1]
  exact decide_eq_decide.mpr iso.targetEdge.injective.eq_iff

include hWall hStar in
/-- **Divided to divided.** -/
theorem transport_divided (res res' : LocalResolution degree) (p p' : Fin 2 → Fin degree)
    (hp : p 0 ≠ p 1) (hp' : p' 0 ≠ p' 1)
    (hPin : ∀ label, iso.edgePerm (star₁.edge label) (p label) = p' label)
    (hL : ∀ x y, res.left.Rel x y ↔ Detach (first.vertexPartition wall) (p 0) x y)
    (hR : ∀ x y, res.right.Rel x y ↔ Detach (first.vertexPartition wall) (p 1) x y)
    (hN : ∀ x y, res.newEdge.Rel x y ↔ Detach2 (first.vertexPartition wall) (p 0) (p 1) x y)
    (hL' : ∀ x y, res'.left.Rel x y ↔ Detach (second.vertexPartition wall') (p' 0) x y)
    (hR' : ∀ x y, res'.right.Rel x y ↔ Detach (second.vertexPartition wall') (p' 1) x y)
    (hN' : ∀ x y, res'.newEdge.Rel x y ↔
      Detach2 (second.vertexPartition wall') (p' 0) (p' 1) x y) :
    Nonempty (ResolutionExpansionFree.TransportFree iso wall wall' star₁.right star'.right
      res res') := by
  set E0 := iso.edgePerm (star₁.edge 0)
  set E1 := iso.edgePerm (star₁.edge 1)
  have hE0 : Agree iso (wall := wall) E0 := agree_edge iso star₁ 0
  have hE1 : Agree iso (wall := wall) E1 := agree_edge iso star₁ 1
  have hSwap : (second.vertexPartition wall').Rel (E0 (p 1)) (p' 1) := by
    rw [← hPin 1]
    exact (cross_rel iso hWall hE0 hE1 _ _).mpr rfl
  set τN := E0.trans (Equiv.swap (E0 (p 1)) (p' 1))
  have hτN : Agree iso (wall := wall) τN := agree_swap iso hWall hE0 hSwap
  have hN0 : τN (p 0) = p' 0 := by
    change Equiv.swap (E0 (p 1)) (p' 1) (E0 (p 0)) = p' 0
    rw [hPin 0]
    refine Equiv.swap_apply_of_ne_of_ne ?_ hp'
    rw [← hPin 0]
    exact fun h ↦ hp (E0.injective h)
  have hN1 : τN (p 1) = p' 1 := by
    change Equiv.swap (E0 (p 1)) (p' 1) (E0 (p 1)) = p' 1
    exact Equiv.swap_apply_left _ _
  refine nonempty_transportFree_of_rel iso wall wall' star₁.right star'.right res res' hWall
    (side_star iso hStar) (fun x y h ↦ detach_rel ((hL x y).mp h))
    (fun x y h ↦ detach_rel ((hR x y).mp h)) E0 E1 τN hE0 hE1 ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    rw [hL, hL', detach_transfer iso hWall hE0 (hPin 0)]
  · intro a b
    rw [hR, hR', detach_transfer iso hWall hE1 (hPin 1)]
  · intro a b
    rw [hN, hN', detach2_transfer iso hWall hτN hN0 hN1]
  · intro s
    rw [hL]
    refine detach_of (rel_of_agree iso hτN hE0 s) ?_
    rw [Equiv.symm_apply_eq, hPin 0, ← hN0, τN.injective.eq_iff]
  · intro s
    rw [hR]
    refine detach_of (rel_of_agree iso hτN hE1 s) ?_
    rw [Equiv.symm_apply_eq, hPin 1, ← hN1, τN.injective.eq_iff]
  · intro edge hInc s
    rcases eq_edge_of_incident star₁ edge hInc with rfl | rfl
    · rw [TwoStar.right_edge_zero]
      simp only [Bool.false_eq_true, ite_false]
      rw [Equiv.symm_apply_apply, hL]
      exact detach_refl _ _ _
    · rw [TwoStar.right_edge_one]
      simp only [ite_true]
      rw [Equiv.symm_apply_apply, hR]
      exact detach_refl _ _ _

include hWall in
/-- **Leaf to leaf.** -/
theorem transport_leaf (res res' : LocalResolution degree) (p q p' q' : Fin degree)
    (hpq : p ≠ q) (hpq' : p' ≠ q') (hW : (first.vertexPartition wall).Rel p q)
    (hPin : ∀ label, iso.edgePerm (star₁.edge label) p = p')
    (hL : ∀ x y, res.left.Rel x y ↔ PairRel p q x y)
    (hR : ∀ x y, res.right.Rel x y ↔ Detach (first.vertexPartition wall) p x y)
    (hN : ∀ x y, res.newEdge.Rel x y ↔ x = y)
    (hW' : (second.vertexPartition wall').Rel p' q')
    (hL' : ∀ x y, res'.left.Rel x y ↔ PairRel p' q' x y)
    (hR' : ∀ x y, res'.right.Rel x y ↔ Detach (second.vertexPartition wall') p' x y)
    (hN' : ∀ x y, res'.newEdge.Rel x y ↔ x = y) :
    Nonempty (ResolutionExpansionFree.TransportFree iso wall wall' (fun _ ↦ true)
      (fun _ ↦ true) res res') := by
  set E0 := iso.edgePerm (star₁.edge 0)
  have hE0 : Agree iso (wall := wall) E0 := agree_edge iso star₁ 0
  have hSwap : (second.vertexPartition wall').Rel (E0 q) q' := by
    refine Eq.trans ?_ hW'
    rw [← hPin 0]
    exact (cross_rel iso hWall hE0 hE0 _ _).mpr hW.symm
  set τO := E0.trans (Equiv.swap (E0 q) q')
  have hτO : Agree iso (wall := wall) τO := agree_swap iso hWall hE0 hSwap
  have hOp : τO p = p' := by
    change Equiv.swap (E0 q) q' (E0 p) = p'
    rw [hPin 0]
    refine Equiv.swap_apply_of_ne_of_ne ?_ hpq'
    rw [← hPin 0]
    exact fun h ↦ hpq (E0.injective h)
  have hOq : τO q = q' := by
    change Equiv.swap (E0 q) q' (E0 q) = q'
    exact Equiv.swap_apply_left _ _
  refine nonempty_transportFree_of_rel iso wall wall' (fun _ ↦ true) (fun _ ↦ true) res res'
    hWall (fun _ ↦ rfl) (fun x y h ↦ ?_) (fun x y h ↦ detach_rel ((hR x y).mp h))
    τO E0 τO hτO hE0 ?_ ?_ ?_ ?_ ?_ ?_
  · rcases (hL x y).mp h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hW
    · exact hW.symm
  · intro a b
    rw [hL, hL']
    unfold PairRel
    rw [← hOp, ← hOq, τO.injective.eq_iff, τO.injective.eq_iff, τO.injective.eq_iff,
      τO.injective.eq_iff, τO.injective.eq_iff]
  · intro a b
    rw [hR, hR', detach_transfer iso hWall hE0 (hPin 0)]
  · intro a b
    rw [hN, hN', τO.injective.eq_iff]
  · intro s
    rw [Equiv.symm_apply_apply, hL]
    exact Or.inl rfl
  · intro s
    rw [hR]
    refine detach_of (rel_of_agree iso hτO hE0 s) ?_
    rw [Equiv.symm_apply_eq, hPin 0, ← hOp, τO.injective.eq_iff]
  · intro edge hInc s
    rw [ite_eq_left rfl, ite_eq_left rfl, hR]
    rcases eq_edge_of_incident star₁ edge hInc with rfl | rfl
    · refine detach_of (rel_of_agree iso (agree_edge iso star₁ 0) hE0 s) ?_
      rw [Equiv.symm_apply_eq, hPin 0, ← hPin 0, E0.injective.eq_iff]
    · refine detach_of (rel_of_agree iso (agree_edge iso star₁ 1) hE0 s) ?_
      rw [Equiv.symm_apply_eq, hPin 0, ← hPin 1, (iso.edgePerm (star₁.edge 1)).injective.eq_iff]

end Transports

/-! ## 4.  The M-1k shape and the pinned sheets, pulled back along a datum isomorphism -/

section Pullback

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- **The M-1k shape pulls back**: `k`, the block size, the dangling direction and the unit
index are all carried by the datum isomorphism. -/
def shape_pullback (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : TwoStar target₂ wall'} {block' : WallBlock second wall'}
    {profile : SourceProfile second star' block'} (shape : Shape profile)
    (profile₁ : SourceProfile first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star')
      (blockPre iso wall block'.1))
    (hSingle : profile₁.singleLabel = profile.singleLabel)
    (hFirst : iso.sourceEdgeEquiv profile₁.first.1 = profile.first.1)
    (hDeleted : iso.sourceEdgeEquiv profile₁.deleted.edge.1 = profile.deleted.edge.1) :
    Shape profile₁ where
  k := shape.k
  one_lt_k := shape.one_lt_k
  blockCard := (blockCard_blockPre iso hWall block'.1).trans shape.blockCard
  deleted_single := by
    apply iso.targetEdge.injective
    rw [M11WallExhaustion.pullbackTwoStar_edge, hSingle, ← shape.deleted_single, ← hDeleted]
    rfl
  unit_index := by
    rw [← iso.sourceEdgeIndex_map, hFirst]
    exact shape.unit_index

/-- **The pinned sheets correspond** under the occurrence permutations of the two wall
directions. -/
theorem pin_map (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V}
    {star₁ : TwoStar target₁ wall} {star' : TwoStar target₂ wall'}
    {block₁ : WallBlock first wall} {block' : WallBlock second wall'}
    {profile₁ : SourceProfile first star₁ block₁} {profile : SourceProfile second star' block'}
    (shape₁ : Shape profile₁)
    (hDouble : profile₁.doubleLabel = profile.doubleLabel)
    (hFirst : iso.sourceEdgeEquiv profile₁.first.1 = profile.first.1)
    (hDeleted : iso.sourceEdgeEquiv profile₁.deleted.edge.1 = profile.deleted.edge.1)
    (label : Fin 2) :
    iso.edgePerm (star₁.edge label) (pinSheet profile₁ label) = pinSheet profile label := by
  have hOcc : iso.sourceEdgeEquiv (pinnedOccurrence profile₁ label).1 =
      (pinnedOccurrence profile label).1 := by
    unfold pinnedOccurrence
    by_cases h : label = profile.doubleLabel
    · rw [ite_eq_left (h.trans hDouble.symm), ite_eq_left h]
      exact hFirst
    · rw [ite_eq_right (fun h' ↦ h (h'.trans hDouble)), ite_eq_right h]
      exact hDeleted
  rw [← pinnedOccurrence_target shape₁ label]
  exact congrArg (fun e : second.SourceEdge ↦ e.1.2) hOcc

end Pullback

/-! ## 5.  Part I's census at an arbitrary member, as relations

At a regrowth `mem` carrying a W2 input and an M-1k profile and shape on its own limit,
Part I's incoming census says its own normal form is one of Figure 33's three members:
`M⁽¹⁾` at the constant placement (a leaf endpoint,
`W2M1kSelectedCensus.exists_selectedCensus_leaf`),
or `M⁽²⁾` or `M⁽³⁾` at the star's placement (`selectedCensus_dichotomy_of_dividedData`,
`selectedCensus_of_aligned`).  Read through §2, the three resolutions are the three
relational shapes of §3. -/

section MemberCensus

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

open M11StarCensusProof (pasted)

/-- **The member's own normal form is one of Figure 33's three members**, as relations. -/
theorem member_census (mem : Regrowth core y degree) (hy : Nondegenerate y)
    {star : TwoStar (mem.frame.limitTarget mem.column) (mergeVertex mem)}
    (input : W2SourceInput mem.limit star) {block : WallBlock mem.limit (mergeVertex mem)}
    {profile : SourceProfile mem.limit star block} (shape : Shape profile) :
    (∃ hP : PlacementSpec mem (fun _ ↦ true), ∃ pair : LeafPair profile,
      (∀ x y, (memberResolution mem _ hP).left.Rel x y ↔
        PairRel (pinSheet profile 0) pair.second x y) ∧
      (∀ x y, (memberResolution mem _ hP).right.Rel x y ↔
        Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile 0) x y) ∧
      (∀ x y, (memberResolution mem _ hP).newEdge.Rel x y ↔ x = y)) ∨
    (∃ hP : PlacementSpec mem star.right, ∃ _ : DividedData profile,
      (∀ x y, (memberResolution mem _ hP).left.Rel x y ↔
        Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile 0) x y) ∧
      (∀ x y, (memberResolution mem _ hP).right.Rel x y ↔
        Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile 1) x y) ∧
      (∀ x y, (memberResolution mem _ hP).newEdge.Rel x y ↔
        Detach2 (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile 0)
          (pinSheet profile 1) x y)) ∨
    (∃ hP : PlacementSpec mem star.right,
      JoinedShape (mem.limit.vertexPartition (mergeVertex mem)) (memberResolution mem _ hP)) := by
  have hForest := InheritedLimitRows.forest mem hy
  have hBackground := W2M1kClosureUnconditional.wall_background mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) input
    profile
  have hNewOf : ∀ (placement : (mem.frame.limitTarget mem.column).edges → Bool)
      (hP : PlacementSpec mem placement),
      (memberResolution mem placement hP).newEdge =
        mem.frame.data.edgePartition (mem.frame.edgeOf mem.column) :=
    fun placement hP ↦ M11IncomingOuterPartitions.transported_edgePartition_new mem.frame.data
      rfl (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      placement hP mem.frame.fullDim.targetConnected mem.frame.fullDim.targetGenus
  -- the joined branch, shared by the aligned and the divided `T₂` cases
  have hJoined : ∀ (hLeftCard : (GluingDatum.incidentEdges
        (mem.frame.edgeOf mem.column : mem.frame.target.V × mem.frame.target.V).1).card = 2)
      (hRightCard : (GluingDatum.incidentEdges
        (mem.frame.edgeOf mem.column : mem.frame.target.V × mem.frame.target.V).2).card = 2)
      (geometry : GlobalM1k.Geometry mem.limit (mergeVertex mem))
      (selected : W2M1kIncomingMatching.SelectedCensus mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) block
        (W2M1kIncomingCensus.zeroEnd rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
          (mem.frame.numEdges_edgeOf mem.column) star)
        (W2M1kIncomingCensus.oneEnd rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
          (mem.frame.numEdges_edgeOf mem.column) star)
        (ContractionRamification.mergedPartition mem.frame.data
          (mem.frame.edgeOf mem.column : mem.frame.target.V × mem.frame.target.V).1
          (mem.frame.edgeOf mem.column : mem.frame.target.V × mem.frame.target.V).2)
        (ContractionRamification.mergedPartition mem.frame.data
          (mem.frame.edgeOf mem.column : mem.frame.target.V × mem.frame.target.V).1
          (mem.frame.edgeOf mem.column : mem.frame.target.V × mem.frame.target.V).2)
        (ContractionRamification.mergedPartition mem.frame.data
          (mem.frame.edgeOf mem.column : mem.frame.target.V × mem.frame.target.V).1
          (mem.frame.edgeOf mem.column : mem.frame.target.V × mem.frame.target.V).2)),
      ∃ hP : PlacementSpec mem star.right,
        JoinedShape (mem.limit.vertexPartition (mergeVertex mem)) (memberResolution mem _ hP) := by
    intro hLeftCard hRightCard geometry selected
    have hP : PlacementSpec mem star.right :=
      W2M1kIncomingMatching.joinedPlacement mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        geometry hLeftCard hRightCard
    obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := W2M1kIncomingMatching.joined_wall_blocks
      mem.frame.data rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
      (mem.frame.numEdges_edgeOf mem.column) mem.frame.fullDim hForest input profile hBackground
      hLeftCard hRightCard geometry selected
    obtain ⟨hOld, hFresh⟩ := W2M1kIncomingCensus.transported_endpoints mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
      hLeftCard hRightCard hP
    have hS := joined_shape (star := star) geometry
    refine ⟨hP, ⟨fun x y ↦ ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩⟩
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hOld)).trans
        ((rel_iff_of_block_eq (hLeftWall x) y).trans (hS.left x y))
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hFresh)).trans
        ((rel_iff_of_block_eq (hRightWall x) y).trans (hS.right x y))
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) (hNewOf _ hP))).trans
        ((rel_iff_of_block_eq (hNewWall x) y).trans (hS.newEdge x y))
  rcases W2M1kClosureUnconditional.headline_cases mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      mem.frame.fullDim profile shape with
    ⟨-, hLeaf⟩ | ⟨⟨pair⟩, hLeftCard, hRightCard⟩ | ⟨⟨divided⟩, hLeftCard, hRightCard⟩
  · obtain ⟨pair, selected⟩ := W2M1kSelectedCensus.exists_selectedCensus_leaf mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      mem.frame.fullDim profile shape hLeaf
    have hP : PlacementSpec mem (fun _ ↦ true) :=
      W2M1kIncomingMatching.leafPlacement mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) input
        profile shape pair hLeaf
    obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := W2M1kIncomingMatching.leaf_wall_blocks
      mem.frame.data rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
      (mem.frame.numEdges_edgeOf mem.column) input profile shape pair selected
      (W2M1kLeafBackground.leafBackgroundCensus mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        mem.frame.fullDim hForest input profile hLeaf)
    obtain ⟨hOld, hFresh⟩ := W2M1kIncomingCensus.leaf_transported_endpoints mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
      hLeaf hP
    refine Or.inl ⟨hP, pair, fun x y ↦ ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hOld)).trans
        ((rel_iff_of_block_eq (hLeftWall x) y).trans (leaf_left_rel input shape pair x y))
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hFresh)).trans
        ((rel_iff_of_block_eq (hRightWall x) y).trans (leaf_right_rel input shape pair x y))
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) (hNewOf _ hP))).trans
        ((rel_iff_of_block_eq (hNewWall x) y).trans (leaf_new_rel input shape pair x y))
  · exact Or.inr (Or.inr (hJoined hLeftCard hRightCard (pair.geometry shape)
      (W2M1kSelectedCensus.selectedCensus_of_aligned mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        mem.frame.fullDim hForest profile shape pair.aligned hLeftCard hRightCard)))
  · rcases W2M1kSelectedCensus.selectedCensus_dichotomy_of_dividedData mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        mem.frame.fullDim hForest profile shape divided hLeftCard hRightCard with
      selected | selected
    · have hP : PlacementSpec mem star.right :=
        W2M1kIncomingMatching.dividedPlacement mem.frame.data rfl
          (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
          profile shape divided hLeftCard hRightCard
      obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := W2M1kIncomingMatching.divided_wall_blocks
        mem.frame.data rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
        (mem.frame.numEdges_edgeOf mem.column) mem.frame.fullDim hForest input profile
        hBackground hLeftCard hRightCard shape divided selected
      obtain ⟨hOld, hFresh⟩ := W2M1kIncomingCensus.transported_endpoints mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
        hLeftCard hRightCard hP
      refine Or.inr (Or.inl ⟨hP, divided, fun x y ↦ ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩)
      · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hOld)).trans
          ((rel_iff_of_block_eq (hLeftWall x) y).trans (divided_left_rel shape divided x y))
      · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hFresh)).trans
          ((rel_iff_of_block_eq (hRightWall x) y).trans (divided_right_rel shape divided x y))
      · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y)
          (hNewOf _ hP))).trans
          ((rel_iff_of_block_eq (hNewWall x) y).trans (divided_new_rel shape divided x y))
    · exact Or.inr (Or.inr (hJoined hLeftCard hRightCard (divided.geometry shape) selected))

end MemberCensus

/-! ## 6.  Transports onto the five anchored members of the wall

A member `mem` with limit isomorphism `ψ`, whose own profile is the wall's pulled back
(`hW`, `hStar`, `hPin`), is carried onto the wall member of its own kind: over the limit
along `ψ` itself, at the remote position along `ψ` followed by the branch swap, which moves
the wall's pinned sheets onto the copy's (`pinSheet_swapProfile`). -/

section Receipts

/-- The branch swap moves each pinned sheet by its own direction's occurrence
permutation. -/
theorem pinSheet_swapProfile {target : CFGraph} {degree : ℕ} {wall : target.V}
    {data : GluingDatum target degree} {star : TwoStar target wall}
    {block : WallBlock data wall} {profile : SourceProfile data star block}
    (shape : Shape profile) (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other) (label : Fin 2) :
    pinSheet (swapProfile profile hConnected other hOther) label =
      (swapRelabeling profile other hOther).edgePermutation (star.edge label)
        (pinSheet profile label) := by
  rw [← pinnedOccurrence_target shape label]
  unfold pinSheet pinnedOccurrence
  by_cases h : label = profile.doubleLabel
  · rw [ite_eq_left h, ite_eq_left (show label = (swapProfile profile hConnected other hOther).doubleLabel
      from h)]
    rfl
  · rw [ite_eq_right h, ite_eq_right (show ¬ label = (swapProfile profile hConnected other hOther).doubleLabel
      from h)]
    rfl

open W2M1kStarCensusProof

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} {hy : Nondegenerate y}
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  {mem : Regrowth core y degree} (ψ : GeometricStar.LimitIso hy mem w)
  {star₁ : TwoStar (mem.frame.limitTarget mem.column) (mergeVertex mem)}
  {block₁ : WallBlock mem.limit (mergeVertex mem)}
  {profile₁ : SourceProfile mem.limit star₁ block₁}
  (hW : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetVertex (mergeVertex mem) =
    mergeVertex w)
  (hStar : ∀ label, (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetEdge
    (star₁.edge label) = star.edge label)
  (hPin : ∀ label, (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
    (star₁.edge label) (pinSheet profile₁ label) = pinSheet profile label)
  (res : LocalResolution degree)

include hW hPin in
/-- **Leaf onto the leaf member over the limit.** -/
theorem receipt_localLeaf (pair₀ : LeafPair profile) (pair₁ : LeafPair profile₁)
    (hL : ∀ x y, res.left.Rel x y ↔ PairRel (pinSheet profile₁ 0) pair₁.second x y)
    (hR : ∀ x y, res.right.Rel x y ↔
      Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁ 0) x y)
    (hN : ∀ x y, res.newEdge.Rel x y ↔ x = y) :
    Nonempty (ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (localLeafAnchor input shape pair₀).φ.symm) (mergeVertex mem)
      (mergeVertex w) (fun _ ↦ true) (localLeafMember input shape pair₀).right res
      (localLeafAnchor input shape pair₀).res) := by
  refine transport_leaf (ψ.datum.trans (localLeafAnchor input shape pair₀).φ.symm) hW
    (star₁ := star₁) res (localLeafAnchor input shape pair₀).res (pinSheet profile₁ 0)
    pair₁.second (pinSheet profile 0) pair₀.second pair₁.ne_second pair₀.ne_second
    pair₁.rel_second ?_ hL hR hN pair₀.rel_second (leaf_left_rel input shape pair₀)
    (leaf_right_rel input shape pair₀) (leaf_new_rel input shape pair₀)
  intro label
  have h := hPin label
  fin_cases label
  · exact h
  · change _ = pinSheet profile 1 at h
    rw [pair₁.aligned, pair₀.aligned]
    exact h

include hW hStar hPin in
/-- **Leaf onto the remote leaf member** over the branch-swapped copy. -/
theorem receipt_remoteLeaf (other : Fin degree)
    (hOther : (w.limit.vertexPartition (mergeVertex w)).Rel (pinSheet profile 0) other)
    (pairR : LeafPair (swapProfile profile input.valid.1 other hOther))
    (pair₁ : LeafPair profile₁)
    (hL : ∀ x y, res.left.Rel x y ↔ PairRel (pinSheet profile₁ 0) pair₁.second x y)
    (hR : ∀ x y, res.right.Rel x y ↔
      Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁ 0) x y)
    (hN : ∀ x y, res.newEdge.Rel x y ↔ x = y) :
    Nonempty (ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (remoteLeafAnchor input shape other hOther pairR).φ.symm) (mergeVertex mem)
      (mergeVertex w) (fun _ ↦ true) (remoteLeafMember input shape other hOther pairR).right res
      (remoteLeafAnchor input shape other hOther pairR).res) := by
  refine transport_leaf (ψ.datum.trans (remoteLeafAnchor input shape other hOther pairR).φ.symm)
    hW (star₁ := star₁) res (remoteLeafAnchor input shape other hOther pairR).res
    (pinSheet profile₁ 0) pair₁.second
    (pinSheet (swapProfile profile input.valid.1 other hOther) 0) pairR.second pair₁.ne_second
    pairR.ne_second pair₁.rel_second ?_ hL hR hN pairR.rel_second
    (leaf_left_rel (swapInput input other hOther) (swapShape shape input.valid.1 other hOther)
      pairR)
    (leaf_right_rel (swapInput input other hOther) (swapShape shape input.valid.1 other hOther)
      pairR)
    (leaf_new_rel (swapInput input other hOther) (swapShape shape input.valid.1 other hOther)
      pairR)
  intro label
  change (swapRelabeling profile other hOther).edgePermutation
    ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetEdge (star₁.edge label))
    ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm (star₁.edge label)
      (pinSheet profile₁ 0)) = _
  have hAligned₁ : pinSheet profile₁ 0 = pinSheet profile₁ label := by
    fin_cases label
    · rfl
    · exact pair₁.aligned
  rw [hStar label, hAligned₁, hPin label,
    ← pinSheet_swapProfile shape input.valid.1 other hOther label]
  fin_cases label
  · rfl
  · exact pairR.aligned.symm

include hW hStar hPin in
/-- **Divided onto the divided member over the limit.** -/
theorem receipt_localDivided (divided₀ : DividedData profile)
    (hp : pinSheet profile₁ 0 ≠ pinSheet profile₁ 1)
    (hL : ∀ x y, res.left.Rel x y ↔
      Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁ 0) x y)
    (hR : ∀ x y, res.right.Rel x y ↔
      Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁ 1) x y)
    (hN : ∀ x y, res.newEdge.Rel x y ↔
      Detach2 (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁ 0)
        (pinSheet profile₁ 1) x y) :
    Nonempty (ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (localDividedAnchor input shape divided₀).φ.symm) (mergeVertex mem)
      (mergeVertex w) star₁.right (localDividedMember input shape divided₀).right res
      (localDividedAnchor input shape divided₀).res) :=
  transport_divided (ψ.datum.trans (localDividedAnchor input shape divided₀).φ.symm) hW
    hStar res (localDividedAnchor input shape divided₀).res (pinSheet profile₁)
    (pinSheet profile) hp divided₀.pins_ne hPin hL hR hN (divided_left_rel shape divided₀)
    (divided_right_rel shape divided₀) (divided_new_rel shape divided₀)

include hW hStar hPin in
/-- **Divided onto the remote divided member** over the branch-swapped copy. -/
theorem receipt_remoteDivided (other : Fin degree)
    (hOther : (w.limit.vertexPartition (mergeVertex w)).Rel (pinSheet profile 0) other)
    (dividedR : DividedData (swapProfile profile input.valid.1 other hOther))
    (hp : pinSheet profile₁ 0 ≠ pinSheet profile₁ 1)
    (hL : ∀ x y, res.left.Rel x y ↔
      Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁ 0) x y)
    (hR : ∀ x y, res.right.Rel x y ↔
      Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁ 1) x y)
    (hN : ∀ x y, res.newEdge.Rel x y ↔
      Detach2 (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁ 0)
        (pinSheet profile₁ 1) x y) :
    Nonempty (ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (remoteDividedAnchor input shape other hOther dividedR).φ.symm)
      (mergeVertex mem) (mergeVertex w) star₁.right
      (remoteDividedMember input shape other hOther dividedR).right res
      (remoteDividedAnchor input shape other hOther dividedR).res) := by
  refine transport_divided
    (ψ.datum.trans (remoteDividedAnchor input shape other hOther dividedR).φ.symm) hW hStar res
    (remoteDividedAnchor input shape other hOther dividedR).res (pinSheet profile₁)
    (pinSheet (swapProfile profile input.valid.1 other hOther)) hp dividedR.pins_ne ?_ hL hR hN
    (divided_left_rel (swapShape shape input.valid.1 other hOther) dividedR)
    (divided_right_rel (swapShape shape input.valid.1 other hOther) dividedR)
    (divided_new_rel (swapShape shape input.valid.1 other hOther) dividedR)
  intro label
  change (swapRelabeling profile other hOther).edgePermutation
    ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetEdge (star₁.edge label))
    ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm (star₁.edge label)
      (pinSheet profile₁ label)) = _
  rw [hStar label, hPin label, ← pinSheet_swapProfile shape input.valid.1 other hOther label]

include hW hStar in
/-- **Joined onto the joined member.** -/
theorem receipt_joined (geometry : GlobalM1k.Geometry w.limit (mergeVertex w))
    (hS : JoinedShape (mem.limit.vertexPartition (mergeVertex mem)) res) :
    Nonempty (ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (joinedAnchor input shape geometry).φ.symm) (mergeVertex mem)
      (mergeVertex w) star₁.right (joinedMember input shape geometry).right res
      (joinedAnchor input shape geometry).res) :=
  nonempty_transportFree_joined (ψ.datum.trans (joinedAnchor input shape geometry).φ.symm)
    (mergeVertex mem) (mergeVertex w) star₁.right (joinedMember input shape geometry).right res
    (joinedAnchor input shape geometry).res hW (side_star _ hStar) hS
    (joined_shape (star := star) geometry)

end Receipts

/-! ## 7.  Exhaustion, and the family clause -/

section Exhaustion

open W2M1kStarCensusProof

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)

/-- At an aligned wall, a statement about a position's anchor is one about the aligned
orientation's. -/
theorem limitAnchor_aligned_iff (hAligned : pinSheet profile 0 = pinSheet profile 1)
    (j : Fin 3) (F : ∀ m : LimitMember w.limit (mergeVertex w), Anchor w m → Prop) :
    F _ (limitAnchor input shape j) ↔
      F _ (alignedAnchor input shape (exists_leafPair shape hAligned).some j) := by
  unfold limitAnchor
  rw [dite_eq_left hAligned]
  exact anchorOf_iff shape _ _ j F

/-- At a separated wall, a statement about a position's anchor is one about the separated
orientation's. -/
theorem limitAnchor_separated_iff (hSeparated : ¬ pinSheet profile 0 = pinSheet profile 1)
    (j : Fin 3) (F : ∀ m : LimitMember w.limit (mergeVertex w), Anchor w m → Prop) :
    F _ (limitAnchor input shape j) ↔
      F _ (separatedAnchor input shape (exists_dividedData shape hSeparated).some j) := by
  unfold limitAnchor
  rw [dite_eq_right hSeparated]
  exact anchorOf_iff shape _ _ j F

/-- **Every star member presents a transport onto the position of its own kind.** -/
theorem exists_transport (mem : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy mem w) :
    ∃ placement : (mem.frame.limitTarget mem.column).edges → Bool,
    ∃ hPlacement : PlacementSpec mem placement, ∃ j : Fin 3,
      Nonempty (PositionTransport w hy input shape mem ψ placement hPlacement j) := by
  have hW : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetVertex
      (mergeVertex mem) = mergeVertex w :=
    M11StarCensusProof.pinned w hy input mem ψ
  have input₁ := input_pullback _ hW input
  obtain ⟨profile₁, hDouble, hSingle, hFirst, -, -, hDeleted⟩ :=
    W2PStarExhaustionProof.exists_profile_pullback _ (InheritedLimitRows.limit_connected mem) hW
      profile
  have shape₁ := shape_pullback _ hW shape profile₁ hSingle hFirst hDeleted
  have hPin := pin_map _ shape₁ hDouble hFirst hDeleted
  have hStar := M11WallExhaustion.pullbackTwoStar_edge _ (mergeVertex mem) (mergeVertex w) hW star
  have hC := RegrowthBalances.limit_connected w
  have hG := RegrowthBalances.limit_genus w
  rcases member_census mem hy input₁ shape₁ with
    ⟨hP, pair₁, hL, hR, hN⟩ | ⟨hP, divided₁, hL, hR, hN⟩ | ⟨hP, hS⟩
  · refine ⟨_, hP, 0, ?_⟩
    by_cases hA : pinSheet profile 0 = pinSheet profile 1
    · exact (limitAnchor_aligned_iff w input shape hA 0 (fun m A ↦
        Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
          (mergeVertex mem) (mergeVertex w) (fun _ ↦ true) m.right
          (memberResolution mem _ hP) A.res))).mpr
        (receipt_localLeaf input shape ψ hW hPin _ _ pair₁ hL hR hN)
    · exact (limitAnchor_separated_iff w input shape hA 0 (fun m A ↦
        Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
          (mergeVertex mem) (mergeVertex w) (fun _ ↦ true) m.right
          (memberResolution mem _ hP) A.res))).mpr
        (receipt_remoteLeaf input shape ψ hW hStar hPin _ (pinSheet profile 1)
          (W2SourceTransport.alignedTogether profile) (remoteLeaf input shape hC hG) pair₁
          hL hR hN)
  · refine ⟨_, hP, 1, ?_⟩
    by_cases hA : pinSheet profile 0 = pinSheet profile 1
    · exact (limitAnchor_aligned_iff w input shape hA 1 (fun m A ↦
        Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
          (mergeVertex mem) (mergeVertex w) _ m.right
          (memberResolution mem _ hP) A.res))).mpr
        (receipt_remoteDivided input shape ψ hW hStar hPin _ _ _
          (remoteDivided input shape (exists_leafPair shape hA).some hC hG) divided₁.pins_ne
          hL hR hN)
    · exact (limitAnchor_separated_iff w input shape hA 1 (fun m A ↦
        Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
          (mergeVertex mem) (mergeVertex w) _ m.right
          (memberResolution mem _ hP) A.res))).mpr
        (receipt_localDivided input shape ψ hW hStar hPin _ _ divided₁.pins_ne hL hR hN)
  · refine ⟨_, hP, 2, ?_⟩
    by_cases hA : pinSheet profile 0 = pinSheet profile 1
    · exact (limitAnchor_aligned_iff w input shape hA 2 (fun m A ↦
        Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
          (mergeVertex mem) (mergeVertex w) _ m.right
          (memberResolution mem _ hP) A.res))).mpr
        (receipt_joined input shape ψ hW hStar _ _ hS)
    · exact (limitAnchor_separated_iff w input shape hA 2 (fun m A ↦
        Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
          (mergeVertex mem) (mergeVertex w) _ m.right
          (memberResolution mem _ hP) A.res))).mpr
        (receipt_joined input shape ψ hW hStar _ _ hS)

variable (initial : StableLengthMatrixLabelling ((columns input shape).member 0).datum (Fin p))

/-- **Any full-dimensional presentation of a position's datum makes the position
nonsingular** at Equation (7)'s labelling: the two labellings differ by a row and a column
permutation. -/
theorem nonsingular_of_fullDim (j : Fin 3)
    (fd : FullDimensionalSourcePresentation ((columns input shape).member j).datum (Fin p)) :
    Nonsingular w input shape initial j := by
  classical
  unfold Nonsingular
  change (GluingDatum.LengthMatrixPresentation.matrix
    (lab w input shape initial j).presentation).det ≠ 0
  rw [DraismaVargas.Count.matrix_labelling_submatrix (lab w input shape initial j) fd.labelling]
  intro h
  have hAbs := Matrix.abs_det_submatrix_equiv_equiv
    ((lab w input shape initial j).row.symm.trans fd.labelling.row)
    ((lab w input shape initial j).targetEdge.trans fd.labelling.targetEdge.symm)
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
  rw [h, abs_zero] at hAbs
  exact fd.det_ne_zero (abs_eq_zero.mp hAbs.symm)

/-- **A position receiving a member is nonsingular**: the member's own cover, lifted along
the transport, presents the position. -/
theorem nonsingular_of_transport {mem : Regrowth core y degree}
    {ψ : GeometricStar.LimitIso hy mem w}
    {placement : (mem.frame.limitTarget mem.column).edges → Bool}
    {hPlacement : PlacementSpec mem placement} (j : Fin 3)
    (t : PositionTransport w hy input shape mem ψ placement hPlacement j) :
    Nonsingular w input shape initial j :=
  nonsingular_of_fullDim w input shape initial j ((limitAnchor input shape j).hD ▸
    W2PStarExhaustionProof.fdOfTransport mem placement hPlacement
      (ψ.datum.trans (limitAnchor input shape j).φ.symm) (limitAnchor input shape j).compat t)

/-- **Every star member is received, by a position transport, at a nonsingular
position.** -/
theorem exists_receipt (member : GeometricStar.StarMember hy w) :
    ∃ ψ : GeometricStar.LimitIso hy member.member w,
    ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
    ∃ hPlacement : PlacementSpec member.member placement,
    ∃ j : Fin 3, ∃ _ : Nonsingular w input shape initial j,
      Nonempty (PositionTransport w hy input shape member.member ψ placement hPlacement j) := by
  obtain ⟨ψ⟩ := member.specializes
  obtain ⟨placement, hP, j, ⟨t⟩⟩ := exists_transport w hy input shape member.member ψ
  exact ⟨ψ, placement, hP, j, nonsingular_of_transport w hy input shape initial j t, ⟨t⟩⟩

/-- **Stage 2 at one wall: the nonsingular positions exhaust the star.** -/
theorem exhausts : Exhausts w hy input shape initial :=
  exhausts_of_transports w hy input shape initial (exists_receipt w hy input shape initial)

end Exhaustion

/-- **The M-1k star exhaustion, at every core, degree and request.** -/
theorem w2M1kStarExhaustion (degree n p : ℕ) :
    W2M1kStarCensusProof.W2M1kStarExhaustion degree n p :=
  fun _ _ hy w _ _ _ input _ _ shape initial ↦ exhausts w hy input shape initial

/-- **The M-1k star census**, unconditionally. -/
theorem w2M1kStarCensus (degree n p : ℕ) : W2M1kStarCensusProof.W2M1kStarCensus degree n p :=
  W2M1kStarCensusProof.w2M1kStarCensus_of_exhaustion (w2M1kStarExhaustion degree n p)

/-- **The `w2M1k` clause of `FamilyStarParity`, at every degree, core size and request.** -/
theorem familyStarParity_w2M1k_general (degree n p : ℕ) :
    RegrowthWallInput.FamilyStarParity degree n p .w2M1k :=
  W2M1kStarCensusProof.familyStarParity_w2M1k_of_census (w2M1kStarCensus degree n p)

/-- **The `w2M1k` clause of `FamilyStarParity` at genus six and degree four, with no
hypothesis.** -/
theorem familyStarParity_w2M1k :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2M1k :=
  W2M1kStarCensusProof.familyStarParity_w2M1k_of_exhaustion (w2M1kStarExhaustion _ _ _)

end DraismaVargas.Count.W2M1kStarExhaustionProof
