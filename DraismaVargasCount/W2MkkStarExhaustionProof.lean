import DraismaVargasCount.W2MkkStarCensusProof
import DraismaVargasCount.W2M1kStarExhaustionProof

/-!
# M-kk star exhaustion: the `w2Mkk` clause with no hypothesis

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).  The residue proved here is the one isolated in `W2MkkStarCensusProof` §6;
the builder is `M11StarExhaustionProof` §3, and the relations and generic transport
lemmas are those of `W2M1kStarExhaustionProof`.  This completes the M-kk case of the
star parity in step 2 of `Assembly`.

## The result, in one paragraph

Every member of a `w2Mkk` wall's star receives a `PositionTransport` onto a nonsingular
position of Equation (8) (`exists_receipt`), so the star is exhausted (`exhausts`) and
`FamilyStarParity … .w2Mkk` holds **with no hypothesis**, at every degree, core size and
request (`familyStarParity_w2Mkk_general`, `familyStarParity_w2Mkk`).  A member's profile
and M-kk `Shape` are pulled back along its limit isomorphism, with `e₁`'s, `e₂`'s and the
pinned sheet carried by the direction permutations (`firstSheet_map`, `secondSheet_map`,
`pinSheet_map`).  Part I's census at the member (`member_census`, from
`W2MkkSelectedCensus.selectedCensus_dichotomy`) says its normal form is a detaching member
-- `t₂` endpoint the `t₂` occurrence partition, `t₃` endpoint and new edge detaching the
pinned sheet from the wall partition and from the `t₂` partition -- or `M⁽³⁾`.  A detaching
member whose pinned sheet lies in `e₁`'s block goes to position `0`, one whose pinned sheet
lies in `e₂`'s to position `1`, `M⁽³⁾` to position `2`; the position is over the limit or,
in the other orientation, over the branch-swapped copy, whose pinned sheet is in the
matching block (`W2MkkTransport.swapProfile_pin_first`, `swapProfile_pin_second`).
`transport_detach` is the builder of `M11StarExhaustionProof` with `τO = E₀`, `τF = E₁`,
`τN = E₀` followed by one transposition inside a `t₂` block.

## What is proved

* §1 `detach_map`, `rel_swap_self`, `rel_swap_iff`, `detach_off_refines`;
  `detach_left_rel`, `detach_right_rel`, `detach_new_rel`, `joined_shape`.
* §2 `edge_rel_map`, **`transport_detach`** (along any datum isomorphism).
* §3 `shape_pullback`, `firstSheet_map`, `secondSheet_map`, `pinSheet_map`,
  `orientedStar_map`, `firstSheet_swapProfile`, `secondSheet_swapProfile`,
  `pinSheet_swapProfile`.  §4 `member_census`.
* §5 `receipt_local`, `receipt_remote`, `receipt_joined`.
* §6 `limitAnchor_first_iff`, `limitAnchor_second_iff`, `exists_transport`,
  `nonsingular_of_fullDim`, `nonsingular_of_transport`, `exists_receipt`, `exhausts`;
  `w2MkkStarExhaustion`, `w2MkkStarCensus`, `familyStarParity_w2Mkk_general`, and
  **`familyStarParity_w2Mkk`**.

## What is NOT proved (every hypothesis, explicitly)

* Nothing is assumed: the main theorems have no hypothesis beyond their binders.
  `exhausts` does not use the `w2Mkk` classification tag.
* The clause is not exhibited at any wall: computer experiments with genus-six walls
  found no M-kk wall, and whether the tag occurs at genus six is not examined, so the
  theorem may be vacuous there; it is untested numerically.
* `ResolutionExpansion.Transport` (the strict transport, with its endpoint sheet
  rigidity) is not produced; the receipts are decoupled `TransportFree`s.

## Consumers

The `w2Mkk` clause of the star parity (step 2 of `Assembly`).
-/

namespace DraismaVargas.Count.W2MkkStarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W2R1Target SecondEquation W4Assembly W2R2SourceProfile
open W2MkkSourceCandidates W2MkkLimitColumns W2MkkTransport
open W2MkkCommonBalance (LimitMember LimitColumns)
open ResolutionM11 (LocalResolution)
open M11StarExhaustionProof (blockPre blockCard_blockPre input_pullback wall_rel_iff
  wall_rel_iff_of_agree eq_edge_of_incident incident_of_edge nonempty_transportFree_of_rel
  nonempty_transportFree_joined JoinedShape)
open W3Nd2StarCensusProof (PlacementSpec memberResolution memberNorm)
open W2M1kStarExhaustionProof (Detach Agree agree_edge rel_of_agree agree_swap detach_refl
  detach_rel detach_of detach_transfer side_star rel_iff_of_block_eq detach_off
  detachSheet_rel_iff)

/-! ## 1.  Figure 34's pasted resolutions, as global relations -/

section Relations

variable {d : ℕ}

/-- A relation carried by a permutation carries its one-sheet detachment. -/
theorem detach_map (W W' : SheetPartition d) (τ : Equiv.Perm (Fin d))
    (hW : ∀ a b, W.Rel a b ↔ W'.Rel (τ a) (τ b)) {p p' : Fin d} (hp : τ p = p') (a b : Fin d) :
    Detach W p a b ↔ Detach W' p' (τ a) (τ b) := by
  subst hp
  unfold Detach
  rw [hW]
  simp only [ne_eq, τ.injective.eq_iff]

/-- A transposition inside one block moves every sheet inside its block. -/
theorem rel_swap_self (P : SheetPartition d) {u v : Fin d} (huv : P.Rel u v) (t : Fin d) :
    P.Rel (Equiv.swap u v t) t := by
  by_cases hu : t = u
  · rw [hu, Equiv.swap_apply_left]
    exact huv.symm
  · by_cases hv : t = v
    · rw [hv, Equiv.swap_apply_right]
      exact huv
    · rw [Equiv.swap_apply_of_ne_of_ne hu hv]
      rfl

theorem rel_swap_iff (P : SheetPartition d) {u v : Fin d} (huv : P.Rel u v) (a b : Fin d) :
    P.Rel (Equiv.swap u v a) (Equiv.swap u v b) ↔ P.Rel a b :=
  ⟨fun h ↦ (rel_swap_self P huv a).symm.trans (h.trans (rel_swap_self P huv b)),
    fun h ↦ (rel_swap_self P huv a).trans (h.trans (rel_swap_self P huv b).symm)⟩

/-- Off the distinguished block, detaching a sheet of it changes nothing in a refinement of
the wall partition. -/
theorem detach_off_refines {W P : SheetPartition d} (hPW : P.Refines W) {A s x : Fin d}
    (hs : W.Rel A s) (hx : ¬ W.Rel A x) (y : Fin d) : Detach P s x y ↔ P.Rel x y := by
  have hxs : x ≠ s := fun h ↦ hx (h ▸ hs)
  constructor
  · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
    · exact (hxs h).elim
    · exact h
  · intro h
    exact Or.inr ⟨hxs, fun hys ↦ hx (hs.trans (hys ▸ hPW _ _ h).symm), h⟩

end Relations

section Pasted

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall} {profile : SourceProfile data star block}
  (input : W2SourceInput data star) (shape : Shape profile)

open M11StarCensusProof (pasted)

include input in
theorem detach_left_rel (detach : DetachData profile) (x y : Fin degree) :
    (pasted (detach.candidate shape)).left.Rel x y ↔ (endpointPartition profile).Rel x y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · exact rel_iff_of_block_eq (W2MkkIncomingMatching.detach_pasted_left_selected shape detach hx) y
  · exact rel_iff_of_block_eq
      (W2MkkIncomingMatching.detach_pasted_left_background input shape detach hx) y

include input in
theorem detach_right_rel (detach : DetachData profile) (x y : Fin degree) :
    (pasted (detach.candidate shape)).right.Rel x y ↔
      Detach (data.vertexPartition wall) (pinSheet profile) x y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · rw [rel_iff_of_block_eq
      (W2MkkIncomingMatching.detach_pasted_right_selected shape detach hx)]
    exact detachSheet_rel_iff _ _ _ _ _ x y
  · rw [rel_iff_of_block_eq
      (W2MkkIncomingMatching.detach_pasted_right_background input shape detach hx),
      detach_off (pinSheet_rel profile) hx]

include input in
theorem detach_new_rel (detach : DetachData profile) (x y : Fin degree) :
    (pasted (detach.candidate shape)).newEdge.Rel x y ↔
      Detach (endpointPartition profile) (pinSheet profile) x y := by
  by_cases hx : (data.vertexPartition wall).Rel block.1 x
  · rw [rel_iff_of_block_eq
      (W2MkkIncomingMatching.detach_pasted_newEdge_selected shape detach hx)]
    exact detachSheet_rel_iff _ _ _ _ _ x y
  · rw [rel_iff_of_block_eq
      (W2MkkIncomingMatching.detach_pasted_newEdge_background input shape detach hx),
      detach_off_refines (endpointPartition_refines profile) (pinSheet_rel profile) hx]

theorem joined_shape (distinguished : Fin degree) :
    JoinedShape (data.vertexPartition wall) (pasted (joinedCandidate profile distinguished)) where
  left x y := rel_iff_of_block_eq (W2MkkIncomingMatching.joined_pasted_left_block distinguished x) y
  right x y :=
    rel_iff_of_block_eq (W2MkkIncomingMatching.joined_pasted_right_block distinguished x) y
  newEdge x y :=
    rel_iff_of_block_eq (W2MkkIncomingMatching.joined_pasted_newEdge_block distinguished x) y

end Pasted

/-! ## 2.  A decoupled transport between two detaching members -/

section Transport

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- An occurrence partition is carried by its own occurrence permutation. -/
theorem edge_rel_map (iso : GeometricDatumIso first second) (edge : target₁.edges)
    (a b : Fin degree) :
    (first.edgePartition edge).Rel a b ↔
      (second.edgePartition (iso.targetEdge edge)).Rel (iso.edgePerm edge a)
        (iso.edgePerm edge b) := by
  rw [iso.edgePartition edge, SheetPartition.relabel_rel_iff]

/-- **Detaching to detaching.**  Along a datum isomorphism carrying the two-stars (label `0`
the doubled direction), a detaching resolution is carried onto a detaching one as soon as
the `t₃` direction carries the pinned sheet and the `t₂` direction carries an anchor of the
pinned sheet's own `t₂` block: the builder of `M11StarExhaustionProof` with `τO = E₀`,
`τF = E₁` and `τN = E₀`
followed by one transposition inside a `t₂` block. -/
theorem transport_detach (iso : GeometricDatumIso first second) {wall : target₁.V}
    {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star₁ : TwoStar target₁ wall} {star' : TwoStar target₂ wall'}
    (hStar : ∀ label, iso.targetEdge (star₁.edge label) = star'.edge label)
    (res res' : LocalResolution degree) (x₁ f₁ x' f' : Fin degree)
    (hf : iso.edgePerm (star₁.edge 0) f₁ = f') (hx : iso.edgePerm (star₁.edge 1) x₁ = x')
    (hfx₁ : (first.edgePartition (star₁.edge 0)).Rel f₁ x₁)
    (hfx' : (second.edgePartition (star'.edge 0)).Rel f' x')
    (hL : ∀ x y, res.left.Rel x y ↔ (first.edgePartition (star₁.edge 0)).Rel x y)
    (hR : ∀ x y, res.right.Rel x y ↔ Detach (first.vertexPartition wall) x₁ x y)
    (hN : ∀ x y, res.newEdge.Rel x y ↔ Detach (first.edgePartition (star₁.edge 0)) x₁ x y)
    (hL' : ∀ x y, res'.left.Rel x y ↔ (second.edgePartition (star'.edge 0)).Rel x y)
    (hR' : ∀ x y, res'.right.Rel x y ↔ Detach (second.vertexPartition wall') x' x y)
    (hN' : ∀ x y, res'.newEdge.Rel x y ↔ Detach (second.edgePartition (star'.edge 0)) x' x y) :
    Nonempty (ResolutionExpansionFree.TransportFree iso wall wall' star₁.right star'.right
      res res') := by
  set E0 := iso.edgePerm (star₁.edge 0)
  set E1 := iso.edgePerm (star₁.edge 1)
  have hE0 : Agree iso (wall := wall) E0 := agree_edge iso star₁ 0
  have hE1 : Agree iso (wall := wall) E1 := agree_edge iso star₁ 1
  have hP : ∀ a b, (first.edgePartition (star₁.edge 0)).Rel a b ↔
      (second.edgePartition (star'.edge 0)).Rel (E0 a) (E0 b) := by
    intro a b
    rw [edge_rel_map iso (star₁.edge 0), hStar 0]
  have hSwapP : (second.edgePartition (star'.edge 0)).Rel (E0 x₁) x' := by
    have h := (hP f₁ x₁).mp hfx₁
    rw [hf] at h
    exact h.symm.trans hfx'
  have hSwapW : (second.vertexPartition wall').Rel (E0 x₁) x' := by
    subst hWall
    exact star'.edgePartition_refines_wall second 0 _ _ hSwapP
  set τN := E0.trans (Equiv.swap (E0 x₁) x')
  have hτN : Agree iso (wall := wall) τN := agree_swap iso hWall hE0 hSwapW
  have hNx : τN x₁ = x' := Equiv.swap_apply_left _ _
  have hPτ : ∀ a b, (first.edgePartition (star₁.edge 0)).Rel a b ↔
      (second.edgePartition (star'.edge 0)).Rel (τN a) (τN b) := by
    intro a b
    rw [hP]
    exact (rel_swap_iff _ hSwapP _ _).symm
  refine nonempty_transportFree_of_rel iso wall wall' star₁.right star'.right res res' hWall
    (side_star iso hStar)
    (fun x y h ↦ star₁.edgePartition_refines_wall first 0 _ _ ((hL x y).mp h))
    (fun x y h ↦ detach_rel ((hR x y).mp h)) E0 E1 τN hE0 hE1 ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    rw [hL, hL', hP]
  · intro a b
    rw [hR, hR', detach_transfer iso hWall hE1 hx]
  · intro a b
    rw [hN, hN', detach_map _ _ τN hPτ hNx]
  · intro s
    rw [hL, hP, Equiv.apply_symm_apply]
    exact rel_swap_self _ hSwapP (E0 s)
  · intro s
    rw [hR]
    refine detach_of (rel_of_agree iso hτN hE1 s) ?_
    rw [Equiv.symm_apply_eq, hx, ← hNx, τN.injective.eq_iff]
  · intro edge hInc s
    rcases eq_edge_of_incident star₁ edge hInc with rfl | rfl
    · rw [TwoStar.right_edge_zero]
      simp only [Bool.false_eq_true, if_false]
      rw [Equiv.symm_apply_apply, hL]
      rfl
    · rw [TwoStar.right_edge_one]
      simp only [if_true]
      rw [Equiv.symm_apply_apply, hR]
      exact detach_refl _ _ _

end Transport

/-! ## 3.  The M-kk shape and the three sheets, pulled back along a datum isomorphism -/

section Pullback

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- **The M-kk shape pulls back**: the dangling direction and both survivor indices are
carried by the datum isomorphism. -/
theorem shape_pullback (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : TwoStar target₂ wall'} {block' : WallBlock second wall'}
    {profile : SourceProfile second star' block'} (shape : Shape profile)
    (profile₁ : SourceProfile first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star')
      (blockPre iso wall block'.1))
    (hSingle : profile₁.singleLabel = profile.singleLabel)
    (hFirst : iso.sourceEdgeEquiv profile₁.first.1 = profile.first.1)
    (hSecond : iso.sourceEdgeEquiv profile₁.second.1 = profile.second.1)
    (hDeleted : iso.sourceEdgeEquiv profile₁.deleted.edge.1 = profile.deleted.edge.1) :
    Shape profile₁ where
  deleted_single := by
    apply iso.targetEdge.injective
    rw [M11WallExhaustion.pullbackTwoStar_edge, hSingle, ← shape.deleted_single, ← hDeleted]
    rfl
  one_lt_first := by
    rw [← iso.sourceEdgeIndex_map, hFirst]
    exact shape.one_lt_first
  one_lt_second := by
    rw [← iso.sourceEdgeIndex_map, hSecond]
    exact shape.one_lt_second

variable (iso : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  {star₁ : TwoStar target₁ wall} {star' : TwoStar target₂ wall'}
  {block₁ : WallBlock first wall} {block' : WallBlock second wall'}
  {profile₁ : SourceProfile first star₁ block₁} {profile : SourceProfile second star' block'}

theorem firstSheet_map (hFirst : iso.sourceEdgeEquiv profile₁.first.1 = profile.first.1) :
    iso.edgePerm (star₁.edge profile₁.doubleLabel) (firstSheet profile₁) = firstSheet profile := by
  rw [← profile₁.first_target]
  exact congrArg (fun e : second.SourceEdge ↦ e.1.2) hFirst

theorem secondSheet_map (hSecond : iso.sourceEdgeEquiv profile₁.second.1 = profile.second.1) :
    iso.edgePerm (star₁.edge profile₁.doubleLabel) (secondSheet profile₁) =
      secondSheet profile := by
  rw [← profile₁.second_target]
  exact congrArg (fun e : second.SourceEdge ↦ e.1.2) hSecond

theorem pinSheet_map (shape₁ : Shape profile₁)
    (hDeleted : iso.sourceEdgeEquiv profile₁.deleted.edge.1 = profile.deleted.edge.1) :
    iso.edgePerm (star₁.edge profile₁.singleLabel) (pinSheet profile₁) = pinSheet profile := by
  rw [← shape₁.deleted_single]
  exact congrArg (fun e : second.SourceEdge ↦ e.1.2) hDeleted

theorem orientedStar_map (hStar : ∀ label, iso.targetEdge (star₁.edge label) = star'.edge label)
    (hDouble : profile₁.doubleLabel = profile.doubleLabel) (label : Fin 2) :
    iso.targetEdge ((orientedStar profile₁).edge label) = (orientedStar profile).edge label := by
  rw [orientedStar, orientStar_edge, hStar, hDouble]
  rfl

end Pullback

/-- The branch swap moves `e₁`'s canonical sheet by the `t₂` occurrence permutation. -/
theorem firstSheet_swapProfile {target : CFGraph} {degree : ℕ} {wall : target.V}
    {data : GluingDatum target degree} {star : TwoStar target wall}
    {block : WallBlock data wall} {profile : SourceProfile data star block}
    (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    firstSheet (swapProfile profile hConnected other hOther) =
      (swapRelabeling profile other hOther).edgePermutation (star.edge profile.doubleLabel)
        (firstSheet profile) := by
  show (swapRelabeling profile other hOther).edgePermutation (profile.first.1.1.1)
    (firstSheet profile) = _
  rw [profile.first_target]

/-- The same for `e₂`. -/
theorem secondSheet_swapProfile {target : CFGraph} {degree : ℕ} {wall : target.V}
    {data : GluingDatum target degree} {star : TwoStar target wall}
    {block : WallBlock data wall} {profile : SourceProfile data star block}
    (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    secondSheet (swapProfile profile hConnected other hOther) =
      (swapRelabeling profile other hOther).edgePermutation (star.edge profile.doubleLabel)
        (secondSheet profile) := by
  show (swapRelabeling profile other hOther).edgePermutation (profile.second.1.1.1)
    (secondSheet profile) = _
  rw [profile.second_target]

/-- The pinned sheet moves by the `t₃` occurrence permutation. -/
theorem pinSheet_swapProfile {target : CFGraph} {degree : ℕ} {wall : target.V}
    {data : GluingDatum target degree} {star : TwoStar target wall}
    {block : WallBlock data wall} {profile : SourceProfile data star block}
    (shape : Shape profile) (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    pinSheet (swapProfile profile hConnected other hOther) =
      (swapRelabeling profile other hOther).edgePermutation (star.edge profile.singleLabel)
        (pinSheet profile) := by
  show (swapRelabeling profile other hOther).edgePermutation (profile.deleted.edge.1.1.1)
    (pinSheet profile) = _
  rw [shape.deleted_single]

/-! ## 4.  Part I's census at an arbitrary member, as relations -/

section MemberCensus

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The member's own normal form is a detaching member or `M⁽³⁾`**, as relations, at
the oriented star's placement (`W2MkkSelectedCensus.selectedCensus_dichotomy`). -/
theorem member_census (mem : Regrowth core y degree) (hy : Nondegenerate y)
    {star : TwoStar (mem.frame.limitTarget mem.column) (mergeVertex mem)}
    (input : W2SourceInput mem.limit star) {block : WallBlock mem.limit (mergeVertex mem)}
    {profile : SourceProfile mem.limit star block} (shape : Shape profile) :
    ∃ hP : PlacementSpec mem (orientedStar profile).right,
      ((∀ x y, (memberResolution mem _ hP).left.Rel x y ↔ (endpointPartition profile).Rel x y) ∧
        (∀ x y, (memberResolution mem _ hP).right.Rel x y ↔
          Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile) x y) ∧
        (∀ x y, (memberResolution mem _ hP).newEdge.Rel x y ↔
          Detach (endpointPartition profile) (pinSheet profile) x y)) ∨
      JoinedShape (mem.limit.vertexPartition (mergeVertex mem)) (memberResolution mem _ hP) := by
  have hForest := InheritedLimitRows.forest mem hy
  have hBackground := W2PStarExhaustionProof.background_of_profile input profile
  obtain ⟨detach⟩ := exists_detachData shape
  obtain ⟨hLeftCard, hRightCard, -, -⟩ := W2MkkSelectedCensus.divalent_endpoints mem.frame.data
    rfl (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    mem.frame.fullDim profile shape
  have hP : PlacementSpec mem (orientedStar profile).right :=
    W2MkkIncomingCensus.member_placement mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) profile
      hLeftCard hRightCard
  obtain ⟨hOld, hFresh⟩ := W2MkkIncomingCensus.transported_endpoints mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) profile
    hLeftCard hRightCard hP
  have hNew := M11IncomingOuterPartitions.transported_edgePartition_new mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) _ hP
    mem.frame.fullDim.targetConnected mem.frame.fullDim.targetGenus
  refine ⟨hP, ?_⟩
  rcases W2MkkSelectedCensus.selectedCensus_dichotomy mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      mem.frame.fullDim hForest profile shape detach hBackground with census | census
  · obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := W2MkkIncomingMatching.detach_wall_blocks
      mem.frame.data rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
      (mem.frame.numEdges_edgeOf mem.column) mem.frame.fullDim hForest input profile hBackground
      hLeftCard hRightCard shape detach census
    refine Or.inl ⟨fun x y ↦ ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hOld)).trans
        ((rel_iff_of_block_eq (hLeftWall x) y).trans (detach_left_rel input shape detach x y))
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hFresh)).trans
        ((rel_iff_of_block_eq (hRightWall x) y).trans (detach_right_rel input shape detach x y))
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hNew)).trans
        ((rel_iff_of_block_eq (hNewWall x) y).trans (detach_new_rel input shape detach x y))
  · obtain ⟨hLeftWall, hRightWall, hNewWall⟩ := W2MkkIncomingMatching.joined_wall_blocks
      mem.frame.data rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
      (mem.frame.numEdges_edgeOf mem.column) mem.frame.fullDim hForest input profile hBackground
      hLeftCard hRightCard (pinSheet profile) census
    have hS := joined_shape (profile := profile) (pinSheet profile)
    refine Or.inr ⟨fun x y ↦ ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hOld)).trans
        ((rel_iff_of_block_eq (hLeftWall x) y).trans (hS.left x y))
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hFresh)).trans
        ((rel_iff_of_block_eq (hRightWall x) y).trans (hS.right x y))
    · exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hNew)).trans
        ((rel_iff_of_block_eq (hNewWall x) y).trans (hS.newEdge x y))

end MemberCensus

/-! ## 5.  The receipts at the three anchored members of the wall -/

section Receipts

open W2MkkStarCensusProof

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
  (hStarO : ∀ label, (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetEdge
    ((orientedStar profile₁).edge label) = (orientedStar profile).edge label)
  (hPinO : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
    ((orientedStar profile₁).edge 1) (pinSheet profile₁) = pinSheet profile)
  (res : LocalResolution degree)
  (hL : ∀ x y, res.left.Rel x y ↔ (endpointPartition profile₁).Rel x y)
  (hR : ∀ x y, res.right.Rel x y ↔
    Detach (mem.limit.vertexPartition (mergeVertex mem)) (pinSheet profile₁) x y)
  (hN : ∀ x y, res.newEdge.Rel x y ↔ Detach (endpointPartition profile₁) (pinSheet profile₁) x y)

include hW hStarO hPinO hL hR hN in
/-- **Detaching onto the detaching member over the limit.** -/
theorem receipt_local (detach₀ : DetachData profile) (f₁ f : Fin degree)
    (hf : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
      ((orientedStar profile₁).edge 0) f₁ = f)
    (hfx₁ : (endpointPartition profile₁).Rel f₁ (pinSheet profile₁))
    (hfx : (endpointPartition profile).Rel f (pinSheet profile)) :
    Nonempty (ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (localAnchor input shape detach₀).φ.symm) (mergeVertex mem)
      (mergeVertex w) (orientedStar profile₁).right (localMember input shape detach₀).right res
      (localAnchor input shape detach₀).res) := by
  refine transport_detach (ψ.datum.trans (localAnchor input shape detach₀).φ.symm) hW
    (star₁ := orientedStar profile₁) (star' := orientedStar profile) hStarO res
    (localAnchor input shape detach₀).res (pinSheet profile₁) f₁ (pinSheet profile) f hf hPinO
    ?_ ?_ ?_ hR ?_ ?_ ?_ ?_
  · rw [orientedStar_edge_zero]; exact hfx₁
  · rw [orientedStar_edge_zero]; exact hfx
  · rw [orientedStar_edge_zero]; exact hL
  · rw [orientedStar_edge_zero]; exact hN
  · rw [orientedStar_edge_zero]; exact detach_left_rel input shape detach₀
  · exact detach_right_rel input shape detach₀
  · rw [orientedStar_edge_zero]; exact detach_new_rel input shape detach₀

include hW hStarO hPinO hL hR hN in
/-- **Detaching onto the remote detaching member** over the branch-swapped copy. -/
theorem receipt_remote (other : Fin degree)
    (hOther : (w.limit.vertexPartition (mergeVertex w)).Rel (pinSheet profile) other)
    (f₁ f fR : Fin degree)
    (hf : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
      ((orientedStar profile₁).edge 0) f₁ = f)
    (hfx₁ : (endpointPartition profile₁).Rel f₁ (pinSheet profile₁))
    (hfR : (swapRelabeling profile other hOther).edgePermutation (star.edge profile.doubleLabel)
      f = fR)
    (hfxR : (endpointPartition (swapProfile profile input.valid.1 other hOther)).Rel fR
      (pinSheet (swapProfile profile input.valid.1 other hOther))) :
    Nonempty (ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (remoteAnchor input shape other hOther).φ.symm) (mergeVertex mem)
      (mergeVertex w) (orientedStar profile₁).right (remoteMember input shape other hOther).right
      res (remoteAnchor input shape other hOther).res) := by
  refine transport_detach (ψ.datum.trans (remoteAnchor input shape other hOther).φ.symm) hW
    (star₁ := orientedStar profile₁)
    (star' := orientedStar (swapProfile profile input.valid.1 other hOther)) hStarO res
    (remoteAnchor input shape other hOther).res (pinSheet profile₁) f₁
    (pinSheet (swapProfile profile input.valid.1 other hOther)) fR ?_ ?_ ?_ ?_ ?_ hR ?_ ?_ ?_ ?_
  · change (swapRelabeling profile other hOther).edgePermutation
      ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetEdge
        ((orientedStar profile₁).edge 0))
      ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
        ((orientedStar profile₁).edge 0) f₁) = fR
    rw [hStarO 0, hf, orientedStar_edge_zero]
    exact hfR
  · change (swapRelabeling profile other hOther).edgePermutation
      ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetEdge
        ((orientedStar profile₁).edge 1))
      ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
        ((orientedStar profile₁).edge 1) (pinSheet profile₁)) = _
    rw [hStarO 1, hPinO, orientedStar_edge_one,
      pinSheet_swapProfile shape input.valid.1 other hOther]
  · rw [orientedStar_edge_zero]; exact hfx₁
  · rw [orientedStar_edge_zero]; exact hfxR
  · rw [orientedStar_edge_zero]; exact hL
  · rw [orientedStar_edge_zero]; exact hN
  · rw [orientedStar_edge_zero]
    exact detach_left_rel (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther)
  · exact detach_right_rel (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther)
  · rw [orientedStar_edge_zero]
    exact detach_new_rel (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) (remoteDetach input shape other hOther)

include hW hStarO in
/-- **Joined onto the joined member.** -/
theorem receipt_joined (distinguished : Fin degree)
    (hS : JoinedShape (mem.limit.vertexPartition (mergeVertex mem)) res) :
    Nonempty (ResolutionExpansionFree.TransportFree
      (ψ.datum.trans (joinedAnchor input shape distinguished).φ.symm) (mergeVertex mem)
      (mergeVertex w) (orientedStar profile₁).right (joinedMember input shape distinguished).right
      res (joinedAnchor input shape distinguished).res) :=
  nonempty_transportFree_joined (ψ.datum.trans (joinedAnchor input shape distinguished).φ.symm)
    (mergeVertex mem) (mergeVertex w) (orientedStar profile₁).right
    (joinedMember input shape distinguished).right res
    (joinedAnchor input shape distinguished).res hW (side_star _ hStarO) hS
    (joined_shape (profile := profile) distinguished)

end Receipts

/-! ## 6.  Exhaustion, and the family clause -/

section Exhaustion

open W2MkkStarCensusProof

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  (detach : DetachData profile) (distinguished : Fin degree)

/-- In the Base II.2.1.M orientation, a statement about a position's anchor is one about
the orientation's own. -/
theorem limitAnchor_first_iff
    (hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)) (j : Fin 3)
    (F : ∀ m : LimitMember w.limit (mergeVertex w), Anchor w m → Prop) :
    F _ (limitAnchor input shape detach distinguished j) ↔
      F _ (firstAnchor input shape distinguished ⟨detach, hPin⟩ j) := by
  unfold limitAnchor
  rw [dif_pos hPin]
  exact anchorOf_iff shape _ _ j F

/-- In the Base II.2.2.M orientation, likewise. -/
theorem limitAnchor_second_iff
    (hPin : ¬ (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile))
    (j : Fin 3) (F : ∀ m : LimitMember w.limit (mergeVertex w), Anchor w m → Prop) :
    F _ (limitAnchor input shape detach distinguished j) ↔
      F _ (secondAnchor input shape distinguished
        ⟨detach, (pinSheet_mem shape).resolve_left hPin⟩ j) := by
  unfold limitAnchor
  rw [dif_neg hPin]
  exact anchorOf_iff shape _ _ j F

/-- **Every star member presents a transport onto the position of its own kind.** -/
theorem exists_transport (mem : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy mem w) :
    ∃ placement : (mem.frame.limitTarget mem.column).edges → Bool,
    ∃ hPlacement : PlacementSpec mem placement, ∃ j : Fin 3,
      Nonempty (PositionTransport w hy input shape detach distinguished mem ψ placement
        hPlacement j) := by
  have hW : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetVertex
      (mergeVertex mem) = mergeVertex w :=
    M11StarCensusProof.pinned w hy input mem ψ
  have input₁ := input_pullback _ hW input
  obtain ⟨profile₁, hDouble, hSingle, hFirst, hSecond, -, hDeleted⟩ :=
    W2PStarExhaustionProof.exists_profile_pullback _ (InheritedLimitRows.limit_connected mem) hW
      profile
  have shape₁ := shape_pullback _ hW shape profile₁ hSingle hFirst hSecond hDeleted
  have hStar := M11WallExhaustion.pullbackTwoStar_edge _ (mergeVertex mem) (mergeVertex w) hW star
  have hStarO := orientedStar_map _ hStar hDouble (profile₁ := profile₁) (profile := profile)
  have hPinO : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
      ((orientedStar profile₁).edge 1) (pinSheet profile₁) = pinSheet profile := by
    rw [orientedStar_edge_one]
    exact pinSheet_map _ shape₁ hDeleted
  have hFirstO : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
      ((orientedStar profile₁).edge 0) (firstSheet profile₁) = firstSheet profile := by
    rw [orientedStar_edge_zero]
    exact firstSheet_map _ hFirst
  have hSecondO : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm
      ((orientedStar profile₁).edge 0) (secondSheet profile₁) = secondSheet profile := by
    rw [orientedStar_edge_zero]
    exact secondSheet_map _ hSecond
  have hC := RegrowthBalances.limit_connected w
  have hG := RegrowthBalances.limit_genus w
  obtain ⟨hP, hK⟩ := member_census mem hy input₁ shape₁
  rcases hK with ⟨hL, hR, hN⟩ | hS
  · rcases pinSheet_mem shape₁ with h₁ | h₁
    · refine ⟨_, hP, 0, ?_⟩
      by_cases hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
      · exact (limitAnchor_first_iff w input shape detach distinguished hPin 0 (fun m A ↦
          Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
            (mergeVertex mem) (mergeVertex w) _ m.right (memberResolution mem _ hP)
            A.res))).mpr
          (receipt_local input shape ψ hW hStarO hPinO _ hL hR hN detach _ _ hFirstO h₁ hPin)
      · exact (limitAnchor_second_iff w input shape detach distinguished hPin 0 (fun m A ↦
          Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
            (mergeVertex mem) (mergeVertex w) _ m.right (memberResolution mem _ hP)
            A.res))).mpr
          (receipt_remote input shape ψ hW hStarO hPinO _ hL hR hN (firstSheet profile)
            (firstSheet_together profile) _ _ _ hFirstO h₁
            (firstSheet_swapProfile input.valid.1 _ _).symm
            (swapProfile_pin_first shape hC hG input.valid.1))
    · refine ⟨_, hP, 1, ?_⟩
      by_cases hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
      · exact (limitAnchor_first_iff w input shape detach distinguished hPin 1 (fun m A ↦
          Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
            (mergeVertex mem) (mergeVertex w) _ m.right (memberResolution mem _ hP)
            A.res))).mpr
          (receipt_remote input shape ψ hW hStarO hPinO _ hL hR hN (secondSheet profile)
            (secondSheet_together profile) _ _ _ hSecondO h₁
            (secondSheet_swapProfile input.valid.1 _ _).symm
            (swapProfile_pin_second shape hC hG input.valid.1))
      · exact (limitAnchor_second_iff w input shape detach distinguished hPin 1 (fun m A ↦
          Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
            (mergeVertex mem) (mergeVertex w) _ m.right (memberResolution mem _ hP)
            A.res))).mpr
          (receipt_local input shape ψ hW hStarO hPinO _ hL hR hN detach _ _ hSecondO h₁
            ((pinSheet_mem shape).resolve_left hPin))
  · refine ⟨_, hP, 2, ?_⟩
    by_cases hPin : (endpointPartition profile).Rel (firstSheet profile) (pinSheet profile)
    · exact (limitAnchor_first_iff w input shape detach distinguished hPin 2 (fun m A ↦
        Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
          (mergeVertex mem) (mergeVertex w) _ m.right (memberResolution mem _ hP)
          A.res))).mpr
        (receipt_joined input shape ψ hW hStarO _ distinguished hS)
    · exact (limitAnchor_second_iff w input shape detach distinguished hPin 2 (fun m A ↦
        Nonempty (ResolutionExpansionFree.TransportFree (ψ.datum.trans A.φ.symm)
          (mergeVertex mem) (mergeVertex w) _ m.right (memberResolution mem _ hP)
          A.res))).mpr
        (receipt_joined input shape ψ hW hStarO _ distinguished hS)

variable (initial : StableLengthMatrixLabelling
  ((columns input shape detach distinguished).member 0).datum (Fin p))

/-- **Any full-dimensional presentation of a position's datum makes the position
nonsingular** at Equation (8)'s labelling. -/
theorem nonsingular_of_fullDim (j : Fin 3)
    (fd : FullDimensionalSourcePresentation
      ((columns input shape detach distinguished).member j).datum (Fin p)) :
    Nonsingular w input shape detach distinguished initial j := by
  classical
  unfold Nonsingular
  change (GluingDatum.LengthMatrixPresentation.matrix
    (lab w input shape detach distinguished initial j).presentation).det ≠ 0
  rw [DraismaVargas.Count.matrix_labelling_submatrix
    (lab w input shape detach distinguished initial j) fd.labelling]
  intro h
  have hAbs := Matrix.abs_det_submatrix_equiv_equiv
    ((lab w input shape detach distinguished initial j).row.symm.trans fd.labelling.row)
    ((lab w input shape detach distinguished initial j).targetEdge.trans
      fd.labelling.targetEdge.symm)
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
  rw [h, abs_zero] at hAbs
  exact fd.det_ne_zero (abs_eq_zero.mp hAbs.symm)

/-- **A position receiving a member is nonsingular.** -/
theorem nonsingular_of_transport {mem : Regrowth core y degree}
    {ψ : GeometricStar.LimitIso hy mem w}
    {placement : (mem.frame.limitTarget mem.column).edges → Bool}
    {hPlacement : PlacementSpec mem placement} (j : Fin 3)
    (t : PositionTransport w hy input shape detach distinguished mem ψ placement hPlacement j) :
    Nonsingular w input shape detach distinguished initial j :=
  nonsingular_of_fullDim w input shape detach distinguished initial j
    ((limitAnchor input shape detach distinguished j).hD ▸
      W2PStarExhaustionProof.fdOfTransport mem placement hPlacement
        (ψ.datum.trans (limitAnchor input shape detach distinguished j).φ.symm)
        (limitAnchor input shape detach distinguished j).compat t)

/-- **Every star member presents a receipt at a nonsingular position.** -/
theorem exists_receipt (member : GeometricStar.StarMember hy w) :
    ∃ ψ : GeometricStar.LimitIso hy member.member w,
    ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
    ∃ hPlacement : PlacementSpec member.member placement,
    ∃ j : Fin 3, ∃ _ : Nonsingular w input shape detach distinguished initial j,
      Nonempty (PositionTransport w hy input shape detach distinguished member.member ψ placement
        hPlacement j) := by
  obtain ⟨ψ⟩ := member.specializes
  obtain ⟨placement, hP, j, ⟨t⟩⟩ :=
    exists_transport w hy input shape detach distinguished member.member ψ
  exact ⟨ψ, placement, hP, j,
    nonsingular_of_transport w hy input shape detach distinguished initial j t, ⟨t⟩⟩

/-- **Stage 2 at one wall: the nonsingular positions exhaust the star.** -/
theorem exhausts : Exhausts w hy input shape detach distinguished initial :=
  exhausts_of_transports w hy input shape detach distinguished initial
    (exists_receipt w hy input shape detach distinguished initial)

end Exhaustion

/-- **The M-kk star exhaustion, at every core, degree and request.** -/
theorem w2MkkStarExhaustion (degree n p : ℕ) :
    W2MkkStarCensusProof.W2MkkStarExhaustion degree n p :=
  fun _ _ hy w _ _ _ input _ _ shape detach distinguished initial ↦
    exhausts w hy input shape detach distinguished initial

/-- **The M-kk star census**, unconditionally. -/
theorem w2MkkStarCensus (degree n p : ℕ) : W2MkkStarCensusProof.W2MkkStarCensus degree n p :=
  W2MkkStarCensusProof.w2MkkStarCensus_of_exhaustion (w2MkkStarExhaustion degree n p)

/-- **The `w2Mkk` clause of `FamilyStarParity`, at every degree, core size and request.** -/
theorem familyStarParity_w2Mkk_general (degree n p : ℕ) :
    RegrowthWallInput.FamilyStarParity degree n p .w2Mkk :=
  W2MkkStarCensusProof.familyStarParity_w2Mkk_of_census (w2MkkStarCensus degree n p)

/-- **The `w2Mkk` clause of `FamilyStarParity` at genus six and degree four, with no
hypothesis.** -/
theorem familyStarParity_w2Mkk :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2Mkk :=
  W2MkkStarCensusProof.familyStarParity_w2Mkk_of_exhaustion (w2MkkStarExhaustion _ _ _)

end DraismaVargas.Count.W2MkkStarExhaustionProof
