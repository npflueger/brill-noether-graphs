import DraismaVargasCount.W2PStarCensusProof
import DraismaVargasCount.W2R1StarExhaustionProof

/-!
# W2P star exhaustion: the `w2P` clause with no hypothesis

Sources: Draisma–Vargas Part I, Case `{w2-r2-nd3-P}`, Figure 35, Equation (9); Vargas,
Part II, the star of a wall.  The reduction completed here is
`W2PStarCensusProof.exhausts_of_transports` (Stage 2 reduced to decoupled transports); the
transport builder is `M11StarExhaustionProof.nonempty_transportFree_of_rel`.

## The result, in one paragraph

Every member of a `w2P` wall's star receives a `PositionTransport` onto a **nonsingular**
position of Equation (9) (`exists_receipt`), so the star is exhausted (`exhausts`), and
`FamilyStarParity … .w2P` holds **with no hypothesis**, at every degree, core size and
positive request (`familyStarParity_w2P_general`, `familyStarParity_w2P`).  A member `m`
with limit isomorphism `ψ` gets the wall's W2 input (`input_pullback`), case-P profile
(`exists_profile_pullback`, with its four occurrences carried by the source-edge
dictionary) and `Shape` (`shape_pullback`) pulled back along `ψ`; the classifier's
background field is automatic (`background_of_profile`); Part I's incoming census at `m`
(`W2PIncomingMatching`) says its normal form has Figure 35's member-`q` shape
(`member_census`); the builder carries that shape onto the wall's member `q`
(`nonempty_transport`, with `τO = τN = E₂`, `τF = E₃`); and the member's own cover, lifted
along the transport, is a full-dimensional presentation of member `q`, which is therefore
nonsingular (`fdOfTransport`, `nonsingular_of_fullDim`).  **No coherence dichotomy
arises**: the `t₂` endpoint and the regrown occurrence see only the `t₂` occurrence
partition, the wall partition and three named sheets, all carried exactly by `E₂`; the
`t₃` endpoint is the whole wall block.

## What is proved

* §1 `exists_profile_pullback` (`M11StarExhaustionProof.nonempty_profile_pullback` with the
  construction exposed), `shape_pullback`.
* §2 `background_of_profile`: a case-P block is the only ramified block of a W2 wall.
* §3 `mergeBlocks_rel_iff`, `detachSheet_rel_iff` (two generic `SheetPartition` relation
  characterizations), `shapeAt`, `shapeAt_candidate`, `members_right`, `pasted_left_rel`,
  `pasted_right_rel`, `pasted_newEdge_rel`.
* §4 `sheet_map`, `fine_rel_iff` (naturality of the three fine partitions), and
  **`nonempty_transport`**.
* §5 `member_census`: Part I's census at an arbitrary regrowth, in relational form.
* §6 `nonsingular_of_fullDim`, `fdOfTransport`.
* §7 `exists_receipt`, `exhausts`; `w2PStarExhaustion`, `w2PStarCensus`,
  `familyStarParity_w2P_general`, and the headline **`familyStarParity_w2P`**.

## Scope

* Nothing is assumed: the headlines have no hypothesis beyond their binders.  `exhausts`
  does not use the `w2P` classification tag; it holds at every regrowth carrying a W2 input,
  a case-P profile and its `Shape`.
* The clause is not exhibited at any wall: no regrowth tagged `w2P` is constructed here.
* `ResolutionExpansion.Transport` (the strict transport) is not produced; the transports
  are decoupled `TransportFree`s.

## Consumers

`StarSupplyAssembly` takes the `w2P` clause `familyStarParity_w2P`, for the trivalent wall
step of `DraismaVargasCount.Assembly`.  The profile pull-back `exists_profile_pullback`,
`fdOfTransport` and `background_of_profile` are reused by
`DraismaVargasCount.W2M1kStarExhaustionProof` and `DraismaVargasCount.W2MkkStarExhaustionProof`.
-/

namespace DraismaVargas.Count.W2PStarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W2R1Target SecondEquation W4Assembly W2R2SourceProfile W2PSourceCandidates W2PSurvival
open ResolutionM11 (LocalResolution)
open M11StarExhaustionProof (blockPre blockPre_rel sourceVertexEquiv_blockPre blockCard_blockPre
  localRamification_blockPre nonDanglingValency_blockPre input_pullback incidentEquivOf
  incidentEquivOf_val incidentEquivOf_target wall_rel_iff wall_rel_iff_of_agree eq_edge_of_incident
  incident_of_edge nonempty_transportFree_of_rel)
open W3Nd2StarCensusProof (PlacementSpec memberResolution memberNorm)
open W2R1StarExhaustionProof (blockPre_rel_iff)

/-! ## 1.  The case-P profile and shape, pulled back along a datum isomorphism -/

section Pullback

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- **A ramification-two profile pulls back along a datum isomorphism**, with its labels and
its four occurrences carried by the source-edge dictionary.  This is
`M11StarExhaustionProof.nonempty_profile_pullback` with the construction exposed: the
occurrence correspondence is what the Figure 35 fine partitions are read through. -/
theorem exists_profile_pullback (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : TwoStar target₂ wall'} {block' : WallBlock second wall'}
    (profile : SourceProfile second star' block') :
    ∃ profile₁ : SourceProfile first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star')
        (blockPre iso wall block'.1),
      profile₁.doubleLabel = profile.doubleLabel ∧ profile₁.singleLabel = profile.singleLabel ∧
      iso.sourceEdgeEquiv profile₁.first.1 = profile.first.1 ∧
      iso.sourceEdgeEquiv profile₁.second.1 = profile.second.1 ∧
      iso.sourceEdgeEquiv profile₁.third.1 = profile.third.1 ∧
      iso.sourceEdgeEquiv profile₁.deleted.edge.1 = profile.deleted.edge.1 := by
  classical
  set star := M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star'
  have hStar : ∀ label, iso.targetEdge (star.edge label) = star'.edge label :=
    M11WallExhaustion.pullbackTwoStar_edge iso wall wall' hWall star'
  set IE := incidentEquivOf iso (sourceVertexEquiv_blockPre iso hWall block')
  have hTarget : ∀ (e : IncidentSourceEdge first
      (WallBlock.sourceVertex first wall (blockPre iso wall block'.1))) (label : Fin 2),
      e.1.1.1 = star.edge label ↔ (IE e).1.1.1 = star'.edge label := by
    intro e label
    rw [incidentEquivOf_target, ← hStar label]
    exact iso.targetEdge.injective.eq_iff.symm
  have hDang : ∀ (e : IncidentSourceEdge first
      (WallBlock.sourceVertex first wall (blockPre iso wall block'.1))),
      IsDangling second (IE e).1 ↔ IsDangling first e.1 :=
    fun e ↦ iso.isDangling_map_iff hConnected e.1
  have hIndex : ∀ (e : IncidentSourceEdge first
      (WallBlock.sourceVertex first wall (blockPre iso wall block'.1))),
      second.sourceEdgeIndex (IE e).1 = first.sourceEdgeIndex e.1 :=
    fun e ↦ iso.sourceEdgeIndex_map e.1
  have hFibre : ∀ label (e : IncidentSourceEdge first
      (WallBlock.sourceVertex first wall (blockPre iso wall block'.1))),
      e ∈ survivingFibre first star (blockPre iso wall block'.1) label ↔
        IE e ∈ survivingFibre second star' block' label := by
    intro label e
    rw [survivingFibre.mem, survivingFibre.mem, hTarget, hDang]
  have hCard := blockCard_blockPre iso hWall block'.1
  let deleted : DeletedOccurrence first (blockPre iso wall block'.1) :=
    { edge := IE.symm profile.deleted.edge
      dangling := by
        rw [← hDang, Equiv.apply_symm_apply]; exact profile.deleted.dangling
      index_one := by
        rw [← hIndex, Equiv.apply_symm_apply]; exact profile.deleted.index_one
      unique := by
        intro other
        rw [← hDang, profile.deleted.unique, Equiv.eq_symm_apply] }
  have h1 := hIndex (IE.symm profile.first)
  have h2 := hIndex (IE.symm profile.second)
  have h3 := hIndex (IE.symm profile.third)
  rw [Equiv.apply_symm_apply] at h1 h2 h3
  have hd : (deleted.edge.1.1.1 = star.edge profile.singleLabel ↔
        profile.deleted.edge.1.1.1 = star'.edge profile.singleLabel) ∧
      (deleted.edge.1.1.1 = star.edge profile.doubleLabel ↔
        profile.deleted.edge.1.1.1 = star'.edge profile.doubleLabel) := by
    constructor <;>
    · change (IE.symm profile.deleted.edge).1.1.1 = _ ↔ _
      rw [hTarget, Equiv.apply_symm_apply]
  refine ⟨⟨?_, ?_, profile.doubleLabel, profile.singleLabel, profile.labels_ne,
    IE.symm profile.first, IE.symm profile.second, IE.symm profile.third, deleted,
    fun h ↦ profile.first_ne_second (IE.symm.injective h), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [localRamification_blockPre iso hWall block']; exact profile.ramification
  · rw [nonDanglingValency_blockPre iso hConnected hWall block']; exact profile.valency
  · rw [hTarget, Equiv.apply_symm_apply]; exact profile.first_target
  · rw [hTarget, Equiv.apply_symm_apply]; exact profile.second_target
  · rw [hTarget, Equiv.apply_symm_apply]; exact profile.third_target
  · rw [← hDang, Equiv.apply_symm_apply]; exact profile.first_survives
  · rw [← hDang, Equiv.apply_symm_apply]; exact profile.second_survives
  · rw [← hDang, Equiv.apply_symm_apply]; exact profile.third_survives
  · ext e
    rw [hFibre, profile.double_fibre]
    simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.eq_symm_apply]
  · ext e
    rw [hFibre, profile.single_fibre]
    simp only [Finset.mem_singleton, Equiv.eq_symm_apply]
  · intro e
    rcases profile.exhaustive (IE e) with h | h | h | h
    · exact Or.inl (IE.eq_symm_apply.mpr h)
    · exact Or.inr (Or.inl (IE.eq_symm_apply.mpr h))
    · exact Or.inr (Or.inr (Or.inl (IE.eq_symm_apply.mpr h)))
    · exact Or.inr (Or.inr (Or.inr (IE.eq_symm_apply.mpr h)))
  · rw [hd.1, hd.2, ← h1, ← h2, ← h3, hCard]
    exact profile.cases
  · exact (incidentEquivOf_val iso _ _).symm.trans (congrArg Subtype.val (IE.apply_symm_apply _))
  · exact (incidentEquivOf_val iso _ _).symm.trans (congrArg Subtype.val (IE.apply_symm_apply _))
  · exact (incidentEquivOf_val iso _ _).symm.trans (congrArg Subtype.val (IE.apply_symm_apply _))
  · exact (incidentEquivOf_val iso _ _).symm.trans (congrArg Subtype.val (IE.apply_symm_apply _))

/-- **The Cardinality P shape pulls back**: the dangling occurrence stays above the doubled
direction. -/
theorem shape_pullback (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : TwoStar target₂ wall'} {block' : WallBlock second wall'}
    {profile : SourceProfile second star' block'} (shape : Shape profile)
    {block₁ : WallBlock first wall}
    (profile₁ : SourceProfile first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star')
      block₁)
    (hDouble : profile₁.doubleLabel = profile.doubleLabel)
    (hDeleted : iso.sourceEdgeEquiv profile₁.deleted.edge.1 = profile.deleted.edge.1) :
    Shape profile₁ := by
  refine ⟨iso.targetEdge.injective ?_⟩
  rw [M11WallExhaustion.pullbackTwoStar_edge, hDouble, ← shape.deleted_double, ← hDeleted]
  rfl

end Pullback

/-! ## 2.  At a divalent wall, a ramification-two block is the only ramified one -/

section Background

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : TwoStar target wall} {block : WallBlock data wall}

/-- **The classifier's `background` field is automatic**: the local ramifications above a
divalent wall add up to two (`W2SourceInput.sum_localRamification`), and a case-P block
carries both units. -/
theorem background_of_profile (input : W2SourceInput data star)
    (profile : SourceProfile data star block) :
    ∀ other : WallBlock data wall, other ≠ block → data.localRamification wall other = 0 := by
  classical
  intro other hNe
  have hPair : data.localRamification wall block + data.localRamification wall other ≤
      ∑ sourceBlock : WallBlock data wall, data.localRamification wall sourceBlock := by
    have hSubset := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun b : WallBlock data wall ↦ data.localRamification wall b)
      (Finset.subset_univ ({block, other} : Finset (WallBlock data wall)))
      (fun b _ _ ↦ input.localRamification_nonneg b)
    rwa [Finset.sum_pair (Ne.symm hNe)] at hSubset
  rw [input.sum_localRamification, profile.ramification] at hPair
  have hNonneg := input.localRamification_nonneg other
  omega

end Background

/-! ## 3.  Figure 35's pasted resolutions, as relations

All three members keep the whole wall block at the `t₃` endpoint and put one fine partition
on the `t₂` endpoint and on the new edge above `A₀` (`W2PSurvival.MemberShape`); the fine
partition is the `t₂` occurrence partition with the dangling sheet merged into `e₁`'s or
`e₂`'s class (`M⁽¹⁾`, `M⁽²⁾`), or the wall block with the dangling sheet detached
(`M⁽³⁾`). -/

section Shape

variable {d : ℕ}

/-- The merged partition, as a relation. -/
theorem mergeBlocks_rel_iff (P : SheetPartition d) (f e : Fin d) (h : ¬ P.Rel f e)
    (x y : Fin d) :
    (P.mergeBlocks f e h).Rel x y ↔
      ((P.Rel f x ∨ P.Rel e x) ∧ (P.Rel f y ∨ P.Rel e y)) ∨
        (¬ (P.Rel f x ∨ P.Rel e x) ∧ P.Rel x y) := by
  by_cases hx : P.Rel f x ∨ P.Rel e x
  · have hfx : (P.mergeBlocks f e h).Rel f x := (P.mergeBlocks_rel_first_iff f e x h).mpr hx
    constructor
    · intro hxy
      exact Or.inl ⟨hx, (P.mergeBlocks_rel_first_iff f e y h).mp (hfx.trans hxy)⟩
    · rintro (⟨-, hy⟩ | ⟨hx', -⟩)
      · exact hfx.symm.trans ((P.mergeBlocks_rel_first_iff f e y h).mpr hy)
      · exact (hx' hx).elim
  · have hBlock := P.mergeBlocks_block_of_separate f e x h (fun h' ↦ hx (Or.inl h'.symm))
      (fun h' ↦ hx (Or.inr h'.symm))
    rw [← SheetPartition.mem_block_iff, hBlock, SheetPartition.mem_block_iff]
    exact ⟨fun hxy ↦ Or.inr ⟨hx, hxy⟩, fun h' ↦ h'.elim (fun h'' ↦ (hx h''.1).elim) And.right⟩

/-- The detached partition, as a relation. -/
theorem detachSheet_rel_iff (W : SheetPartition d) (s r : Fin d) (hne : s ≠ r)
    (hTogether : W.Rel s r) (x y : Fin d) :
    (W.detachSheet s r hne hTogether).Rel x y ↔
      (x = s ∧ y = s) ∨ (x ≠ s ∧ y ≠ s ∧ W.Rel x y) := by
  by_cases hxs : x = s
  · subst hxs
    rw [W.detachSheet_rel_single_iff x r y hne hTogether]
    constructor
    · intro h; exact Or.inl ⟨rfl, h.symm⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h.symm
      · exact (h rfl).elim
  · by_cases hsx : W.Rel s x
    · -- `x` lies in the residual block
      have hRepr := W.detachSheet_repr_of_rel_of_ne s r x hne hTogether hxs hsx
      constructor
      · intro hxy
        by_cases hys : y = s
        · subst hys
          have := (W.detachSheet_rel_single_iff y r x hne hTogether).mp hxy.symm
          exact (hxs this.symm).elim
        · have hW := (W.detachSheet_refines s r hne hTogether).rel hxy
          exact Or.inr ⟨hxs, hys, hW⟩
      · rintro (⟨h, -⟩ | ⟨-, hys, hW⟩)
        · exact (hxs h).elim
        · have hsy : W.Rel s y := hsx.trans hW
          have hRepr' := W.detachSheet_repr_of_rel_of_ne s r y hne hTogether hys hsy
          change (W.detachSheet s r hne hTogether).repr x = (W.detachSheet s r hne hTogether).repr y
          rw [hRepr, hRepr']
    · have hBlock := W.detachSheet_block_of_not_rel s r x hne hTogether hsx
      rw [← SheetPartition.mem_block_iff, hBlock, SheetPartition.mem_block_iff]
      constructor
      · intro hW
        exact Or.inr ⟨hxs, fun hys ↦ hsx (hys ▸ hW.symm), hW⟩
      · rintro (⟨h, -⟩ | ⟨-, -, hW⟩)
        · exact (hxs h).elim
        · exact hW

variable {target : CFGraph} {wall : target.V} {data : GluingDatum target d}
  {star : TwoStar target wall} {block : WallBlock data wall}
  {profile : SourceProfile data star block}

/-- Figure 35's three member shapes, indexed as Equation (9). -/
noncomputable def shapeAt (shape : Shape profile) : Fin 3 → MemberShape profile :=
  ![firstShape shape, secondShape shape, thirdShape shape]

theorem shapeAt_candidate (shape : Shape profile) (q : Fin 3) :
    (shapeAt shape q).candidate = W2PCommonBalance.members profile shape q := by
  fin_cases q <;> rfl

theorem members_right (shape : Shape profile) (q : Fin 3) :
    (W2PCommonBalance.members profile shape q).right = (orientedStar profile).right := by
  fin_cases q <;> rfl

/-- **The pasted `t₂` endpoint of member `q`, as a relation.** -/
theorem pasted_left_rel (shape : Shape profile) (q : Fin 3) (x y : Fin d) :
    (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q)).left.Rel x y ↔
      (data.vertexPartition wall).Rel x y ∧
        ((data.vertexPartition wall).Rel block.1 x → (shapeAt shape q).fine.Rel x y) := by
  rw [← shapeAt_candidate]
  by_cases h : (data.vertexPartition wall).Rel block.1 x
  · refine ((shapeAt shape q).pasted_left_rel_iff_of_rel x y h).trans ?_
    exact ⟨fun h' ↦ ⟨(shapeAt shape q).refines.rel h', fun _ ↦ h'⟩, fun h' ↦ h'.2 h⟩
  · refine ((shapeAt shape q).pasted_left_rel_iff_of_not_rel x y h).trans ?_
    exact ⟨fun h' ↦ ⟨h', fun h'' ↦ (h h'').elim⟩, fun h' ↦ h'.1⟩

/-- **The pasted `t₃` endpoint of every member is the wall partition.** -/
theorem pasted_right_rel (shape : Shape profile) (q : Fin 3) (x y : Fin d) :
    (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q)).right.Rel x y ↔
      (data.vertexPartition wall).Rel x y := by
  rw [← shapeAt_candidate]
  exact Iff.of_eq (congrArg (fun P : SheetPartition d ↦ P.Rel x y)
    (shapeAt shape q).pasted_right_eq)

/-- **The pasted regrown occurrence of member `q`, as a relation** (the `t₂` endpoint's). -/
theorem pasted_newEdge_rel (shape : Shape profile) (q : Fin 3) (x y : Fin d) :
    (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q)).newEdge.Rel x y ↔
      (data.vertexPartition wall).Rel x y ∧
        ((data.vertexPartition wall).Rel block.1 x → (shapeAt shape q).fine.Rel x y) := by
  rw [← shapeAt_candidate]
  by_cases h : (data.vertexPartition wall).Rel block.1 x
  · refine ((shapeAt shape q).pasted_newEdge_rel_iff_of_rel x y h).trans ?_
    exact ⟨fun h' ↦ ⟨(shapeAt shape q).refines.rel h', fun _ ↦ h'⟩, fun h' ↦ h'.2 h⟩
  · refine ((shapeAt shape q).pasted_newEdge_rel_iff_of_not_rel x y h).trans ?_
    exact ⟨fun h' ↦ ⟨h', fun h'' ↦ (h h'').elim⟩, fun h' ↦ h'.1⟩

end Shape

/-! ## 4.  A decoupled transport from a member's shape

Everything a Figure 35 member's `t₂` endpoint and new edge see -- the `t₂` occurrence
partition, the wall partition and the three named sheets `e₁`, `e₂`, `e₄` -- is carried
exactly by the `t₂` occurrence permutation `E₂` of the datum isomorphism, and the `t₃`
endpoint is the wall partition, carried by the `t₃` occurrence permutation `E₃`.  So
the builder `M11StarExhaustionProof.nonempty_transportFree_of_rel` applies with
`τO = τN = E₂`, `τF = E₃`: no piecewise gluing and no coherence condition. -/

section Receipt

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (iso : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  (hWall : iso.targetVertex wall = wall')
  {star' : TwoStar target₂ wall'} {block' : WallBlock second wall'}
  {profile : SourceProfile second star' block'} (shape : Shape profile)
  {profile₁ : SourceProfile first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star')
    (blockPre iso wall block'.1)}
  (shape₁ : Shape profile₁)
  (hDouble : profile₁.doubleLabel = profile.doubleLabel)
  (hSingle : profile₁.singleLabel = profile.singleLabel)
  (hFirst : iso.sourceEdgeEquiv profile₁.first.1 = profile.first.1)
  (hSecond : iso.sourceEdgeEquiv profile₁.second.1 = profile.second.1)
  (hDeleted : iso.sourceEdgeEquiv profile₁.deleted.edge.1 = profile.deleted.edge.1)

include hDouble in
/-- An occurrence of the doubled direction has its sheet carried by `E₂`. -/
theorem sheet_map {e₁ : first.SourceEdge} {e : second.SourceEdge}
    (hTarget : e₁.1.1 = (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge
      profile₁.doubleLabel)
    (hMap : iso.sourceEdgeEquiv e₁ = e) :
    iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge
        profile.doubleLabel) e₁.1.2 = e.1.2 := by
  rw [← hMap, ← hDouble, ← hTarget]
  rfl

include hDouble hFirst hSecond hDeleted in
/-- **The fine partitions are natural**: member `q`'s fine partition over the pulled-back
profile is the wall's, along `E₂`. -/
theorem fine_rel_iff (q : Fin 3) (a b : Fin degree) :
    (shapeAt shape₁ q).fine.Rel a b ↔
      (shapeAt shape q).fine.Rel
        (iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge
          profile.doubleLabel) a)
        (iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge
          profile.doubleLabel) b) := by
  set E := iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge profile.doubleLabel)
  have hP : ∀ x y, (endpointPartition profile₁).Rel x y ↔
      (endpointPartition profile).Rel (E x) (E y) := by
    intro x y
    change (first.edgePartition ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge profile₁.doubleLabel)).Rel x y ↔
      (second.edgePartition (star'.edge profile.doubleLabel)).Rel (E x) (E y)
    rw [hDouble]
    exact W2R1StarExhaustionProof.edge_rel_iff iso hWall (star' := star') _ x y
  have hE : ∀ s, (first.vertexPartition wall).Rel
      ((iso.vertexPerm wall).symm (E s)) s :=
    fun s ↦ iso.compatible ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge profile.doubleLabel) wall
      (incident_of_edge (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star') profile.doubleLabel) s
  have hW := wall_rel_iff_of_agree iso hWall E hE
  have h1 : E (firstSheet profile₁) = firstSheet profile :=
    sheet_map iso hWall hDouble profile₁.first_target hFirst
  have h2 : E (secondSheet profile₁) = secondSheet profile :=
    sheet_map iso hWall hDouble profile₁.second_target hSecond
  have h4 : E (extraSheet profile₁) = extraSheet profile :=
    sheet_map iso hWall hDouble shape₁.deleted_double hDeleted
  fin_cases q
  · change ((endpointPartition profile₁).mergeBlocks (firstSheet profile₁) (extraSheet profile₁)
        (first_extra_separate shape₁)).Rel a b ↔
      ((endpointPartition profile).mergeBlocks (firstSheet profile) (extraSheet profile)
        (first_extra_separate shape)).Rel (E a) (E b)
    rw [mergeBlocks_rel_iff, mergeBlocks_rel_iff, hP, hP, hP, hP, hP, h1, h4]
  · change ((endpointPartition profile₁).mergeBlocks (secondSheet profile₁) (extraSheet profile₁)
        (second_extra_separate shape₁)).Rel a b ↔
      ((endpointPartition profile).mergeBlocks (secondSheet profile) (extraSheet profile)
        (second_extra_separate shape)).Rel (E a) (E b)
    rw [mergeBlocks_rel_iff, mergeBlocks_rel_iff, hP, hP, hP, hP, hP, h2, h4]
  · change (thirdFine shape₁).Rel a b ↔ (thirdFine shape).Rel (E a) (E b)
    unfold thirdFine
    rw [detachSheet_rel_iff, detachSheet_rel_iff, hW, ← h4]
    simp only [ne_eq, E.injective.eq_iff]

include shape shape₁ hDouble hSingle hFirst hSecond hDeleted in
/-- **The transport from a member's shape.**  A resolution with Figure 35's member-`q` shape
over the pulled-back profile is carried onto the wall's member `q` by a decoupled
transport along the datum isomorphism, with `τO = τN = E₂` and `τF = E₃`. -/
theorem nonempty_transport (res : LocalResolution degree) (q : Fin 3)
    (hL : ∀ x y, res.left.Rel x y ↔
      (M11StarCensusProof.pasted (W2PCommonBalance.members profile₁ shape₁ q)).left.Rel x y)
    (hR : ∀ x y, res.right.Rel x y ↔
      (M11StarCensusProof.pasted (W2PCommonBalance.members profile₁ shape₁ q)).right.Rel x y)
    (hN : ∀ x y, res.newEdge.Rel x y ↔
      (M11StarCensusProof.pasted (W2PCommonBalance.members profile₁ shape₁ q)).newEdge.Rel x y) :
    Nonempty (ResolutionExpansionFree.TransportFree iso wall wall'
      (orientedStar profile₁).right (W2PCommonBalance.members profile shape q).right res
      (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q))) := by
  set E2 := iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge
    profile.doubleLabel)
  set E3 := iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge
    profile.singleLabel)
  have hE2 : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (E2 s)) s :=
    fun s ↦ iso.compatible _ wall
      (incident_of_edge (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star') _) s
  have hE3 : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (E3 s)) s :=
    fun s ↦ iso.compatible _ wall
      (incident_of_edge (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star') _) s
  have hW2 := wall_rel_iff_of_agree iso hWall E2 hE2
  have hW3 := wall_rel_iff_of_agree iso hWall E3 hE3
  have hA : ∀ x, (first.vertexPartition wall).Rel (blockPre iso wall block'.1).1 x ↔
      (second.vertexPartition wall').Rel block'.1 (E2 x) :=
    fun x ↦ blockPre_rel_iff iso hWall E2 hE2 block'.1 x
  have hFine := fine_rel_iff iso hWall shape shape₁ hDouble hFirst hSecond hDeleted q
  have h32 : ∀ s, (first.vertexPartition wall).Rel (E3.symm (E2 s)) s := by
    intro s
    have h := hE3 (E3.symm (E2 s))
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (hE2 s)
  refine nonempty_transportFree_of_rel iso wall wall' (orientedStar profile₁).right
    (W2PCommonBalance.members profile shape q).right res
    (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q)) hWall ?_
    (fun x y h ↦ ((pasted_left_rel shape₁ q x y).mp ((hL x y).mp h)).1)
    (fun x y h ↦ (pasted_right_rel shape₁ q x y).mp ((hR x y).mp h))
    E2 E3 E2 hE2 hE3 ?_ ?_ ?_ ?_ ?_ ?_
  · intro edge
    rw [members_right]
    unfold TwoStar.right
    rw [orientedStar_edge_one, orientedStar_edge_one, hSingle,
      ← M11WallExhaustion.pullbackTwoStar_edge iso wall wall' hWall star' profile.singleLabel]
    exact decide_eq_decide.mpr iso.targetEdge.injective.eq_iff
  · intro a b
    rw [hL, pasted_left_rel, pasted_left_rel, hW2, hA, hFine]
  · intro a b
    rw [hR, pasted_right_rel, pasted_right_rel, hW3]
  · intro a b
    rw [hN, pasted_newEdge_rel, pasted_newEdge_rel, hW2, hA, hFine]
  · intro s
    rw [Equiv.symm_apply_apply]
    exact rfl
  · intro s
    exact (hR _ _).mpr ((pasted_right_rel shape₁ q _ _).mpr (h32 s))
  · intro edge hInc s
    rcases eq_edge_of_incident (orientedStar profile₁) edge hInc with rfl | rfl
    · rw [TwoStar.right_edge_zero]
      simp only [Bool.false_eq_true, if_false]
      rw [show iso.edgePerm ((orientedStar profile₁).edge 0) s = E2 s by
        rw [orientedStar_edge_zero, hDouble], Equiv.symm_apply_apply]
      exact rfl
    · rw [TwoStar.right_edge_one]
      simp only [if_true]
      rw [show iso.edgePerm ((orientedStar profile₁).edge 1) s = E3 s by
        rw [orientedStar_edge_one, hSingle], Equiv.symm_apply_apply]
      exact rfl

end Receipt

/-! ## 5.  Part I's census at an arbitrary member

At a regrowth `mem` carrying a W2 input and a case-P profile and shape on its own limit (the
wall's, pulled back), Part I's incoming census (`W2PIncomingMatching`) says the regrowth's
own cover is Figure 35's member `q` for some `q`: its normal form at the oriented star's
placement has member `q`'s three pasted partitions, as relations.  This is
`W2PIncomingMatching.wall_blocks` read at the placement the normal form uses. -/

section MemberCensus

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

private theorem rel_iff_of_block_eq {d : ℕ} {P Q : SheetPartition d} {x : Fin d}
    (h : P.block x = Q.block x) (y : Fin d) : P.Rel x y ↔ Q.Rel x y := by
  rw [← SheetPartition.mem_block_iff, h, SheetPartition.mem_block_iff]

/-- **The member's own normal form has Figure 35's member-`q` shape**, for some `q`. -/
theorem member_census (mem : Regrowth core y degree) (hy : Nondegenerate y)
    {star : TwoStar (mem.frame.limitTarget mem.column) (mergeVertex mem)}
    (input : W2SourceInput mem.limit star) {block : WallBlock mem.limit (mergeVertex mem)}
    {profile : SourceProfile mem.limit star block} (shape : Shape profile)
    (hPlacement : PlacementSpec mem (orientedStar profile).right) :
    ∃ q : Fin 3,
      (∀ x y, (memberResolution mem (orientedStar profile).right hPlacement).left.Rel x y ↔
        (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q)).left.Rel x y) ∧
      (∀ x y, (memberResolution mem (orientedStar profile).right hPlacement).right.Rel x y ↔
        (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q)).right.Rel x y) ∧
      (∀ x y, (memberResolution mem (orientedStar profile).right hPlacement).newEdge.Rel x y ↔
        (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q)).newEdge.Rel
          x y) := by
  have hForest := InheritedLimitRows.forest mem hy
  have hBackground := background_of_profile input profile
  obtain ⟨q, hSel⟩ := W2PIncomingMatching.exists_selector mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    mem.frame.fullDim hForest star profile shape hBackground
  have hCensus := W2PIncomingMatching.census_of_selector mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    mem.frame.fullDim hForest star profile shape hBackground q hSel
  have hEnds := W2PIncomingMatching.transported_endpoints mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    mem.frame.fullDim hForest star profile shape hBackground (orientedStar profile).right rfl
    hPlacement
  have hNew := M11IncomingOuterPartitions.transported_edgePartition_new mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    (orientedStar profile).right hPlacement mem.frame.fullDim.targetConnected
    mem.frame.fullDim.targetGenus
  refine ⟨q, fun x y ↦ ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩
  · have hB := W2PIncomingMatching.block_eq_of_split_dictionary
      (ContractionRamification.mergedPartition mem.frame.data _ _) block.1
      (W2PIncomingCensus.memberShape mem.frame.data rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
        (mem.frame.numEdges_edgeOf mem.column) star profile shape q).fine
      (ContractionRamification.mergedPartition mem.frame.data _ _) _ _ hCensus
      (W2PIncomingMatching.member_left_selected mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
        profile shape q)
      (W2PIncomingCensus.background_block_doubleEnd mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        mem.frame.fullDim hForest star profile shape hBackground)
      (W2PIncomingMatching.member_left_background mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
        profile shape q) x
    exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hEnds.1)).trans
      (rel_iff_of_block_eq hB y)
  · have hB := W2PIncomingMatching.block_eq_of_split_dictionary
      (ContractionRamification.mergedPartition mem.frame.data _ _) block.1
      (ContractionRamification.mergedPartition mem.frame.data _ _) (ContractionRamification.mergedPartition mem.frame.data _ _)
      (mem.frame.data.vertexPartition (W2PIncomingCensus.singleEnd mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
        profile))
      (M11StarCensusProof.pasted (W2PCommonBalance.members profile shape q)).right
      (W2PIncomingCensus.singleEnd_block mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        mem.frame.fullDim hForest star profile shape hBackground)
      (fun sheet _ ↦ W2PIncomingMatching.member_right_block mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
        profile shape q sheet)
      (W2PIncomingCensus.background_block_singleEnd mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        mem.frame.fullDim hForest star profile shape hBackground)
      (fun sheet _ ↦ W2PIncomingMatching.member_right_block mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
        profile shape q sheet) x
    exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hEnds.2)).trans
      (rel_iff_of_block_eq hB y)
  · have hB := W2PIncomingMatching.block_eq_of_split_dictionary
      (ContractionRamification.mergedPartition mem.frame.data _ _) block.1
      (W2PIncomingCensus.memberShape mem.frame.data rfl (fst_ne_snd (mem.frame.edgeOf mem.column))
        (mem.frame.numEdges_edgeOf mem.column) star profile shape q).fine
      (ContractionRamification.mergedPartition mem.frame.data _ _) _ _
      (fun sheet hSheet ↦ (W2PIncomingCensus.contracted_block_eq_doubleEnd_block mem.frame.data
        rfl (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        mem.frame.fullDim hForest star profile shape hBackground sheet hSheet).trans
          (hCensus sheet hSheet))
      (W2PIncomingMatching.member_newEdge_selected mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
        profile shape q)
      (W2PIncomingCensus.background_block_contracted mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
        mem.frame.fullDim hForest star profile shape hBackground)
      (W2PIncomingMatching.member_newEdge_background mem.frame.data rfl
        (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column) star
        profile shape q) x
    exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hNew)).trans
      (rel_iff_of_block_eq hB y)

end MemberCensus

/-! ## 6.  A position that receives a member is nonsingular -/

section Nonsingular

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree}
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (W2PCommonBalance.members profile shape incoming).datum (Fin p))

/-- **Any full-dimensional presentation of a position's datum makes the position
nonsingular** (as `M11StarExhaustionProof.nonsingular_of_fullDim`, at Equation (9)'s
labelling): the two labellings differ by a row and a column permutation. -/
theorem nonsingular_of_fullDim (q : Fin 3)
    (fd : FullDimensionalSourcePresentation (W2PCommonBalance.members profile shape q).datum
      (Fin p)) :
    W2PStarCensusProof.Nonsingular w input shape incomingFD q := by
  classical
  unfold W2PStarCensusProof.Nonsingular
  rw [DraismaVargas.Count.matrix_labelling_submatrix
    (W2PStarCensusProof.lab w input shape incomingFD q) fd.labelling]
  intro h
  have hAbs := Matrix.abs_det_submatrix_equiv_equiv
    ((W2PStarCensusProof.lab w input shape incomingFD q).row.symm.trans fd.labelling.row)
    ((W2PStarCensusProof.lab w input shape incomingFD q).targetEdge.trans
      fd.labelling.targetEdge.symm)
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
  rw [h, abs_zero] at hAbs
  exact fd.det_ne_zero (abs_eq_zero.mp hAbs.symm)

end Nonsingular

/-- **A received member hands its full-dimensional presentation to the position**: its own
cover, normalized and lifted along the transport. -/
noncomputable def fdOfTransport {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
    (mem : Regrowth core y degree)
    (placement : (mem.frame.limitTarget mem.column).edges → Bool)
    (hPlacement : PlacementSpec mem placement)
    {T : CFGraph} {second : GluingDatum T degree} (iso : GeometricDatumIso mem.limit second)
    {otherWall : T.V} {R : T.edges → Bool} {res' : LocalResolution degree}
    (hOther : GlobalResolution.OldCompatible second otherWall R res')
    (t : ResolutionExpansionFree.TransportFree iso (mergeVertex mem) otherWall placement R
      (memberResolution mem placement hPlacement) res') :
    FullDimensionalSourcePresentation (GlobalResolution.datum second otherWall R res' hOther)
      (Fin p) :=
  GeometricMultiplicity.transportFullDim
    ((memberNorm mem placement hPlacement).trans
      (ResolutionExpansionFree.liftFree iso (mergeVertex mem) otherWall placement R
        (memberResolution mem placement hPlacement) res'
        (M11WallExhaustion.incomingOldCompatible mem.frame.data rfl
          (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
          placement hPlacement mem.frame.fullDim.targetConnected mem.frame.fullDim.targetGenus)
        hOther t))
    mem.frame.fullDim

/-! ## 7.  Exhaustion, and the family clause -/

section Exhaustion

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) {block : WallBlock w.limit (mergeVertex w)}
  {profile : SourceProfile w.limit star block} (shape : Shape profile)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (W2PCommonBalance.members profile shape incoming).datum (Fin p))

/-- **Every star member is received, by a position transport, at a nonsingular
position.** -/
theorem exists_receipt (member : GeometricStar.StarMember hy w) :
    ∃ ψ : GeometricStar.LimitIso hy member.member w,
    ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
    ∃ hPlacement : PlacementSpec member.member placement,
    ∃ q : Fin 3, ∃ _ : W2PStarCensusProof.Nonsingular w input shape incomingFD q,
      Nonempty (W2PStarCensusProof.PositionTransport w hy shape member.member ψ placement
        hPlacement q) := by
  obtain ⟨ψ⟩ := member.specializes
  set mem := member.member
  set iso := ψ.datum.trans (GeometricDatumIso.refl w.limit).symm
  have hW : iso.targetVertex (mergeVertex mem) = mergeVertex w :=
    M11StarCensusProof.pinned w hy input mem ψ
  have input₁ := input_pullback iso hW input
  obtain ⟨profile₁, hDouble, hSingle, hFirst, hSecond, -, hDeleted⟩ :=
    exists_profile_pullback iso (InheritedLimitRows.limit_connected mem) hW profile
  have shape₁ := shape_pullback iso hW shape profile₁ hDouble hDeleted
  have hPlacement : PlacementSpec mem (orientedStar profile₁).right :=
    W2PIncomingCensus.member_placement mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      mem.frame.fullDim (InheritedLimitRows.forest mem hy) _ profile₁ shape₁
      (background_of_profile input₁ profile₁)
  obtain ⟨q, hL, hR, hN⟩ := member_census mem hy input₁ shape₁ hPlacement
  obtain ⟨t⟩ := nonempty_transport iso hW shape shape₁ hDouble hSingle hFirst hSecond hDeleted
    _ q hL hR hN
  exact ⟨ψ, _, hPlacement, q,
    nonsingular_of_fullDim input shape incomingFD q
      (fdOfTransport mem _ hPlacement iso (GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (W2PCommonBalance.members profile shape q).exterior) t), ⟨t⟩⟩

/-- **Stage 2 at one wall: the nonsingular positions exhaust the star.** -/
theorem exhausts : W2PStarCensusProof.Exhausts w hy input shape incomingFD :=
  W2PStarCensusProof.exhausts_of_transports w hy input shape incomingFD
    (exists_receipt w hy input shape incomingFD)

end Exhaustion

/-- **The W2P star exhaustion, at every core, degree and request.** -/
theorem w2PStarExhaustion (degree n p : ℕ) : W2PStarCensusProof.W2PStarExhaustion degree n p :=
  fun _ _ hy w _ _ _ input _ _ shape _ incomingFD ↦ exhausts w hy input shape incomingFD

/-- **The W2P star census**, unconditionally. -/
theorem w2PStarCensus (degree n p : ℕ) : W2PStarCensusProof.W2PStarCensus degree n p :=
  W2PStarCensusProof.w2PStarCensus_of_exhaustion (w2PStarExhaustion degree n p)

/-- **The `w2P` clause of `FamilyStarParity`, at every degree, core size and request.** -/
theorem familyStarParity_w2P_general (degree n p : ℕ) :
    RegrowthWallInput.FamilyStarParity degree n p .w2P :=
  W2PStarCensusProof.familyStarParity_w2P_of_census (w2PStarCensus degree n p)

/-- **The `w2P` clause of `FamilyStarParity` at genus six and degree four, with no
hypothesis.** -/
theorem familyStarParity_w2P :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2P :=
  W2PStarCensusProof.familyStarParity_w2P_of_exhaustion (w2PStarExhaustion _ _ _)

end DraismaVargas.Count.W2PStarExhaustionProof
