module

public import DraismaVargasCount.W2R1StarCensusProof
public import DraismaVargasCount.M11StarExhaustionProof

@[expose] public section

/-!
# W2R1 star exhaustion: the `w2R1` clause with no hypothesis

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r1}`, Figures 37 and 38,
Equation (10); Vargas, Part II (arXiv:2609.09109), the star of a wall.  This file proves the
exhaustion that `W2R1StarCensusProof` reduces the census to (its `W2R1StarExhaustion`), using
the transport builder `M11StarExhaustionProof.nonempty_transportFree_of_rel`.

## The result, in one paragraph

Every member of a `w2R1` wall's star receives a `PositionTransport` onto one of Equation
(10)'s two positions (`exists_receipt`), so the star is exhausted (`exhausts`), and
`FamilyStarParity … .w2R1` holds **with no hypothesis**, at every degree, core size and
positive request (`familyStarParity_w2R1_general`, `familyStarParity_w2R1`).  A member
`m` with limit isomorphism `ψ` gets the wall's W2 input (`M11StarExhaustionProof.input_pullback`)
and the wall's `{w2-r1}` pair (`exists_pair_pullback`) pulled back along `ψ`; Part I's incoming
census at `m` (`W2R1IncomingMatching`) then says its normal form at the star's own
placement has Figure 37/38's member-`q` shape for some `q` (`member_census`); and a
member-`q` shape over the pulled-back pair is carried onto the wall's member `q` by the
builder, with the regrown occurrence's permutation glued from the two wall-direction
occurrence permutations (`newPerm`, `nonempty_transport`).  **No coherence dichotomy
arises**: unlike M-11, where a split member's two occurrence permutations may disagree on the
distinguished block and the branch swap repairs it, here each endpoint partition involves a
single wall direction, so each is carried by that direction's own permutation, and the
member lands at the position of the same index.

## What is proved

* §1 `exists_profile_pullback`, `exists_pair_pullback`: a `W2R1SourceProfile.SourceProfile`
  and a `W2R1SourceCandidates.Pair` pull back along an arbitrary `GeometricDatumIso`, keeping
  their direction labels and sending blocks to `M11StarExhaustionProof.blockPre`.
* §2 `Fine` (the sheets member `q` resolves with direction `l`), `fine_congr`,
  `not_fine_one_of_fine_zero`, `memberLocal_left_rel`, `memberLocal_right_rel`,
  `memberLocal_newEdge_rel`, and `pasted_left_rel`, `pasted_right_rel`,
  `pasted_newEdge_rel`: Figures 37/38's pasted resolutions as relations.
* §3 `blockPre_rel_iff`, `fine_pullback` (naturality), `edge_rel_iff`, `newPerm`,
  `newPerm_apply`, and **`nonempty_transport`**: a member-`q` shape is received at
  position `q`, family-free in the datum isomorphism.
* §4 `member_census`: Part I's census at an arbitrary regrowth, in relational form.
* §5 `exists_receipt`, `exhausts`; `w2R1StarExhaustion`, `w2R1StarCensus`,
  `familyStarParity_w2R1_general`, and the headline **`familyStarParity_w2R1`**.

## What is NOT proved (every surviving hypothesis, explicitly)

* Nothing is assumed: the headlines have no hypothesis beyond their binders.  `exhausts`
  does not use the `w2R1` classification tag; it holds at every regrowth carrying a W2 input
  and a `{w2-r1}` pair.
* The clause is not exhibited at a concrete `w2R1` regrowth: none is constructed in this
  library, and no example with an inhabited antecedent is given.  A computer enumeration of
  walls (not part of this library) finds one `R1` wall, with two classes of multiplicity one,
  as the census proves must happen.
* `ResolutionExpansion.Transport` (the strict wall-permutation transport) is not produced;
  the receipts are decoupled `TransportFree`s, which is what `exhausts_of_transports`
  consumes.

## Consumers

`StarSupplyAssembly`, through `familyStarParity_w2R1` (the `w2R1` clause of
`FamilyStarParity`, with no hypothesis), and so the star parity of step 2 (trivalent walls)
of `DraismaVargasCount/Assembly.lean`.
-/

namespace DraismaVargas.Count.W2R1StarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open W2R1Target SecondEquation W4Assembly W2R1SourceCandidates
open ResolutionM11 (LocalResolution)
open M11StarExhaustionProof (blockPre blockPre_rel sourceVertexEquiv_blockPre blockCard_blockPre
  localRamification_blockPre nonDanglingValency_blockPre input_pullback incidentEquivOf
  incidentEquivOf_target wall_rel_iff wall_rel_iff_of_agree eq_edge_of_incident incident_of_edge
  nonempty_transportFree_of_rel)
open W3Nd2StarCensusProof (PlacementSpec memberResolution)

/-! ## 1.  The `{w2-r1}` profile and pair, pulled back along a datum isomorphism -/

section Pullback

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- **A ramification-one profile pulls back along a datum isomorphism**, to the pulled-back
star and block, keeping its direction labels. -/
theorem exists_profile_pullback (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : TwoStar target₂ wall'} {block' : WallBlock second wall'}
    (profile : W2R1SourceProfile.SourceProfile second star' block') :
    ∃ profile₁ : W2R1SourceProfile.SourceProfile first
        (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star')
        (blockPre iso wall block'.1),
      profile₁.doubleLabel = profile.doubleLabel := by
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
  have hCard := blockCard_blockPre iso hWall block'.1
  have h1 := hIndex (IE.symm profile.first)
  have h2 := hIndex (IE.symm profile.second)
  have h3 := hIndex (IE.symm profile.third)
  rw [Equiv.apply_symm_apply] at h1 h2 h3
  have hVal := nonDanglingValency_blockPre iso hConnected hWall block'
  refine ⟨{ doubleLabel := profile.doubleLabel
            singleLabel := profile.singleLabel
            labels_ne := profile.labels_ne
            first := IE.symm profile.first
            second := IE.symm profile.second
            third := IE.symm profile.third
            first_ne_second := fun h ↦ profile.first_ne_second (IE.symm.injective h)
            first_target := by rw [hTarget, Equiv.apply_symm_apply]; exact profile.first_target
            second_target := by rw [hTarget, Equiv.apply_symm_apply]; exact profile.second_target
            third_target := by rw [hTarget, Equiv.apply_symm_apply]; exact profile.third_target
            exhaustive := by
              intro e
              rcases profile.exhaustive (IE e) with h | h | h
              · exact Or.inl (IE.eq_symm_apply.mpr h)
              · exact Or.inr (Or.inl (IE.eq_symm_apply.mpr h))
              · exact Or.inr (Or.inr (IE.eq_symm_apply.mpr h))
            pair_index := by rw [← h1, ← h2, hCard]; exact profile.pair_index
            single_index := by rw [← h3, hCard]; exact profile.single_index
            ramification := by
              rw [localRamification_blockPre iso hWall block']; exact profile.ramification
            second_survives := by
              rw [← hDang, Equiv.apply_symm_apply]; exact profile.second_survives
            third_survives := by
              rw [← hDang, Equiv.apply_symm_apply]; exact profile.third_survives
            cases := by
              rw [hVal, ← hDang, Equiv.apply_symm_apply, ← h1, ← h2, ← h3]
              exact profile.cases }, rfl⟩

/-- **A `{w2-r1}` pair pulls back along a datum isomorphism**: its two blocks to their
preimage blocks, its profiles with their labels, its background by
`localRamification_blockPre`. -/
theorem exists_pair_pullback (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : TwoStar target₂ wall'} (pair : Pair second star') :
    ∃ pair₁ : Pair first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star'),
      pair₁.first = blockPre iso wall pair.first.1 ∧
      pair₁.second = blockPre iso wall pair.second.1 ∧
      pair₁.firstProfile.doubleLabel = pair.firstProfile.doubleLabel ∧
      pair₁.secondProfile.doubleLabel = pair.secondProfile.doubleLabel := by
  classical
  obtain ⟨p1, hp1⟩ := exists_profile_pullback iso hConnected hWall pair.firstProfile
  obtain ⟨p2, hp2⟩ := exists_profile_pullback iso hConnected hWall pair.secondProfile
  set W := first.vertexPartition wall
  set W' := second.vertexPartition wall'
  have hPreRel : ∀ block' : WallBlock second wall', ∀ block : WallBlock first wall,
      blockPre iso wall block'.1 = block ↔ W'.Rel block'.1 (iso.vertexPerm wall block.1) := by
    intro block' block
    constructor
    · rintro rfl
      rw [wall_rel_iff iso hWall, Equiv.symm_apply_apply]
      exact (blockPre_rel iso wall block'.1).symm
    · intro h
      apply Subtype.ext
      have hRel : W.Rel ((iso.vertexPerm wall).symm block'.1) block.1 := by
        rw [wall_rel_iff iso hWall, Equiv.symm_apply_apply] at h
        exact h
      change W.repr ((iso.vertexPerm wall).symm block'.1) = block.1
      rw [show W.repr ((iso.vertexPerm wall).symm block'.1) = W.repr block.1 from hRel]
      exact block.2
  refine ⟨{ first := blockPre iso wall pair.first.1
            second := blockPre iso wall pair.second.1
            distinct := ?_
            firstProfile := p1
            secondProfile := p2
            background := ?_ }, rfl, rfl, hp1, hp2⟩
  · intro h
    apply pair.separate
    have h' := (hPreRel pair.second (blockPre iso wall pair.first.1)).mp h.symm
    have h2 : W'.Rel (iso.vertexPerm wall (blockPre iso wall pair.first.1).1) pair.first.1 := by
      rw [wall_rel_iff iso hWall, Equiv.symm_apply_apply]
      exact blockPre_rel iso wall pair.first.1
    exact (h'.trans h2).symm
  · intro block hA hB
    set block' := WallBlock.ofSheet second wall' (iso.vertexPerm wall block.1)
    have hPre : blockPre iso wall block'.1 = block :=
      (hPreRel block' block).mpr (W'.rel_repr_left _)
    rw [← hPre, localRamification_blockPre iso hWall block']
    refine pair.background block' ?_ ?_
    · intro h
      exact hA (hPre.symm.trans (congrArg (fun b : WallBlock second wall' ↦
        blockPre iso wall b.1) h))
    · intro h
      exact hB (hPre.symm.trans (congrArg (fun b : WallBlock second wall' ↦
        blockPre iso wall b.1) h))

end Pullback

/-! ## 2.  Figures 37/38's pasted resolutions, as relations

Above a ramification-one block a member is either joined (`position = double`) or resolves
the block with its doubled direction's occurrence partition, on that direction's endpoint
and on the new edge (`sideFine`).  So each pasted partition is the wall relation,
strengthened by the direction-`l` occurrence relation exactly on the sheets where the member
resolves with direction `l` (`Fine`). -/

section Shape

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : TwoStar target wall}

/-- **The sheets where Equation (10)'s member `q` resolves with direction `l`**: the block
`A₀` if `q ≠ δ(A₀) = l`, the block `B₀` if `other q ≠ δ(B₀) = l`. -/
def Fine (pair : Pair data star) (q l : Fin 2) (x : Fin degree) : Prop :=
  ((data.vertexPartition wall).Rel pair.first.1 x ∧ q ≠ pair.firstProfile.doubleLabel ∧
      pair.firstProfile.doubleLabel = l) ∨
    ((data.vertexPartition wall).Rel pair.second.1 x ∧
      W2R1SourceCandidates.other q ≠ pair.secondProfile.doubleLabel ∧
      pair.secondProfile.doubleLabel = l)

noncomputable instance (pair : Pair data star) (q l : Fin 2) : DecidablePred (Fine pair q l) :=
  Classical.decPred _

theorem fine_congr (pair : Pair data star) (q l : Fin 2) {x y : Fin degree}
    (h : (data.vertexPartition wall).Rel x y) : Fine pair q l x ↔ Fine pair q l y := by
  unfold Fine
  constructor
  · rintro (⟨hA, h1, h2⟩ | ⟨hB, h1, h2⟩)
    · exact Or.inl ⟨hA.trans h, h1, h2⟩
    · exact Or.inr ⟨hB.trans h, h1, h2⟩
  · rintro (⟨hA, h1, h2⟩ | ⟨hB, h1, h2⟩)
    · exact Or.inl ⟨hA.trans h.symm, h1, h2⟩
    · exact Or.inr ⟨hB.trans h.symm, h1, h2⟩

/-- A sheet is resolved with at most one direction. -/
theorem not_fine_one_of_fine_zero (pair : Pair data star) (q : Fin 2) {x : Fin degree}
    (h0 : Fine pair q 0 x) : ¬ Fine pair q 1 x := by
  rintro (⟨hA, -, h1⟩ | ⟨hB, -, h1⟩) <;> rcases h0 with ⟨hA', -, h0⟩ | ⟨hB', -, h0⟩
  · exact absurd (h0.symm.trans h1) (by decide)
  · exact pair.separate (hA.trans hB'.symm)
  · exact pair.separate (hA'.trans hB.symm)
  · exact absurd (h0.symm.trans h1) (by decide)

theorem memberLocal_left_rel (d q : Fin 2) (x y : Fin degree) :
    (memberLocal data star d q).left.Rel x y ↔
      (data.vertexPartition wall).Rel x y ∧
        (q ≠ d ∧ d = 0 → (data.edgePartition (star.edge 0)).Rel x y) := by
  unfold memberLocal
  split_ifs with hq
  · exact ⟨fun h ↦ ⟨h, fun h' ↦ (h'.1 hq).elim⟩, fun h ↦ h.1⟩
  · by_cases hd : d = 0
    · rw [sideFine_left_of_zero data star hd]
      subst hd
      exact ⟨fun h ↦ ⟨(star.edgePartition_refines_wall data 0).rel h, fun _ ↦ h⟩,
        fun h ↦ h.2 ⟨hq, rfl⟩⟩
    · rw [sideFine_left_of_ne_zero data star hd]
      exact ⟨fun h ↦ ⟨h, fun h' ↦ (hd h'.2).elim⟩, fun h ↦ h.1⟩

theorem memberLocal_right_rel (d q : Fin 2) (x y : Fin degree) :
    (memberLocal data star d q).right.Rel x y ↔
      (data.vertexPartition wall).Rel x y ∧
        (q ≠ d ∧ d = 1 → (data.edgePartition (star.edge 1)).Rel x y) := by
  unfold memberLocal
  split_ifs with hq
  · exact ⟨fun h ↦ ⟨h, fun h' ↦ (h'.1 hq).elim⟩, fun h ↦ h.1⟩
  · by_cases hd : d = 0
    · rw [sideFine_right_of_zero data star hd]
      exact ⟨fun h ↦ ⟨h, fun h' ↦ absurd (hd.symm.trans h'.2) (by decide)⟩, fun h ↦ h.1⟩
    · have hd1 : d = 1 := by omega
      rw [sideFine_right_of_ne_zero data star hd]
      subst hd1
      exact ⟨fun h ↦ ⟨(star.edgePartition_refines_wall data 1).rel h, fun _ ↦ h⟩,
        fun h ↦ h.2 ⟨hq, rfl⟩⟩

theorem memberLocal_newEdge_rel (d q : Fin 2) (x y : Fin degree) :
    (memberLocal data star d q).newEdge.Rel x y ↔
      (data.vertexPartition wall).Rel x y ∧
        (q ≠ d ∧ d = 0 → (data.edgePartition (star.edge 0)).Rel x y) ∧
        (q ≠ d ∧ d = 1 → (data.edgePartition (star.edge 1)).Rel x y) := by
  unfold memberLocal
  split_ifs with hq
  · exact ⟨fun h ↦ ⟨h, fun h' ↦ (h'.1 hq).elim, fun h' ↦ (h'.1 hq).elim⟩, fun h ↦ h.1⟩
  · rw [sideFine_newEdge]
    by_cases hd : d = 0
    · subst hd
      exact ⟨fun h ↦ ⟨(star.edgePartition_refines_wall data 0).rel h, fun _ ↦ h,
          fun h' ↦ absurd h'.2 (by decide)⟩,
        fun h ↦ h.2.1 ⟨hq, rfl⟩⟩
    · have hd1 : d = 1 := by omega
      subst hd1
      exact ⟨fun h ↦ ⟨(star.edgePartition_refines_wall data 1).rel h,
          fun h' ↦ absurd h'.2 (by decide), fun _ ↦ h⟩,
        fun h ↦ h.2.2 ⟨hq, rfl⟩⟩

/-- The three regions of a sheet: the pasted resolution at a sheet is the pair's local
resolution there. -/
private theorem resolution_cases (pair : Pair data star) (q : Fin 2) (x : Fin degree) :
    ((data.vertexPartition wall).Rel pair.first.1 x ∧
        pair.resolution q ((data.vertexPartition wall).repr x) =
          memberLocal data star pair.firstProfile.doubleLabel q ∧
        ¬ (data.vertexPartition wall).Rel pair.second.1 x) ∨
      ((data.vertexPartition wall).Rel pair.second.1 x ∧
        pair.resolution q ((data.vertexPartition wall).repr x) =
          memberLocal data star pair.secondProfile.doubleLabel (W2R1SourceCandidates.other q) ∧
        ¬ (data.vertexPartition wall).Rel pair.first.1 x) ∨
      (¬ (data.vertexPartition wall).Rel pair.first.1 x ∧
        ¬ (data.vertexPartition wall).Rel pair.second.1 x ∧
        pair.resolution q ((data.vertexPartition wall).repr x) =
          ResolutionM11.joinedResolutionAt (data.vertexPartition wall)) := by
  set W := data.vertexPartition wall
  by_cases hA : W.Rel pair.first.1 x
  · exact Or.inl ⟨hA, pair.resolution_of_first q (hA.trans (W.rel_repr_right x)),
      fun hB ↦ pair.separate (hA.trans hB.symm)⟩
  · by_cases hB : W.Rel pair.second.1 x
    · exact Or.inr (Or.inl ⟨hB, pair.resolution_of_second q (hB.trans (W.rel_repr_right x)),
        hA⟩)
    · exact Or.inr (Or.inr ⟨hA, hB, pair.resolution_of_background q
        (fun h ↦ hA (h.trans (W.rel_repr_left x))) (fun h ↦ hB (h.trans (W.rel_repr_left x)))⟩)

/-- **The pasted `t`-direction-`0` endpoint, as a relation.** -/
theorem pasted_left_rel (pair : Pair data star) (q : Fin 2) (x y : Fin degree) :
    (M11StarCensusProof.pasted (pair.candidate q)).left.Rel x y ↔
      (data.vertexPartition wall).Rel x y ∧
        (Fine pair q 0 x → (data.edgePartition (star.edge 0)).Rel x y) := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall) (pair.candidate q).resolution
    (pair.candidate q).contracts).Rel x y ↔ _
  unfold LocalResolution.pasteLeft
  rw [SheetPartition.paste_rel_iff]
  change (pair.resolution q ((data.vertexPartition wall).repr x)).left.Rel x y ↔ _
  rcases resolution_cases pair q x with ⟨hA, hRes, hB⟩ | ⟨hB, hRes, hA⟩ | ⟨hA, hB, hRes⟩
  · rw [hRes, memberLocal_left_rel]
    simp only [Fine, hA, hB, true_and, false_and, or_false]
  · rw [hRes, memberLocal_left_rel]
    simp only [Fine, hA, hB, true_and, false_and, false_or]
  · rw [hRes]
    simp only [Fine, hA, hB, false_and, or_self, false_imp_iff, and_true]
    rfl

/-- **The pasted direction-`1` endpoint, as a relation.** -/
theorem pasted_right_rel (pair : Pair data star) (q : Fin 2) (x y : Fin degree) :
    (M11StarCensusProof.pasted (pair.candidate q)).right.Rel x y ↔
      (data.vertexPartition wall).Rel x y ∧
        (Fine pair q 1 x → (data.edgePartition (star.edge 1)).Rel x y) := by
  change (LocalResolution.pasteRight (data.vertexPartition wall) (pair.candidate q).resolution
    (pair.candidate q).contracts).Rel x y ↔ _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_rel_iff]
  change (pair.resolution q ((data.vertexPartition wall).repr x)).right.Rel x y ↔ _
  rcases resolution_cases pair q x with ⟨hA, hRes, hB⟩ | ⟨hB, hRes, hA⟩ | ⟨hA, hB, hRes⟩
  · rw [hRes, memberLocal_right_rel]
    simp only [Fine, hA, hB, true_and, false_and, or_false]
  · rw [hRes, memberLocal_right_rel]
    simp only [Fine, hA, hB, true_and, false_and, false_or]
  · rw [hRes]
    simp only [Fine, hA, hB, false_and, or_self, false_imp_iff, and_true]
    rfl

/-- **The pasted regrown occurrence, as a relation.** -/
theorem pasted_newEdge_rel (pair : Pair data star) (q : Fin 2) (x y : Fin degree) :
    (M11StarCensusProof.pasted (pair.candidate q)).newEdge.Rel x y ↔
      (data.vertexPartition wall).Rel x y ∧
        (Fine pair q 0 x → (data.edgePartition (star.edge 0)).Rel x y) ∧
        (Fine pair q 1 x → (data.edgePartition (star.edge 1)).Rel x y) := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall) (pair.candidate q).resolution
    (pair.candidate q).contracts).Rel x y ↔ _
  unfold LocalResolution.pasteNewEdge
  rw [SheetPartition.paste_rel_iff]
  change (pair.resolution q ((data.vertexPartition wall).repr x)).newEdge.Rel x y ↔ _
  rcases resolution_cases pair q x with ⟨hA, hRes, hB⟩ | ⟨hB, hRes, hA⟩ | ⟨hA, hB, hRes⟩
  · rw [hRes, memberLocal_newEdge_rel]
    simp only [Fine, hA, hB, true_and, false_and, or_false]
  · rw [hRes, memberLocal_newEdge_rel]
    simp only [Fine, hA, hB, true_and, false_and, false_or]
  · rw [hRes]
    simp only [Fine, hA, hB, false_and, or_self, false_imp_iff, and_true]
    rfl

end Shape

/-! ## 3.  The receipt: a decoupled transport from a member's shape

A datum isomorphism carries each wall-direction occurrence relation exactly along its own
occurrence permutation, and carries the wall relation along any permutation agreeing with
the wall permutation modulo the merged partition.  So the direction-`0` endpoint is carried
by the direction-`0` occurrence permutation `E₀`, the direction-`1` endpoint by `E₁`, and the
regrown occurrence by `E₁` on the sheets resolved with direction `1` and by `E₀` elsewhere
(`newPerm`).  This is the only family-specific input to the transport builder
`M11StarExhaustionProof.nonempty_transportFree_of_rel`. -/

section Receipt

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (iso : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  (hWall : iso.targetVertex wall = wall')
  {star' : TwoStar target₂ wall'} (pair : Pair second star')
  (pair₁ : Pair first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star'))
  (hFirst : pair₁.first = blockPre iso wall pair.first.1)
  (hSecond : pair₁.second = blockPre iso wall pair.second.1)
  (hDA : pair₁.firstProfile.doubleLabel = pair.firstProfile.doubleLabel)
  (hDB : pair₁.secondProfile.doubleLabel = pair.secondProfile.doubleLabel)

include hWall in
/-- A pulled-back block contains a sheet exactly when the wall block contains its image
under any permutation agreeing with the wall permutation. -/
theorem blockPre_rel_iff (τ : Equiv.Perm (Fin degree))
    (hτ : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (τ s)) s)
    (A x : Fin degree) :
    (first.vertexPartition wall).Rel (blockPre iso wall A).1 x ↔
      (second.vertexPartition wall').Rel A (τ x) := by
  rw [wall_rel_iff iso hWall]
  have h1 := blockPre_rel iso wall A
  have h2 := hτ x
  constructor
  · intro h
    exact h1.symm.trans (h.trans h2.symm)
  · intro h
    exact h1.trans (h.trans h2)

include hFirst hSecond hDA hDB in
/-- **`Fine` is natural**: the pulled-back pair resolves a sheet with direction `l` exactly
when the wall's pair resolves its image. -/
theorem fine_pullback (τ : Equiv.Perm (Fin degree))
    (hτ : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (τ s)) s)
    (q l : Fin 2) (x : Fin degree) :
    Fine pair₁ q l x ↔ Fine pair q l (τ x) := by
  have eA : (first.vertexPartition wall).Rel pair₁.first.1 x ↔
      (second.vertexPartition wall').Rel pair.first.1 (τ x) := by
    rw [show pair₁.first.1 = (blockPre iso wall pair.first.1).1 from congrArg Subtype.val hFirst]
    exact blockPre_rel_iff iso hWall τ hτ _ x
  have eB : (first.vertexPartition wall).Rel pair₁.second.1 x ↔
      (second.vertexPartition wall').Rel pair.second.1 (τ x) := by
    rw [show pair₁.second.1 = (blockPre iso wall pair.second.1).1 from
      congrArg Subtype.val hSecond]
    exact blockPre_rel_iff iso hWall τ hτ _ x
  unfold Fine
  rw [eA, eB, hDA, hDB]

/-- The pulled-back star's occurrence relations are the wall's, along the occurrence
permutations. -/
theorem edge_rel_iff (label : Fin 2) (a b : Fin degree) :
    (first.edgePartition ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge
        label)).Rel a b ↔
      (second.edgePartition (star'.edge label)).Rel
        (iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge label) a)
        (iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge label)
          b) := by
  rw [← M11WallExhaustion.pullbackTwoStar_edge iso wall wall' hWall star' label,
    iso.edgePartition, SheetPartition.relabel_rel_iff]

/-- The regrown occurrence's permutation: `E₁` where the member resolves with direction `1`,
`E₀` elsewhere.  A permutation, since both agree with the wall permutation modulo the
merged partition and `Fine` is a union of wall blocks. -/
noncomputable def newPerm (q : Fin 2) : Equiv.Perm (Fin degree) := by
  classical
  let inh := M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star'
  let E0 := iso.edgePerm (inh.edge 0)
  let E1 := iso.edgePerm (inh.edge 1)
  let f : Fin degree → Fin degree := fun x ↦ if Fine pair₁ q 1 x then E1 x else E0 x
  refine Equiv.ofBijective f (Finite.injective_iff_bijective.mp ?_)
  have hE : ∀ (label : Fin 2) s, (first.vertexPartition wall).Rel
      ((iso.vertexPerm wall).symm (iso.edgePerm (inh.edge label) s)) s :=
    fun label s ↦ iso.compatible (inh.edge label) wall (incident_of_edge inh label) s
  have hSame : ∀ x y, (first.vertexPartition wall).Rel
      ((iso.vertexPerm wall).symm (E1 x)) ((iso.vertexPerm wall).symm (E0 y)) →
      (first.vertexPartition wall).Rel x y := fun x y h ↦ (hE 1 x).symm.trans (h.trans (hE 0 y))
  intro x y hxy
  by_cases hx : Fine pair₁ q 1 x <;> by_cases hy : Fine pair₁ q 1 y
  · simp only [f, hx, hy, ite_true] at hxy
    exact E1.injective hxy
  · simp only [f, hx, hy, ite_true, ite_false] at hxy
    have hRel := hSame x y (by rw [hxy]; exact rfl)
    exact absurd ((fine_congr pair₁ q 1 hRel).mp hx) hy
  · simp only [f, hx, hy, ite_true, ite_false] at hxy
    have hRel := hSame y x (by rw [hxy]; exact rfl)
    exact absurd ((fine_congr pair₁ q 1 hRel).mp hy) hx
  · simp only [f, hx, hy, ite_false] at hxy
    exact E0.injective hxy

theorem newPerm_apply (q : Fin 2) (x : Fin degree) :
    newPerm iso hWall pair₁ q x =
      if Fine pair₁ q 1 x then
        iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge 1) x
      else iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge 0) x := by
  classical
  unfold newPerm
  simp only [Equiv.ofBijective_apply]

include hFirst hSecond hDA hDB in
/-- **The receipt from a member's shape.**  A resolution with Figures 37/38's member-`q`
shape over the pulled-back pair is carried onto the wall's member `q` by a decoupled
transport along the datum isomorphism. -/
theorem nonempty_transport (res : LocalResolution degree) (q : Fin 2)
    (hL : ∀ x y, res.left.Rel x y ↔ (M11StarCensusProof.pasted (pair₁.candidate q)).left.Rel x y)
    (hR : ∀ x y,
      res.right.Rel x y ↔ (M11StarCensusProof.pasted (pair₁.candidate q)).right.Rel x y)
    (hN : ∀ x y,
      res.newEdge.Rel x y ↔ (M11StarCensusProof.pasted (pair₁.candidate q)).newEdge.Rel x y) :
    Nonempty (ResolutionExpansionFree.TransportFree iso wall wall'
      (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').right
      (pair.candidate q).right res (M11StarCensusProof.pasted (pair.candidate q))) := by
  classical
  set W := first.vertexPartition wall
  set W' := second.vertexPartition wall'
  set V := iso.vertexPerm wall
  set E0 := iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge 0)
  set E1 := iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge 1)
  set N := newPerm iso hWall pair₁ q
  have hE0 : ∀ s, W.Rel (V.symm (E0 s)) s :=
    fun s ↦ iso.compatible ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge 0) wall (incident_of_edge (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star') 0) s
  have hE1 : ∀ s, W.Rel (V.symm (E1 s)) s :=
    fun s ↦ iso.compatible ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge 1) wall (incident_of_edge (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star') 1) s
  have hN0 : ∀ s, ¬ Fine pair₁ q 1 s → N s = E0 s := by
    intro s hs
    rw [newPerm_apply, ite_eq_right hs]
  have hN1 : ∀ s, Fine pair₁ q 1 s → N s = E1 s := by
    intro s hs
    rw [newPerm_apply, ite_eq_left hs]
  have hNm : ∀ s, W.Rel (V.symm (N s)) s := by
    intro s
    by_cases hs : Fine pair₁ q 1 s
    · rw [hN1 s hs]; exact hE1 s
    · rw [hN0 s hs]; exact hE0 s
  have hW0 := wall_rel_iff_of_agree iso hWall E0 hE0
  have hW1 := wall_rel_iff_of_agree iso hWall E1 hE1
  have hWN := wall_rel_iff_of_agree iso hWall N hNm
  have hF0 := fine_pullback iso hWall pair pair₁ hFirst hSecond hDA hDB E0 hE0 q
  have hF1 := fine_pullback iso hWall pair pair₁ hFirst hSecond hDA hDB E1 hE1 q
  have hP0 := edge_rel_iff iso hWall (star' := star') 0
  have hP1 := edge_rel_iff iso hWall (star' := star') 1
  -- the two endpoints of the member refine the member's wall partition
  have hLref : res.left.Refines W := fun x y h ↦
    ((pasted_left_rel pair₁ q x y).mp ((hL x y).mp h)).1
  have hRref : res.right.Refines W := fun x y h ↦
    ((pasted_right_rel pair₁ q x y).mp ((hR x y).mp h)).1
  -- E₀ and E₁ differ inside wall blocks only
  have h01 : ∀ s, W.Rel (E0.symm (E1 s)) s := by
    intro s
    have h := hE0 (E0.symm (E1 s))
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (hE1 s)
  have h10 : ∀ s, W.Rel (E1.symm (E0 s)) s := by
    intro s
    have h := hE1 (E1.symm (E0 s))
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (hE0 s)
  refine nonempty_transportFree_of_rel iso wall wall' (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').right (pair.candidate q).right res
    (M11StarCensusProof.pasted (pair.candidate q)) hWall ?_ hLref hRref E0 E1 N hE0 hE1
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- the side assignment is the pulled-back one
    intro edge
    change star'.right (iso.targetEdge edge) = (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').right edge
    unfold TwoStar.right
    rw [← M11WallExhaustion.pullbackTwoStar_edge iso wall wall' hWall star' 1]
    exact decide_eq_decide.mpr iso.targetEdge.injective.eq_iff
  · intro a b
    rw [hL, pasted_left_rel, pasted_left_rel, hW0, hF0 0 a, hP0]
  · intro a b
    rw [hR, pasted_right_rel, pasted_right_rel, hW1, hF1 1 a, hP1]
  · intro a b
    rw [hN, pasted_newEdge_rel, pasted_newEdge_rel]
    by_cases hWab : W.Rel a b
    swap
    · have hW' : ¬ W'.Rel (N a) (N b) := fun h ↦ hWab ((hWN a b).mpr h)
      exact ⟨fun h ↦ (hWab h.1).elim, fun h ↦ (hW' h.1).elim⟩
    have hQb : Fine pair₁ q 1 b ↔ Fine pair₁ q 1 a := (fine_congr pair₁ q 1 hWab).symm
    by_cases hQ : Fine pair₁ q 1 a
    · rw [hN1 a hQ, hN1 b (hQb.mpr hQ)]
      have h0 : ¬ Fine pair₁ q 0 a := fun h ↦ not_fine_one_of_fine_zero pair₁ q h hQ
      have hW' : W'.Rel (E1 a) (E1 b) := (hW1 a b).mp hWab
      constructor
      · rintro ⟨-, -, h1⟩
        exact ⟨hW', fun h ↦ (h0 ((hF1 0 a).mpr h)).elim, fun _ ↦ (hP1 a b).mp (h1 hQ)⟩
      · rintro ⟨-, -, h1⟩
        exact ⟨hWab, fun h ↦ (h0 h).elim, fun _ ↦ (hP1 a b).mpr (h1 ((hF1 1 a).mp hQ))⟩
    · rw [hN0 a hQ, hN0 b (fun h ↦ hQ (hQb.mp h))]
      have hW' : W'.Rel (E0 a) (E0 b) := (hW0 a b).mp hWab
      constructor
      · rintro ⟨-, h0, -⟩
        exact ⟨hW', fun h ↦ (hP0 a b).mp (h0 ((hF0 0 a).mpr h)),
          fun h ↦ (hQ ((hF0 1 a).mpr h)).elim⟩
      · rintro ⟨-, h0, -⟩
        exact ⟨hWab, fun h ↦ (hP0 a b).mpr (h0 ((hF0 0 a).mp h)), fun h ↦ (hQ h).elim⟩
  · intro s
    rw [hL, pasted_left_rel]
    by_cases hQ : Fine pair₁ q 1 s
    · rw [hN1 s hQ]
      refine ⟨h01 s, fun h0 ↦ ?_⟩
      have h0' := (fine_congr pair₁ q 0 (h01 s)).mp h0
      exact (not_fine_one_of_fine_zero pair₁ q h0' hQ).elim
    · rw [hN0 s hQ, Equiv.symm_apply_apply]
      exact ⟨rfl, fun _ ↦ rfl⟩
  · intro s
    rw [hR, pasted_right_rel]
    by_cases hQ : Fine pair₁ q 1 s
    · rw [hN1 s hQ, Equiv.symm_apply_apply]
      exact ⟨rfl, fun _ ↦ rfl⟩
    · rw [hN0 s hQ]
      refine ⟨h10 s, fun h1 ↦ ?_⟩
      exact (hQ ((fine_congr pair₁ q 1 (h10 s)).mp h1)).elim
  · intro edge hInc s
    rcases eq_edge_of_incident (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star') edge hInc with rfl | rfl
    · rw [TwoStar.right_edge_zero]
      simp only [Bool.false_eq_true, ite_false]
      rw [show iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge 0) s
        = E0 s from rfl, Equiv.symm_apply_apply]
      exact rfl
    · rw [TwoStar.right_edge_one]
      simp only [ite_true]
      rw [show iso.edgePerm ((M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star').edge 1) s
        = E1 s from rfl, Equiv.symm_apply_apply]
      exact rfl

end Receipt

/-! ## 4.  Part I's census at an arbitrary member

At a regrowth `mem` carrying a W2 input and a `{w2-r1}` pair on its own limit (the wall's,
pulled back along the limit isomorphism), Part I's incoming census
(`W2R1IncomingMatching`) says the regrowth's own cover is Figure 37/38's member `q` for
some `q`: its normal form at the star's own placement has member `q`'s three pasted
partitions, as relations.  The placement is the star's own, because a `{w2-r1}` wall is
`(2,2)` (`W2R1IncomingCensus.member_placement`). -/

section MemberCensus

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

private theorem rel_iff_of_block_eq {d : ℕ} {P Q : SheetPartition d} {x : Fin d}
    (h : P.block x = Q.block x) (y : Fin d) : P.Rel x y ↔ Q.Rel x y := by
  rw [← SheetPartition.mem_block_iff, h, SheetPartition.mem_block_iff]

/-- **The member's own normal form has Figure 37/38's member-`q` shape**, for some `q`. -/
theorem member_census (mem : Regrowth core y degree) (hy : Nondegenerate y)
    {star : TwoStar (mem.frame.limitTarget mem.column) (mergeVertex mem)}
    (pair : Pair mem.limit star) (hPlacement : PlacementSpec mem star.right) :
    ∃ q : Fin 2,
      (∀ x y, (memberResolution mem star.right hPlacement).left.Rel x y ↔
        (M11StarCensusProof.pasted (pair.candidate q)).left.Rel x y) ∧
      (∀ x y, (memberResolution mem star.right hPlacement).right.Rel x y ↔
        (M11StarCensusProof.pasted (pair.candidate q)).right.Rel x y) ∧
      (∀ x y, (memberResolution mem star.right hPlacement).newEdge.Rel x y ↔
        (M11StarCensusProof.pasted (pair.candidate q)).newEdge.Rel x y) := by
  have hForest := InheritedLimitRows.forest mem hy
  obtain ⟨q, hSel⟩ := W2R1IncomingMatching.exists_selector mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    mem.frame.fullDim hForest star pair
  obtain ⟨h1, h2⟩ := W2R1IncomingMatching.census_of_selector mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    mem.frame.fullDim hForest star pair q hSel
  have hEnds := W2R1IncomingCensus.transported_endpoints mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    mem.frame.fullDim star pair star.right rfl hPlacement
  have hNew := M11IncomingOuterPartitions.transported_edgePartition_new mem.frame.data rfl
    (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
    star.right hPlacement mem.frame.fullDim.targetConnected mem.frame.fullDim.targetGenus
  refine ⟨q, fun x y ↦ ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩
  · have hB := W2R1IncomingMatching.wall_blocks_side mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      mem.frame.fullDim hForest star pair q h1 h2 0 x
    rw [W2R1IncomingMatching.resolutionSide_zero] at hB
    exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hEnds.1)).trans
      (rel_iff_of_block_eq hB y)
  · have hB := W2R1IncomingMatching.wall_blocks_side mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      mem.frame.fullDim hForest star pair q h1 h2 1 x
    rw [W2R1IncomingMatching.resolutionSide_one] at hB
    exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hEnds.2)).trans
      (rel_iff_of_block_eq hB y)
  · have hB := W2R1IncomingMatching.wall_blocks_new mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      mem.frame.fullDim hForest star pair q h1 h2 x
    exact (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) hNew)).trans
      (rel_iff_of_block_eq hB y)

end MemberCensus

/-! ## 5.  Exhaustion, and the family clause -/

section Exhaustion

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W2SourceInput w.limit star) (pair : Pair w.limit star)
  {incoming : Fin 2}
  (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum (Fin p))

include input in
/-- **Every star member presents a receipt.** -/
theorem exists_receipt (member : GeometricStar.StarMember hy w) :
    ∃ ψ : GeometricStar.LimitIso hy member.member w,
    ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
    ∃ hPlacement : PlacementSpec member.member placement,
    ∃ q : Fin 2, Nonempty (W2R1StarCensusProof.PositionTransport w hy pair member.member ψ
      placement hPlacement q) := by
  obtain ⟨ψ⟩ := member.specializes
  set mem := member.member
  set iso := ψ.datum.trans (GeometricDatumIso.refl w.limit).symm
  have hW : iso.targetVertex (mergeVertex mem) = mergeVertex w :=
    M11StarCensusProof.pinned w hy input mem ψ
  obtain ⟨pair₁, hFirst, hSecond, hDA, hDB⟩ :=
    exists_pair_pullback iso (InheritedLimitRows.limit_connected mem) hW pair
  have hPlacement : PlacementSpec mem
      (M11WallExhaustion.pullbackTwoStar iso (mergeVertex mem) (mergeVertex w) hW star).right :=
    W2R1IncomingCensus.member_placement mem.frame.data rfl
      (fst_ne_snd (mem.frame.edgeOf mem.column)) (mem.frame.numEdges_edgeOf mem.column)
      mem.frame.fullDim _ pair₁
  obtain ⟨q, hL, hR, hN⟩ := member_census mem hy pair₁ hPlacement
  exact ⟨ψ, _, hPlacement, q,
    nonempty_transport iso hW pair pair₁ hFirst hSecond hDA hDB _ q hL hR hN⟩

include input in
/-- **Stage 2 at one wall: the two positions exhaust the star.** -/
theorem exhausts (hValid : w.limit.Valid) :
    W2R1StarCensusProof.Exhausts w hy pair hValid incomingFD :=
  W2R1StarCensusProof.exhausts_of_transports w hy pair hValid incomingFD
    (exists_receipt w hy input pair)

end Exhaustion

/-- **The W2R1 star exhaustion, at every core, degree and request.** -/
theorem w2R1StarExhaustion (degree n p : ℕ) :
    W2R1StarCensusProof.W2R1StarExhaustion degree n p :=
  fun _ _ hy w _ _ _ input pair _ incomingFD ↦ exhausts w hy input pair incomingFD input.valid

/-- **The W2R1 star census**, unconditionally. -/
theorem w2R1StarCensus (degree n p : ℕ) : W2R1StarCensusProof.W2R1StarCensus degree n p :=
  W2R1StarCensusProof.w2R1StarCensus_of_exhaustion (w2R1StarExhaustion degree n p)

/-- **The `w2R1` clause of `FamilyStarParity`, at every degree, core size and request.** -/
theorem familyStarParity_w2R1_general (degree n p : ℕ) :
    RegrowthWallInput.FamilyStarParity degree n p .w2R1 :=
  W2R1StarCensusProof.familyStarParity_w2R1_of_census (w2R1StarCensus degree n p)

/-- **The `w2R1` clause of `FamilyStarParity` at genus six and degree four, with no
hypothesis.** -/
theorem familyStarParity_w2R1 :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2R1 :=
  W2R1StarCensusProof.familyStarParity_w2R1_of_exhaustion (w2R1StarExhaustion _ _ _)

end DraismaVargas.Count.W2R1StarExhaustionProof
