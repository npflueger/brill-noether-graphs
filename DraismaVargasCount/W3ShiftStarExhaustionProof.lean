import DraismaVargasCount.W3ShiftStarCensusProof
import DraismaVargasCount.W3Nd3StarExhaustionProof
import DraismaVargas.LocalCases.W3ShiftClosureFinal

/-!
# W3Shift star exhaustion: the `w3Shift` clause with no hypothesis

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w3-r1-nd3-t2-(a>k₄)}`, Figure 29,
Equation (3), and `lemma-dangling-no-glue`.  Census and reduction: the companion
`W3ShiftStarCensusProof`.  Machinery: `W3Nd2StarExhaustionProof` §2, §4, §9–§11 and
`W3Nd3StarExhaustionProof` §1.

## The result, in one paragraph

Take any star member and any limit isomorphism `ψ₀` to the wall.  Part I's census at the
member's own contraction (`W3ShiftClosureFinal.exists_shiftProfile_census`, run on the
pulled-back input and nd3 profile) gives it a Figure 29 orientation whose moving direction is
its divalent one, and Part I's identification (`W3ShiftIncomingMatching.shift_sameBlocks`)
gives its read-off resolution one of the two shapes: Position II.b
`(e_α, A₀ ∖ {x} | {x}, e_α ∖ {x} | {x})` with its own detached sheet `x`, or Position II.a
`(e_α ∪ {y}, A₀, e_α ∪ {y})` with its own transferred sheet `y` (§3).  The direction `d` is
the one `ψ₀` sends the moving direction to, and the position is `(d, 0)` or `(d, 1)`.  The
transport runs along `ψ` followed by the position's inverse anchor (the two branch swaps
undone).  Beyond the wall-block bookkeeping, a transport onto Position II.b needs **both
retained directions** to carry `x` to the position's detached sheet `x_d`, and one onto
Position II.a needs **the moving direction** to carry `y` to the position's `y_d` (§2).  Both
sheets dangle above those directions (`x ∉ e_β ∪ e_γ` is `ShrinkData`'s content,
`y ∉ e_α` is `ShiftProfile.extra`'s), so the limit isomorphism is re-chosen by pendant
automorphisms exchanging two dangling sheets on one branch (§4, `exists_realign`: twice for
II.b, once for II.a).  A received position is automatically nonsingular (multiplicity is a
geometric invariant, `absMult_eq_of_datumIso`), so Stage 2 holds at every wall and every
setup (§6), and with the census, the family clause holds with no hypothesis (§7).

## What is proved

* §1 `detachSheet_rel_iff`, `mergeBlocks_rel_iff`, `swap_rel`, `piece_same`, `inj_iff_eq`;
  `sourceEdgeEquiv_sourceEdge`, `isDangling_sourceEdge_iff`, `distinguishedBlock_eq_blockPre`
  (the distinguished block is intrinsic).
* §2 (family-generic) `agree_of_rel`, **`nonempty_transportFree_shrink`**,
  **`nonempty_transportFree_grow`**.
* §3 `directions₁`, `largest_lt₁`, `res`, **`member_shape`**.
* §4 `rel_of_survives`, `sourceEdge_anchor`, `isDangling_of_not_rel`, `movingAnchor_survives`,
  `transfer_isDangling`, `extra_isDangling`; `pendant_at_wall'` (any set of dangling sheets of
  one wall block), **`exists_realign`**.
* §5 `pos_shrink`, `pos_grow`, `incident_pos`, `exists_direction`, `isoAt`,
  `anchor_symm_edge`, `isoAt_wall`, `isoAt_targetEdge`, `isoAt_targetEdge_symm`,
  `isoAt_edgePerm`, **`nonsingular_of_transport`**, `exhausts_of_transports'`.
* §6 `blockPre_congr`, `hPos_setup`, `mem_incident_symm`, `wall_sheet_of_base`,
  `wall_sheet_of_member`, `survivor_rel`, **`exists_receipt`**, **`exhausts`**.
* §7 **`w3ShiftStarExhaustion`**, **`w3ShiftStarCensus`**, **`w3ShiftStarCard`** (every
  `w3Shift` star has exactly as many classes as Equation (3) has nonsingular positions),
  **`familyStarParity_w3Shift`**.

## What is NOT proved (every surviving hypothesis, explicitly)

* Nothing is assumed: the headlines have no hypothesis beyond their binders.  `exhausts` holds
  for **every** `Setup`, and does not use the `w3Shift` tag.
* **Non-vacuity is not shown**: no `w3Shift` regrowth is constructed in this library, and none
  occurs in a computer enumeration of walls (not part of this library), so the result is
  untested numerically and no `example` at a concrete instance is given.  Whether the family
  occurs at genus six is not settled (the shift arithmetic alone admits degree four; see the
  census file).
* Which of the six positions are singular is not determined; the census counts the
  nonsingular ones, and `nonsingular_of_transport` shows every received position is one.

## Remarks

* **Exhaustion from this file's own transports** works, with one new ingredient beyond
  nd2/nd3: the coherence to be arranged is at a **single sheet** (the member's own `x` or `y`
  against the position's), on **one or two** branches, and the pendant set is the block's
  dangling sheets above that direction rather than the whole block (`pendant_at_wall'`).
* **Positions over a twice-branch-swapped copy** are harmless: only the anchor's
  target maps being the identity (`Anchor.vertex_fix`, `edge_fix`) is used; its sheet
  permutations are absorbed by the realigned sheet (`wall_sheet_of_base`).
* *Nonsingularity*: the census's `exhausts_of_transports` asks for a nonsingularity receipt; it
  is not an extra obligation (`nonsingular_of_transport`, from `absMult_eq_of_datumIso`).

## Consumers

`StarSupplyAssembly.familyStarParity_all`, through `familyStarParity_w3Shift` (the `w3Shift`
clause of `FamilyStarParity`), and so the star parity of step 2 (trivalent walls) of
`DraismaVargasCount/Assembly.lean`.  `ValencyThreeResolutionMatch` and `ValencyThreeCoreSlots`
reuse lemmas of §1, §2 and §4.
-/

namespace DraismaVargas.Count.W3ShiftStarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open ThirdEquation W3R1SourceProfile
open M11StarExhaustionProof (blockPre blockPre_rel)
open W3Nd2StarExhaustionProof (Piece piece_of_blocks piece_transport edge_rel_iff_symm
  edgePerm_agree edgePerm_agree_symm agree_symm_apply sel_iff incident_iff mem_L mem_G mem_T
  incident_cases rightOf_pullback rightOf_eq_false rightOf_eq_true)
open W3Nd2SourceCandidates (rightOf)

/-! ## 1.  Two partition relations, and three facts about limit isomorphisms -/

section Partitions

variable {d : ℕ}

/-- **Detaching a sheet, as a relation.** -/
theorem detachSheet_rel_iff (P : SheetPartition d) (x r : Fin d) (hne : x ≠ r)
    (hxr : P.Rel x r) (u v : Fin d) :
    (P.detachSheet x r hne hxr).Rel u v ↔ P.Rel u v ∧ (u = x ↔ v = x) := by
  by_cases hu : u = x
  · subst hu
    rw [SheetPartition.detachSheet_rel_single_iff]
    exact ⟨fun h ↦ h ▸ ⟨rfl, Iff.rfl⟩, fun h ↦ (h.2.mp rfl).symm⟩
  by_cases hv : v = x
  · subst hv
    have h := P.detachSheet_rel_single_iff v r u hne hxr
    constructor
    · intro huv
      exact (hu (h.mp huv.symm).symm).elim
    · intro huv
      exact (hu (huv.2.mpr rfl)).elim
  have hRx : ∀ z, z ≠ x → P.Rel x z →
      (P.detachSheet x r hne hxr).repr z = r := fun z hz hRel ↦
    P.detachSheet_repr_of_rel_of_ne x r z hne hxr hz hRel
  have hNx : ∀ z, ¬ P.Rel x z → (P.detachSheet x r hne hxr).repr z = P.repr z :=
    fun z hRel ↦ P.detachSheet_repr_of_not_rel x r z hne hxr hRel
  have hRepr : ∀ z, ¬ P.Rel x z → r ≠ P.repr z := by
    intro z hz hEq
    apply hz
    have : P.Rel r z := by
      change P.repr r = P.repr z
      rw [hEq, P.repr_idem]
    exact hxr.trans this
  have hiff : (u = x ↔ v = x) := ⟨fun h ↦ (hu h).elim, fun h ↦ (hv h).elim⟩
  simp only [hiff, and_true]
  change (P.detachSheet x r hne hxr).repr u = (P.detachSheet x r hne hxr).repr v ↔ _
  by_cases hxu : P.Rel x u <;> by_cases hxv : P.Rel x v
  · rw [hRx u hu hxu, hRx v hv hxv]
    exact iff_of_true rfl (hxu.symm.trans hxv)
  · rw [hRx u hu hxu, hNx v hxv]
    exact iff_of_false (hRepr v hxv) (fun h ↦ hxv (hxu.trans h))
  · rw [hNx u hxu, hRx v hv hxv]
    exact iff_of_false (fun h ↦ hRepr u hxu h.symm) (fun h ↦ hxu (hxv.trans h.symm))
  · rw [hNx u hxu, hNx v hxv]
    rfl

/-- **Merging two blocks, as a relation.** -/
theorem mergeBlocks_rel_iff (P : SheetPartition d) (f e : Fin d) (h : ¬ P.Rel f e)
    (u v : Fin d) :
    (P.mergeBlocks f e h).Rel u v ↔
      P.Rel u v ∨ ((P.Rel f u ∨ P.Rel e u) ∧ (P.Rel f v ∨ P.Rel e v)) := by
  have hFirst := P.mergeBlocks_rel_first_iff f e
  by_cases hu : (P.mergeBlocks f e h).Rel f u
  · have hu' := (hFirst u h).mp hu
    constructor
    · intro huv
      exact Or.inr ⟨hu', (hFirst v h).mp (hu.trans huv)⟩
    · rintro (huv | ⟨-, hv⟩)
      · rcases hu' with hfu | heu
        · exact hu.symm.trans ((hFirst v h).mpr (Or.inl (hfu.trans huv)))
        · exact hu.symm.trans ((hFirst v h).mpr (Or.inr (heu.trans huv)))
      · exact hu.symm.trans ((hFirst v h).mpr hv)
  · have hu' : ¬ (P.Rel f u ∨ P.Rel e u) := fun h' ↦ hu ((hFirst u h).mpr h')
    have hBlock := P.mergeBlocks_block_of_separate f e u h
      (fun h' ↦ hu' (Or.inl h'.symm)) (fun h' ↦ hu' (Or.inr h'.symm))
    have hiff : (P.mergeBlocks f e h).Rel u v ↔ P.Rel u v := by
      rw [← SheetPartition.mem_block_iff, hBlock, SheetPartition.mem_block_iff]
    rw [hiff]
    exact ⟨Or.inl, fun h' ↦ h'.elim id (fun h'' ↦ (hu' h''.1).elim)⟩

/-- A transposition of two related sheets moves nothing out of its block. -/
theorem swap_rel (P : SheetPartition d) {a c : Fin d} (h : P.Rel a c) (s : Fin d) :
    P.Rel (Equiv.swap a c s) s := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

/-- A piece whose two regions carry one refining partition is that partition. -/
theorem piece_same {W : SheetPartition d} {b : Fin d} {X R : SheetPartition d}
    (hX : X.Refines W) (h : Piece W b X X R) (u v : Fin d) : R.Rel u v ↔ X.Rel u v := by
  rw [h u v]
  constructor
  · rintro ⟨-, h1, h2⟩
    by_cases hb : W.Rel b u
    · exact h1 hb
    · exact h2 hb
  · intro h'
    exact ⟨hX.rel h', fun _ ↦ h', fun _ ↦ h'⟩

theorem inj_iff_eq {f : Equiv.Perm (Fin d)} {x₁ x₂ : Fin d} (h : f x₁ = x₂) (u : Fin d) :
    f u = x₂ ↔ u = x₁ := by
  subst h
  exact f.injective.eq_iff

end Partitions

section Isos

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

theorem sourceEdgeEquiv_sourceEdge (iso : GeometricDatumIso first second) (e : target₁.edges)
    (s : Fin degree) :
    iso.sourceEdgeEquiv (first.sourceEdge e s) =
      second.sourceEdge (iso.targetEdge e) (iso.edgePerm e s) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change iso.edgePerm e ((first.edgePartition e).repr s) =
    (second.edgePartition (iso.targetEdge e)).repr (iso.edgePerm e s)
  rw [iso.edgePartition e]
  change _ = iso.edgePerm e ((first.edgePartition e).repr ((iso.edgePerm e).symm (iso.edgePerm e s)))
  rw [Equiv.symm_apply_apply]

/-- **Isomorphisms carry dangling source edges.** -/
theorem isDangling_sourceEdge_iff (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) (e : target₁.edges) (s : Fin degree) :
    IsDangling second (second.sourceEdge (iso.targetEdge e) (iso.edgePerm e s)) ↔
      IsDangling first (first.sourceEdge e s) := by
  rw [← sourceEdgeEquiv_sourceEdge]
  exact iso.isDangling_map_iff hConnected _

/-- **The distinguished block is intrinsic**: any two W3 inputs on isomorphic data have
corresponding distinguished blocks. -/
theorem distinguishedBlock_eq_blockPre (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star₁ : ThreeStar target₁ wall} {star₂ : ThreeStar target₂ wall'}
    (input₁ : W3SourceInput first star₁) (input₂ : W3SourceInput second star₂) :
    input₁.distinguishedBlock = blockPre iso wall input₂.distinguishedBlock.1 := by
  by_contra hNe
  have h0 := input₁.localRamification_eq_zero_of_ne (Ne.symm hNe)
  rw [M11StarExhaustionProof.localRamification_blockPre iso hWall input₂.distinguishedBlock,
    input₂.localRamification_distinguishedBlock] at h0
  exact one_ne_zero h0

end Isos

/-! ## 2.  Transports onto Figure 29's two positions, from shapes (family-generic)

As in `W3Nd2StarExhaustionProof` §4, the wall has three incident occurrences on the second
side: `L`, the moving direction (the divalent side), and `G`, `T`, the two retained ones.
The shapes are pieces on the distinguished block: Position II.b is
`(e_α, A₀ ∖ {x} | {x}, e_α ∖ {x} | {x})` and Position II.a is `(e_α ∪ {y}, A₀, e_α ∪ {y})`,
with the background `(e_α, A₀, e_α)` off the block in both. -/

section Transport

open ResolutionExpansionFree W4Assembly
open ResolutionM11 (LocalResolution)

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (iso : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  (hWall : iso.targetVertex wall = wall')
  (b : Fin degree) (L G T : target₂.edges)
  (hEdges : ∀ e, e ∈ GluingDatum.incidentEdges wall' ↔ e = L ∨ e = G ∨ e = T)

include hWall in
/-- A permutation that stays inside the blocks of an agreeing one agrees too. -/
theorem agree_of_rel (σ τ : Equiv.Perm (Fin degree))
    (hσ : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (σ s)) s)
    (hτσ : ∀ s, (second.vertexPartition wall').Rel (τ s) (σ s)) (s : Fin degree) :
    (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (τ s)) s :=
  ((M11StarExhaustionProof.wall_rel_iff iso hWall _ _).mp (hτσ s)).trans (hσ s)

include hWall hEdges in
/-- **The Position II.b transport.**  The retained endpoint and the regrown occurrence use the
moving direction's permutation, the latter corrected by one transposition inside `e_α`; the
fresh endpoint uses `G`'s.  It needs both retained directions to carry the member's detached
sheet to the position's. -/
theorem nonempty_transportFree_shrink (right : target₁.edges → Bool)
    (res res' : LocalResolution degree)
    (hSide : ∀ edge, rightOf L (iso.targetEdge edge) = right edge)
    (L₁ : target₁.edges) (hL₁ : L₁ = iso.targetEdge.symm L)
    (x₁ x₂ : Fin degree) (R₁ N₁ R₂ N₂ : SheetPartition degree)
    (hR₁ : ∀ u v, R₁.Rel u v ↔ (first.vertexPartition wall).Rel u v ∧ (u = x₁ ↔ v = x₁))
    (hN₁ : ∀ u v, N₁.Rel u v ↔
      (first.edgePartition L₁).Rel u v ∧ (u = x₁ ↔ v = x₁))
    (hR₂ : ∀ u v, R₂.Rel u v ↔ (second.vertexPartition wall').Rel u v ∧ (u = x₂ ↔ v = x₂))
    (hN₂ : ∀ u v, N₂.Rel u v ↔ (second.edgePartition L).Rel u v ∧ (u = x₂ ↔ v = x₂))
    (hx : (second.edgePartition L).Rel (iso.edgePerm (iso.targetEdge.symm L) x₁) x₂)
    (hG : iso.edgePerm (iso.targetEdge.symm G) x₁ = x₂)
    (hT : iso.edgePerm (iso.targetEdge.symm T) x₁ = x₂)
    (hLeft : Piece (first.vertexPartition wall) (blockPre iso wall b).1
      (first.edgePartition L₁) (first.edgePartition L₁)
      res.left)
    (hRight : Piece (first.vertexPartition wall) (blockPre iso wall b).1 R₁
      (first.vertexPartition wall) res.right)
    (hNew : Piece (first.vertexPartition wall) (blockPre iso wall b).1 N₁
      (first.edgePartition L₁) res.newEdge)
    (hLeft' : Piece (second.vertexPartition wall') b (second.edgePartition L)
      (second.edgePartition L) res'.left)
    (hRight' : Piece (second.vertexPartition wall') b R₂ (second.vertexPartition wall') res'.right)
    (hNew' : Piece (second.vertexPartition wall') b N₂ (second.edgePartition L) res'.newEdge) :
    Nonempty (TransportFree iso wall wall' right (rightOf L) res res') := by
  subst hL₁
  classical
  set W := first.vertexPartition wall
  set σ := iso.edgePerm (iso.targetEdge.symm L)
  set ρ := iso.edgePerm (iso.targetEdge.symm G)
  set τN : Equiv.Perm (Fin degree) := σ.trans (Equiv.swap (σ x₁) x₂)
  have hσ := edgePerm_agree_symm iso hWall L (mem_L L G T hEdges)
  have hρ := edgePerm_agree_symm iso hWall G (mem_G L G T hEdges)
  have hSref := StableLocalProperties.refines_of_mem_incidentEdges second (mem_L L G T hEdges)
  have hNσ : ∀ s, (second.edgePartition L).Rel (τN s) (σ s) := fun s ↦ swap_rel _ hx (σ s)
  have hτN := agree_of_rel iso hWall σ τN hσ (fun s ↦ hSref.rel (hNσ s))
  have hN1 : τN x₁ = x₂ := by
    change Equiv.swap (σ x₁) x₂ (σ x₁) = x₂
    exact Equiv.swap_apply_left _ _
  have hWσ := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall σ hσ
  have hWρ := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall ρ hρ
  have hWN := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall τN hτN
  have hbσ := sel_iff iso hWall b σ hσ
  have hbρ := sel_iff iso hWall b ρ hρ
  have hbN := sel_iff iso hWall b τN hτN
  have hPs := edge_rel_iff_symm iso L
  have hSref₁ : (first.edgePartition (iso.targetEdge.symm L)).Refines W := by
    intro x y h
    exact (hWσ x y).mpr (hSref.rel ((hPs x y).mp h))
  have hPN : ∀ x y, (first.edgePartition (iso.targetEdge.symm L)).Rel x y ↔
      (second.edgePartition L).Rel (τN x) (τN y) := by
    intro x y
    rw [hPs]
    exact ⟨fun h ↦ (hNσ x).trans (h.trans (hNσ y).symm),
      fun h ↦ (hNσ x).symm.trans (h.trans (hNσ y))⟩
  have hLeftSame := piece_same hSref₁ hLeft
  have hR₁ref : R₁.Refines W := fun u v h ↦ ((hR₁ u v).mp h).1
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel iso wall wall' right _ res _ hWall
    hSide hLeft.refines hRight.refines σ ρ τN hσ hρ ?_ ?_ ?_ ?_ ?_ ?_
  · exact piece_transport σ hWσ hbσ (fun x y _ ↦ hPs x y) (fun x y _ ↦ hPs x y) hLeft hLeft'
  · refine piece_transport ρ hWρ hbρ ?_ (fun x y _ ↦ hWρ x y) hRight hRight'
    intro x y _
    rw [hR₁, hR₂, hWρ, inj_iff_eq hG, inj_iff_eq hG]
  · refine piece_transport τN hWN hbN ?_ (fun x y _ ↦ hPN x y) hNew hNew'
    intro x y _
    rw [hN₁, hN₂, hPN, inj_iff_eq hN1, inj_iff_eq hN1]
  · intro s
    rw [hLeftSame, hPs, Equiv.apply_symm_apply]
    exact hNσ s
  · intro s
    have hAg := agree_symm_apply iso ρ τN hρ hτN s
    refine (hRight _ _).mpr ⟨hAg, fun _ ↦ (hR₁ _ _).mpr ⟨hAg, ?_⟩, fun _ ↦ hAg⟩
    rw [Equiv.symm_apply_eq, hG, inj_iff_eq hN1]
  · intro edge hInc s
    have hInc' := (incident_iff iso hWall edge).mp hInc
    by_cases hr : right edge = true
    · rw [if_pos hr, if_pos hr]
      rcases incident_cases iso L G T hEdges edge hInc' with h | h | h
      · subst h
        rw [← hSide, Equiv.apply_symm_apply] at hr
        simp [rightOf] at hr
      · subst h
        rw [Equiv.symm_apply_apply]; rfl
      · subst h
        have hAg := agree_symm_apply iso ρ _ hρ (edgePerm_agree_symm iso hWall T
          (mem_T L G T hEdges)) s
        refine (hRight _ _).mpr ⟨hAg, fun _ ↦ (hR₁ _ _).mpr ⟨hAg, ?_⟩, fun _ ↦ hAg⟩
        rw [Equiv.symm_apply_eq, hG, inj_iff_eq hT]
    · rw [if_neg hr, if_neg hr]
      have hEq : iso.targetEdge edge = L :=
        rightOf_eq_false (by rw [hSide edge]; simpa using hr)
      have hEdge : edge = iso.targetEdge.symm L := (Equiv.eq_symm_apply _).mpr hEq
      subst hEdge
      rw [Equiv.symm_apply_apply]; rfl

include hWall hEdges in
/-- **The Position II.a transport.**  The divalent side and the regrown occurrence use the
moving direction's permutation; it must carry the member's transferred sheet into the
position's transferred sheet's class. -/
theorem nonempty_transportFree_grow (right : target₁.edges → Bool)
    (res res' : LocalResolution degree)
    (hSide : ∀ edge, rightOf L (iso.targetEdge edge) = right edge)
    (L₁ : target₁.edges) (hL₁ : L₁ = iso.targetEdge.symm L)
    (m₁ y₁ m₂ y₂ : Fin degree) (G₁ G₂ : SheetPartition degree)
    (hG₁ : ∀ u v, G₁.Rel u v ↔ (first.edgePartition L₁).Rel u v ∨
      (((first.edgePartition L₁).Rel m₁ u ∨
          (first.edgePartition L₁).Rel y₁ u) ∧
        ((first.edgePartition L₁).Rel m₁ v ∨
          (first.edgePartition L₁).Rel y₁ v)))
    (hG₂ : ∀ u v, G₂.Rel u v ↔ (second.edgePartition L).Rel u v ∨
      (((second.edgePartition L).Rel m₂ u ∨ (second.edgePartition L).Rel y₂ u) ∧
        ((second.edgePartition L).Rel m₂ v ∨ (second.edgePartition L).Rel y₂ v)))
    (hm : (second.edgePartition L).Rel (iso.edgePerm (iso.targetEdge.symm L) m₁) m₂)
    (hy : (second.edgePartition L).Rel (iso.edgePerm (iso.targetEdge.symm L) y₁) y₂)
    (hLeft : Piece (first.vertexPartition wall) (blockPre iso wall b).1 G₁
      (first.edgePartition L₁) res.left)
    (hRight : Piece (first.vertexPartition wall) (blockPre iso wall b).1
      (first.vertexPartition wall) (first.vertexPartition wall) res.right)
    (hNew : Piece (first.vertexPartition wall) (blockPre iso wall b).1 G₁
      (first.edgePartition L₁) res.newEdge)
    (hLeft' : Piece (second.vertexPartition wall') b G₂ (second.edgePartition L) res'.left)
    (hRight' : Piece (second.vertexPartition wall') b (second.vertexPartition wall')
      (second.vertexPartition wall') res'.right)
    (hNew' : Piece (second.vertexPartition wall') b G₂ (second.edgePartition L) res'.newEdge) :
    Nonempty (TransportFree iso wall wall' right (rightOf L) res res') := by
  subst hL₁
  classical
  set W := first.vertexPartition wall
  set σ := iso.edgePerm (iso.targetEdge.symm L)
  set ρ := iso.edgePerm (iso.targetEdge.symm G)
  have hσ := edgePerm_agree_symm iso hWall L (mem_L L G T hEdges)
  have hρ := edgePerm_agree_symm iso hWall G (mem_G L G T hEdges)
  have hWσ := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall σ hσ
  have hWρ := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall ρ hρ
  have hbσ := sel_iff iso hWall b σ hσ
  have hbρ := sel_iff iso hWall b ρ hρ
  have hPs := edge_rel_iff_symm iso L
  have hRightSame := piece_same (SheetPartition.Refines.refl _) hRight
  have hGG : ∀ x y, G₁.Rel x y ↔ G₂.Rel (σ x) (σ y) := by
    intro x y
    have hmx : ∀ z, (first.edgePartition (iso.targetEdge.symm L)).Rel m₁ z ↔
        (second.edgePartition L).Rel m₂ (σ z) := fun z ↦ by
      rw [hPs]; exact ⟨fun h ↦ hm.symm.trans h, fun h ↦ hm.trans h⟩
    have hyx : ∀ z, (first.edgePartition (iso.targetEdge.symm L)).Rel y₁ z ↔
        (second.edgePartition L).Rel y₂ (σ z) := fun z ↦ by
      rw [hPs]; exact ⟨fun h ↦ hy.symm.trans h, fun h ↦ hy.trans h⟩
    rw [hG₁, hG₂, hPs, hmx, hmx, hyx, hyx]
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel iso wall wall' right _ res _ hWall
    hSide hLeft.refines hRight.refines σ ρ σ hσ hρ ?_ ?_ ?_ ?_ ?_ ?_
  · exact piece_transport σ hWσ hbσ (fun x y _ ↦ hGG x y) (fun x y _ ↦ hPs x y) hLeft hLeft'
  · exact piece_transport ρ hWρ hbρ (fun x y _ ↦ hWρ x y) (fun x y _ ↦ hWρ x y) hRight hRight'
  · exact piece_transport σ hWσ hbσ (fun x y _ ↦ hGG x y) (fun x y _ ↦ hPs x y) hNew hNew'
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro s
    rw [hRightSame]
    exact agree_symm_apply iso ρ σ hρ hσ s
  · intro edge hInc s
    have hInc' := (incident_iff iso hWall edge).mp hInc
    by_cases hr : right edge = true
    · rw [if_pos hr, if_pos hr, hRightSame]
      exact agree_symm_apply iso ρ _ hρ (edgePerm_agree iso hWall edge hInc') s
    · rw [if_neg hr, if_neg hr]
      have hEq : iso.targetEdge edge = L :=
        rightOf_eq_false (by rw [hSide edge]; simpa using hr)
      have hEdge : edge = iso.targetEdge.symm L := (Equiv.eq_symm_apply _).mpr hEq
      subst hEdge
      rw [Equiv.symm_apply_apply]; rfl

end Transport

/-! ## 3.  An arbitrary star member, read through a limit isomorphism

Part I's census at the member's own contraction
(`W3ShiftClosureFinal.exists_shiftProfile_census`, run on the pulled-back input and nd3
profile) and Part I's identification (`W3ShiftIncomingMatching.shift_sameBlocks`) give the
member's read-off resolution one of Figure 29's two shapes, in the member's own
coordinates, around a shift profile whose moving direction is the member's divalent one. -/

section Member

open W4Assembly W3ShiftSourceCandidates W3Nd2IncomingTargetPlacement
open W3Nd2StarExhaustionProof (isoOf isoOf_wall star₁ input₁ sel₁_eq divalent₁)
open W3Nd3StarExhaustionProof (profile₁ index_symm target_symm')

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : W3SourceInput w.limit star)
  (profile : Nd3Profile w.limit input.distinguishedBlock)
  (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
  (largest_lt : w.limit.sourceEdgeIndex profile.largest.1 <
    (w.limit.vertexPartition (mergeVertex w)).blockCard input.distinguishedBlock.1)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

include directions in
theorem directions₁ : (profile₁ w hy input profile other ψ).first.1.1.1 ≠
    (profile₁ w hy input profile other ψ).second.1.1.1 := by
  intro h
  apply directions
  have h1 : (profile₁ w hy input profile other ψ).first.1.1.1 =
      (isoOf w hy other ψ).targetEdge.symm profile.first.1.1.1 :=
    target_symm' (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input profile.first
  have h2 : (profile₁ w hy input profile other ψ).second.1.1.1 =
      (isoOf w hy other ψ).targetEdge.symm profile.second.1.1.1 :=
    target_symm' (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input profile.second
  rw [h1, h2] at h
  exact (isoOf w hy other ψ).targetEdge.symm.injective h

include largest_lt in
theorem largest_lt₁ :
    other.limit.sourceEdgeIndex (profile₁ w hy input profile other ψ).largest.1 <
      (other.limit.vertexPartition (mergeVertex other)).blockCard
        (input₁ w hy input other ψ).distinguishedBlock.1 :=
  calc other.limit.sourceEdgeIndex (profile₁ w hy input profile other ψ).largest.1
      = w.limit.sourceEdgeIndex profile.largest.1 :=
        index_symm (isoOf w hy other ψ) (isoOf_wall w hy input other ψ) input profile.largest
    _ < _ := largest_lt
    _ = _ := (W3Nd2StarExhaustionProof.blockCard_distinguished (isoOf w hy other ψ)
        (isoOf_wall w hy input other ψ) input).symm

/-- The member's read-off resolution at a placement. -/
noncomputable abbrev res (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hP : W3Nd2StarCensusProof.PlacementSpec other placement) :=
  W3Nd2StarCensusProof.memberResolution other placement hP

include directions largest_lt in
/-- **Every member has one of Figure 29's two shapes**, around its own orientation. -/
theorem member_shape :
    ∃ σ₁ : ShiftProfile (input₁ w hy input other ψ),
      σ₁.movingTarget = divalent₁ w hy input other ψ ∧
      ∃ hP : W3Nd2StarCensusProof.PlacementSpec other (rightOf σ₁.movingTarget),
      ((∃ sh : ShrinkData σ₁,
          Piece (other.limit.vertexPartition (mergeVertex other)) σ₁.movingAnchor
              (other.limit.edgePartition σ₁.movingTarget)
              (other.limit.edgePartition σ₁.movingTarget)
              (res other (rightOf σ₁.movingTarget) hP).left ∧
            Piece (other.limit.vertexPartition (mergeVertex other)) σ₁.movingAnchor
              ((other.limit.vertexPartition (mergeVertex other)).detachSheet sh.transfer
                sh.remainder sh.transfer_ne_remainder sh.remainder_wall_rel)
              (other.limit.vertexPartition (mergeVertex other))
              (res other (rightOf σ₁.movingTarget) hP).right ∧
            Piece (other.limit.vertexPartition (mergeVertex other)) σ₁.movingAnchor
              ((other.limit.edgePartition σ₁.movingTarget).detachSheet sh.transfer
                sh.remainder sh.transfer_ne_remainder sh.remainder_moving)
              (other.limit.edgePartition σ₁.movingTarget)
              (res other (rightOf σ₁.movingTarget) hP).newEdge) ∨
        (Piece (other.limit.vertexPartition (mergeVertex other)) σ₁.movingAnchor
              σ₁.growPartition (other.limit.edgePartition σ₁.movingTarget)
              (res other (rightOf σ₁.movingTarget) hP).left ∧
            Piece (other.limit.vertexPartition (mergeVertex other)) σ₁.movingAnchor
              (other.limit.vertexPartition (mergeVertex other))
              (other.limit.vertexPartition (mergeVertex other))
              (res other (rightOf σ₁.movingTarget) hP).right ∧
            Piece (other.limit.vertexPartition (mergeVertex other)) σ₁.movingAnchor
              σ₁.growPartition (other.limit.edgePartition σ₁.movingTarget)
              (res other (rightOf σ₁.movingTarget) hP).newEdge)) := by
  classical
  have hForest := InheritedLimitRows.forest other hy
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    hForest
  obtain ⟨σ₁, hMoving, -, hCases⟩ := W3ShiftClosureFinal.exists_shiftProfile_census
    other.frame.data rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) other.frame.fullDim hForest hCompat
    (star₁ w hy input other ψ) (input₁ w hy input other ψ) (profile₁ w hy input profile other ψ)
    (directions₁ w hy input profile directions other ψ)
    (largest_lt₁ w hy input profile largest_lt other ψ)
  have hP : W3Nd2StarCensusProof.PlacementSpec other (rightOf σ₁.movingTarget) :=
    W3ShiftIncomingCensus.placement_of_movingTarget_eq other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      other.frame.fullDim (star₁ w hy input other ψ) _
      (fun e ↦ congrArg (fun t ↦ rightOf t e) hMoving)
  refine ⟨σ₁, hMoving, hP, ?_⟩
  have hA := σ₁.movingTarget_refines
  rcases hCases with ⟨sh, hCensus⟩ | hCensus
  · left
    refine ⟨sh, ?_⟩
    set C := sh.shrinkCandidate
    have hSS := W3ShiftIncomingMatching.shift_sameBlocks other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      other.frame.fullDim hForest (star₁ w hy input other ψ) (input₁ w hy input other ψ) σ₁
      hMoving C (W3ShiftIncomingCensus.shrinkCandidate_right sh) hP _ _ _ hCensus
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_left_selected sh s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_right_selected sh s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_newEdge_selected sh s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_left_background sh s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_right_background sh s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_newEdge_background sh s hs)
    have hL := piece_of_blocks hA hA
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_left_selected sh s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_left_background sh s hs)
    have hR := piece_of_blocks
      (fun u v h ↦ ((detachSheet_rel_iff _ _ _ _ _ u v).mp h).1) (SheetPartition.Refines.refl _)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_right_selected sh s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_right_background sh s hs)
    have hN := piece_of_blocks
      (fun u v h ↦ hA.rel ((detachSheet_rel_iff _ _ _ _ _ u v).mp h).1) hA
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_newEdge_selected sh s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.shrink_newEdge_background sh s hs)
    refine ⟨hL.of_sameBlocks ?_, hR.of_sameBlocks ?_, hN.of_sameBlocks ?_⟩
    · have h := hSS.1 (oldVertex (other.frame.limitTarget other.column) (mergeVertex other))
      have h2 := M11StarCensusProof.candidate_oldWall C
      exact fun x y ↦ (h x y).trans
        (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
    · have h := hSS.1 (freshVertex (other.frame.limitTarget other.column))
      have h2 := M11StarCensusProof.candidate_fresh C
      exact fun x y ↦ (h x y).trans
        (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
    · have h := hSS.2 (occurrenceEquiv (other.frame.limitTarget other.column) (mergeVertex other)
        C.right none)
      have h2 := W3Nd2IncomingMemberMatching.candidate_edgePartition_new C
      exact fun x y ↦ (h x y).trans
        (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
  · right
    set C := σ₁.growCandidate
    have hSS := W3ShiftIncomingMatching.shift_sameBlocks other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      other.frame.fullDim hForest (star₁ w hy input other ψ) (input₁ w hy input other ψ) σ₁
      hMoving C (W3ShiftIncomingCensus.growCandidate_right σ₁) hP _ _ _ hCensus
      (fun s hs ↦ W3ShiftIncomingCensus.grow_left_selected σ₁ s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_right_selected σ₁ s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_newEdge_selected σ₁ s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_left_background σ₁ s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_right_background σ₁ s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_newEdge_background σ₁ s hs)
    have hL := piece_of_blocks σ₁.growPartition_refines hA
      (fun s hs ↦ W3ShiftIncomingCensus.grow_left_selected σ₁ s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_left_background σ₁ s hs)
    have hR := piece_of_blocks (SheetPartition.Refines.refl _) (SheetPartition.Refines.refl _)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_right_selected σ₁ s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_right_background σ₁ s hs)
    have hN := piece_of_blocks σ₁.growPartition_refines hA
      (fun s hs ↦ W3ShiftIncomingCensus.grow_newEdge_selected σ₁ s hs)
      (fun s hs ↦ W3ShiftIncomingCensus.grow_newEdge_background σ₁ s hs)
    refine ⟨hL.of_sameBlocks ?_, hR.of_sameBlocks ?_, hN.of_sameBlocks ?_⟩
    · have h := hSS.1 (oldVertex (other.frame.limitTarget other.column) (mergeVertex other))
      have h2 := M11StarCensusProof.candidate_oldWall C
      exact fun x y ↦ (h x y).trans
        (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
    · have h := hSS.1 (freshVertex (other.frame.limitTarget other.column))
      have h2 := M11StarCensusProof.candidate_fresh C
      exact fun x y ↦ (h x y).trans
        (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
    · have h := hSS.2 (occurrenceEquiv (other.frame.limitTarget other.column) (mergeVertex other)
        C.right none)
      have h2 := W3Nd2IncomingMemberMatching.candidate_edgePartition_new C
      exact fun x y ↦ (h x y).trans
        (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))

end Member

/-! ## 4.  Survivors, dangling sheets, and realigning one dangling sheet -/

section Sheets

open W3ShiftSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}
  {input : W3SourceInput data star}

/-- A sheet of the distinguished block whose occurrence above a survivor's direction
survives lies in that survivor's class. -/
theorem rel_of_survives
    (survivor : IncidentSourceEdge data (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hUnique : ∀ candidate ∈ survivors data input.distinguishedBlock,
      candidate.1.1.1 = survivor.1.1.1 → candidate = survivor)
    (u : Fin degree) (hu : (data.vertexPartition wall).Rel input.distinguishedBlock.1 u)
    (hS : ¬ IsDangling data (data.sourceEdge survivor.1.1.1 u)) :
    (data.edgePartition survivor.1.1.1).Rel survivor.1.1.2 u := by
  have hMem : survivor.1.1.1 ∈ GluingDatum.incidentEdges wall :=
    ((incident_wallBlock_sourceVertex_iff data input.distinguishedBlock survivor.1).mp
      survivor.2).1
  have hIncident := W3FourSourceCandidates.sourceEdge_incident (data := data)
    input.distinguishedBlock
    survivor.1.1.1 hMem u hu
  have hIn : (⟨data.sourceEdge survivor.1.1.1 u, hIncident⟩ :
      IncidentSourceEdge data (WallBlock.sourceVertex data wall input.distinguishedBlock)) ∈
      survivors data input.distinguishedBlock :=
    (mem_survivors data input.distinguishedBlock _).mpr hS
  have hEq := hUnique _ hIn rfl
  have hValue := congrArg (fun edge : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦ edge.1.1.2) hEq
  change (data.edgePartition survivor.1.1.1).repr survivor.1.1.2 =
    (data.edgePartition survivor.1.1.1).repr u
  rw [survivor.1.2]
  exact hValue.symm

/-- The survivor's own source edge is its anchor's. -/
theorem sourceEdge_anchor (e : data.SourceEdge) : data.sourceEdge e.1.1 e.1.2 = e :=
  Subtype.ext (Prod.ext rfl e.2)

/-- A sheet of the distinguished block outside a survivor's class dangles above its
direction. -/
theorem isDangling_of_not_rel
    (survivor : IncidentSourceEdge data (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hUnique : ∀ candidate ∈ survivors data input.distinguishedBlock,
      candidate.1.1.1 = survivor.1.1.1 → candidate = survivor)
    (u : Fin degree) (hu : (data.vertexPartition wall).Rel input.distinguishedBlock.1 u)
    (hNot : ¬ (data.edgePartition survivor.1.1.1).Rel survivor.1.1.2 u) :
    IsDangling data (data.sourceEdge survivor.1.1.1 u) := by
  by_contra h
  exact hNot (rel_of_survives survivor hUnique u hu h)

/-- **The moving survivor's anchor survives.** -/
theorem movingAnchor_survives (shift : ShiftProfile input) :
    ¬ IsDangling data (data.sourceEdge shift.movingTarget shift.movingAnchor) := by
  rw [sourceEdge_anchor]
  exact W3ShiftSelectedCensus.moving_survives shift

/-- **Position II.b's sheet dangles above every retained direction.** -/
theorem transfer_isDangling {shift : ShiftProfile input} (sh : ShrinkData shift)
    (e : target.edges) (he : e ∈ GluingDatum.incidentEdges wall) (hne : e ≠ shift.movingTarget) :
    IsDangling data (data.sourceEdge e sh.transfer) := by
  have hE := shift.incidentEdges_eq
  rw [hE] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h
  · exact (hne h).elim
  · subst h
    exact isDangling_of_not_rel shift.firstRest (firstRest_unique shift) _
      sh.transfer_wall_rel sh.transfer_not_first
  · subst h
    exact isDangling_of_not_rel shift.secondRest (secondRest_unique shift) _
      sh.transfer_wall_rel sh.transfer_not_second

/-- **Position II.a's sheet dangles above the moving direction.** -/
theorem extra_isDangling (shift : ShiftProfile input) :
    IsDangling data (data.sourceEdge shift.movingTarget shift.extra) :=
  isDangling_of_not_rel shift.moving (moving_unique shift) _ shift.extra_wall_rel
    shift.extra_separate

end Sheets

section PendantRealign

open TargetBranchRegion DanglingSideStructure
open W3Nd2StarExhaustionProof (Pendant pendantLimitIso branchPerm farEnd farEnd_ne
  edgeMoved_self edgeMoved_other exists_branch_cut mem_side_of_moved)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **The pendant hypothesis at a regrowth wall, for any set of dangling sheets of one wall
block** (`W3Nd2StarExhaustionProof.pendant_at_wall` for a whole block). -/
theorem pendant_at_wall' (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hNoGlue : DanglingEdgeNoGlue w.limit)
    {e : (w.frame.limitTarget w.column).edges}
    (hInc : (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
        mergeVertex w ∨
      (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
        mergeVertex w) (b : Fin degree) (D : Fin degree → Prop)
    (hDsub : ∀ s, D s → (w.limit.vertexPartition (mergeVertex w)).Rel b s)
    (hDang : ∀ s, D s → IsDangling w.limit (w.limit.sourceEdge e s))
    (hPos : 0 < nonDanglingValency w.limit (w.limit.sourceEndpoint (mergeVertex w) b)) :
    Pendant w.limit (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) D := by
  have hVD : ∀ v, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) v = true →
      ∀ s, D s → nonDanglingValency w.limit (w.limit.sourceEndpoint v s) = 0 := by
    intro v hv s hs
    obtain ⟨cut⟩ := exists_branch_cut w.limit hInc (hDsub s hs) hPos (hDang s hs)
    exact nonDanglingValency_eq_zero_of_mem_side w.limit cut
      (mem_side_of_moved w.limit (farEnd_ne hInc) s cut rfl hv)
  have hED : ∀ f, edgeMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) f = true →
      ∀ s, D s → IsDangling w.limit (w.limit.sourceEdge f s) := by
    intro f hf s hs
    have hEnd : ∃ u, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) u =
        true ∧ f ∈ GluingDatum.incidentEdges u := by
      unfold edgeMoved at hf
      rcases Bool.or_eq_true_iff.mp hf with h | h
      · exact ⟨_, h, by simp [GluingDatum.incidentEdges]⟩
      · exact ⟨_, h, by simp [GluingDatum.incidentEdges]⟩
    obtain ⟨u, hu, hMem⟩ := hEnd
    exact (nonDanglingValency_eq_zero_iff w.limit _).mp (hVD u hu s hs) _
      (incident_sourceEdge_sourceEndpoint w.limit u f hMem s)
  refine ⟨?_, ?_, hVD, hED⟩
  · intro v hv s hs t hst
    have hvWall : v ≠ mergeVertex w := by
      intro h
      rw [h, vertexMoved_wall] at hv
      exact Bool.false_ne_true hv
    have hva : v.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1 := by
      intro h
      exact hvWall (Subtype.ext h)
    have hvb : v.1 ≠ (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2 := v.2
    have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
      (InheritedLimitRows.forest w hy)
    set x := w.frame.data.sourceEndpoint v.1 s
    have hMap := WallDegeneration.nonDanglingValency_sourceVertexMap w.frame.data hCompat x hva hvb
    have hPart : w.limit.vertexPartition v = w.frame.data.vertexPartition v.1 :=
      contractVertexPartition_of_ne w.frame.data _ _ hva
    have hImage : sourceVertexMap w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) x = w.limit.sourceEndpoint v s := by
      change w.limit.sourceEndpoint (GraphContraction.fold _ _ v.1)
        ((w.frame.data.vertexPartition v.1).repr s) = _
      have hFold : GraphContraction.fold w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
          v.1 = v := GraphContraction.fold_coe _ _ v
      refine (congrArg (fun z : (w.frame.limitTarget w.column).V ↦
        w.limit.sourceEndpoint z ((w.frame.data.vertexPartition v.1).repr s)) hFold).trans ?_
      apply M11StarExhaustionProof.sourceEndpoint_of_rel
      rw [hPart]
      exact (w.frame.data.vertexPartition v.1).rel_repr_left s
    rw [hImage] at hMap
    have h0 : nonDanglingValency w.frame.data x = 0 := hMap.symm.trans (hVD v hv s hs)
    obtain ⟨hOne, -⟩ := PendantFibre.degree_one_of_nonDanglingValency_zero w.frame.fullDim x h0
    change (w.frame.data.vertexPartition v.1).blockCard
      ((w.frame.data.vertexPartition v.1).repr s) = 1 at hOne
    have hBlock := (w.frame.data.vertexPartition v.1).block_eq_of_rel
      ((w.frame.data.vertexPartition v.1).rel_repr_right s)
    unfold SheetPartition.blockCard at hOne
    rw [← hBlock] at hOne
    have hSingle := (w.frame.data.vertexPartition v.1).block_eq_singleton_of_blockCard_eq_one
      s hOne
    rw [hPart] at hst
    have hMem := ((w.frame.data.vertexPartition v.1).mem_block_iff s t).mpr hst
    rw [hSingle, Finset.mem_singleton] at hMem
    exact hMem
  · intro f hf s hs t hst
    have hIndex := hNoGlue _ (hED f hf s hs)
    change (w.limit.edgePartition f).blockCard ((w.limit.edgePartition f).repr s) = 1 at hIndex
    have hBlock := (w.limit.edgePartition f).block_eq_of_rel
      ((w.limit.edgePartition f).rel_repr_right s)
    unfold SheetPartition.blockCard at hIndex
    rw [← hBlock] at hIndex
    have hSingle := (w.limit.edgePartition f).block_eq_singleton_of_blockCard_eq_one s hIndex
    have hMem := ((w.limit.edgePartition f).mem_block_iff s t).mpr hst
    rw [hSingle, Finset.mem_singleton] at hMem
    exact hMem

/-- **Realigning one dangling sheet.**  Two sheets of the distinguished block that both dangle
above an incident direction `E` can be exchanged on `E`'s branch alone: the limit
isomorphism is re-chosen (composed with a pendant automorphism) so that its `E`-permutation
carries a given member sheet to a given wall sheet, and every other incident permutation and
the target maps are untouched. -/
theorem exists_realign (w : Regrowth core y degree) (hy : Nondegenerate y)
    {star : ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
    (input : W3SourceInput w.limit star) (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w) (E : (w.frame.limitTarget w.column).edges)
    (hE : E ∈ GluingDatum.incidentEdges (mergeVertex w))
    (hPos : 0 < nonDanglingValency w.limit
      (w.limit.sourceEndpoint (mergeVertex w) input.distinguishedBlock.1))
    (u q : Fin degree)
    (hp : (w.limit.vertexPartition (mergeVertex w)).Rel input.distinguishedBlock.1
        (ψ.datum.edgePerm (ψ.datum.targetEdge.symm E) u) ∧
      IsDangling w.limit (w.limit.sourceEdge E (ψ.datum.edgePerm (ψ.datum.targetEdge.symm E) u)))
    (hq : (w.limit.vertexPartition (mergeVertex w)).Rel input.distinguishedBlock.1 q ∧
      IsDangling w.limit (w.limit.sourceEdge E q)) :
    ∃ ψ' : GeometricStar.LimitIso hy other w,
      ψ'.datum.targetEdge = ψ.datum.targetEdge ∧
      ψ'.datum.edgePerm (ψ.datum.targetEdge.symm E) u = q ∧
      ∀ e ∈ GluingDatum.incidentEdges (mergeVertex w), e ≠ E →
        ψ'.datum.edgePerm (ψ.datum.targetEdge.symm e) =
          ψ.datum.edgePerm (ψ.datum.targetEdge.symm e) := by
  classical
  have hIncE : ((E : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
      mergeVertex w ∨
      (E : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
        mergeVertex w) := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hE
  set D : Fin degree → Prop := fun s ↦
    (w.limit.vertexPartition (mergeVertex w)).Rel input.distinguishedBlock.1 s ∧
      IsDangling w.limit (w.limit.sourceEdge E s)
  set a := ψ.datum.edgePerm (ψ.datum.targetEdge.symm E) u
  have hP := pendant_at_wall' w hy input.dangling_no_glue hIncE input.distinguishedBlock.1 D
    (fun s hs ↦ hs.1) (fun s hs ↦ hs.2) hPos
  set π := Equiv.swap a q
  have hπ : ∀ x, ¬ D x → π x = x := by
    intro x hx
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · rintro rfl; exact hx hp
    · rintro rfl; exact hx hq
  have hπD : ∀ x, D x → D (π x) := by
    intro x hx
    change D (Equiv.swap a q x)
    rw [Equiv.swap_apply_def]
    split_ifs
    · exact hq
    · exact hp
    · exact hx
  have hD : ∀ s t, D s → D t → (w.limit.vertexPartition (mergeVertex w)).Rel s t :=
    fun s t hs ht ↦ hs.1.symm.trans ht.1
  set α := pendantLimitIso (hy := hy) hP hD π hπ hπD
  refine ⟨ψ.trans α, Equiv.ext fun _ ↦ rfl, ?_, ?_⟩
  · have hmap : (ψ.trans α).datum.edgePerm (ψ.datum.targetEdge.symm E) u =
        branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) E) (farEnd_ne hIncE)
          (ψ.datum.targetEdge (ψ.datum.targetEdge.symm E))) π a := rfl
    rw [hmap, Equiv.apply_symm_apply, edgeMoved_self hIncE]
    exact Equiv.swap_apply_left a q
  · intro e he hne
    have hInce : ((e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
        mergeVertex w ∨
        (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
          mergeVertex w) := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using he
    ext s
    have hmap : (ψ.trans α).datum.edgePerm (ψ.datum.targetEdge.symm e) s =
        branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) E) (farEnd_ne hIncE)
          (ψ.datum.targetEdge (ψ.datum.targetEdge.symm e))) π
          (ψ.datum.edgePerm (ψ.datum.targetEdge.symm e) s) := rfl
    rw [hmap, Equiv.apply_symm_apply, edgeMoved_other (W4StarParity.limitTarget_connected w)
      (W4StarParity.limitTarget_genus w) hIncE hInce hne]
    rfl

end PendantRealign

/-! ## 5.  The six positions over their gauge bases, and the transport isomorphisms -/

section Positions

open W3ShiftSourceCandidates W3ShiftStarCensusProof
open W3ShiftSixMemberMatrices (MemberIndex)
open W3ShiftSixMemberBalance (orientation)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w)

/-- **Position II.b over its gauge base.** -/
theorem pos_shrink (d : Fin 3) :
    Piece ((S.P d).base.vertexPartition (mergeVertex w)) (S.P d).gaugeShift.movingAnchor
        ((S.P d).base.edgePartition (S.P d).gaugeShift.movingTarget)
        ((S.P d).base.edgePartition (S.P d).gaugeShift.movingTarget)
        (M11StarCensusProof.pasted (S.mem (d, 0))).left ∧
      Piece ((S.P d).base.vertexPartition (mergeVertex w)) (S.P d).gaugeShift.movingAnchor
        (((S.P d).base.vertexPartition (mergeVertex w)).detachSheet (S.P d).shrink.transfer
          (S.P d).shrink.remainder (S.P d).shrink.transfer_ne_remainder
          (S.P d).shrink.remainder_wall_rel)
        ((S.P d).base.vertexPartition (mergeVertex w))
        (M11StarCensusProof.pasted (S.mem (d, 0))).right ∧
      Piece ((S.P d).base.vertexPartition (mergeVertex w)) (S.P d).gaugeShift.movingAnchor
        (((S.P d).base.edgePartition (S.P d).gaugeShift.movingTarget).detachSheet
          (S.P d).shrink.transfer (S.P d).shrink.remainder (S.P d).shrink.transfer_ne_remainder
          (S.P d).shrink.remainder_moving)
        ((S.P d).base.edgePartition (S.P d).gaugeShift.movingTarget)
        (M11StarCensusProof.pasted (S.mem (d, 0))).newEdge := by
  have hA := (S.P d).gaugeShift.movingTarget_refines
  refine ⟨piece_of_blocks hA hA
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_selected (S.P d).shrink 0 s hs).1)
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_background (S.P d).shrink 0 s
        hs).1),
    piece_of_blocks (fun u v h ↦ ((detachSheet_rel_iff _ _ _ _ _ u v).mp h).1)
      (SheetPartition.Refines.refl _)
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_selected (S.P d).shrink 0 s
        hs).2.1)
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_background (S.P d).shrink 0 s
        hs).2.1),
    piece_of_blocks (fun u v h ↦ hA.rel ((detachSheet_rel_iff _ _ _ _ _ u v).mp h).1) hA
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_selected (S.P d).shrink 0 s
        hs).2.2)
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_background (S.P d).shrink 0 s
        hs).2.2)⟩

/-- **Position II.a over its gauge base.** -/
theorem pos_grow (d : Fin 3) :
    Piece ((S.P d).base.vertexPartition (mergeVertex w)) (S.P d).gaugeShift.movingAnchor
        (S.P d).gaugeShift.growPartition
        ((S.P d).base.edgePartition (S.P d).gaugeShift.movingTarget)
        (M11StarCensusProof.pasted (S.mem (d, 1))).left ∧
      Piece ((S.P d).base.vertexPartition (mergeVertex w)) (S.P d).gaugeShift.movingAnchor
        ((S.P d).base.vertexPartition (mergeVertex w))
        ((S.P d).base.vertexPartition (mergeVertex w))
        (M11StarCensusProof.pasted (S.mem (d, 1))).right ∧
      Piece ((S.P d).base.vertexPartition (mergeVertex w)) (S.P d).gaugeShift.movingAnchor
        (S.P d).gaugeShift.growPartition
        ((S.P d).base.edgePartition (S.P d).gaugeShift.movingTarget)
        (M11StarCensusProof.pasted (S.mem (d, 1))).newEdge := by
  have hA := (S.P d).gaugeShift.movingTarget_refines
  have hG := (S.P d).gaugeShift.growPartition_refines
  refine ⟨piece_of_blocks hG hA
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_selected (S.P d).shrink 1 s hs).1)
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_background (S.P d).shrink 1 s
        hs).1),
    piece_of_blocks (SheetPartition.Refines.refl _) (SheetPartition.Refines.refl _)
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_selected (S.P d).shrink 1 s
        hs).2.1)
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_background (S.P d).shrink 1 s
        hs).2.1),
    piece_of_blocks hG hA
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_selected (S.P d).shrink 1 s
        hs).2.2)
      (fun s hs ↦ (W3ShiftIncomingMatching.shiftMembers_pasted_background (S.P d).shrink 1 s
        hs).2.2)⟩

/-- The three incident occurrences at the wall, in position `d`'s orientation. -/
theorem incident_pos (d : Fin 3) (e : (w.frame.limitTarget w.column).edges) :
    e ∈ GluingDatum.incidentEdges (mergeVertex w) ↔
      e = (S.P d).gaugeShift.movingTarget ∨ e = (S.P d).gaugeShift.firstTarget ∨
        e = (S.P d).gaugeShift.secondTarget := by
  rw [(S.P d).gaugeShift.incidentEdges_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- Every incident occurrence is some direction's moving one. -/
theorem exists_direction (e : (w.frame.limitTarget w.column).edges)
    (he : e ∈ GluingDatum.incidentEdges (mergeVertex w)) :
    ∃ d : Fin 3, (S.P d).gaugeShift.movingTarget = e := by
  have h0 := (orientation S.profile S.directions S.largest_lt 0).incidentEdges_eq
  rw [h0] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h
  · exact ⟨0, ((S.pairs 0).copy.movingTarget).trans h.symm⟩
  · exact ⟨1, ((S.pairs 1).copy.movingTarget).trans h.symm⟩
  · exact ⟨2, ((S.pairs 2).copy.movingTarget).trans h.symm⟩

variable (hy : Nondegenerate y) (other : Regrowth core y degree)

/-- The isomorphism a position's transport is stated along. -/
noncomputable abbrev isoAt (ψ : GeometricStar.LimitIso hy other w) (d : Fin 3) :
    GeometricDatumIso other.limit (S.P d).base :=
  ψ.datum.trans (S.pairs d).anchor.φ.symm

theorem anchor_symm_edge (d : Fin 3) (e : (w.frame.limitTarget w.column).edges) :
    (S.pairs d).anchor.φ.targetEdge.symm e = e :=
  (Equiv.symm_apply_eq _).mpr ((S.pairs d).anchor.edge_fix e).symm

theorem isoAt_wall (ψ : GeometricStar.LimitIso hy other w) (d : Fin 3) :
    (isoAt S hy other ψ d).targetVertex (mergeVertex other) = mergeVertex w := by
  have h : ψ.datum.targetVertex (mergeVertex other) = mergeVertex w :=
    W3Nd2StarExhaustionProof.isoOf_wall w hy S.input other ψ
  change (S.pairs d).anchor.φ.targetVertex.symm (ψ.datum.targetVertex (mergeVertex other)) = _
  rw [h]
  exact (Equiv.symm_apply_eq _).mpr ((S.pairs d).anchor.vertex_fix _).symm

theorem isoAt_targetEdge (ψ : GeometricStar.LimitIso hy other w) (d : Fin 3)
    (e : (other.frame.limitTarget other.column).edges) :
    (isoAt S hy other ψ d).targetEdge e = ψ.datum.targetEdge e :=
  anchor_symm_edge S d _

theorem isoAt_targetEdge_symm (ψ : GeometricStar.LimitIso hy other w) (d : Fin 3)
    (e : (w.frame.limitTarget w.column).edges) :
    (isoAt S hy other ψ d).targetEdge.symm e = ψ.datum.targetEdge.symm e := by
  rw [Equiv.symm_apply_eq, isoAt_targetEdge, Equiv.apply_symm_apply]

theorem isoAt_edgePerm (ψ : GeometricStar.LimitIso hy other w) (d : Fin 3)
    (e : (w.frame.limitTarget w.column).edges) (s : Fin degree) :
    (isoAt S hy other ψ d).edgePerm ((isoAt S hy other ψ d).targetEdge.symm e) s =
      (S.pairs d).anchor.φ.symm.edgePerm e (ψ.datum.edgePerm (ψ.datum.targetEdge.symm e) s) := by
  rw [isoAt_targetEdge_symm]
  change (S.pairs d).anchor.φ.symm.edgePerm (ψ.datum.targetEdge (ψ.datum.targetEdge.symm e))
    (ψ.datum.edgePerm (ψ.datum.targetEdge.symm e) s) = _
  rw [Equiv.apply_symm_apply]

/-- **A nonsingularity receipt**: a member received at a position makes it nonsingular
(the member is full-dimensional, and multiplicity is an invariant of geometric
isomorphism). -/
theorem nonsingular_of_transport (member : GeometricStar.StarMember hy w)
    (ψ : GeometricStar.LimitIso hy member.member w)
    (placement : (member.member.frame.limitTarget member.member.column).edges → Bool)
    (hPlacement : W3Nd2StarCensusProof.PlacementSpec member.member placement) (i : MemberIndex)
    (t : S.PositionTransport hy member.member ψ placement hPlacement i) : S.Nonsingular hy i := by
  set iso := StarCensusEngine.anchoredDatum (w := w) (hy := hy) (D := (S.mem i).datum)
    (M := (S.P i.1).base) (φ := (S.pairs i.1).anchor.φ)
    (res := M11StarCensusProof.pasted (S.mem i))
    (compat := GlobalAssembly.blockwiseCompatible _ _ _ _ _ (S.mem i).exterior)
    rfl member.member ψ (W3Nd2StarCensusProof.memberNorm member.member placement hPlacement) t
  have hAbs := GeometricMultiplicity.absMult_eq_of_datumIso iso
    member.member.frame.fullDim.valid.1 member.member.frame.fullDim.labelling (S.engLab hy i)
  have hfd := (W4StarParity.absMult_ne_zero_iff
    member.member.frame.fullDim.labelling.presentation).mpr member.member.frame.fullDim.det_ne_zero
  exact (W4StarParity.absMult_ne_zero_iff (S.engLab hy i).presentation).mp (hAbs ▸ hfd)

/-- **Stage 2 reduced to transports, with no separate nonsingularity receipt.** -/
theorem exhausts_of_transports'
    (h : ∀ member : GeometricStar.StarMember hy w,
      ∃ ψ : GeometricStar.LimitIso hy member.member w,
      ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
      ∃ hPlacement : W3Nd2StarCensusProof.PlacementSpec member.member placement,
      ∃ i : MemberIndex,
        Nonempty (S.PositionTransport hy member.member ψ placement hPlacement i)) :
    S.Exhausts hy := by
  refine S.exhausts_of_transports hy fun member ↦ ?_
  obtain ⟨ψ, placement, hPlacement, i, ⟨t⟩⟩ := h member
  exact ⟨ψ, placement, hPlacement, i,
    nonsingular_of_transport S hy member ψ placement hPlacement i t, ⟨t⟩⟩

end Positions

/-! ## 6.  Every member is received: realign, then transport -/

section Receipt

open W3ShiftSourceCandidates W3ShiftStarCensusProof
open W3ShiftSixMemberMatrices (MemberIndex)
open W3Nd2StarExhaustionProof (isoOf_wall)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ} {w : Regrowth core y degree}
  (S : Setup w) (hy : Nondegenerate y) (other : Regrowth core y degree)

theorem blockPre_congr {target₁ target₂ : CFGraph} {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {s t : Fin degree} (h : (second.vertexPartition wall').Rel s t) :
    (first.vertexPartition wall).Rel (blockPre iso wall s).1 (blockPre iso wall t).1 :=
  (blockPre_rel iso wall s).trans (((M11StarExhaustionProof.wall_rel_iff iso hWall s t).mp h).trans
    (blockPre_rel iso wall t).symm)

theorem hPos_setup : 0 < nonDanglingValency w.limit
    (w.limit.sourceEndpoint (mergeVertex w) S.input.distinguishedBlock.1) := by
  change 0 < nonDanglingValency w.limit
    (WallBlock.sourceVertex w.limit (mergeVertex w) S.input.distinguishedBlock)
  rw [← card_survivors]
  exact Finset.card_pos.mpr ⟨S.profile.first, by rw [S.profile.surviving]; simp⟩

include S in
theorem mem_incident_symm (ψ : GeometricStar.LimitIso hy other w)
    {E : (w.frame.limitTarget w.column).edges} (hE : E ∈ GluingDatum.incidentEdges (mergeVertex w)) :
    ψ.datum.targetEdge.symm E ∈ GluingDatum.incidentEdges (mergeVertex other) := by
  have h := (incident_iff ψ.datum (isoOf_wall w hy S.input other ψ) (ψ.datum.targetEdge.symm E)).mpr
    (by rw [Equiv.apply_symm_apply]; exact hE)
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- A dangling sheet of a position's gauge base, pulled back to the wall's limit. -/
theorem wall_sheet_of_base (d : Fin 3) {E : (w.frame.limitTarget w.column).edges}
    (hE : E ∈ GluingDatum.incidentEdges (mergeVertex w)) (x : Fin degree)
    (hx : ((S.P d).base.vertexPartition (mergeVertex w)).Rel
      (S.P d).gaugeInput.distinguishedBlock.1 x)
    (hDang : IsDangling (S.P d).base ((S.P d).base.sourceEdge E x)) :
    (w.limit.vertexPartition (mergeVertex w)).Rel S.input.distinguishedBlock.1
        (((S.pairs d).anchor.φ.symm.edgePerm E).symm x) ∧
      IsDangling w.limit (w.limit.sourceEdge E (((S.pairs d).anchor.φ.symm.edgePerm E).symm x)) := by
  set φs := (S.pairs d).anchor.φ.symm
  have hφW : φs.targetVertex (mergeVertex w) = mergeVertex w :=
    (Equiv.symm_apply_eq _).mpr ((S.pairs d).anchor.vertex_fix _).symm
  have hφE : φs.targetEdge E = E := anchor_symm_edge S d E
  have hIncE : φs.targetEdge E ∈ GluingDatum.incidentEdges (mergeVertex w) := by
    rw [hφE]; exact hE
  have hAg := edgePerm_agree φs hφW E hIncE
  have hsel := sel_iff φs hφW (S.P d).gaugeInput.distinguishedBlock.1 _ hAg
    ((φs.edgePerm E).symm x)
  have hdb := distinguishedBlock_eq_blockPre φs hφW S.input (S.P d).gaugeInput
  refine ⟨?_, ?_⟩
  · rw [hdb]
    exact hsel.mpr (by rw [Equiv.apply_symm_apply]; exact hx)
  · refine (isDangling_sourceEdge_iff φs (InheritedLimitRows.limit_connected w) E _).mp ?_
    rw [hφE, Equiv.apply_symm_apply]
    exact hDang

/-- A dangling sheet of a member, pushed to the wall's limit. -/
theorem wall_sheet_of_member (ψ : GeometricStar.LimitIso hy other w)
    {E : (w.frame.limitTarget w.column).edges} (hE : E ∈ GluingDatum.incidentEdges (mergeVertex w))
    {st₁ : ThreeStar (other.frame.limitTarget other.column) (mergeVertex other)}
    (i₁ : W3SourceInput other.limit st₁) (u : Fin degree)
    (hu : (other.limit.vertexPartition (mergeVertex other)).Rel i₁.distinguishedBlock.1 u)
    (hDang : IsDangling other.limit (other.limit.sourceEdge (ψ.datum.targetEdge.symm E) u)) :
    (w.limit.vertexPartition (mergeVertex w)).Rel S.input.distinguishedBlock.1
        (ψ.datum.edgePerm (ψ.datum.targetEdge.symm E) u) ∧
      IsDangling w.limit (w.limit.sourceEdge E (ψ.datum.edgePerm (ψ.datum.targetEdge.symm E) u)) := by
  have hψW : ψ.datum.targetVertex (mergeVertex other) = mergeVertex w :=
    isoOf_wall w hy S.input other ψ
  have hAg := edgePerm_agree_symm ψ.datum hψW E hE
  have hsel := sel_iff ψ.datum hψW S.input.distinguishedBlock.1 _ hAg u
  have hdb := distinguishedBlock_eq_blockPre ψ.datum hψW i₁ S.input
  refine ⟨hsel.mp (by rw [← hdb]; exact hu), ?_⟩
  have h := (isDangling_sourceEdge_iff ψ.datum (InheritedLimitRows.limit_connected other)
    (ψ.datum.targetEdge.symm E) u).mpr hDang
  rwa [Equiv.apply_symm_apply] at h

/-- **The moving survivor goes to the moving survivor**, along any transport isomorphism. -/
theorem survivor_rel (ψ : GeometricStar.LimitIso hy other w) (d : Fin 3)
    {st₁ : ThreeStar (other.frame.limitTarget other.column) (mergeVertex other)}
    {i₁ : W3SourceInput other.limit st₁} (σ₁ : ShiftProfile i₁)
    (hα : σ₁.movingTarget =
      (isoAt S hy other ψ d).targetEdge.symm (S.P d).gaugeShift.movingTarget) :
    ((S.P d).base.edgePartition (S.P d).gaugeShift.movingTarget).Rel
      (S.P d).gaugeShift.movingAnchor
      ((isoAt S hy other ψ d).edgePerm
        ((isoAt S hy other ψ d).targetEdge.symm (S.P d).gaugeShift.movingTarget)
        σ₁.movingAnchor) := by
  set J := isoAt S hy other ψ d
  have hJW := isoAt_wall S hy other ψ d
  have hAg := edgePerm_agree_symm J hJW _ (S.P d).gaugeShift.movingTarget_mem
  have hu : ((S.P d).base.vertexPartition (mergeVertex w)).Rel
      (S.P d).gaugeInput.distinguishedBlock.1
      (J.edgePerm (J.targetEdge.symm (S.P d).gaugeShift.movingTarget) σ₁.movingAnchor) := by
    have hsel := sel_iff J hJW (S.P d).gaugeInput.distinguishedBlock.1 _ hAg σ₁.movingAnchor
    have hdb := distinguishedBlock_eq_blockPre J hJW i₁ (S.P d).gaugeInput
    apply hsel.mp
    rw [← hdb]
    exact σ₁.movingAnchor_wall_rel
  have hS : ¬ IsDangling (S.P d).base ((S.P d).base.sourceEdge (S.P d).gaugeShift.movingTarget
      (J.edgePerm (J.targetEdge.symm (S.P d).gaugeShift.movingTarget) σ₁.movingAnchor)) := by
    intro h
    have h' := (isDangling_sourceEdge_iff J (InheritedLimitRows.limit_connected other)
      (J.targetEdge.symm (S.P d).gaugeShift.movingTarget) σ₁.movingAnchor).mp
      (by rw [Equiv.apply_symm_apply]; exact h)
    rw [← hα] at h'
    exact movingAnchor_survives σ₁ h'
  exact rel_of_survives (S.P d).gaugeShift.moving (moving_unique _) _ hu hS

/-- **Every star member is received at some position.** -/
theorem exists_receipt (member : GeometricStar.StarMember hy w) :
    ∃ ψ : GeometricStar.LimitIso hy member.member w,
    ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
    ∃ hPlacement : W3Nd2StarCensusProof.PlacementSpec member.member placement,
    ∃ i : MemberIndex, Nonempty (S.PositionTransport hy member.member ψ placement hPlacement i) := by
  classical
  obtain ⟨ψ₀⟩ := member.specializes
  obtain ⟨σ₁, -, hP, hShape⟩ := member_shape w hy S.input S.profile S.directions S.largest_lt
    member.member ψ₀
  have hψ₀W : ψ₀.datum.targetVertex (mergeVertex member.member) = mergeVertex w :=
    isoOf_wall w hy S.input member.member ψ₀
  have hMem₁ := σ₁.movingTarget_mem
  have hEnds : ((σ₁.movingTarget : (member.member.frame.limitTarget member.member.column).V ×
      (member.member.frame.limitTarget member.member.column).V).1 = mergeVertex member.member ∨
      (σ₁.movingTarget : (member.member.frame.limitTarget member.member.column).V ×
        (member.member.frame.limitTarget member.member.column).V).2 = mergeVertex member.member) := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hMem₁
  have ht := (incident_iff ψ₀.datum hψ₀W σ₁.movingTarget).mp hEnds
  obtain ⟨d, hd⟩ := exists_direction S _ ht
  have hEdges := incident_pos S d
  have memL := (S.P d).gaugeShift.movingTarget_mem
  have memG := (S.P d).gaugeShift.firstTarget_mem
  have memT := (S.P d).gaugeShift.secondTarget_mem
  have hLG : (S.P d).gaugeShift.movingTarget ≠ (S.P d).gaugeShift.firstTarget :=
    (S.P d).gaugeShift.moving_target_ne_first
  have hLT : (S.P d).gaugeShift.movingTarget ≠ (S.P d).gaugeShift.secondTarget :=
    (S.P d).gaugeShift.moving_target_ne_second
  have hGT : (S.P d).gaugeShift.firstTarget ≠ (S.P d).gaugeShift.secondTarget :=
    (S.P d).gaugeShift.first_target_ne_second
  have hα : ∀ ψ : GeometricStar.LimitIso hy member.member w,
      ψ.datum.targetEdge = ψ₀.datum.targetEdge →
      σ₁.movingTarget = (isoAt S hy member.member ψ d).targetEdge.symm
        (S.P d).gaugeShift.movingTarget := by
    intro ψ hψ
    rw [Equiv.eq_symm_apply, isoAt_targetEdge, hψ, hd]
  have hne : ∀ ψ : GeometricStar.LimitIso hy member.member w,
      ψ.datum.targetEdge = ψ₀.datum.targetEdge →
      ∀ E, E ≠ (S.P d).gaugeShift.movingTarget → ψ.datum.targetEdge.symm E ≠ σ₁.movingTarget := by
    intro ψ hψ E hE h
    apply hE
    rw [hd, ← hψ, ← h, Equiv.apply_symm_apply]
  have hb : ∀ ψ : GeometricStar.LimitIso hy member.member w,
      (member.member.limit.vertexPartition (mergeVertex member.member)).Rel σ₁.movingAnchor
        (blockPre (isoAt S hy member.member ψ d) (mergeVertex member.member)
          (S.P d).gaugeShift.movingAnchor).1 := by
    intro ψ
    have hJW := isoAt_wall S hy member.member ψ d
    have hdb := distinguishedBlock_eq_blockPre _ hJW (W3Nd2StarExhaustionProof.input₁ w hy S.input
      member.member ψ₀) (S.P d).gaugeInput
    have h1 := σ₁.movingAnchor_wall_rel
    rw [hdb] at h1
    exact h1.symm.trans (blockPre_congr _ hJW (S.P d).gaugeShift.movingAnchor_wall_rel)
  have hSide : ∀ ψ : GeometricStar.LimitIso hy member.member w,
      ψ.datum.targetEdge = ψ₀.datum.targetEdge →
      ∀ edge, rightOf (S.P d).gaugeShift.movingTarget ((isoAt S hy member.member ψ d).targetEdge edge) =
        rightOf σ₁.movingTarget edge := by
    intro ψ hψ edge
    rw [rightOf_pullback, ← hα ψ hψ]
  rcases hShape with ⟨sh, hL, hR, hN⟩ | ⟨hL, hR, hN⟩
  · -- Position II.b: realign the detached sheet on both retained branches
    set x₂ := (S.P d).shrink.transfer
    have hx₂ := (S.P d).shrink.transfer_wall_rel
    have hq : ∀ E, E ∈ GluingDatum.incidentEdges (mergeVertex w) →
        E ≠ (S.P d).gaugeShift.movingTarget → _ := fun E hE hEL ↦
      wall_sheet_of_base S d hE x₂ hx₂ (transfer_isDangling (S.P d).shrink E hE (Ne.symm (Ne.symm hEL)))
    have hp : ∀ ψ : GeometricStar.LimitIso hy member.member w,
        ψ.datum.targetEdge = ψ₀.datum.targetEdge →
        ∀ E, E ∈ GluingDatum.incidentEdges (mergeVertex w) →
        E ≠ (S.P d).gaugeShift.movingTarget → _ := fun ψ hψ E hE hEL ↦
      wall_sheet_of_member S hy member.member ψ hE _ sh.transfer sh.transfer_wall_rel
        (transfer_isDangling sh _ (mem_incident_symm S hy member.member ψ hE)
          (hne ψ hψ E hEL))
    obtain ⟨ψ₁, h₁E, h₁G, h₁rest⟩ := exists_realign w hy S.input member.member ψ₀
      (S.P d).gaugeShift.firstTarget memG (hPos_setup S) sh.transfer _
      (hp ψ₀ rfl _ memG hLG.symm) (hq _ memG hLG.symm)
    obtain ⟨ψ₂, h₂E, h₂T, h₂rest⟩ := exists_realign w hy S.input member.member ψ₁
      (S.P d).gaugeShift.secondTarget memT (hPos_setup S) sh.transfer _
      (hp ψ₁ h₁E _ memT hLT.symm) (hq _ memT hLT.symm)
    have h₂₀ : ψ₂.datum.targetEdge = ψ₀.datum.targetEdge := h₂E.trans h₁E
    set J := isoAt S hy member.member ψ₂ d
    have hG : J.edgePerm (J.targetEdge.symm (S.P d).gaugeShift.firstTarget) sh.transfer = x₂ := by
      rw [isoAt_edgePerm, h₂E, h₂rest _ memG hGT, h₁E, h₁G, Equiv.apply_symm_apply]
    have hT : J.edgePerm (J.targetEdge.symm (S.P d).gaugeShift.secondTarget) sh.transfer = x₂ := by
      rw [isoAt_edgePerm, h₂E, h₂T, Equiv.apply_symm_apply]
    have hm := survivor_rel S hy member.member ψ₂ d σ₁ (hα ψ₂ h₂₀)
    have hx : ((S.P d).base.edgePartition (S.P d).gaugeShift.movingTarget).Rel
        (J.edgePerm (J.targetEdge.symm (S.P d).gaugeShift.movingTarget) sh.transfer) x₂ := by
      have h1 : (member.member.limit.edgePartition
          (J.targetEdge.symm (S.P d).gaugeShift.movingTarget)).Rel σ₁.movingAnchor sh.transfer := by
        rw [← hα ψ₂ h₂₀]; exact sh.transfer_moving
      have h2 := (edge_rel_iff_symm J _ _ _).mp h1
      exact h2.symm.trans (hm.symm.trans (S.P d).shrink.transfer_moving)
    obtain ⟨pL, pR, pN⟩ := pos_shrink S d
    refine ⟨ψ₂, rightOf σ₁.movingTarget, hP, (d, 0), ?_⟩
    exact nonempty_transportFree_shrink J (isoAt_wall S hy member.member ψ₂ d)
      (S.P d).gaugeShift.movingAnchor _ _ _ hEdges _ _ _ (hSide ψ₂ h₂₀) σ₁.movingTarget
      (hα ψ₂ h₂₀) sh.transfer x₂ _ _ _ _ (detachSheet_rel_iff _ _ _ _ _)
      (detachSheet_rel_iff _ _ _ _ _) (detachSheet_rel_iff _ _ _ _ _)
      (detachSheet_rel_iff _ _ _ _ _) hx hG hT (hL.congr_anchor (hb ψ₂))
      (hR.congr_anchor (hb ψ₂)) (hN.congr_anchor (hb ψ₂)) pL pR pN
  · -- Position II.a: realign the transferred sheet on the moving branch
    set y₂ := (S.P d).gaugeShift.extra
    have hsym : ψ₀.datum.targetEdge.symm (S.P d).gaugeShift.movingTarget = σ₁.movingTarget := by
      rw [Equiv.symm_apply_eq, hd]
    have hp := wall_sheet_of_member S hy member.member ψ₀ memL _ σ₁.extra σ₁.extra_wall_rel
      (by rw [hsym]; exact extra_isDangling σ₁)
    have hq := wall_sheet_of_base S d memL y₂ (S.P d).gaugeShift.extra_wall_rel
      (extra_isDangling (S.P d).gaugeShift)
    obtain ⟨ψ₁, h₁E, h₁L, -⟩ := exists_realign w hy S.input member.member ψ₀
      (S.P d).gaugeShift.movingTarget memL (hPos_setup S) σ₁.extra _ hp hq
    set J := isoAt S hy member.member ψ₁ d
    have hyJ : J.edgePerm (J.targetEdge.symm (S.P d).gaugeShift.movingTarget) σ₁.extra = y₂ := by
      rw [isoAt_edgePerm, h₁E, h₁L, Equiv.apply_symm_apply]
    have hm := survivor_rel S hy member.member ψ₁ d σ₁ (hα ψ₁ h₁E)
    obtain ⟨pL, pR, pN⟩ := pos_grow S d
    refine ⟨ψ₁, rightOf σ₁.movingTarget, hP, (d, 1), ?_⟩
    refine nonempty_transportFree_grow J (isoAt_wall S hy member.member ψ₁ d)
      (S.P d).gaugeShift.movingAnchor _ _ _ hEdges _ _ _ (hSide ψ₁ h₁E) σ₁.movingTarget
      (hα ψ₁ h₁E) σ₁.movingAnchor σ₁.extra (S.P d).gaugeShift.movingAnchor y₂ _ _
      (mergeBlocks_rel_iff _ _ _ _) (mergeBlocks_rel_iff _ _ _ _) hm.symm
      (by rw [hyJ]; change _ = _; rfl)
      (hL.congr_anchor (hb ψ₁)) (hR.congr_anchor (hb ψ₁)) (hN.congr_anchor (hb ψ₁)) pL pR pN

/-- **Stage 2 at one `w3Shift` wall, for every setup.** -/
theorem exhausts : S.Exhausts hy :=
  exhausts_of_transports' S hy (exists_receipt S hy)

end Receipt

/-! ## 7.  The W3Shift star census and the family clause, with no hypothesis -/

section Family

open W3ShiftStarCensusProof

variable (degree n p : ℕ)

/-- **The W3Shift star exhaustion**, at every core, degree and request, for every setup. -/
theorem w3ShiftStarExhaustion : W3ShiftStarExhaustion degree n p :=
  fun _ _ hy _ _ _ S ↦ exhausts S hy

/-- **The W3Shift star census**, unconditionally: at every `w3Shift` regrowth and every setup,
the star is in bijection with Equation (3)'s nonsingular positions, each class carrying its
term's `|num|`. -/
theorem w3ShiftStarCensus : W3ShiftStarCensus degree n p :=
  w3ShiftStarCensus_of_exhaustion (w3ShiftStarExhaustion degree n p)

/-- **Every `w3Shift` star has exactly as many classes as Equation (3) has nonsingular
positions.** -/
theorem w3ShiftStarCard (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y)
    (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (_htag : cls.sourceCase = .w3Shift) (S : Setup w) :
    Nat.card (GeometricStar.Star hy w) = Nat.card {i // S.Nonsingular hy i} :=
  (S.exhausts_iff_card hy).mp (exhausts S hy)

/-- **The `w3Shift` clause of `FamilyStarParity` at genus six and degree four, with no
hypothesis.** -/
theorem familyStarParity_w3Shift :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Shift :=
  familyStarParity_w3Shift_of_exhaustion (w3ShiftStarExhaustion _ _ _)

end Family

end DraismaVargas.Count.W3ShiftStarExhaustionProof
