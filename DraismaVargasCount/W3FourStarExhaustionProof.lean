module

public import DraismaVargasCount.W3FourStarCensusProof
public import DraismaVargasCount.W3Nd3StarExhaustionProof

@[expose] public section

/-!
# W3Four star exhaustion: the `w3Four` clause with no hypothesis

Sources: Draisma–Vargas Part I, Case `{w3-r1-nd3-t2-(a=k₄)}`, Figure 28, Equation (2), and
the dangling-no-glue lemma `lemma-dangling-no-glue`; Vargas, Part II, the star of a wall.
The reduction completed here is that of `DraismaVargasCount.W3FourStarCensusProof`
(`Setup.exhausts_of_transports`); the machinery comes from
`DraismaVargasCount.W3Nd2StarExhaustionProof`, `DraismaVargasCount.W3Nd3StarExhaustionProof`
and `DraismaVargasCount.M11StarExhaustionProof`.

## The result, in one paragraph

Every star member of a `w3Four` wall presents a decoupled transport (its *receipt*) onto
one of Figure 28's four positions, at a nonsingular position (`exists_receipt`), so
`W3FourStarCensusProof.W3FourStarExhaustion` holds at every degree, core size and request
(`w3FourStarExhaustion`), hence the census (`w3FourStarCensus`), the count
(`w3FourStarCard`: the star has exactly as many classes as Equation (2) has nonsingular
positions) and **`familyStarParity_w3Four`, with no hypothesis**.  The member's type is read
by Part I's census at its own contraction (`W3FourSelectedCensus.exists_selectedCensus`,
through the setup pulled back along its limit isomorphism): Position I (the pulled-back
`e₂`, `e₃` disjoint), Position II.b (they meet; the member's own outside sheet `x`), or
Position II.a on `t₂` or `t₃` (the member's own transferred sheet `y`).

## The mechanism, and where coherence enters

* **Position I (`M⁽¹⁾`)** needs **no** coherence.  Both refinements are "same side of
  `e₂`" (`positionOne_fine_rel_iff`) and on both sides `e₃` is exactly the other side
  (`positionOne_cover`), so the `t₂`- and `t₃`-permutations agree on it automatically
  (`receiptZero`), along the limit isomorphism followed by `M⁽¹⁾`'s branch swap.
* **Position II.b (`M⁽²⁾`)** needs the member's own outside sheet `x` sent to the
  position's `x₁` by **both** the `t₂`- and the `t₃`-permutation.  Neither holds for a given
  isomorphism; both are achieved by composing with **two** pendant transpositions, one on
  the `t₂`-branch and one on the `t₃`-branch (`receiptOne`), the branch swap `permTwo` being
  undone on the target side (`v₃ = permTwo⁻¹ x₁`).
* **Position II.a (`M⁽³⁾`, `M⁽⁴⁾`)** needs the member's transferred sheet `y` sent to the
  grow profile's default `y₀`: one pendant transposition on the grow branch
  (`growReceipt`).  So the question that `W3FourSelectedCensus` leaves open (matching `y`
  against `GrowProfile.extraSheet`, i.e. which Position II.a member the cover is) need
  not be settled for the star census: it is **absorbed by re-choosing the isomorphism**,
  not by identifying `y`.
* `W3Nd2StarExhaustionProof.pendant_at_wall` needs the whole distinguished block to dangle
  on the branch; at a `w3Four` wall only `A₀ ∖ e` dangles over the survivor's direction.
  `pendant_at_wall'` is the same argument for exactly those sheets (`DangSet`), and
  `grow_isDangling` is the literal `nd = 3` statement that they dangle.

## What is proved

* §1 `mergeBlocks_rel_iff`, `mergeBlocks_transport`.  §2 (family-generic)
  `nonempty_transportFree_grow`, `nonempty_transportFree_reversed` (the coarse/fine
  transports of `W3Nd2StarExhaustionProof` with arbitrary refinements in place of edge
  partitions).
* §3 `res`, `divalent`, `member_pieces` (a member identified with a Figure 28 wall member
  has its shape, from `W3FourIncomingMatching.member_sameBlocks`).
* §4 `iso₀`, `wall₀`, `star₁`, `input₁`, `profile₁`, `pull_sheet`, `first₁`, `second₁`,
  `largest₁`, `firstSheet₁`, `secondSheet₁`, `directions₁`, `largest_index₁`.
* §5 `DangSet`, `pendant_at_wall'`.  §6 `grow_isDangling`, `grow_not_isDangling`.
* §7 `nonsingular_of_transport`.  §8 `piece_congr_Y`, `setup_hPos`, `swap_mem`, `swap_fix`,
  `growReceipt`.  §9 `positionOne_fine_rel_iff`, `positionOne_cover`,
  `positionTwo_fine_rel_iff`.  §10 `reversedReceipt`.  §11 `G₁`, `swap_edgePerm_fixed`,
  `swap_edgePerm_moved`, `receiptZero`.  §12 `swap_rel`, `receiptOne`.
* §13 `exists_receipt`, `exhausts`, **`w3FourStarExhaustion`**, **`w3FourStarCensus`**,
  **`w3FourStarCard`**, **`familyStarParity_w3Four`**.

## Scope

* Nothing is assumed: the four headlines have no hypothesis beyond their binders.
* Non-vacuity is not shown: no `w3Four` regrowth is constructed here.
* `ResolutionExpansion.Transport` (the strict transport) is not produced; the transports
  are decoupled `TransportFree`s, which is what `Setup.exhausts_of_transports` consumes.
* With `W3FourStarCensusProof.Setup.card_nonsingular_ne_one`, `w3FourStarCard` shows that
  the star of a `w3Four` wall never has exactly one class.

## Consumers

`StarSupplyAssembly` takes the `w3Four` clause `familyStarParity_w3Four`, for the
trivalent wall step of `DraismaVargasCount.Assembly`.
-/

namespace DraismaVargas.Count.W3FourStarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open ThirdEquation W3R1SourceProfile
open M11StarExhaustionProof (blockPre blockPre_rel)
open W3Nd2StarExhaustionProof (Piece piece_of_blocks piece_transport piece_self piecewisePerm
  piecewisePerm_of_pos piecewisePerm_of_neg edge_rel_iff edge_rel_iff_symm incident_iff
  edgePerm_agree edgePerm_agree_symm agree_symm_apply sel_iff mem_L mem_G mem_T incident_cases
  rightOf_eq_false rightOf_eq_true)
open W3Nd2SourceCandidates (rightOf)

/-! ## 1.  Merged blocks, as a relation -/

section Merge

variable {d : ℕ}

theorem mergeBlocks_rel_iff (P : SheetPartition d) (f e : Fin d) (h : ¬ P.Rel f e) (x y : Fin d) :
    (P.mergeBlocks f e h).Rel x y ↔
      P.Rel x y ∨ ((P.Rel f x ∨ P.Rel e x) ∧ (P.Rel f y ∨ P.Rel e y)) := by
  by_cases hx : P.Rel f x ∨ P.Rel e x
  · have hfx : (P.mergeBlocks f e h).Rel f x := (P.mergeBlocks_rel_first_iff f e x h).mpr hx
    constructor
    · intro hxy
      exact Or.inr ⟨hx, (P.mergeBlocks_rel_first_iff f e y h).mp (hfx.trans hxy)⟩
    · rintro (hxy | ⟨_, hy⟩)
      · rcases hx with hx | hx
        · exact hfx.symm.trans ((P.mergeBlocks_rel_first_iff f e y h).mpr (Or.inl (hx.trans hxy)))
        · exact hfx.symm.trans ((P.mergeBlocks_rel_first_iff f e y h).mpr (Or.inr (hx.trans hxy)))
      · exact hfx.symm.trans ((P.mergeBlocks_rel_first_iff f e y h).mpr hy)
  · push Not at hx
    have hBlock := P.mergeBlocks_block_of_separate f e x h (fun h' ↦ hx.1 h'.symm)
      (fun h' ↦ hx.2 h'.symm)
    have hIff : (P.mergeBlocks f e h).Rel x y ↔ P.Rel x y := by
      rw [← SheetPartition.mem_block_iff, hBlock, SheetPartition.mem_block_iff]
    rw [hIff]
    refine ⟨Or.inl, fun h' ↦ h'.elim id (fun h'' ↦ ?_)⟩
    rcases h''.1 with h3 | h3
    · exact (hx.1 h3).elim
    · exact (hx.2 h3).elim

/-- A permutation carrying a partition, and the two merged blocks, carries the merge. -/
theorem mergeBlocks_transport (P P' : SheetPartition d) (f e f' e' : Fin d) (h : ¬ P.Rel f e)
    (h' : ¬ P'.Rel f' e') (τ : Equiv.Perm (Fin d))
    (hP : ∀ a b, P.Rel a b ↔ P'.Rel (τ a) (τ b)) (hf : P'.Rel (τ f) f') (he : P'.Rel (τ e) e')
    (x y : Fin d) :
    (P.mergeBlocks f e h).Rel x y ↔ (P'.mergeBlocks f' e' h').Rel (τ x) (τ y) := by
  rw [mergeBlocks_rel_iff, mergeBlocks_rel_iff, hP, hP f, hP e, hP f, hP e]
  have k1 : ∀ z, P'.Rel (τ f) z ↔ P'.Rel f' z := fun z ↦ ⟨fun h ↦ hf.symm.trans h, fun h ↦ hf.trans h⟩
  have k2 : ∀ z, P'.Rel (τ e) z ↔ P'.Rel e' z := fun z ↦ ⟨fun h ↦ he.symm.trans h, fun h ↦ he.trans h⟩
  rw [k1, k1, k2, k2]

end Merge

/-! ## 2.  Transports from shapes (family-generic)

Two shapes, generalizing the coarse and fine transports
(`W3Nd2StarExhaustionProof.nonempty_transportFree_coarse`,
`W3Nd2StarExhaustionProof.nonempty_transportFree_fine`) from edge partitions to
arbitrary partitions on the distinguished block.  `G` is the direction a position isolates
at its divalent end, `L` a direction at its trivalent end, `T` the third. -/

section Transport

open ResolutionExpansionFree W4Assembly
open ResolutionM11 (LocalResolution)

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  (iso : GeometricDatumIso first second) {wall : target₁.V} {wall' : target₂.V}
  (hWall : iso.targetVertex wall = wall')
  (b : Fin degree) (L G T : target₂.edges)
  (hEdges : ∀ e, e ∈ GluingDatum.incidentEdges wall' ↔ e = L ∨ e = G ∨ e = T)

include hWall hEdges in
/-- **The grow transport.**  Both ends and the regrown occurrence are carried by the
isolated direction's occurrence permutation; the trivalent end is the whole wall block. -/
theorem nonempty_transportFree_grow (right : target₁.edges → Bool)
    (res res' : LocalResolution degree) (A C A' C' : SheetPartition degree)
    (hSide : ∀ edge, rightOf G (iso.targetEdge edge) = right edge)
    (hLeft : Piece (first.vertexPartition wall) (blockPre iso wall b).1 A
      (first.edgePartition (iso.targetEdge.symm G)) res.left)
    (hRight : Piece (first.vertexPartition wall) (blockPre iso wall b).1
      (first.vertexPartition wall) (first.vertexPartition wall) res.right)
    (hNew : Piece (first.vertexPartition wall) (blockPre iso wall b).1 C
      (first.edgePartition (iso.targetEdge.symm G)) res.newEdge)
    (hLeft' : Piece (second.vertexPartition wall') b A' (second.edgePartition G) res'.left)
    (hRight' : Piece (second.vertexPartition wall') b (second.vertexPartition wall')
      (second.vertexPartition wall') res'.right)
    (hNew' : Piece (second.vertexPartition wall') b C' (second.edgePartition G) res'.newEdge)
    (hA : ∀ x y, (first.vertexPartition wall).Rel (blockPre iso wall b).1 x →
      (A.Rel x y ↔ A'.Rel (iso.edgePerm (iso.targetEdge.symm G) x)
        (iso.edgePerm (iso.targetEdge.symm G) y)))
    (hC : ∀ x y, (first.vertexPartition wall).Rel (blockPre iso wall b).1 x →
      (C.Rel x y ↔ C'.Rel (iso.edgePerm (iso.targetEdge.symm G) x)
        (iso.edgePerm (iso.targetEdge.symm G) y))) :
    Nonempty (TransportFree iso wall wall' right (rightOf G) res res') := by
  set τ := iso.edgePerm (iso.targetEdge.symm G)
  have hτ := edgePerm_agree_symm iso hWall G (mem_G L G T hEdges)
  have hW := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall τ hτ
  have hb := sel_iff iso hWall b τ hτ
  have hP := edge_rel_iff_symm iso G
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel iso wall wall' right _ res _ hWall
    hSide hLeft.refines hRight.refines τ τ τ hτ hτ ?_ ?_ ?_ ?_ ?_ ?_
  · exact piece_transport τ hW hb hA (fun x y _ ↦ hP x y) hLeft hLeft'
  · exact piece_transport τ hW hb (fun x y _ ↦ hW x y) (fun x y _ ↦ hW x y) hRight hRight'
  · exact piece_transport τ hW hb hC (fun x y _ ↦ hP x y) hNew hNew'
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro s; rw [Equiv.symm_apply_apply]; rfl
  · intro edge hInc s
    have hInc' := (incident_iff iso hWall edge).mp hInc
    by_cases hr : right edge = true
    · rw [ite_eq_left hr, ite_eq_left hr]
      have hAg := agree_symm_apply iso τ _ hτ (edgePerm_agree iso hWall edge hInc') s
      exact (hRight _ _).mpr ⟨hAg, fun _ ↦ hAg, fun _ ↦ hAg⟩
    · rw [ite_eq_right hr, ite_eq_right hr]
      have hEq : iso.targetEdge edge = G :=
        rightOf_eq_false (by rw [hSide edge]; simpa using hr)
      have hEdge : edge = iso.targetEdge.symm G := (Equiv.eq_symm_apply _).mpr hEq
      subst hEdge
      rw [Equiv.symm_apply_apply]; rfl

include hWall hEdges in
/-- **The reversed transport.**  The divalent end is the whole wall block beside `G`; the
trivalent end and the regrown occurrence carry a refinement `F` of the distinguished block,
carried by `L`'s permutation, and the third direction must agree with `L` modulo it
(`hCoh`). -/
theorem nonempty_transportFree_reversed (right : target₁.edges → Bool)
    (res res' : LocalResolution degree) (F F' : SheetPartition degree)
    (hF₁ : F.Refines (first.vertexPartition wall)) (hF₂ : F'.Refines (second.vertexPartition wall'))
    (hSide : ∀ edge, rightOf G (iso.targetEdge edge) = right edge)
    (hLeft : Piece (first.vertexPartition wall) (blockPre iso wall b).1 (first.vertexPartition wall)
      (first.edgePartition (iso.targetEdge.symm G)) res.left)
    (hRight : Piece (first.vertexPartition wall) (blockPre iso wall b).1 F
      (first.vertexPartition wall) res.right)
    (hNew : Piece (first.vertexPartition wall) (blockPre iso wall b).1 F
      (first.edgePartition (iso.targetEdge.symm G)) res.newEdge)
    (hLeft' : Piece (second.vertexPartition wall') b (second.vertexPartition wall')
      (second.edgePartition G) res'.left)
    (hRight' : Piece (second.vertexPartition wall') b F' (second.vertexPartition wall') res'.right)
    (hNew' : Piece (second.vertexPartition wall') b F' (second.edgePartition G) res'.newEdge)
    (hF : ∀ x y, (first.vertexPartition wall).Rel (blockPre iso wall b).1 x →
      (F.Rel x y ↔ F'.Rel (iso.edgePerm (iso.targetEdge.symm L) x)
        (iso.edgePerm (iso.targetEdge.symm L) y)))
    (hCoh : ∀ s, (first.vertexPartition wall).Rel (blockPre iso wall b).1 s →
      F'.Rel (iso.edgePerm (iso.targetEdge.symm T) s) (iso.edgePerm (iso.targetEdge.symm L) s)) :
    Nonempty (TransportFree iso wall wall' right (rightOf G) res res') := by
  classical
  set W := first.vertexPartition wall
  set σ := iso.edgePerm (iso.targetEdge.symm L)
  set ρ := iso.edgePerm (iso.targetEdge.symm G)
  have hσ := edgePerm_agree_symm iso hWall L (mem_L L G T hEdges)
  have hρ := edgePerm_agree_symm iso hWall G (mem_G L G T hEdges)
  have hbσ := sel_iff iso hWall b σ hσ
  have hbρ := sel_iff iso hWall b ρ hρ
  set τN := piecewisePerm (fun x ↦ W.Rel (blockPre iso wall b).1 x)
    (fun x ↦ (second.vertexPartition wall').Rel b x) σ ρ
    (fun x hx ↦ (hbσ x).mp hx) (fun x hx h ↦ hx ((hbρ x).mpr h))
  have hτN : ∀ s, W.Rel ((iso.vertexPerm wall).symm (τN s)) s := by
    intro s
    by_cases hs : W.Rel (blockPre iso wall b).1 s
    · rw [piecewisePerm_of_pos hs]; exact hσ s
    · rw [piecewisePerm_of_neg hs]; exact hρ s
  have hWσ := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall σ hσ
  have hWρ := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall ρ hρ
  have hWN := M11StarExhaustionProof.wall_rel_iff_of_agree iso hWall τN hτN
  have hbN := sel_iff iso hWall b τN hτN
  have hPl := edge_rel_iff_symm iso G
  refine M11StarExhaustionProof.nonempty_transportFree_of_rel iso wall wall' right _ res _ hWall
    hSide hLeft.refines hRight.refines ρ σ τN hρ hσ ?_ ?_ ?_ ?_ ?_ ?_
  · exact piece_transport ρ hWρ hbρ (fun x y _ ↦ hWρ x y) (fun x y _ ↦ hPl x y) hLeft hLeft'
  · exact piece_transport σ hWσ hbσ hF (fun x y _ ↦ hWσ x y) hRight hRight'
  · refine piece_transport τN hWN hbN ?_ ?_ hNew hNew'
    · intro x y hx
      rw [piecewisePerm_of_pos hx]
      by_cases hy : W.Rel (blockPre iso wall b).1 y
      · rw [piecewisePerm_of_pos hy]; exact hF x y hx
      · rw [piecewisePerm_of_neg hy]
        constructor
        · intro h; exact (hy (hx.trans (hF₁.rel h))).elim
        · intro h
          exact (hy ((hbρ y).mpr (((hbσ x).mp hx).trans (hF₂.rel h)))).elim
    · intro x y hx
      rw [piecewisePerm_of_neg hx]
      by_cases hy : W.Rel (blockPre iso wall b).1 y
      · rw [piecewisePerm_of_pos hy]
        have hLref := StableLocalProperties.refines_of_mem_incidentEdges second
          (mem_G L G T hEdges)
        have hLref₁ : (first.edgePartition (iso.targetEdge.symm G)).Refines W := by
          intro x y h
          exact (hWρ x y).mpr (hLref.rel ((hPl x y).mp h))
        constructor
        · intro h; exact (hx (hy.trans (hLref₁.rel h).symm)).elim
        · intro h
          exact (hx ((hbρ x).mpr (((hbσ y).mp hy).trans (hLref.rel h).symm))).elim
      · rw [piecewisePerm_of_neg hy]; exact hPl x y
  · intro s
    by_cases hs : W.Rel (blockPre iso wall b).1 s
    · rw [piecewisePerm_of_pos hs]
      exact hLeft.rel_of_sel (SheetPartition.Refines.refl _)
        ((hbρ _).mpr (by rw [Equiv.apply_symm_apply]; exact (hbσ s).mp hs))
        (agree_symm_apply iso ρ σ hρ hσ s)
    · rw [piecewisePerm_of_neg hs, Equiv.symm_apply_apply]; rfl
  · intro s
    by_cases hs : W.Rel (blockPre iso wall b).1 s
    · rw [piecewisePerm_of_pos hs, Equiv.symm_apply_apply]; rfl
    · rw [piecewisePerm_of_neg hs]
      exact hRight.rel_of_off (SheetPartition.Refines.refl _)
        (fun h ↦ hs (h.trans (agree_symm_apply iso σ ρ hσ hρ s)))
        (agree_symm_apply iso σ ρ hσ hρ s)
  · intro edge hInc s
    have hInc' := (incident_iff iso hWall edge).mp hInc
    by_cases hr : right edge = true
    · rw [ite_eq_left hr, ite_eq_left hr]
      have hNotG : edge ≠ iso.targetEdge.symm G := by
        rintro rfl
        rw [← hSide, Equiv.apply_symm_apply] at hr
        simp [rightOf] at hr
      rcases incident_cases iso L G T hEdges edge hInc' with h | h | h
      · subst h; rw [Equiv.symm_apply_apply]; rfl
      · exact (hNotG h).elim
      · subst h
        have hAg := agree_symm_apply iso σ _ hσ (edgePerm_agree_symm iso hWall T
          (mem_T L G T hEdges)) s
        by_cases hs : W.Rel (blockPre iso wall b).1 s
        · refine (hRight _ _).mpr ⟨hAg, fun _ ↦ ?_, fun h' ↦ (h' (hs.trans hAg.symm)).elim⟩
          have hs' : W.Rel (blockPre iso wall b).1 (σ.symm (iso.edgePerm (iso.targetEdge.symm T) s)) :=
            hs.trans hAg.symm
          rw [hF _ _ hs', Equiv.apply_symm_apply]
          exact hCoh s hs
        · exact hRight.rel_of_off (SheetPartition.Refines.refl _)
            (fun h ↦ hs (h.trans hAg)) hAg
    · rw [ite_eq_right hr, ite_eq_right hr]
      have hEq : iso.targetEdge edge = G :=
        rightOf_eq_false (by rw [hSide edge]; simpa using hr)
      have hEdge : edge = iso.targetEdge.symm G := (Equiv.eq_symm_apply _).mpr hEq
      subst hEdge
      rw [Equiv.symm_apply_apply]; rfl

end Transport

/-! ## 3.  A star member's shape, from Part I's identification at its own contraction -/

section MemberShape

open W4Assembly W3FourIncomingCensus

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (other : Regrowth core y degree) (hy : Nondegenerate y)
  {star : ThreeStar (other.frame.limitTarget other.column) (mergeVertex other)}
  (input : W3SourceInput other.limit star)

/-- The resolution a member reads off at a placement. -/
noncomputable abbrev res (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hP : W3Nd2StarCensusProof.PlacementSpec other placement) :=
  M11WallExhaustion.incomingResolution other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    placement hP

/-- The member's own isolated direction. -/
noncomputable abbrev divalent : (other.frame.limitTarget other.column).edges :=
  W3Nd2IncomingTargetPlacement.divalentOccurrence other.frame.data (contracted := other.frame.edgeOf other.column) rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim star

include hy in
/-- **A member identified with a Figure 28 wall member has that member's shape**, read as
pieces around the distinguished block. -/
theorem member_pieces (member : WallMember other.limit (mergeVertex other)
      input.distinguishedBlock.1)
    (hIso : member.isolated = divalent other (star := star))
    (hCensus : W3ShiftIncomingMatching.SelectedCensus other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      star input member.selectedLeft member.selectedRight member.selectedNew)
    (hMem : member.isolated ∈ GluingDatum.incidentEdges (mergeVertex other))
    (hLref : member.selectedLeft.Refines (other.limit.vertexPartition (mergeVertex other)))
    (hRref : member.selectedRight.Refines (other.limit.vertexPartition (mergeVertex other)))
    (hNref : member.selectedNew.Refines (other.limit.vertexPartition (mergeVertex other))) :
    ∃ hP : W3Nd2StarCensusProof.PlacementSpec other member.candidate.right,
    Piece (other.limit.vertexPartition (mergeVertex other)) input.distinguishedBlock.1
        member.selectedLeft (other.limit.edgePartition member.isolated)
        (res other member.candidate.right hP).left ∧
      Piece (other.limit.vertexPartition (mergeVertex other)) input.distinguishedBlock.1
        member.selectedRight (other.limit.vertexPartition (mergeVertex other))
        (res other member.candidate.right hP).right ∧
      Piece (other.limit.vertexPartition (mergeVertex other)) input.distinguishedBlock.1
        member.selectedNew (other.limit.edgePartition member.isolated)
        (res other member.candidate.right hP).newEdge := by
  have hIref := StableLocalProperties.refines_of_mem_incidentEdges other.limit hMem
  refine ⟨member_placement other.frame.data rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) other.frame.fullDim star member hIso, ?_⟩
  obtain ⟨hV, hE⟩ := W3FourIncomingMatching.member_sameBlocks other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    other.frame.fullDim (InheritedLimitRows.forest other hy) star input member hIso hCensus
  have hL : Piece (other.limit.vertexPartition (mergeVertex other)) input.distinguishedBlock.1
      member.selectedLeft (other.limit.edgePartition member.isolated)
      (W3Nd2IncomingMemberMatching.pasted member.candidate).left :=
    piece_of_blocks hLref hIref member.left_selected member.left_background
  have hR : Piece (other.limit.vertexPartition (mergeVertex other)) input.distinguishedBlock.1
      member.selectedRight (other.limit.vertexPartition (mergeVertex other))
      (W3Nd2IncomingMemberMatching.pasted member.candidate).right :=
    piece_of_blocks hRref (SheetPartition.Refines.refl _) member.right_selected
      member.right_background
  have hN : Piece (other.limit.vertexPartition (mergeVertex other)) input.distinguishedBlock.1
      member.selectedNew (other.limit.edgePartition member.isolated)
      (W3Nd2IncomingMemberMatching.pasted member.candidate).newEdge :=
    piece_of_blocks hNref hIref member.newEdge_selected member.newEdge_background
  refine ⟨hL.of_sameBlocks ?_, hR.of_sameBlocks ?_, hN.of_sameBlocks ?_⟩
  · have h := hV (oldVertex (other.frame.limitTarget other.column) (mergeVertex other))
    have h2 := M11StarCensusProof.candidate_oldWall member.candidate
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
  · have h := hV (freshVertex (other.frame.limitTarget other.column))
    have h2 := M11StarCensusProof.candidate_fresh member.candidate
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))
  · have h := hE (occurrenceEquiv (other.frame.limitTarget other.column) (mergeVertex other)
      member.candidate.right none)
    have h2 := W3Nd2IncomingMemberMatching.candidate_edgePartition_new member.candidate
    exact fun x y ↦ (h x y).trans (Iff.of_eq (congrArg (fun P : SheetPartition degree ↦ P.Rel x y) h2))

end MemberShape

/-! ## 4.  The setup, pulled back to a star member -/

section Pullback

open W3FourStarCensusProof

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} (hy : Nondegenerate y) (S : Setup w)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

/-- The limit isomorphism, as a datum isomorphism. -/
noncomputable abbrev iso₀ : GeometricDatumIso other.limit w.limit :=
  W3Nd2StarExhaustionProof.isoOf w hy other ψ

include S in
theorem wall₀ : (iso₀ hy other ψ).targetVertex (mergeVertex other) = mergeVertex w :=
  W3Nd2StarExhaustionProof.isoOf_wall w hy S.input other ψ

noncomputable abbrev star₁ : ThreeStar (other.frame.limitTarget other.column) (mergeVertex other) :=
  W3Nd2StarExhaustionProof.star₁ w hy S.input other ψ

noncomputable abbrev input₁ : W3SourceInput other.limit (star₁ hy S other ψ) :=
  W3Nd2StarExhaustionProof.input₁ w hy S.input other ψ

noncomputable abbrev profile₁ : Nd3Profile other.limit (input₁ hy S other ψ).distinguishedBlock :=
  W3Nd3StarExhaustionProof.profile₁ w hy S.input S.profile other ψ

/-- A pulled-back survivor's sheet is carried to the survivor's sheet. -/
theorem pull_sheet {target₁ target₂ : CFGraph} {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : ThreeStar target₂ wall'} (input : W3SourceInput second star')
    (E : IncidentSourceEdge second (WallBlock.sourceVertex second wall' input.distinguishedBlock)) :
    iso.edgePerm ((W3Nd2StarExhaustionProof.distinguishedIncident iso hWall input).symm E).1.1.1
        ((W3Nd2StarExhaustionProof.distinguishedIncident iso hWall input).symm E).1.1.2 =
      E.1.1.2 := by
  have h := (W3Nd2StarExhaustionProof.distinguishedIncident iso hWall input).apply_symm_apply E
  exact congrArg (fun e : IncidentSourceEdge second _ ↦ e.1.1.2) h

theorem first₁ : (profile₁ hy S other ψ).first.1.1.1 =
    (iso₀ hy other ψ).targetEdge.symm S.profile.first.1.1.1 :=
  W3Nd3StarExhaustionProof.target_symm' _ (wall₀ hy S other ψ) S.input S.profile.first

theorem second₁ : (profile₁ hy S other ψ).second.1.1.1 =
    (iso₀ hy other ψ).targetEdge.symm S.profile.second.1.1.1 :=
  W3Nd3StarExhaustionProof.target_symm' _ (wall₀ hy S other ψ) S.input S.profile.second

theorem largest₁ : (profile₁ hy S other ψ).largest.1.1.1 =
    (iso₀ hy other ψ).targetEdge.symm S.profile.largest.1.1.1 :=
  W3Nd3StarExhaustionProof.target_symm' _ (wall₀ hy S other ψ) S.input S.profile.largest

theorem firstSheet₁ : (iso₀ hy other ψ).edgePerm (profile₁ hy S other ψ).first.1.1.1
    (profile₁ hy S other ψ).first.1.1.2 = S.profile.first.1.1.2 :=
  pull_sheet _ (wall₀ hy S other ψ) S.input S.profile.first

theorem secondSheet₁ : (iso₀ hy other ψ).edgePerm (profile₁ hy S other ψ).second.1.1.1
    (profile₁ hy S other ψ).second.1.1.2 = S.profile.second.1.1.2 :=
  pull_sheet _ (wall₀ hy S other ψ) S.input S.profile.second

theorem directions₁ : (profile₁ hy S other ψ).first.1.1.1 ≠ (profile₁ hy S other ψ).second.1.1.1 := by
  rw [first₁, second₁]
  exact fun h ↦ S.directions ((iso₀ hy other ψ).targetEdge.symm.injective h)

theorem largest_index₁ : other.limit.sourceEdgeIndex (profile₁ hy S other ψ).largest.1 =
    (other.limit.vertexPartition (mergeVertex other)).blockCard
      (input₁ hy S other ψ).distinguishedBlock.1 := by
  have h1 := W3Nd3StarExhaustionProof.index_symm _ (wall₀ hy S other ψ) S.input S.profile.largest
  have h2 := W3Nd2StarExhaustionProof.blockCard_distinguished _ (wall₀ hy S other ψ) S.input
  change other.limit.sourceEdgeIndex (((W3Nd2StarExhaustionProof.distinguishedIncident _
    (wall₀ hy S other ψ) S.input).symm S.profile.largest).1) = _
  rw [h1, h2]
  exact S.largest_index

end Pullback

/-! ## 5.  Pendant sheets on a branch, for a partly surviving direction

`W3Nd2StarExhaustionProof.pendant_at_wall` asks the whole distinguished block to dangle on
the branch.  At a `w3Four` wall only the sheets of `A₀` outside the survivor's class
dangle; the same proof gives the pendant hypothesis for exactly those. -/

section PendantPart

open TargetBranchRegion DanglingSideStructure
open W3Nd2StarExhaustionProof (Pendant farEnd farEnd_ne exists_branch_cut mem_side_of_moved)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The sheets of the block of `b` whose occurrence above `e` dangles. -/
def DangSet (w : Regrowth core y degree) (e : (w.frame.limitTarget w.column).edges)
    (b : Fin degree) (s : Fin degree) : Prop :=
  (w.limit.vertexPartition (mergeVertex w)).Rel b s ∧ IsDangling w.limit (w.limit.sourceEdge e s)

/-- **The pendant hypothesis for the dangling sheets of a block over a branch.** -/
theorem pendant_at_wall' (w : Regrowth core y degree) (hy : Nondegenerate y)
    (hNoGlue : DanglingEdgeNoGlue w.limit)
    {e : (w.frame.limitTarget w.column).edges}
    (hInc : (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).1 =
        mergeVertex w ∨
      (e : (w.frame.limitTarget w.column).V × (w.frame.limitTarget w.column).V).2 =
        mergeVertex w) (b : Fin degree)
    (hPos : 0 < nonDanglingValency w.limit (w.limit.sourceEndpoint (mergeVertex w) b)) :
    Pendant w.limit (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc)
      (DangSet w e b) := by
  have hVD : ∀ v, vertexMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) v = true →
      ∀ s, DangSet w e b s →
      nonDanglingValency w.limit (w.limit.sourceEndpoint v s) = 0 := by
    intro v hv s hs
    obtain ⟨cut⟩ := exists_branch_cut w.limit hInc hs.1 hPos hs.2
    exact nonDanglingValency_eq_zero_of_mem_side w.limit cut
      (mem_side_of_moved w.limit (farEnd_ne hInc) s cut rfl hv)
  have hED : ∀ f, edgeMoved (mergeVertex w) (farEnd (mergeVertex w) e) (farEnd_ne hInc) f = true →
      ∀ s, DangSet w e b s →
      IsDangling w.limit (w.limit.sourceEdge f s) := by
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

end PendantPart

/-! ## 6.  Which occurrences of the distinguished block dangle -/

section Dangling

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}
  {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- **Off the grow survivor's class, the grow direction's occurrences of `A₀` dangle**
(the literal `nd = 3` statement). -/
theorem grow_isDangling (grown : W3FourSourceCandidates.GrowProfile input) (s : Fin degree)
    (hs : (data.vertexPartition wall).Rel input.distinguishedBlock.1 s)
    (hNe : ¬ (data.edgePartition grown.growTarget).Rel grown.growAnchor s) :
    IsDangling data (data.sourceEdge grown.growTarget s) := by
  have hMem : grown.growTarget ∈ GluingDatum.incidentEdges wall := grown.growTarget_mem
  have hIncident := W3FourSourceCandidates.sourceEdge_incident (data := data)
    input.distinguishedBlock grown.growTarget hMem s hs
  by_contra hSurvives
  have hIn : (⟨data.sourceEdge grown.growTarget s, hIncident⟩ :
      IncidentSourceEdge data (WallBlock.sourceVertex data wall input.distinguishedBlock)) ∈
      survivors data input.distinguishedBlock :=
    (mem_survivors data input.distinguishedBlock _).mpr hSurvives
  have hEq := W3FourSourceCandidates.grow_unique grown _ hIn rfl
  have hValue := congrArg (fun edge : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦ edge.1.1.2) hEq
  apply hNe
  change (data.edgePartition grown.grow.1.1.1).repr grown.grow.1.1.2 =
    (data.edgePartition grown.grow.1.1.1).repr s
  rw [grown.grow.1.2]
  exact hValue.symm

/-- **The grow survivor itself does not dangle.** -/
theorem grow_not_isDangling (grown : W3FourSourceCandidates.GrowProfile input) :
    ¬ IsDangling data (data.sourceEdge grown.growTarget grown.growAnchor) := by
  classical
  have h := (mem_survivors data input.distinguishedBlock grown.grow).mp
    (by rw [grown.surviving]; exact Finset.mem_insert_self _ _)
  rwa [show data.sourceEdge grown.growTarget grown.growAnchor = grown.grow.1 from
    GluingDatum.sourceEdge_self data grown.grow.1]

end Dangling

/-! ## 7.  A received member makes its position nonsingular -/

section Nonsingular

open W3FourStarCensusProof

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} (hy : Nondegenerate y) (S : Setup w)

/-- **A position receiving a member is nonsingular**: the member hands it a
full-dimensional presentation, through its normal form and the lifted transport. -/
theorem nonsingular_of_transport (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w)
    (placement : (other.frame.limitTarget other.column).edges → Bool)
    (hPlacement : W3Nd2StarCensusProof.PlacementSpec other placement) (i : Fin 4)
    (t : S.PositionTransport hy other ψ placement hPlacement i) : S.Nonsingular i := by
  have fd : FullDimensionalSourcePresentation (S.cd i).rowData.candidate.datum (Fin p) :=
    GeometricMultiplicity.transportFullDim
      ((W3Nd2StarCensusProof.memberNorm other placement hPlacement).trans
        (ResolutionExpansionFree.liftFree _ (mergeVertex other) (mergeVertex w) placement _ _ _ _
          (GlobalAssembly.blockwiseCompatible _ _ _ _ _ (S.cd i).rowData.candidate.exterior) t))
      other.frame.fullDim
  have hFd : absMult fd.labelling.presentation ≠ 0 :=
    (W4StarParity.absMult_ne_zero_iff _).mpr fd.det_ne_zero
  rw [← absMult_labelling_indep (S.engLab hy i) fd.labelling, S.absMult_engLab hy i] at hFd
  unfold Setup.Nonsingular
  intro hDet
  apply hFd
  unfold signedMult
  rw [hDet, mul_zero, abs_zero]

end Nonsingular

/-! ## 8.  The grow receipt (`M⁽³⁾`, `M⁽⁴⁾`): re-choose the limit isomorphism on the grow branch

A member isolating the grow direction `t` displays Figure 28's Position II.a class
`e ∪ {y}` for its **own** transferred sheet `y`, while the position displays the grow
profile's default one `y₀`.  Both lie in `A₀ ∖ e`, whose occurrences above `t` dangle over
the whole `t`-branch (`pendant_at_wall'`), so composing the limit isomorphism with the
pendant transposition exchanging the image of `y` and `y₀` on that branch carries one class
onto the other (the move of `W3Nd2StarExhaustionProof.exists_coherent`). -/

section Grow

open W3FourStarCensusProof W3FourIncomingCensus TargetBranchRegion
open W3Nd2StarExhaustionProof (Pendant farEnd farEnd_ne pendantLimitIso edgeMoved_self branchPerm
  isoOf isoOf_wall rightOf_pullback sel₁_eq)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} (hy : Nondegenerate y) (S : Setup w)
  (other : Regrowth core y degree)

theorem piece_congr_Y {d : ℕ} {W : SheetPartition d} {b : Fin d} {X Y Y' R : SheetPartition d}
    (h : Y = Y') (hp : Piece W b X Y R) : Piece W b X Y' R := h ▸ hp

omit hy in
theorem setup_hPos : 0 < nonDanglingValency w.limit
    (w.limit.sourceEndpoint (mergeVertex w) S.input.distinguishedBlock.1) := by
  change 0 < nonDanglingValency w.limit
    (W4StableSource.WallBlock.sourceVertex w.limit (mergeVertex w) S.input.distinguishedBlock)
  rw [← card_survivors]
  exact Finset.card_pos.mpr ⟨S.profile.first, by rw [S.profile.surviving]; simp⟩

/-- A transposition of two sheets of a set keeps the set and its complement. -/
theorem swap_mem {d : ℕ} (D : Fin d → Prop) {u v : Fin d} (hu : D u) (hv : D v) (x : Fin d)
    (hx : D x) : D (Equiv.swap u v x) := by
  rcases eq_or_ne x u with rfl | hxu
  · rw [Equiv.swap_apply_left]; exact hv
  rcases eq_or_ne x v with rfl | hxv
  · rw [Equiv.swap_apply_right]; exact hu
  rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]; exact hx

theorem swap_fix {d : ℕ} (D : Fin d → Prop) {u v : Fin d} (hu : D u) (hv : D v) (x : Fin d)
    (hx : ¬ D x) : Equiv.swap u v x = x :=
  Equiv.swap_apply_of_ne_of_ne (fun h ↦ hx (h ▸ hu)) (fun h ↦ hx (h ▸ hv))

/-- **The grow receipt.** -/
theorem growReceipt (grown : W3FourSourceCandidates.GrowProfile S.input)
    (ψ₀ : GeometricStar.LimitIso hy other w)
    (G₁ : W3FourSourceCandidates.GrowProfile (input₁ hy S other ψ₀))
    (hT : G₁.growTarget = (iso₀ hy other ψ₀).targetEdge.symm grown.growTarget)
    (hA : (iso₀ hy other ψ₀).edgePerm G₁.growTarget G₁.growAnchor = grown.growAnchor)
    (hIso : (growMember G₁).isolated = divalent other (star := star₁ hy S other ψ₀))
    (hCensus : W3ShiftIncomingMatching.SelectedCensus other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (star₁ hy S other ψ₀) (input₁ hy S other ψ₀) (growMember G₁).selectedLeft
      (growMember G₁).selectedRight (growMember G₁).selectedNew) :
    ∃ ψ : GeometricStar.LimitIso hy other w,
    ∃ pl : (other.frame.limitTarget other.column).edges → Bool,
    ∃ hP : W3Nd2StarCensusProof.PlacementSpec other pl,
      Nonempty (ResolutionExpansionFree.TransportFree
        (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm) (mergeVertex other) (mergeVertex w)
        pl (rightOf grown.growTarget) (res other pl hP)
        (M11StarCensusProof.pasted grown.growCandidate)) := by
  classical
  obtain ⟨hP, hL, hR, hN⟩ := member_pieces other hy (input₁ hy S other ψ₀) (growMember G₁) hIso
    hCensus G₁.growTarget_mem G₁.growPartition_refines (SheetPartition.Refines.refl _)
    G₁.growPartition_refines
  set W := w.limit.vertexPartition (mergeVertex w) with hWdef
  set b := S.input.distinguishedBlock.1 with hbdef
  set t := grown.growTarget with htdef
  set iso := iso₀ hy other ψ₀ with hisodef
  have hW₀ := wall₀ hy S other ψ₀
  have hTm : t ∈ GluingDatum.incidentEdges (mergeVertex w) := grown.growTarget_mem
  have hInc := (mem_incidentEdges_iff _ _).mp hTm
  set ρ₀ := iso.edgePerm (iso.targetEdge.symm t) with hρ₀def
  have hρ₀ := edgePerm_agree_symm iso hW₀ t hTm
  have hEP : iso.edgePerm G₁.growTarget = ρ₀ := by rw [hT]
  have hET : iso.targetEdge G₁.growTarget = t := by rw [hT, Equiv.apply_symm_apply]
  have hb₁ : (input₁ hy S other ψ₀).distinguishedBlock.1 = (blockPre iso (mergeVertex other) b).1 :=
    sel₁_eq w hy S.input other ψ₀
  -- the two transferred sheets, and the dangling set they live in
  set yM := G₁.extraSheet
  set u := ρ₀ yM
  set y₀ := grown.extraSheet
  set D := DangSet w t b
  have hDy₀ : D y₀ := ⟨grown.extraSheet_wall_rel,
    grow_isDangling grown y₀ grown.extraSheet_wall_rel grown.extraSheet_separate⟩
  have hDu : D u := by
    have hWu : W.Rel b u := (sel_iff iso hW₀ b ρ₀ hρ₀ yM).mp (by
      rw [← hb₁]; exact G₁.extraSheet_wall_rel)
    have hNe : ¬ (w.limit.edgePartition t).Rel grown.growAnchor u := by
      intro h
      apply G₁.extraSheet_separate
      rw [edge_rel_iff iso, hET, hA, hEP]
      exact h
    exact ⟨hWu, grow_isDangling grown u hWu hNe⟩
  have hDg : ¬ D grown.growAnchor := fun h ↦ grow_not_isDangling grown h.2
  set π := Equiv.swap u y₀
  have hπ : ∀ x, ¬ D x → π x = x := swap_fix D hDu hDy₀
  have hπD : ∀ x, D x → D (π x) := swap_mem D hDu hDy₀
  have hD : ∀ s t', D s → D t' → W.Rel s t' := fun s t' hs ht ↦ hs.1.symm.trans ht.1
  have hPend := pendant_at_wall' w hy S.input.dangling_no_glue hInc b (setup_hPos S)
  set α := pendantLimitIso (hy := hy) hPend hD π hπ hπD
  set ψ := ψ₀.trans α
  set ι := isoOf w hy other ψ
  have hWι : ι.targetVertex (mergeVertex other) = mergeVertex w := isoOf_wall w hy S.input other ψ
  have hιT : ∀ e, ι.targetEdge.symm e = iso.targetEdge.symm e := fun _ ↦ rfl
  set ρ := ι.edgePerm (ι.targetEdge.symm t) with hρdef
  have hρ : ∀ s, ρ s = π (ρ₀ s) := by
    intro s
    change branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) t) (farEnd_ne hInc)
      (iso.targetEdge (iso.targetEdge.symm t))) π (ρ₀ s) = π (ρ₀ s)
    rw [Equiv.apply_symm_apply, edgeMoved_self hInc]
    rfl
  have hρagree := edgePerm_agree_symm ι hWι t hTm
  -- the member's anchor, moved to the new isomorphism's block
  have hbm : (other.limit.vertexPartition (mergeVertex other)).Rel
      (blockPre ι (mergeVertex other) b).1 (input₁ hy S other ψ₀).distinguishedBlock.1 := by
    rw [sel_iff ι hWι b ρ hρagree, hρ]
    have h0 : W.Rel b (ρ₀ (input₁ hy S other ψ₀).distinguishedBlock.1) :=
      (sel_iff iso hW₀ b ρ₀ hρ₀ _).mp (by rw [← hb₁]; rfl)
    by_cases hx : D (ρ₀ (input₁ hy S other ψ₀).distinguishedBlock.1)
    · exact (hπD _ hx).1
    · rw [hπ _ hx]; exact h0
  have hOff : other.limit.edgePartition G₁.growTarget =
      other.limit.edgePartition (ι.targetEdge.symm t) := by rw [hT]; rfl
  have hL₁ := piece_congr_Y hOff (hL.congr_anchor hbm.symm)
  have hR₁ := hR.congr_anchor hbm.symm
  have hN₁ := piece_congr_Y hOff (hN.congr_anchor hbm.symm)
  -- the position's pieces
  have hL' : Piece W b grown.growPartition (w.limit.edgePartition t)
      (M11StarCensusProof.pasted grown.growCandidate).left :=
    piece_of_blocks grown.growPartition_refines grown.growTarget_refines
      (growMember grown).left_selected (growMember grown).left_background
  have hR' : Piece W b W W (M11StarCensusProof.pasted grown.growCandidate).right :=
    piece_of_blocks (SheetPartition.Refines.refl _) (SheetPartition.Refines.refl _)
      (growMember grown).right_selected (growMember grown).right_background
  have hN' : Piece W b grown.growPartition (w.limit.edgePartition t)
      (M11StarCensusProof.pasted grown.growCandidate).newEdge :=
    piece_of_blocks grown.growPartition_refines grown.growTarget_refines
      (growMember grown).newEdge_selected (growMember grown).newEdge_background
  -- the merged class is carried
  have hPm : ∀ a c, (other.limit.edgePartition G₁.growTarget).Rel a c ↔
      (w.limit.edgePartition t).Rel (ρ a) (ρ c) := by
    rw [hOff]; exact edge_rel_iff_symm ι t
  have hf : (w.limit.edgePartition t).Rel (ρ G₁.growAnchor) grown.growAnchor := by
    rw [hρ, ← hEP, hA, hπ _ hDg]; rfl
  have he : (w.limit.edgePartition t).Rel (ρ yM) y₀ := by
    rw [hρ]
    change (w.limit.edgePartition t).Rel (π u) y₀
    rw [Equiv.swap_apply_left]; rfl
  have hMerge := mergeBlocks_transport _ _ _ _ _ _ G₁.extraSheet_separate
    grown.extraSheet_separate ρ hPm hf he
  have hEdges : ∀ e, e ∈ GluingDatum.incidentEdges (mergeVertex w) ↔
      e = grown.otherTarget ∨ e = t ∨ e = grown.largestTarget := by
    intro e
    rw [grown.incidentEdges_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨ψ, (growMember G₁).candidate.right, hP, ?_⟩
  refine nonempty_transportFree_grow ι hWι b grown.otherTarget t grown.largestTarget hEdges _ _ _
    G₁.growPartition G₁.growPartition grown.growPartition grown.growPartition ?_ hL₁ hR₁ hN₁
    hL' hR' hN' (fun x z _ ↦ hMerge x z) (fun x z _ ↦ hMerge x z)
  intro edge
  rw [rightOf_pullback, hιT, ← hT]
  rfl

end Grow

/-! ## 9.  Positions I and II.b, as relations on the distinguished block -/

section FineChar

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {data : GluingDatum target degree}

/-- **Position I's refinement of `A₀` is "same side of `e₂`".** -/
theorem positionOne_fine_rel_iff (position : W3FourClosure.PositionOne data wall) {a : Fin degree}
    (ha : (data.vertexPartition wall).Rel position.growAnchor a) {x : Fin degree}
    (hx : (data.vertexPartition wall).Rel a x) (z : Fin degree) :
    position.fine.Rel x z ↔ (data.vertexPartition wall).Rel a z ∧
      ((data.edgePartition position.growTarget).Rel position.growAnchor x ↔
        (data.edgePartition position.growTarget).Rel position.growAnchor z) := by
  have hGref := position.toFourStarGeometry.grow_refines
  have hxg : (data.vertexPartition wall).Rel position.growAnchor x := ha.trans hx
  by_cases hgx : (data.edgePartition position.growTarget).Rel position.growAnchor x
  · have hFx : position.fine.Rel position.growAnchor x := position.fine_rel_growAnchor_iff.mpr hgx
    constructor
    · intro hxz
      have h := position.fine_rel_growAnchor_iff.mp (hFx.trans hxz)
      exact ⟨ha.symm.trans (hGref.rel h), iff_of_true hgx h⟩
    · rintro ⟨-, hq⟩
      exact hFx.symm.trans (position.fine_rel_growAnchor_iff.mpr (hq.mp hgx))
  · have hFx : position.fine.Rel position.otherAnchor x :=
      position.fine_rel_otherAnchor_iff.mpr ⟨hxg, hgx⟩
    constructor
    · intro hxz
      have h := position.fine_rel_otherAnchor_iff.mp (hFx.trans hxz)
      exact ⟨ha.symm.trans h.1, iff_of_false hgx h.2⟩
    · rintro ⟨hz, hq⟩
      exact hFx.symm.trans (position.fine_rel_otherAnchor_iff.mpr
        ⟨ha.trans hz, fun h ↦ hgx (hq.mpr h)⟩)

/-- **Position I's two classes tile `A₀`**: off `e₂` means on `e₃`. -/
theorem positionOne_cover (position : W3FourClosure.PositionOne data wall) {u : Fin degree}
    (hu : (data.vertexPartition wall).Rel position.growAnchor u) :
    (data.edgePartition position.growTarget).Rel position.growAnchor u ↔
      ¬ (data.edgePartition position.otherTarget).Rel position.otherAnchor u := by
  constructor
  · intro hg ho
    exact Finset.disjoint_left.mp position.disjoint
      (((data.edgePartition position.growTarget).mem_block_iff _ _).mpr hg)
      (((data.edgePartition position.otherTarget).mem_block_iff _ _).mpr ho)
  · intro ho
    by_contra hg
    apply ho
    have hFine : position.fine.Rel position.otherAnchor u :=
      position.fine_rel_otherAnchor_iff.mpr ⟨hu, hg⟩
    have hSub : (data.edgePartition position.otherTarget).block position.otherAnchor ⊆
        position.fine.block position.otherAnchor := by
      intro v hv
      rw [SheetPartition.mem_block_iff] at hv ⊢
      exact position.other_refines_fine.rel hv
    have hEq : (data.edgePartition position.otherTarget).block position.otherAnchor =
        position.fine.block position.otherAnchor :=
      Finset.eq_of_subset_of_card_le hSub (by
        have h := position.fine_blockCard_otherAnchor
        unfold SheetPartition.blockCard at h
        rw [h])
    rw [← SheetPartition.mem_block_iff, hEq, SheetPartition.mem_block_iff]
    exact hFine

/-- **Position II.b's refinement of `A₀` is "is the outside sheet".** -/
theorem positionTwo_fine_rel_iff (position : W3FourClosure.PositionTwo data wall) {a : Fin degree}
    (ha : (data.vertexPartition wall).Rel position.growAnchor a) {x : Fin degree}
    (hx : (data.vertexPartition wall).Rel a x) (z : Fin degree) :
    position.fine.Rel x z ↔ (data.vertexPartition wall).Rel a z ∧
      (x = position.outside ↔ z = position.outside) := by
  have hao : (data.vertexPartition wall).Rel a position.outside :=
    ha.symm.trans position.outside_wall
  have hRem : ∀ v, position.fine.Rel position.growAnchor v ↔
      v ≠ position.outside ∧ (data.vertexPartition wall).Rel position.outside v := by
    intro v
    have hB := (data.vertexPartition wall).detachSheet_block_remainder position.outside
      position.growAnchor position.outside_ne_growAnchor position.outside_wall.symm
    change position.fine.block position.growAnchor = _ at hB
    rw [← SheetPartition.mem_block_iff, hB, Finset.mem_erase, SheetPartition.mem_block_iff]
  by_cases hxo : x = position.outside
  · subst hxo
    have hS := (data.vertexPartition wall).detachSheet_rel_single_iff position.outside
      position.growAnchor z position.outside_ne_growAnchor position.outside_wall.symm
    change position.fine.Rel position.outside z ↔ _ at hS
    rw [hS]
    constructor
    · rintro rfl; exact ⟨hao, Iff.rfl⟩
    · rintro ⟨-, h⟩; exact (h.mp rfl).symm
  · have hFx : position.fine.Rel position.growAnchor x := (hRem x).mpr ⟨hxo, hao.symm.trans hx⟩
    constructor
    · intro hxz
      obtain ⟨hz, hzw⟩ := (hRem z).mp (hFx.trans hxz)
      exact ⟨hao.trans hzw, iff_of_false hxo hz⟩
    · rintro ⟨hz, hq⟩
      exact hFx.symm.trans ((hRem z).mpr ⟨fun h ↦ hxo (hq.mpr h), hao.symm.trans hz⟩)

end FineChar

/-! ## 10.  The reversed receipt, from a characterization of the refinement -/

section Reversed

open ResolutionExpansionFree
open ResolutionM11 (LocalResolution)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} (other : Regrowth core y degree)

/-- **The reversed receipt**: a member of Position-I/II.b shape transports onto a position
of the same shape, as soon as the two refinements are "same value of `Q`" and the
permutations of `L` and `T` read `Q` alike. -/
theorem reversedReceipt {B : GluingDatum (w.frame.limitTarget w.column) degree}
    (ι : GeometricDatumIso other.limit B)
    (hWι : ι.targetVertex (mergeVertex other) = mergeVertex w)
    (b : Fin degree) (L G T : (w.frame.limitTarget w.column).edges)
    (hEdges : ∀ e, e ∈ GluingDatum.incidentEdges (mergeVertex w) ↔ e = L ∨ e = G ∨ e = T)
    (bm : Fin degree)
    (hbm : (other.limit.vertexPartition (mergeVertex other)).Rel
      (blockPre ι (mergeVertex other) b).1 bm)
    (pl : (other.frame.limitTarget other.column).edges → Bool)
    (hP : W3Nd2StarCensusProof.PlacementSpec other pl) (res' : LocalResolution degree)
    (F₁ F₂ : SheetPartition degree)
    (hF₁ : F₁.Refines (other.limit.vertexPartition (mergeVertex other)))
    (hF₂ : F₂.Refines (B.vertexPartition (mergeVertex w)))
    (Q₁ Q₂ : Fin degree → Prop)
    (hChar₁ : ∀ x, (other.limit.vertexPartition (mergeVertex other)).Rel bm x → ∀ z,
      F₁.Rel x z ↔ (other.limit.vertexPartition (mergeVertex other)).Rel bm z ∧ (Q₁ x ↔ Q₁ z))
    (hChar₂ : ∀ x, (B.vertexPartition (mergeVertex w)).Rel b x → ∀ z,
      F₂.Rel x z ↔ (B.vertexPartition (mergeVertex w)).Rel b z ∧ (Q₂ x ↔ Q₂ z))
    (hQ : ∀ x, (other.limit.vertexPartition (mergeVertex other)).Rel bm x →
      (Q₁ x ↔ Q₂ (ι.edgePerm (ι.targetEdge.symm L) x)))
    (hQT : ∀ x, (other.limit.vertexPartition (mergeVertex other)).Rel bm x →
      (Q₂ (ι.edgePerm (ι.targetEdge.symm T) x) ↔ Q₂ (ι.edgePerm (ι.targetEdge.symm L) x)))
    (hSide : ∀ edge, rightOf G (ι.targetEdge edge) = pl edge)
    (hL : Piece (other.limit.vertexPartition (mergeVertex other)) bm
      (other.limit.vertexPartition (mergeVertex other))
      (other.limit.edgePartition (ι.targetEdge.symm G)) (res other pl hP).left)
    (hR : Piece (other.limit.vertexPartition (mergeVertex other)) bm F₁
      (other.limit.vertexPartition (mergeVertex other)) (res other pl hP).right)
    (hN : Piece (other.limit.vertexPartition (mergeVertex other)) bm F₁
      (other.limit.edgePartition (ι.targetEdge.symm G)) (res other pl hP).newEdge)
    (hL' : Piece (B.vertexPartition (mergeVertex w)) b (B.vertexPartition (mergeVertex w))
      (B.edgePartition G) res'.left)
    (hR' : Piece (B.vertexPartition (mergeVertex w)) b F₂ (B.vertexPartition (mergeVertex w))
      res'.right)
    (hN' : Piece (B.vertexPartition (mergeVertex w)) b F₂ (B.edgePartition G) res'.newEdge) :
    Nonempty (TransportFree ι (mergeVertex other) (mergeVertex w) pl (rightOf G)
      (res other pl hP) res') := by
  set W := other.limit.vertexPartition (mergeVertex other)
  set W' := B.vertexPartition (mergeVertex w)
  set σ := ι.edgePerm (ι.targetEdge.symm L)
  set τ := ι.edgePerm (ι.targetEdge.symm T)
  have hσ := edgePerm_agree_symm ι hWι L (mem_L L G T hEdges)
  have hτ := edgePerm_agree_symm ι hWι T (mem_T L G T hEdges)
  have hBlk : ∀ (π : Equiv.Perm (Fin degree)),
      (∀ s, W.Rel ((ι.vertexPerm (mergeVertex other)).symm (π s)) s) →
      ∀ x, W.Rel bm x ↔ W'.Rel b (π x) := by
    intro π hπ x
    rw [← sel_iff ι hWι b π hπ x]
    exact ⟨fun h ↦ hbm.trans h, fun h ↦ hbm.symm.trans h⟩
  have hWσ := M11StarExhaustionProof.wall_rel_iff_of_agree ι hWι σ hσ
  have hF : ∀ x z, W.Rel (blockPre ι (mergeVertex other) b).1 x →
      (F₁.Rel x z ↔ F₂.Rel (σ x) (σ z)) := by
    intro x z hx
    have hx' : W.Rel bm x := hbm.symm.trans hx
    rw [hChar₁ x hx' z, hChar₂ (σ x) ((hBlk σ hσ x).mp hx') (σ z), hQ x hx']
    constructor
    · rintro ⟨hz, hq⟩
      exact ⟨(hBlk σ hσ z).mp hz, hq.trans (hQ z hz)⟩
    · rintro ⟨hz, hq⟩
      have hz' := (hBlk σ hσ z).mpr hz
      exact ⟨hz', hq.trans (hQ z hz').symm⟩
  have hCoh : ∀ s, W.Rel (blockPre ι (mergeVertex other) b).1 s → F₂.Rel (τ s) (σ s) := by
    intro s hs
    have hs' : W.Rel bm s := hbm.symm.trans hs
    have h := (hChar₂ (σ s) ((hBlk σ hσ s).mp hs') (τ s)).mpr
      ⟨(hBlk τ hτ s).mp hs', (hQT s hs').symm⟩
    exact h.symm
  exact nonempty_transportFree_reversed ι hWι b L G T hEdges pl _ _ F₁ F₂ hF₁ hF₂ hSide
    (hL.congr_anchor hbm.symm) (hR.congr_anchor hbm.symm) (hN.congr_anchor hbm.symm)
    hL' hR' hN' hF hCoh

end Reversed

/-! ## 11.  Position I receives the disjoint-type `t₄` members -/

section PositionZero

open W3FourStarCensusProof W3FourIncomingCensus TargetBranchRegion
open W3Nd2StarExhaustionProof (isoOf isoOf_wall rightOf_pullback sel₁_eq)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} (hy : Nondegenerate y) (S : Setup w)
  (other : Regrowth core y degree)

/-- The pulled-back four-star geometry of a member. -/
noncomputable abbrev G₁ (ψ₀ : GeometricStar.LimitIso hy other w) :
    W3FourSourceCandidates.GrowProfile (input₁ hy S other ψ₀) :=
  W3FourSourceCandidates.growProfileFirst (profile₁ hy S other ψ₀) (directions₁ hy S other ψ₀) (largest_index₁ hy S other ψ₀)

/-- The branch swap as a datum isomorphism, on sheets. -/
theorem swap_edgePerm_fixed (rel : w.limit.SheetRelabeling) (root : (w.frame.limitTarget w.column).V)
    (hRoot : root ≠ mergeVertex w) (perm : Equiv.Perm (Fin degree))
    (hFix : ∀ s, (w.limit.vertexPartition (mergeVertex w)).Rel (perm s) s)
    (hRel : rel = W3FourDisjointness.branchSwapOfPerm w.limit (mergeVertex w) root hRoot perm hFix)
    (e : (w.frame.limitTarget w.column).edges)
    (he : TargetBranchRegion.edgeMoved (mergeVertex w) root hRoot e = false) (s : Fin degree) :
    (GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling rel)).edgePerm e s = s := by
  subst hRel
  exact W3FourSurvival.branchSwap_edgePermutation_of_fixed root hRoot perm hFix e he s

theorem swap_edgePerm_moved (rel : w.limit.SheetRelabeling) (root : (w.frame.limitTarget w.column).V)
    (hRoot : root ≠ mergeVertex w) (perm : Equiv.Perm (Fin degree))
    (hFix : ∀ s, (w.limit.vertexPartition (mergeVertex w)).Rel (perm s) s)
    (hRel : rel = W3FourDisjointness.branchSwapOfPerm w.limit (mergeVertex w) root hRoot perm hFix)
    (e : (w.frame.limitTarget w.column).edges)
    (he : TargetBranchRegion.edgeMoved (mergeVertex w) root hRoot e = true) (s : Fin degree) :
    (GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling rel)).edgePerm e s = perm s := by
  subst hRel
  exact W3FourSurvival.branchSwap_edgePermutation_of_moved root hRoot perm hFix e he s

/-- **Position I receives every `t₄` member whose pulled-back `e₂`, `e₃` are disjoint**,
along its limit isomorphism followed by `M⁽¹⁾`'s branch swap, with no coherence condition:
both refinements are "same side of `e₂`", and `e₃` is the other side on both. -/
theorem receiptZero (ψ₀ : GeometricStar.LimitIso hy other w)
    (hD : Disjoint ((other.limit.edgePartition (G₁ hy S other ψ₀).growTarget).block
        (G₁ hy S other ψ₀).growAnchor)
      ((other.limit.edgePartition (G₁ hy S other ψ₀).otherTarget).block
        (G₁ hy S other ψ₀).otherAnchor))
    (hIso : (positionOneMember (⟨W3FourClosure.ofGrowProfile (G₁ hy S other ψ₀), hD⟩ : W3FourClosure.PositionOne other.limit (mergeVertex other)) (W3FourSurvival.SelectedSurvival.ofGrowProfile (G₁ hy S other ψ₀))
        (input₁ hy S other ψ₀).distinguishedBlock.1
        (G₁ hy S other ψ₀).growAnchor_wall_rel).isolated =
      divalent other (star := star₁ hy S other ψ₀))
    (hCensus : W3ShiftIncomingMatching.SelectedCensus other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (star₁ hy S other ψ₀) (input₁ hy S other ψ₀)
      (other.limit.vertexPartition (mergeVertex other))
      (W3FourClosure.PositionOne.fine (⟨W3FourClosure.ofGrowProfile (G₁ hy S other ψ₀), hD⟩ : W3FourClosure.PositionOne other.limit (mergeVertex other)))
      (W3FourClosure.PositionOne.fine (⟨W3FourClosure.ofGrowProfile (G₁ hy S other ψ₀), hD⟩ : W3FourClosure.PositionOne other.limit (mergeVertex other)))) :
    ∃ pl : (other.frame.limitTarget other.column).edges → Bool,
    ∃ hP : W3Nd2StarCensusProof.PlacementSpec other pl,
      Nonempty (S.PositionTransport hy other ψ₀ pl hP 0) := by
  classical
  set pos₁ : W3FourClosure.PositionOne other.limit (mergeVertex other) :=
    (⟨W3FourClosure.ofGrowProfile (G₁ hy S other ψ₀), hD⟩ : W3FourClosure.PositionOne other.limit (mergeVertex other))
  set b₁ := (input₁ hy S other ψ₀).distinguishedBlock.1
  set m := positionOneMember pos₁ (W3FourSurvival.SelectedSurvival.ofGrowProfile (G₁ hy S other ψ₀))
    b₁ (G₁ hy S other ψ₀).growAnchor_wall_rel
  obtain ⟨hP, hL, hR, hN⟩ := member_pieces other hy (input₁ hy S other ψ₀) m hIso hCensus
    pos₁.toFourStarGeometry.largestTarget_mem (SheetPartition.Refines.refl _) pos₁.fine_refines
    pos₁.fine_refines
  set W := w.limit.vertexPartition (mergeVertex w)
  set Wm := other.limit.vertexPartition (mergeVertex other)
  set b := S.input.distinguishedBlock.1
  set iso := iso₀ hy other ψ₀
  have hW₀ := wall₀ hy S other ψ₀
  set X := GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling S.relOne)
  set ι : GeometricDatumIso other.limit S.relOne.apply := ψ₀.datum.trans X
  have hWι : ι.targetVertex (mergeVertex other) = mergeVertex w := hW₀
  set L := S.positionOne.growTarget
  set G := S.positionOne.largestTarget
  set T := S.positionOne.otherTarget
  have hLeq : L = S.profile.first.1.1.1 := S.growTargetOne
  have hGeq : G = S.profile.largest.1.1.1 := S.largestOne
  have hTeq : T = S.profile.second.1.1.1 := S.otherTargetOne
  have hLm : pos₁.growTarget = ι.targetEdge.symm L := by rw [hLeq]; exact first₁ hy S other ψ₀
  have hGm : pos₁.largestTarget = ι.targetEdge.symm G := by rw [hGeq]; exact largest₁ hy S other ψ₀
  have hTm : pos₁.otherTarget = ι.targetEdge.symm T := by rw [hTeq]; exact second₁ hy S other ψ₀
  have hLfix : TargetBranchRegion.edgeMoved (mergeVertex w) S.root S.hRoot L = false := by
    rw [hLeq]; exact S.hGrowFixed
  have hTmov : TargetBranchRegion.edgeMoved (mergeVertex w) S.root S.hRoot T = true := by
    rw [hTeq]; exact S.hOtherMoved
  -- the three occurrence permutations of `ι`
  set σ := ι.edgePerm (ι.targetEdge.symm L)
  set τ := ι.edgePerm (ι.targetEdge.symm T)
  have hσ : ∀ s, σ s = iso.edgePerm (iso.targetEdge.symm L) s := fun s ↦
    swap_edgePerm_fixed S.relOne S.root S.hRoot S.permOne S.fixOne rfl _
      (by change edgeMoved (mergeVertex w) S.root S.hRoot (ι.targetEdge (ι.targetEdge.symm L)) = false
          rw [Equiv.apply_symm_apply]; exact hLfix) _
  have hτ : ∀ s, τ s = S.permOne (iso.edgePerm (iso.targetEdge.symm T) s) := fun s ↦
    swap_edgePerm_moved S.relOne S.root S.hRoot S.permOne S.fixOne rfl _
      (by change edgeMoved (mergeVertex w) S.root S.hRoot (ι.targetEdge (ι.targetEdge.symm T)) = true
          rw [Equiv.apply_symm_apply]; exact hTmov) _
  have hgm : σ pos₁.growAnchor = S.positionOne.growAnchor := by
    rw [hσ, S.anchorOne, show iso.targetEdge.symm L = pos₁.growTarget from hLm.symm]
    exact firstSheet₁ hy S other ψ₀
  have hom : τ pos₁.otherAnchor = S.positionOne.otherAnchor := by
    rw [hτ, S.otherAnchorOne, show iso.targetEdge.symm T = pos₁.otherTarget from hTm.symm]
    exact congrArg S.permOne (secondSheet₁ hy S other ψ₀)
  have hLmem := S.positionOne.toFourStarGeometry.growTarget_mem
  have hGmem := S.positionOne.toFourStarGeometry.largestTarget_mem
  have hTmem := S.positionOne.toFourStarGeometry.otherTarget_mem
  have hEdges : ∀ e, e ∈ GluingDatum.incidentEdges (mergeVertex w) ↔ e = L ∨ e = G ∨ e = T := by
    intro e
    rw [S.positionOne.toFourStarGeometry.incidentEdges_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hσag := edgePerm_agree_symm ι hWι L hLmem
  have hτag := edgePerm_agree_symm ι hWι T hTmem
  set WB := S.relOne.apply.vertexPartition (mergeVertex w)
  have hWB : WB = W := S.wallOne
  have hb₁ : b₁ = (blockPre iso (mergeVertex other) b).1 := sel₁_eq w hy S.input other ψ₀
  have hbm : Wm.Rel (blockPre ι (mergeVertex other) b).1 b₁ := by
    rw [sel_iff ι hWι b σ hσag, hσ]
    change WB.Rel b _
    rw [hWB]
    exact (sel_iff iso hW₀ b _ (edgePerm_agree_symm iso hW₀ L hLmem) b₁).mp (by rw [hb₁]; rfl)
  have hgaB : WB.Rel S.positionOne.growAnchor b := by
    rw [hWB, S.anchorOne]; exact S.grownFirst.growAnchor_wall_rel.symm
  set Q₁ : Fin degree → Prop := fun x ↦
    (other.limit.edgePartition pos₁.growTarget).Rel pos₁.growAnchor x
  set Q₂ : Fin degree → Prop := fun v ↦
    (S.relOne.apply.edgePartition L).Rel S.positionOne.growAnchor v
  have hChar₁ : ∀ x, Wm.Rel b₁ x → ∀ z, pos₁.fine.Rel x z ↔ Wm.Rel b₁ z ∧ (Q₁ x ↔ Q₁ z) :=
    fun x hx z ↦ positionOne_fine_rel_iff pos₁ (G₁ hy S other ψ₀).growAnchor_wall_rel.symm hx z
  have hChar₂ : ∀ x, WB.Rel b x → ∀ z, S.positionOne.fine.Rel x z ↔ WB.Rel b z ∧ (Q₂ x ↔ Q₂ z) :=
    fun x hx z ↦ positionOne_fine_rel_iff S.positionOne hgaB hx z
  have hQ : ∀ x, Wm.Rel b₁ x → (Q₁ x ↔ Q₂ (σ x)) := by
    intro x _
    change (other.limit.edgePartition pos₁.growTarget).Rel pos₁.growAnchor x ↔ _
    rw [hLm, edge_rel_iff_symm ι L, hgm]
  have hBlkτ : ∀ x, Wm.Rel b₁ x → WB.Rel b (τ x) := fun x hx ↦
    (sel_iff ι hWι b τ hτag x).mp (hbm.trans hx)
  have hQT : ∀ x, Wm.Rel b₁ x → (Q₂ (τ x) ↔ Q₂ (σ x)) := by
    intro x hx
    have hxg : Wm.Rel pos₁.growAnchor x := (G₁ hy S other ψ₀).growAnchor_wall_rel.symm.trans hx
    have hτx : WB.Rel S.positionOne.growAnchor (τ x) := hgaB.trans (hBlkτ x hx)
    rw [← hQ x hx]
    change (S.relOne.apply.edgePartition L).Rel S.positionOne.growAnchor (τ x) ↔
      (other.limit.edgePartition pos₁.growTarget).Rel pos₁.growAnchor x
    rw [positionOne_cover S.positionOne hτx, positionOne_cover pos₁ hxg, hTm,
      edge_rel_iff_symm ι T, hom]
  have hSide : ∀ edge, rightOf G (ι.targetEdge edge) = m.candidate.right edge := by
    intro edge
    rw [rightOf_pullback]
    change rightOf (ι.targetEdge.symm G) edge = rightOf pos₁.largestTarget edge
    rw [hGm]
  have hOff : other.limit.edgePartition m.isolated =
      other.limit.edgePartition (ι.targetEdge.symm G) := congrArg _ hGm
  have hRootB : WB.Rel b S.positionOne.growAnchor := hgaB.symm
  set mB := positionOneMember S.positionOne S.survivalOne b hRootB
  have hL' : Piece WB b WB (S.relOne.apply.edgePartition G)
      (M11StarCensusProof.pasted S.positionOne.candidate).left :=
    piece_of_blocks (SheetPartition.Refines.refl _) S.positionOne.toFourStarGeometry.largest_refines
      mB.left_selected mB.left_background
  have hR' : Piece WB b S.positionOne.fine WB
      (M11StarCensusProof.pasted S.positionOne.candidate).right :=
    piece_of_blocks S.positionOne.fine_refines (SheetPartition.Refines.refl _)
      mB.right_selected mB.right_background
  have hN' : Piece WB b S.positionOne.fine (S.relOne.apply.edgePartition G)
      (M11StarCensusProof.pasted S.positionOne.candidate).newEdge :=
    piece_of_blocks S.positionOne.fine_refines S.positionOne.toFourStarGeometry.largest_refines
      mB.newEdge_selected mB.newEdge_background
  exact ⟨m.candidate.right, hP, reversedReceipt other ι hWι b L G T hEdges b₁ hbm _ hP _ pos₁.fine
    S.positionOne.fine pos₁.fine_refines S.positionOne.fine_refines Q₁ Q₂ hChar₁ hChar₂ hQ hQT
    hSide (piece_congr_Y hOff hL) hR (piece_congr_Y hOff hN) hL' hR' hN'⟩

end PositionZero

/-! ## 12.  Position II.b receives the meeting-type `t₄` members, after two pendant moves

A `t₄` member whose pulled-back `e₂`, `e₃` meet displays Position II.b's refinement for its
**own** outside sheet `x`, while `M⁽²⁾` displays it for `x₁ = positionTwo.outside`.  The
receipt needs both the `t₂`- and the `t₃`-permutation to send `x` to `x₁`: the first is
achieved by a pendant transposition on the `t₂`-branch (whose dangling sheets are
`A₀ ∖ e₂`), the second by one on the `t₃`-branch (dangling sheets `A₀ ∖ e₃`), the branch
swap `permTwo` being undone on the target side. -/

section PositionOne

open W3FourStarCensusProof W3FourIncomingCensus TargetBranchRegion
open W3Nd2StarExhaustionProof (Pendant farEnd farEnd_ne pendantLimitIso edgeMoved_self
  edgeMoved_other branchPerm isoOf isoOf_wall rightOf_pullback sel₁_eq)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} (hy : Nondegenerate y) (S : Setup w)
  (other : Regrowth core y degree)

/-- A sheet of the block of `b`, moved by a transposition of two sheets of a subset of that
block, stays in the block. -/
theorem swap_rel {d : ℕ} (W : SheetPartition d) (b : Fin d) (D : Fin d → Prop)
    (hDW : ∀ s, D s → W.Rel b s) {u v : Fin d} (hu : D u) (hv : D v) {x : Fin d}
    (hx : W.Rel b x) : W.Rel b (Equiv.swap u v x) := by
  by_cases h : D x
  · exact hDW _ (swap_mem D hu hv x h)
  · rw [swap_fix D hu hv x h]; exact hx

/-- **Position II.b receives every meeting-type `t₄` member**, along a limit isomorphism
re-chosen by two pendant transpositions. -/
theorem receiptOne (ψ₀ : GeometricStar.LimitIso hy other w) (x : Fin degree)
    (hxWall : (other.limit.vertexPartition (mergeVertex other)).Rel (G₁ hy S other ψ₀).growAnchor x)
    (hxGrow : ¬ (other.limit.edgePartition (G₁ hy S other ψ₀).growTarget).Rel
      (G₁ hy S other ψ₀).growAnchor x)
    (hxOther : ¬ (other.limit.edgePartition (G₁ hy S other ψ₀).otherTarget).Rel
      (G₁ hy S other ψ₀).otherAnchor x)
    (hIso : (positionTwoMember (⟨W3FourClosure.ofGrowProfile (G₁ hy S other ψ₀), x, hxWall,
        hxGrow, hxOther⟩ : W3FourClosure.PositionTwo other.limit (mergeVertex other))
        (W3FourSurvival.SelectedSurvival.ofGrowProfile (G₁ hy S other ψ₀))
        (input₁ hy S other ψ₀).distinguishedBlock.1
        (G₁ hy S other ψ₀).growAnchor_wall_rel).isolated =
      divalent other (star := star₁ hy S other ψ₀))
    (hCensus : W3ShiftIncomingMatching.SelectedCensus other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      (star₁ hy S other ψ₀) (input₁ hy S other ψ₀)
      (other.limit.vertexPartition (mergeVertex other))
      (W3FourClosure.PositionTwo.fine (⟨W3FourClosure.ofGrowProfile (G₁ hy S other ψ₀), x, hxWall,
        hxGrow, hxOther⟩ : W3FourClosure.PositionTwo other.limit (mergeVertex other)))
      (W3FourClosure.PositionTwo.fine (⟨W3FourClosure.ofGrowProfile (G₁ hy S other ψ₀), x, hxWall,
        hxGrow, hxOther⟩ : W3FourClosure.PositionTwo other.limit (mergeVertex other)))) :
    ∃ ψ : GeometricStar.LimitIso hy other w,
    ∃ pl : (other.frame.limitTarget other.column).edges → Bool,
    ∃ hP : W3Nd2StarCensusProof.PlacementSpec other pl,
      Nonempty (S.PositionTransport hy other ψ pl hP 1) := by
  classical
  set pos₂ : W3FourClosure.PositionTwo other.limit (mergeVertex other) :=
    ⟨W3FourClosure.ofGrowProfile (G₁ hy S other ψ₀), x, hxWall, hxGrow, hxOther⟩
  set b₁ := (input₁ hy S other ψ₀).distinguishedBlock.1
  set m := positionTwoMember pos₂ (W3FourSurvival.SelectedSurvival.ofGrowProfile (G₁ hy S other ψ₀))
    b₁ (G₁ hy S other ψ₀).growAnchor_wall_rel
  obtain ⟨hP, hL, hR, hN⟩ := member_pieces other hy (input₁ hy S other ψ₀) m hIso hCensus
    pos₂.toFourStarGeometry.largestTarget_mem (SheetPartition.Refines.refl _) pos₂.fine_refines
    pos₂.fine_refines
  set W := w.limit.vertexPartition (mergeVertex w)
  set Wm := other.limit.vertexPartition (mergeVertex other)
  set b := S.input.distinguishedBlock.1
  set iso := iso₀ hy other ψ₀
  have hW₀ := wall₀ hy S other ψ₀
  have hb₁ : b₁ = (blockPre iso (mergeVertex other) b).1 := sel₁_eq w hy S.input other ψ₀
  set t₂ := S.profile.first.1.1.1
  set t₃ := S.profile.second.1.1.1
  set x₁ := S.positionTwo.outside
  have hGeomGrowT : S.positionTwo.growTarget = t₂ := congrArg W3FourClosure.FourStarGeometry.growTarget S.geomTwo
  have hGeomOtherT : S.positionTwo.otherTarget = t₃ :=
    congrArg W3FourClosure.FourStarGeometry.otherTarget S.geomTwo
  have hGeomOtherA : S.positionTwo.otherAnchor = S.permTwo S.geometry.otherAnchor :=
    congrArg W3FourClosure.FourStarGeometry.otherAnchor S.geomTwo
  have hGeomLargeT : S.positionTwo.largestTarget = S.profile.largest.1.1.1 := S.largestTwo
  have ht₂mem : t₂ ∈ GluingDatum.incidentEdges (mergeVertex w) := S.grownFirst.growTarget_mem
  have ht₃mem : t₃ ∈ GluingDatum.incidentEdges (mergeVertex w) := S.grownSecond.growTarget_mem
  have hInc₂ := (mem_incidentEdges_iff _ _).mp ht₂mem
  have hInc₃ := (mem_incidentEdges_iff _ _).mp ht₃mem
  have h23 : t₂ ≠ t₃ := S.directions
  -- the member's sheet, read on each branch
  set ρ₂ := iso.edgePerm (iso.targetEdge.symm t₂)
  set ρ₃ := iso.edgePerm (iso.targetEdge.symm t₃)
  have hρ₂ag := edgePerm_agree_symm iso hW₀ t₂ ht₂mem
  have hρ₃ag := edgePerm_agree_symm iso hW₀ t₃ ht₃mem
  have hgT : pos₂.growTarget = iso.targetEdge.symm t₂ := first₁ hy S other ψ₀
  have hoT : pos₂.otherTarget = iso.targetEdge.symm t₃ := second₁ hy S other ψ₀
  have hxb : Wm.Rel b₁ x := (G₁ hy S other ψ₀).growAnchor_wall_rel.trans hxWall
  have hBlk₀ : ∀ (π : Equiv.Perm (Fin degree)),
      (∀ s, Wm.Rel ((iso.vertexPerm (mergeVertex other)).symm (π s)) s) →
      ∀ z, Wm.Rel b₁ z → W.Rel b (π z) := fun π hπ z hz ↦
    (sel_iff iso hW₀ b π hπ z).mp (by rw [← hb₁]; exact hz)
  set u₂ := ρ₂ x
  set u₃ := ρ₃ x
  set v₃ := S.permTwo.symm x₁
  set D₂ := DangSet w t₂ b
  set D₃ := DangSet w t₃ b
  have hx₁W : W.Rel b x₁ := by
    have h := S.positionTwo.outside_wall
    rw [S.wallTwo, S.anchorTwo] at h
    exact S.grownFirst.growAnchor_wall_rel.trans h
  have hDu₂ : D₂ u₂ := by
    have hW' := hBlk₀ ρ₂ hρ₂ag x hxb
    refine ⟨hW', grow_isDangling S.grownFirst u₂ hW' ?_⟩
    intro h
    apply hxGrow
    change (other.limit.edgePartition pos₂.growTarget).Rel pos₂.growAnchor x
    rw [hgT, edge_rel_iff_symm iso t₂]
    rw [show iso.edgePerm (iso.targetEdge.symm t₂) pos₂.growAnchor = S.grownFirst.growAnchor from
      (congrArg (fun e ↦ iso.edgePerm e pos₂.growAnchor) hgT).symm.trans (firstSheet₁ hy S other ψ₀)]
    exact h
  have hDx₁ : D₂ x₁ := by
    refine ⟨hx₁W, grow_isDangling S.grownFirst x₁ hx₁W ?_⟩
    have h := S.positionTwo.outside_grow
    rw [W3FourDisjointness.branchSwapOfPerm_edgePartition_of_fixed _ _ _ _ _ _ _
      (by rw [hGeomGrowT]; exact S.hGrowFixed), hGeomGrowT, S.anchorTwo] at h
    exact h
  have hDu₃ : D₃ u₃ := by
    have hW' := hBlk₀ ρ₃ hρ₃ag x hxb
    refine ⟨hW', grow_isDangling S.grownSecond u₃ hW' ?_⟩
    intro h
    apply hxOther
    change (other.limit.edgePartition pos₂.otherTarget).Rel pos₂.otherAnchor x
    rw [hoT, edge_rel_iff_symm iso t₃]
    rw [show iso.edgePerm (iso.targetEdge.symm t₃) pos₂.otherAnchor = S.grownSecond.growAnchor from
      (congrArg (fun e ↦ iso.edgePerm e pos₂.otherAnchor) hoT).symm.trans (secondSheet₁ hy S other ψ₀)]
    exact h
  have hDv₃ : D₃ v₃ := by
    have hWv : W.Rel b v₃ := by
      have h := S.fixTwo v₃
      rw [Equiv.apply_symm_apply] at h
      exact hx₁W.trans h
    refine ⟨hWv, grow_isDangling S.grownSecond v₃ hWv ?_⟩
    have h := S.positionTwo.outside_other
    rw [W3FourDisjointness.branchSwapOfPerm_edgePartition_of_moved _ _ _ _ _ _ _
      (by rw [hGeomOtherT]; exact S.hOtherMoved), hGeomOtherT, hGeomOtherA] at h
    intro h'
    apply h
    rw [show S.positionTwo.outside = S.permTwo v₃ from (Equiv.apply_symm_apply _ _).symm,
      SheetPartition.relabel_rel_iff]
    exact h'
  -- the two pendant moves
  set π₂ := Equiv.swap u₂ x₁
  have hπ₂ := swap_fix D₂ hDu₂ hDx₁
  have hπ₂D := swap_mem D₂ hDu₂ hDx₁
  have hD₂ : ∀ s t, D₂ s → D₂ t → W.Rel s t := fun s t hs ht ↦ hs.1.symm.trans ht.1
  have hPend₂ := pendant_at_wall' w hy S.input.dangling_no_glue hInc₂ b (setup_hPos S)
  set α₂ := pendantLimitIso (hy := hy) hPend₂ hD₂ π₂ hπ₂ hπ₂D
  set π₃ := Equiv.swap u₃ v₃
  have hπ₃ := swap_fix D₃ hDu₃ hDv₃
  have hπ₃D := swap_mem D₃ hDu₃ hDv₃
  have hD₃ : ∀ s t, D₃ s → D₃ t → W.Rel s t := fun s t hs ht ↦ hs.1.symm.trans ht.1
  have hPend₃ := pendant_at_wall' w hy S.input.dangling_no_glue hInc₃ b (setup_hPos S)
  set α₃ := pendantLimitIso (hy := hy) hPend₃ hD₃ π₃ hπ₃ hπ₃D
  set ψ := (ψ₀.trans α₂).trans α₃
  set X := GeometricDatumIso.ofStrict (Transport.DatumIso.ofSheetRelabeling S.relTwo)
  set ι : GeometricDatumIso other.limit S.relTwo.apply := ψ.datum.trans X
  have hWι : ι.targetVertex (mergeVertex other) = mergeVertex w := hW₀
  have hConn := W4StarParity.limitTarget_connected w
  have hGen := W4StarParity.limitTarget_genus w
  have hm23 : edgeMoved (mergeVertex w) (farEnd (mergeVertex w) t₃) (farEnd_ne hInc₃) t₂ = false :=
    edgeMoved_other hConn hGen hInc₃ hInc₂ h23
  have hm32 : edgeMoved (mergeVertex w) (farEnd (mergeVertex w) t₂) (farEnd_ne hInc₂) t₃ = false :=
    edgeMoved_other hConn hGen hInc₂ hInc₃ h23.symm
  set σ := ι.edgePerm (ι.targetEdge.symm t₂)
  set τ := ι.edgePerm (ι.targetEdge.symm t₃)
  have hσ : ∀ s, σ s = π₂ (ρ₂ s) := by
    intro s
    change X.edgePerm (iso.targetEdge (iso.targetEdge.symm t₂))
      (branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) t₃) (farEnd_ne hInc₃)
        (iso.targetEdge (iso.targetEdge.symm t₂))) π₃
      (branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) t₂) (farEnd_ne hInc₂)
        (iso.targetEdge (iso.targetEdge.symm t₂))) π₂ (ρ₂ s))) = _
    rw [Equiv.apply_symm_apply, edgeMoved_self hInc₂, hm23]
    unfold branchPerm
    rw [ite_eq_left rfl, ite_eq_right Bool.false_ne_true]
    exact swap_edgePerm_fixed S.relTwo S.root S.hRoot S.permTwo S.fixTwo rfl t₂ S.hGrowFixed _
  have hτ : ∀ s, τ s = S.permTwo (π₃ (ρ₃ s)) := by
    intro s
    change X.edgePerm (iso.targetEdge (iso.targetEdge.symm t₃))
      (branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) t₃) (farEnd_ne hInc₃)
        (iso.targetEdge (iso.targetEdge.symm t₃))) π₃
      (branchPerm (edgeMoved (mergeVertex w) (farEnd (mergeVertex w) t₂) (farEnd_ne hInc₂)
        (iso.targetEdge (iso.targetEdge.symm t₃))) π₂ (ρ₃ s))) = _
    rw [Equiv.apply_symm_apply, edgeMoved_self hInc₃, hm32]
    unfold branchPerm
    rw [ite_eq_left rfl, ite_eq_right Bool.false_ne_true]
    exact swap_edgePerm_moved S.relTwo S.root S.hRoot S.permTwo S.fixTwo rfl t₃ S.hOtherMoved _
  have hσx : σ x = x₁ := by rw [hσ]; exact Equiv.swap_apply_left _ _
  have hτx : τ x = x₁ := by
    rw [hτ]
    change S.permTwo (π₃ u₃) = x₁
    rw [Equiv.swap_apply_left]
    exact Equiv.apply_symm_apply _ _
  set G := S.positionTwo.largestTarget
  have hGmem : G ∈ GluingDatum.incidentEdges (mergeVertex w) :=
    S.positionTwo.toFourStarGeometry.largestTarget_mem
  have hEdges : ∀ e, e ∈ GluingDatum.incidentEdges (mergeVertex w) ↔ e = t₂ ∨ e = G ∨ e = t₃ := by
    intro e
    rw [S.grownFirst.incidentEdges_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [show S.grownFirst.largestTarget = G from hGeomLargeT.symm]
    tauto
  have hσag := edgePerm_agree_symm ι hWι t₂ ht₂mem
  set WB := S.relTwo.apply.vertexPartition (mergeVertex w)
  have hWB : WB = W := S.wallTwo
  have hbm : Wm.Rel (blockPre ι (mergeVertex other) b).1 b₁ := by
    rw [sel_iff ι hWι b σ hσag, hσ]
    change WB.Rel b _
    rw [hWB]
    exact swap_rel W b D₂ (fun s hs ↦ hs.1) hDu₂ hDx₁ (hBlk₀ ρ₂ hρ₂ag b₁ rfl)
  have hgaB : WB.Rel S.positionTwo.growAnchor b := by
    rw [hWB, S.anchorTwo]; exact S.grownFirst.growAnchor_wall_rel.symm
  have hChar₁ : ∀ z, Wm.Rel b₁ z → ∀ z', pos₂.fine.Rel z z' ↔
      Wm.Rel b₁ z' ∧ ((fun v ↦ v = x) z ↔ (fun v ↦ v = x) z') :=
    fun z hz z' ↦ positionTwo_fine_rel_iff pos₂ (G₁ hy S other ψ₀).growAnchor_wall_rel.symm hz z'
  have hChar₂ : ∀ z, WB.Rel b z → ∀ z', S.positionTwo.fine.Rel z z' ↔
      WB.Rel b z' ∧ ((fun v ↦ v = x₁) z ↔ (fun v ↦ v = x₁) z') :=
    fun z hz z' ↦ positionTwo_fine_rel_iff S.positionTwo hgaB hz z'
  have hQ : ∀ z, Wm.Rel b₁ z → ((fun v ↦ v = x) z ↔ (fun v ↦ v = x₁) (σ z)) := by
    intro z _
    exact ⟨fun h ↦ h ▸ hσx, fun h ↦ σ.injective (h.trans hσx.symm)⟩
  have hQT : ∀ z, Wm.Rel b₁ z → ((fun v ↦ v = x₁) (τ z) ↔ (fun v ↦ v = x₁) (σ z)) := by
    intro z _
    change τ z = x₁ ↔ σ z = x₁
    constructor
    · intro h; rw [τ.injective (h.trans hτx.symm)]; exact hσx
    · intro h; rw [σ.injective (h.trans hσx.symm)]; exact hτx
  have hGm : pos₂.largestTarget = ι.targetEdge.symm G := by
    rw [hGeomLargeT]; exact largest₁ hy S other ψ₀
  have hSide : ∀ edge, rightOf G (ι.targetEdge edge) = m.candidate.right edge := by
    intro edge
    rw [rightOf_pullback]
    change rightOf (ι.targetEdge.symm G) edge = rightOf pos₂.largestTarget edge
    rw [hGm]
  have hOff : other.limit.edgePartition m.isolated =
      other.limit.edgePartition (ι.targetEdge.symm G) := congrArg _ hGm
  set mB := positionTwoMember S.positionTwo S.survivalTwo b hgaB.symm
  have hL' : Piece WB b WB (S.relTwo.apply.edgePartition G)
      (M11StarCensusProof.pasted S.positionTwo.candidate).left :=
    piece_of_blocks (SheetPartition.Refines.refl _) S.positionTwo.toFourStarGeometry.largest_refines
      mB.left_selected mB.left_background
  have hR' : Piece WB b S.positionTwo.fine WB
      (M11StarCensusProof.pasted S.positionTwo.candidate).right :=
    piece_of_blocks S.positionTwo.fine_refines (SheetPartition.Refines.refl _)
      mB.right_selected mB.right_background
  have hN' : Piece WB b S.positionTwo.fine (S.relTwo.apply.edgePartition G)
      (M11StarCensusProof.pasted S.positionTwo.candidate).newEdge :=
    piece_of_blocks S.positionTwo.fine_refines S.positionTwo.toFourStarGeometry.largest_refines
      mB.newEdge_selected mB.newEdge_background
  exact ⟨ψ, m.candidate.right, hP, reversedReceipt other ι hWι b t₂ G t₃ hEdges b₁ hbm _ hP _
    pos₂.fine S.positionTwo.fine pos₂.fine_refines S.positionTwo.fine_refines _ _ hChar₁ hChar₂
    hQ hQT hSide (piece_congr_Y hOff hL) hR (piece_congr_Y hOff hN) hL' hR' hN'⟩

end PositionOne

/-! ## 13.  Every star member presents a receipt; the W3Four star exhaustion -/

section Exhaustion

open W3FourStarCensusProof

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree} (hy : Nondegenerate y) (S : Setup w)

/-- **Every star member presents a receipt at a nonsingular position.**  Part I's census at
the member's own contraction (`W3FourSelectedCensus.exists_selectedCensus`, read through
the pulled-back setup) puts it in Position I, Position II.b, or Position II.a on `t₂` or
`t₃`; the four receipts are `receiptZero`, `receiptOne`, `growReceipt` (twice), and the
receiving position is nonsingular because the member hands it a full-dimensional
presentation. -/
theorem exists_receipt (member : GeometricStar.StarMember hy w) :
    ∃ ψ : GeometricStar.LimitIso hy member.member w,
    ∃ placement : (member.member.frame.limitTarget member.member.column).edges → Bool,
    ∃ hPlacement : W3Nd2StarCensusProof.PlacementSpec member.member placement,
    ∃ i : Fin 4, ∃ _ : S.Nonsingular i,
      Nonempty (S.PositionTransport hy member.member ψ placement hPlacement i) := by
  obtain ⟨ψ₀⟩ := member.specializes
  set other := member.member
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
    (InheritedLimitRows.forest other hy)
  rcases W3FourSelectedCensus.exists_selectedCensus other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column)) (other.frame.numEdges_edgeOf other.column)
      other.frame.fullDim (InheritedLimitRows.forest other hy) hCompat (star₁ hy S other ψ₀)
      (input₁ hy S other ψ₀) (profile₁ hy S other ψ₀) (directions₁ hy S other ψ₀)
      (largest_index₁ hy S other ψ₀) with
    ⟨hDiv, ⟨hD, hC⟩ | ⟨x, hxW, hxG, hxO, hC⟩⟩ | ⟨hDiv, yM, hSep, hyW, hC⟩ |
      ⟨hDiv, yM, hSep, hyW, hC⟩
  · obtain ⟨pl, hP, ⟨t⟩⟩ := receiptZero hy S other ψ₀ hD hDiv.symm hC
    exact ⟨ψ₀, pl, hP, 0, nonsingular_of_transport hy S other ψ₀ pl hP 0 t, ⟨t⟩⟩
  · obtain ⟨ψ, pl, hP, ⟨t⟩⟩ := receiptOne hy S other ψ₀ x hxW hxG hxO hDiv.symm hC
    exact ⟨ψ, pl, hP, 1, nonsingular_of_transport hy S other ψ pl hP 1 t, ⟨t⟩⟩
  · obtain ⟨ψ, pl, hP, ⟨t⟩⟩ := growReceipt hy S other S.grownFirst ψ₀
      ((W3FourSourceCandidates.growProfileFirst (profile₁ hy S other ψ₀) (directions₁ hy S other ψ₀)
        (largest_index₁ hy S other ψ₀)).withExtra yM hyW hSep)
      (first₁ hy S other ψ₀) (firstSheet₁ hy S other ψ₀) hDiv.symm hC
    exact ⟨ψ, pl, hP, 2, nonsingular_of_transport hy S other ψ pl hP 2 t, ⟨t⟩⟩
  · obtain ⟨ψ, pl, hP, ⟨t⟩⟩ := growReceipt hy S other S.grownSecond ψ₀
      ((W3FourSourceCandidates.growProfileSecond (profile₁ hy S other ψ₀) (directions₁ hy S other ψ₀)
        (largest_index₁ hy S other ψ₀)).withExtra yM hyW hSep)
      (second₁ hy S other ψ₀) (secondSheet₁ hy S other ψ₀) hDiv.symm hC
    exact ⟨ψ, pl, hP, 3, nonsingular_of_transport hy S other ψ pl hP 3 t, ⟨t⟩⟩

/-- **Stage 2 at one `w3Four` wall.** -/
theorem exhausts : S.Exhausts hy :=
  S.exhausts_of_transports hy (exists_receipt hy S)

end Exhaustion

section Family

variable (degree n p : ℕ)

/-- **The W3Four star exhaustion, at every core, degree and request.** -/
theorem w3FourStarExhaustion : W3FourStarCensusProof.W3FourStarExhaustion degree n p :=
  fun _ _ hy _ _ _ S ↦ exhausts hy S

/-- **The W3Four star census**, unconditionally. -/
theorem w3FourStarCensus : W3FourStarCensusProof.W3FourStarCensus degree n p :=
  W3FourStarCensusProof.w3FourStarCensus_of_exhaustion (w3FourStarExhaustion degree n p)

/-- **Every `w3Four` star has exactly as many classes as Equation (2) has nonsingular
positions.** -/
theorem w3FourStarCard : W3FourStarCensusProof.W3FourStarCard degree n p :=
  W3FourStarCensusProof.w3FourStarExhaustion_iff_card.mp (w3FourStarExhaustion degree n p)

/-- **The `w3Four` clause of `FamilyStarParity` at genus six and degree four, with no
hypothesis.** -/
theorem familyStarParity_w3Four :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w3Four :=
  W3FourStarCensusProof.familyStarParity_w3Four_of_exhaustion (w3FourStarExhaustion _ _ _)

end Family

end DraismaVargas.Count.W3FourStarExhaustionProof
