import GenusSixExistence.BrillNoetherRank.Tripod.GluingPieceIdent
import GenusSixExistence.BrillNoetherRank.Tripod.GluingLayoutStages

/-!
# Positivity of the gluing: the coordinates are the geometric lengths

The proof of `GluingClasses.exists_gluedIdent_closed` from one statement about the old rows
(`exists_pieceLabels`, from `GluingLayoutStages`). Prose proof:
`Research/genus-six-brill-noether-rank.md`, §5.2 (Positivity and change-minimality) and §6.3
(Admissible requests, and the parity of the claw classes); section numbers in this file refer to
that note.

* **Coordinates from lengths** (`coordsAt_eq_of_realises`): if a vector of target lengths
  realises the request along every stable path of a frame, it is the frame's coordinate vector at
  every labelling (`FibreMember.coords_unique`).
* **The legs and the arms** (`realises_extendLengths`): the old rows only involve the edges
  of `T₃`, and the leg of mark `k` passes twice over its arm, with index one, and otherwise over
  edges of `T₃` in the new sheet. Define the arm by the leg equation,
  `arm k = (ℓ_k - (the new-sheet length of leg k)) / 2`.
* **Long legs** (`armLength_pos`): the new-sheet length of a leg is at most the total
  length of `T₃`, which is at most four times the total length of `G̃`: every edge of `T₃` carries a
  surviving source edge of index at most four (`noDanglingTargetFibres`), and the surviving edges
  of `refine₃` add up, row by row, to the requested lengths of the G-slots. So `arm k > 0` by
  `LongLegs`.

The placement at the actual positions of the marks, the labels of the glued old paths by the
pieces of the marked core, with their ends, and the geometric lengths of the edges of `T₃`,
non-negative, realising the request on the old rows (`exists_pieceLabels`) come from
`GluingLayout` and `GluingLayoutStages`: the stable paths of `ψ` are oriented chains,
and each mark is placed at its actual position on its chain, one at a time. The core
identification with the glued labels is built from the labels in `GluingPieceIdent`.
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

namespace Positivity

/-! ## 1. Coordinates from lengths -/

section Frames

open Classical in
/-- The length of a stable path under a vector of target lengths. -/
def pathSum {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (w : S.edges → ℚ) (Q : StablePath E) :
    ℚ :=
  ∑ x : NonDanglingEdge E, if x.stablePath = Q then w x.1.1.1 / E.sourceEdgeIndex x.1 else 0

/-- **A vector of target lengths realises a request** along a row labelling. -/
def Realises {S : CFGraph} {k P : ℕ} (E : GluingDatum S k) (lab : StablePath E → Fin P)
    (y : Fin P → ℚ) (w : S.edges → ℚ) : Prop :=
  ∀ Q, pathSum E w Q = y (lab Q)

variable {N P degree : ℕ} {C : Core N P}

/-- **The coordinates of a frame are any lengths realising the request**, read through the column
labelling. -/
theorem coordsAt_eq_of_realises (κ : Frame C degree) {y : Fin P → ℚ} {w : κ.target.edges → ℚ}
    (hw : Realises κ.data κ.ident.row y w) (col : Fin P) :
    κ.coordsAt y col = w (κ.fullDim.labelling.targetEdge col) := by
  classical
  have h : (κ.member y).matrix.mulVec (fun c ↦ w (κ.fullDim.labelling.targetEdge c)) =
      fun row ↦ y ((κ.member y).ident.row ((κ.member y).fullDim.labelling.row.symm row)) := by
    funext r
    show (GluingDatum.LengthMatrixPresentation.matrix κ.fullDim.labelling.presentation).mulVec
      _ r = y (κ.ident.row (κ.fullDim.labelling.row.symm r))
    rw [Onto.mulVec_eq_sum, ← hw (κ.fullDim.labelling.row.symm r), pathSum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Equiv.apply_symm_apply]
    by_cases hx : κ.fullDim.labelling.row x.stablePath = r
    · rw [if_pos hx, if_pos ((Equiv.eq_symm_apply _).mpr hx)]
    · rw [if_neg hx, if_neg (fun h ↦ hx ((Equiv.eq_symm_apply _).mp h))]
  exact (congrFun ((κ.member y).coords_unique _ h) col).symm

end Frames

/-! ## 2. The target edges of the glued datum, and the lengths of the arms -/

section Lengths

variable {T : CFGraph} {d : ℕ} (π : Placement T d)

/-- The target edges of the glued datum: the edges of `T₃`, and the three arms. -/
noncomputable def targetEquiv : π.T₃.edges ⊕ Fin 3 ≃ π.T₆.edges :=
  Equiv.ofBijective (Sum.elim π.liftE₃ π.armEdge) (by
    constructor
    · rintro (a | a) (b | b) h
      all_goals simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [π.liftE₃_injective h]
      · exact absurd h (π.liftE₃_ne_armEdge _ _)
      · exact absurd h.symm (π.liftE₃_ne_armEdge _ _)
      · rw [π.armEdge_injective h]
    · intro ε
      rcases π.T₆_edge_cases ε with ⟨e, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨Sum.inl e, rfl⟩
      · exact ⟨Sum.inr k, rfl⟩)

/-- Lengths on `T₃`, extended by lengths of the three arms. -/
def extendLengths (w₃ : π.T₃.edges → ℚ) (arm : Fin 3 → ℚ) (ε : π.T₆.edges) : ℚ :=
  Sum.elim w₃ arm ((targetEquiv π).symm ε)

theorem extendLengths_liftE₃ (w₃ : π.T₃.edges → ℚ) (arm : Fin 3 → ℚ) (e : π.T₃.edges) :
    extendLengths π w₃ arm (π.liftE₃ e) = w₃ e := by
  unfold extendLengths
  rw [show π.liftE₃ e = targetEquiv π (Sum.inl e) from rfl, Equiv.symm_apply_apply]
  rfl

theorem extendLengths_armEdge (w₃ : π.T₃.edges → ℚ) (arm : Fin 3 → ℚ) (k : Fin 3) :
    extendLengths π w₃ arm (π.armEdge k) = arm k := by
  unfold extendLengths
  rw [show π.armEdge k = targetEquiv π (Sum.inr k) from rfl, Equiv.symm_apply_apply]
  rfl

theorem extendLengths_nonneg {w₃ : π.T₃.edges → ℚ} {arm : Fin 3 → ℚ} (h₃ : ∀ e, 0 ≤ w₃ e)
    (ha : ∀ k, 0 ≤ arm k) (ε : π.T₆.edges) : 0 ≤ extendLengths π w₃ arm ε := by
  rcases π.T₆_edge_cases ε with ⟨e, rfl⟩ | ⟨k, rfl⟩
  · rw [extendLengths_liftE₃]; exact h₃ e
  · rw [extendLengths_armEdge]; exact ha k

end Lengths

/-! ## 3. The glued rows -/

section GluedRows

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {ψ : FibreMember core (baseRequest s y) (2 + 2)} {π : Placement ψ.target (2 + 2)}
  (hπ : π.NonDangling ψ.data)
  {ident : CoreIdentification (tripodCore core s) (glueDatum ψ.data π)}
  (hL : GluedLabels s ψ π ident (GeometricDatumIso.refl _))

/-- The leg of mark `k`: the stable path of its hairpin. -/
def hairpinPath (ψ : FibreMember core (baseRequest s y) (2 + 2)) (π : Placement ψ.target (2 + 2))
    (k : Fin 3) : StablePath (glueDatum ψ.data π) :=
  (Onto.legND (π := π) ψ.fullDim.valid.1 ψ.fullDim.targetConnected k).stablePath

/-- The second arm of the hairpin of mark `k`, in the new sheet. -/
def armND₂ (ψ : FibreMember core (baseRequest s y) (2 + 2)) (π : Placement ψ.target (2 + 2))
    (k : Fin 3) : NonDanglingEdge (glueDatum ψ.data π) :=
  ⟨_, (hairpin_not_isDangling ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected k).2⟩

theorem armND₂_stablePath (k : Fin 3) : (armND₂ ψ π k).stablePath = hairpinPath ψ π k :=
  (stablePath_hairpin ψ.data π (glueDatum_connected ψ.data π ψ.fullDim.valid.1
    ψ.fullDim.targetConnected) k _ _).symm

include hL in
theorem row_hairpinPath (k : Fin 3) : ident.row (hairpinPath ψ π k) = legSlot p k := by
  obtain ⟨e', he', hr⟩ := hL.leg k
  have : e' = Onto.legND (π := π) ψ.fullDim.valid.1 ψ.fullDim.targetConnected k := Subtype.ext he'
  rw [← hr, this]
  rfl

include hL in
theorem hairpinPath_injective : Function.Injective (hairpinPath ψ π) := by
  intro k j h
  have := congrArg ident.row h
  rw [row_hairpinPath hL, row_hairpinPath hL] at this
  exact Fin.natAdd_injective _ _ this

include hL hπ in
/-- **Every stable path of the glued datum is a glued old path or a leg** (`Onto.exists_gluedPath_eq_gSlot`
at the frame of any full-dimensional presentation, and the clause `leg`). -/
theorem stablePath_cases (Q : StablePath (glueDatum ψ.data π)) :
    (∃ z, Q = CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) ∨
      ∃ k, Q = hairpinPath ψ π k := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hT0 := ψ.fullDim.targetGenus
  obtain ⟨fd⟩ := nonempty_fullDim_glueDatum ψ π hπ
  let φ := (⟨_, _, fd, ident⟩ : Frame (tripodCore core s) (3 + 2)).member y
  rcases Dichotomy.isGSlot_or_eq_legSlot (ident.row Q) with hj | ⟨k, hk⟩
  · obtain ⟨z, hz⟩ := Onto.exists_gluedPath_eq_gSlot hD hT hπ hT0 (φ := φ)
      (GeometricDatumIso.refl _) (⟨hL.mark, hL.centre, hL.leg⟩ :
        Onto.ShapeLabels s ψ.data π φ.ident (GeometricDatumIso.refl _)) ⟨_, hj⟩
    left
    refine ⟨z, ?_⟩
    have hG := glueDatum_connected ψ.data π hD hT
    change (GeometricDatumIso.refl (glueDatum ψ.data π)).stablePathEquiv hG
      (CutPaths.gluedPath ψ.data π hD hT hπ z) = ident.row.symm (Fin.castAdd 3 ⟨_, hj⟩) at hz
    rw [GeometricDatumIso.stablePathEquiv_refl, Equiv.refl_apply] at hz
    rw [hz]
    show Q = ident.row.symm _
    rw [Equiv.eq_symm_apply]
    exact Fin.ext rfl
  · exact Or.inr ⟨k, ident.row.injective (hk.trans (row_hairpinPath hL k).symm)⟩

include hπ in
/-- **An old row**: its length only involves the edges of `T₃`, through the old edges. -/
theorem pathSum_gluedPath (w₃ : π.T₃.edges → ℚ) (arm : Fin 3 → ℚ)
    (z₀ : NonDanglingEdge (refine₃ ψ.data π)) :
    pathSum (glueDatum ψ.data π) (extendLengths π w₃ arm)
        (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z₀) =
      ∑ z : NonDanglingEdge (refine₃ ψ.data π),
        if CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z =
          CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z₀
        then w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 else 0 := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  unfold pathSum
  rw [CutPaths.sum_eq_sum_liftND hD hT hπ]
  · refine Finset.sum_congr rfl fun z _ ↦ ?_
    show (if CutPaths.gluedPath ψ.data π hD hT hπ z = _ then
      extendLengths π w₃ arm (π.liftE₃ z.1.1.1) /
        ((glueDatum ψ.data π).sourceEdgeIndex (liftSE ψ.data π z.1) : ℚ) else 0) = _
    rw [extendLengths_liftE₃, CutPaths.sourceEdgeIndex_liftSE]
  · intro x hx
    rw [if_neg]
    intro h
    exact hx ((CutPaths.isOld_iff_of_stablePath_eq hD hT hπ h).mpr
      (CutPaths.isOld_liftND hD hT hπ z₀))

/-- The two arms of the hairpin of mark `k`, as the only surviving edges over the arms. -/
theorem nd_over_arm (x : NonDanglingEdge (glueDatum ψ.data π)) (j : Fin 3)
    (hx : x.1.1.1 = π.armEdge j) :
    x = Onto.legND (π := π) ψ.fullDim.valid.1 ψ.fullDim.targetConnected j ∨ x = armND₂ ψ π j := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hx' := eq_armSheetEdge ψ.data π x.1 hx
  have hnd := x.2
  rw [hx'] at hnd
  rcases ((hairpinShaped_nonDangling ψ.data π hD hT) j x.1.1.2).mp hnd with h | h
  · left
    apply Subtype.ext
    rw [hx', h]
    rfl
  · right
    apply Subtype.ext
    rw [hx', h]
    rfl

theorem legND_ne_armND₂ (k : Fin 3) :
    Onto.legND (π := π) ψ.fullDim.valid.1 ψ.fullDim.targetConnected k ≠ armND₂ ψ π k := by
  intro h
  have h1 := congrArg (fun x : NonDanglingEdge (glueDatum ψ.data π) ↦ x.1.1.2) h
  change (armSheetEdge ψ.data π k (π.sheet k).castSucc).1.2 =
    (armSheetEdge ψ.data π k (Fin.last _)).1.2 at h1
  rw [armSheetEdge_sheet, armSheetEdge_sheet] at h1
  exact (Fin.castSucc_lt_last _).ne h1

include hL in
/-- **A leg row**: twice the arm, plus the rest of the leg at zero arm length. -/
theorem pathSum_hairpinPath (w₃ : π.T₃.edges → ℚ) (arm : Fin 3 → ℚ) (k : Fin 3) :
    pathSum (glueDatum ψ.data π) (extendLengths π w₃ arm) (hairpinPath ψ π k) =
      pathSum (glueDatum ψ.data π) (extendLengths π w₃ 0) (hairpinPath ψ π k) + 2 * arm k := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  set a₁ := Onto.legND (π := π) hD hT k with ha₁
  set a₂ := armND₂ ψ π k with ha₂
  have hterm : ∀ x : NonDanglingEdge (glueDatum ψ.data π),
      (if x.stablePath = hairpinPath ψ π k then
        extendLengths π w₃ arm x.1.1.1 / ((glueDatum ψ.data π).sourceEdgeIndex x.1 : ℚ) else 0) =
      (if x.stablePath = hairpinPath ψ π k then
        extendLengths π w₃ 0 x.1.1.1 / ((glueDatum ψ.data π).sourceEdgeIndex x.1 : ℚ) else 0) +
        ((if x = a₁ then arm k else 0) + (if x = a₂ then arm k else 0)) := by
    intro x
    rcases π.T₆_edge_cases x.1.1.1 with ⟨e, he⟩ | ⟨j, hj⟩
    · have h1 : x ≠ a₁ := by
        intro h
        rw [h, ha₁, Onto.legND_val] at he
        exact π.liftE₃_ne_armEdge e k (he.symm.trans rfl)
      have h2 : x ≠ a₂ := by
        intro h
        rw [h] at he
        exact π.liftE₃_ne_armEdge e k (he.symm.trans rfl)
      rw [if_neg h1, if_neg h2, he, extendLengths_liftE₃, extendLengths_liftE₃]
      ring
    · have hidx : ((glueDatum ψ.data π).sourceEdgeIndex x.1 : ℚ) = 1 := by
        rw [eq_armSheetEdge ψ.data π x.1 hj, sourceEdgeIndex_armSheetEdge]
        rfl
      rw [hj, extendLengths_armEdge, extendLengths_armEdge, hidx, div_one, div_one,
        Pi.zero_apply, ite_self, zero_add]
      have harm_ne : ∀ {j' : Fin 3} {x' : NonDanglingEdge (glueDatum ψ.data π)},
          x'.1.1.1 = π.armEdge j' → j' ≠ k → x' ≠ a₁ ∧ x' ≠ a₂ := by
        intro j' x' hx' hjk
        refine ⟨fun h ↦ hjk (π.armEdge_injective ?_), fun h ↦ hjk (π.armEdge_injective ?_)⟩
        · rw [← hx', h, ha₁, Onto.legND_val]; rfl
        · rw [← hx', h]; rfl
      rcases nd_over_arm x j hj with hx | hx
      · have hsp : x.stablePath = hairpinPath ψ π j := by rw [hx]; rfl
        by_cases hjk : j = k
        · subst hjk
          rw [if_pos hsp, if_pos (hx.trans ha₁.symm),
            if_neg (fun h ↦ legND_ne_armND₂ j ((hx.symm.trans h).trans ha₂))]
          ring
        · obtain ⟨h1, h2⟩ := harm_ne hj hjk
          rw [if_neg (fun h ↦ hjk (hairpinPath_injective hL (hsp.symm.trans h))), if_neg h1,
            if_neg h2]
          ring
      · have hsp : x.stablePath = hairpinPath ψ π j := by rw [hx]; exact armND₂_stablePath j
        by_cases hjk : j = k
        · subst hjk
          rw [if_pos hsp, if_pos (hx.trans ha₂.symm),
            if_neg (fun h ↦ legND_ne_armND₂ j (ha₁.symm.trans (h.symm.trans hx)))]
          ring
        · obtain ⟨h1, h2⟩ := harm_ne hj hjk
          rw [if_neg (fun h ↦ hjk (hairpinPath_injective hL (hsp.symm.trans h))), if_neg h1,
            if_neg h2]
          ring
  unfold pathSum
  rw [Finset.sum_congr rfl fun x _ ↦ hterm x, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
    if_pos (Finset.mem_univ _)]
  ring

end GluedRows

/-! ## 4. The bound on the legs -/

section Bounds

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {ψ : FibreMember core (baseRequest s y) (2 + 2)} {π : Placement ψ.target (2 + 2)}
  (hπ : π.NonDangling ψ.data)
  {ident : CoreIdentification (tripodCore core s) (glueDatum ψ.data π)}
  (hL : GluedLabels s ψ π ident (GeometricDatumIso.refl _))
  {w₃ : π.T₃.edges → ℚ} (hw₃ : ∀ e, 0 ≤ w₃ e)

/-- At most one surviving edge lies over a given source edge. -/
theorem sum_ite_val_le {S : CFGraph} {k : ℕ} {E : GluingDatum S k} (c : E.SourceEdge) {a : ℚ}
    (ha : 0 ≤ a) : (∑ x : NonDanglingEdge E, if x.1 = c then a else 0) ≤ a := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun x : NonDanglingEdge E ↦ x.1 = c).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb ↦
      Subtype.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have : ((Finset.univ.filter fun x : NonDanglingEdge E ↦ x.1 = c).card : ℚ) ≤ 1 := by
    exact_mod_cast hcard
  nlinarith

theorem sourceEdgeIndex_newSE (ε : π.T₃.edges) :
    (glueDatum ψ.data π).sourceEdgeIndex (newSE ψ.data π ε) = 1 := by
  show ((glueDatum ψ.data π).edgePartition (π.liftE₃ ε)).blockCard (Fin.last _) = 1
  rw [glueDatum_edgePartition_liftE₃, SheetOps.blockCard_extendNew_last]

include hπ hw₃ in
/-- **A leg at zero arm length is at most the total length of `T₃`**: it passes over new-sheet
edges only, each once with index one, and over the arms. -/
theorem pathSum_hairpinPath_le (k : Fin 3) :
    pathSum (glueDatum ψ.data π) (extendLengths π w₃ 0) (hairpinPath ψ π k) ≤ ∑ ε, w₃ ε := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hterm : ∀ x : NonDanglingEdge (glueDatum ψ.data π),
      (if x.stablePath = hairpinPath ψ π k then
        extendLengths π w₃ 0 x.1.1.1 / ((glueDatum ψ.data π).sourceEdgeIndex x.1 : ℚ) else 0) ≤
      ∑ ε, if x.1 = newSE ψ.data π ε then w₃ ε else 0 := by
    intro x
    have hR : 0 ≤ ∑ ε, if x.1 = newSE ψ.data π ε then w₃ ε else 0 :=
      Finset.sum_nonneg fun ε _ ↦ by split_ifs; exacts [hw₃ ε, le_rfl]
    rcases sourceEdge_cases_glue ψ.data π x.1 with ⟨z, hz⟩ | ⟨ε₀, hε₀⟩ | ⟨j, i, hji⟩
    · rw [if_neg]
      · exact hR
      intro hx
      obtain ⟨z', hz'⟩ := (CutPaths.isOld_iff_of_stablePath_eq hD hT hπ hx).mp ⟨z, hz⟩
      exact liftSE_ne_arm ψ.data π z' k _ hz'.symm
    · have hRe : (∑ ε, if x.1 = newSE ψ.data π ε then w₃ ε else 0) = w₃ ε₀ := by
        rw [hε₀]
        simp_rw [(newSE_injective ψ.data π).eq_iff]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      rw [hRe]
      split_ifs
      · rw [hε₀]
        show extendLengths π w₃ 0 (π.liftE₃ ε₀) /
          ((glueDatum ψ.data π).sourceEdgeIndex (newSE ψ.data π ε₀) : ℚ) ≤ _
        rw [extendLengths_liftE₃, sourceEdgeIndex_newSE, Nat.cast_one, div_one]
      · exact hw₃ ε₀
    · have hx : x.1.1.1 = π.armEdge j := by rw [hji]; rfl
      rw [hx, extendLengths_armEdge]
      split_ifs
      · rw [Pi.zero_apply, zero_div]; exact hR
      · exact hR
  unfold pathSum
  calc _ ≤ ∑ x : NonDanglingEdge (glueDatum ψ.data π),
        ∑ ε, (if x.1 = newSE ψ.data π ε then w₃ ε else 0) := Finset.sum_le_sum fun x _ ↦ hterm x
    _ = ∑ ε, ∑ x : NonDanglingEdge (glueDatum ψ.data π),
        (if x.1 = newSE ψ.data π ε then w₃ ε else 0) := Finset.sum_comm
    _ ≤ ∑ ε, w₃ ε := Finset.sum_le_sum fun ε _ ↦ sum_ite_val_le _ (hw₃ ε)

/-- **Every edge of `T₃` carries a surviving source edge**: its parent does
(`noDanglingTargetFibres`), and the piece of a surviving edge survives. -/
theorem exists_nd_over (ε : π.T₃.edges) :
    ∃ z : NonDanglingEdge (refine₃ ψ.data π), z.1.1.1 = ε := by
  have hD := ψ.fullDim.valid.1
  obtain ⟨x, hx1, hx2⟩ := ψ.fullDim.noDanglingTargetFibres (Onto.parent₃ π ε)
  have hrepr : ((refine₃ ψ.data π).edgePartition ε).repr x.1.2 = x.1.2 := by
    rw [refineDatum_edgePartition, refineDatum_edgePartition, refineDatum_edgePartition]
    change (ψ.data.edgePartition (Onto.parent₃ π ε)).repr x.1.2 = x.1.2
    rw [← hx1]
    exact x.2
  let z₁ : (refine₃ ψ.data π).SourceEdge := ⟨(ε, x.1.2), hrepr⟩
  have hpar : parentSE₃ ψ.data π z₁ = x := Subtype.ext (Prod.ext hx1.symm rfl)
  have hnd : ¬ IsDangling (refine₃ ψ.data π) z₁ := by
    rw [isDangling_iff₃ ψ.data π hD, hpar]
    exact hx2
  exact ⟨⟨z₁, hnd⟩, rfl⟩

include hw₃ in
/-- **The total length of `T₃` is at most four times the length of its surviving edges**: every
edge of `T₃` carries a surviving edge, of index at most four. -/
theorem sum_w₃_le :
    ∑ ε, w₃ ε ≤ 4 * ∑ z : NonDanglingEdge (refine₃ ψ.data π),
      w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 := by
  classical
  choose zε hzε using exists_nd_over (ψ := ψ) (π := π)
  set g : NonDanglingEdge (refine₃ ψ.data π) → ℚ :=
    fun z ↦ w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z ↦ div_nonneg (hw₃ _) (Nat.cast_nonneg _)
  have hinj : Function.Injective zε := fun a b h ↦ by rw [← hzε a, ← hzε b, h]
  have hstep : ∀ ε, w₃ ε ≤ 4 * g (zε ε) := by
    intro ε
    have hpos : (0 : ℚ) < (refine₃ ψ.data π).sourceEdgeIndex (zε ε).1 := by
      exact_mod_cast ((refine₃ ψ.data π).edgePartition (zε ε).1.1.1).blockCard_pos (zε ε).1.1.2
    have hle : ((refine₃ ψ.data π).sourceEdgeIndex (zε ε).1 : ℚ) ≤ 4 := by
      exact_mod_cast DraismaVargas.LocalCases.MatrixAtlas.sourceEdgeIndex_le_degree _ _
    rw [hg]
    simp only
    rw [hzε ε, mul_div_assoc', le_div_iff₀ hpos]
    nlinarith [hw₃ ε]
  calc ∑ ε, w₃ ε ≤ ∑ ε, 4 * g (zε ε) := Finset.sum_le_sum fun ε _ ↦ hstep ε
    _ = 4 * ∑ z ∈ Finset.univ.image zε, g z := by
        rw [← Finset.mul_sum, Finset.sum_image fun a _ b _ h ↦ hinj h]
    _ ≤ 4 * ∑ z, g z := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun z _ _ ↦ hg0 z

include hπ hL hw₃ in
/-- **The surviving edges of `refine₃` add up to the length of `G̃`**: grouped by glued old path,
each group is the requested length of a G-slot of `Γ̃`. -/
theorem sum_g_le (hpos : ∀ i, 0 < y i)
    (hold : ∀ z₀ : NonDanglingEdge (refine₃ ψ.data π),
      (∑ z : NonDanglingEdge (refine₃ ψ.data π),
        if CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z =
          CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z₀
        then w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 else 0) =
        y (ident.row (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1
          ψ.fullDim.targetConnected hπ z₀))) :
    ∑ z : NonDanglingEdge (refine₃ ψ.data π),
      w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 ≤ ∑ i, baseRequest s y i := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  set gp := CutPaths.gluedPath ψ.data π hD hT hπ with hgp
  set g : NonDanglingEdge (refine₃ ψ.data π) → ℚ :=
    fun z ↦ w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z ↦ div_nonneg (hw₃ _) (Nat.cast_nonneg _)
  -- a glued old path lies on a G-slot
  have hGs : ∀ z, IsGSlot (ident.row (gp z)) := by
    intro z
    rcases Dichotomy.isGSlot_or_eq_legSlot (ident.row (gp z)) with h | ⟨k, hk⟩
    · exact h
    · exfalso
      have := ident.row.injective (hk.trans (row_hairpinPath hL k).symm)
      exact CutPaths.gluedPath_ne_hairpin hD hT hπ z k this
  have hfib : ∀ Q : StablePath (glueDatum ψ.data π),
      (∑ z, if gp z = Q then g z else 0) ≤ if IsGSlot (ident.row Q) then y (ident.row Q) else 0 := by
    intro Q
    by_cases hQ : ∃ z₀, gp z₀ = Q
    · obtain ⟨z₀, rfl⟩ := hQ
      rw [if_pos (hGs z₀)]
      exact (hold z₀).le
    · push Not at hQ
      rw [Finset.sum_eq_zero fun z _ ↦ if_neg (hQ z)]
      split_ifs
      · exact (hpos _).le
      · exact le_rfl
  have hsplit : ∑ z, g z = ∑ Q : StablePath (glueDatum ψ.data π), ∑ z, if gp z = Q then g z else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  have hG : (∑ Q : StablePath (glueDatum ψ.data π),
      if IsGSlot (ident.row Q) then y (ident.row Q) else 0) = ∑ i, baseRequest s y i := by
    rw [ident.row.sum_comp (fun j ↦ if IsGSlot j then y j else 0), sum_baseRequest,
      Fin.sum_univ_add]
    have h1 : ∀ i : Fin (p + 1 + 1 + 1), IsGSlot (Fin.castAdd 3 i) := fun i ↦ by
      unfold IsGSlot
      simp only [Fin.val_castAdd]
      exact i.isLt
    have h2 : ∀ i : Fin 3, ¬ IsGSlot (Fin.natAdd (p + 1 + 1 + 1) i) := fun i ↦ by
      unfold IsGSlot
      simp only [Fin.val_natAdd]
      omega
    simp only [h1, h2, ↓reduceIte, Finset.sum_const_zero, add_zero]
    rfl
  calc ∑ z, g z = _ := hsplit
    _ ≤ _ := Finset.sum_le_sum fun Q _ ↦ hfib Q
    _ = _ := hG

end Bounds

/-! ## 5. The assembly -/

section Assembly

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p}

/-- **The pieces at the actual positions, and the geometric lengths of `T₃`** (§5.2,
positivity; §5.5, well-definedness): at a positive request, an open
member `ψ` at the base request has a placement on its core, a labelling of the glued old paths by
the slots of the marked core with the ends of those slots (`PieceIdent.PieceLabels`), and
non-negative lengths on the edges of `T₃` along which every glued old path has the requested length
of its label. -/
theorem exists_pieceLabels {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (ψ : FibreMember core (baseRequest s y) (2 + 2)) (hψ : ψ.Open) :
    ∃ π : Placement ψ.target (2 + 2), ∃ hπ : π.NonDangling ψ.data,
      ∃ lab : StablePath (glueDatum ψ.data π) → Fin (p + 1 + 1 + 1),
        PieceIdent.PieceLabels s ψ hπ lab ∧
        ∃ w₃ : π.T₃.edges → ℚ, (∀ e, 0 ≤ w₃ e) ∧
          ∀ z₀ : NonDanglingEdge (refine₃ ψ.data π),
            (∑ z : NonDanglingEdge (refine₃ ψ.data π),
              if CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z =
                CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z₀
              then w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 else 0) =
              y (Fin.castAdd 3 (lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1
                ψ.fullDim.targetConnected hπ z₀))) := by
  -- The marks at their actual positions, one at a time (`Chains.forward`, three times, from the
  -- stable paths of `ψ` as oriented chains, `Chains.exists_layout₀`); the labels of the third stage
  -- are piece labels of the glued old paths (`Chains.pieceLabels_of_labelData`).
  exact Chains.exists_pieceLabels_of_open hpos ψ hψ

/-- **The glued labels at the actual positions, and the geometric lengths of `T₃`** (§5.2,
positivity; §5.5, well-definedness): at a positive request, an open
member `ψ` at the base request has a placement on its core, a core identification of the glued
datum with `Γ̃` carrying the glued labels, and non-negative lengths on the edges of `T₃` along which
every glued old path has the requested length of its slot of `Γ̃`. From `exists_pieceLabels` and
`PieceIdent.exists_ident_of_pieceLabels`. -/
theorem exists_gluedIdent_pieces {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (ψ : FibreMember core (baseRequest s y) (2 + 2)) (hψ : ψ.Open) :
    ∃ π : Placement ψ.target (2 + 2), ∃ hπ : π.NonDangling ψ.data,
      ∃ ident : CoreIdentification (tripodCore core s) (glueDatum ψ.data π),
        GluedLabels s ψ π ident (GeometricDatumIso.refl _) ∧
        ∃ w₃ : π.T₃.edges → ℚ, (∀ e, 0 ≤ w₃ e) ∧
          ∀ z₀ : NonDanglingEdge (refine₃ ψ.data π),
            (∑ z : NonDanglingEdge (refine₃ ψ.data π),
              if CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z =
                CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z₀
              then w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 else 0) =
              y (ident.row (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1
                ψ.fullDim.targetConnected hπ z₀)) := by
  obtain ⟨π, hπ, lab, hl, w₃, hw₃, hlen⟩ := exists_pieceLabels hpos ψ hψ
  obtain ⟨ident, hL, hrow⟩ := PieceIdent.exists_ident_of_pieceLabels hπ hl
  exact ⟨π, hπ, ident, hL, w₃, hw₃, fun z₀ ↦ by rw [hrow]; exact hlen z₀⟩

/-- **The glued labels, closed at `y`**, from `exists_gluedIdent_pieces`: the arm lengths are read
off the leg rows, and they are positive by long legs. -/
theorem exists_gluedIdent_closed {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (hlong : LongLegs s y) (ψ : FibreMember core (baseRequest s y) (2 + 2)) (hψ : ψ.Open) :
    ∃ π : Placement ψ.target (2 + 2), π.NonDangling ψ.data ∧
      ∃ ident : CoreIdentification (tripodCore core s) (glueDatum ψ.data π),
        GluedLabels s ψ π ident (GeometricDatumIso.refl _) ∧
        ∀ (fd : FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)))
          (col : Fin (p + 1 + 1 + 1 + 3)),
          0 ≤ (⟨_, _, fd, ident⟩ : Frame (tripodCore core s) (3 + 2)).coordsAt y col := by
  classical
  obtain ⟨π, hπ, ident, hL, w₃, hw₃, hold⟩ := exists_gluedIdent_pieces hpos ψ hψ
  set N : Fin 3 → ℚ := fun k ↦
    pathSum (glueDatum ψ.data π) (extendLengths π w₃ 0) (hairpinPath ψ π k) with hN
  set arm : Fin 3 → ℚ := fun k ↦ (y (legSlot p k) - N k) / 2 with harm
  -- the arms are positive
  have harm0 : ∀ k, 0 ≤ arm k := by
    intro k
    have h1 := pathSum_hairpinPath_le hπ hw₃ (ψ := ψ) k
    have h2 := sum_w₃_le hw₃ (ψ := ψ) (π := π)
    have h3 := sum_g_le hπ hL hw₃ hpos hold
    have h4 := hlong k
    unfold legLength at h4
    show 0 ≤ (y (legSlot p k) - N k) / 2
    have : N k ≤ ∑ ε, w₃ ε := h1
    linarith
  -- the lengths realise the request
  have hreal : Realises (glueDatum ψ.data π) ident.row y (extendLengths π w₃ arm) := by
    intro Q
    rcases stablePath_cases hπ hL Q with ⟨z₀, rfl⟩ | ⟨k, rfl⟩
    · rw [pathSum_gluedPath hπ, hold]
    · rw [pathSum_hairpinPath hL, row_hairpinPath hL]
      show N k + 2 * ((y (legSlot p k) - N k) / 2) = _
      ring
  refine ⟨π, hπ, ident, hL, fun fd col ↦ ?_⟩
  rw [coordsAt_eq_of_realises (⟨_, _, fd, ident⟩ : Frame (tripodCore core s) (3 + 2)) hreal]
  exact extendLengths_nonneg π hw₃ harm0 _

end Assembly

end Positivity

end GenusSixExistence.Tripod.Gluing

end
