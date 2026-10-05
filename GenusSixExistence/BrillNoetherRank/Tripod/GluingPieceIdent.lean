import GenusSixExistence.BrillNoetherRank.Tripod.GluingOntoOpen

/-!
# The core identification of a glued datum from labels of its pieces

For a placement `π` on the core of a member `ψ` over `G̃`, the stable graph of
`glueDatum ψ.data π` is identified with `Γ̃ = tripodCore core s`, with the glued labels, as soon as
the glued old paths are labelled by the slots of the marked core so that

* distinct glued old paths get distinct labels,
* each label merges back to the slot of `G̃` of its row (`mergeOne`),
* the ends of each glued old path are the ends of its slot: its incidences at the old branch
  vertices and at the marks are those of its slot in the marked core (`PieceLabels`).

`exists_ident_of_pieceLabels` builds the identification: the branch vertices of the
glued datum are the old ones, the three marks and one new-sheet vertex, the centre
(`vinv_bijective`); its stable paths are the glued old paths and the three legs (`rinv_bijective`);
and the incidences are read off the labels, except at a leg, which meets its mark once (by its
arm) and the centre once (it has two ends, `StablePathCount.endCount_eq_two`). This is the
combinatorial part of `GluingPositivity.exists_gluedIdent_pieces`; the rest there is the
placement at the actual positions and the lengths. Prose:
`Research/genus-six-brill-noether-rank.md`, §5.5 (The bijection).
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

namespace PieceIdent

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {yG : Fin p → ℚ}

/-- An old vertex of `G̃` in the marked core. -/
def mOld (v : Fin n) : Fin (n + 1 + 1 + 1) := v.castSucc.castSucc.castSucc

/-- **Labels of the glued old paths by the slots of the marked core**: injective, merging back to
the slot of the row, and with the ends of the slot. -/
structure PieceLabels (s : MarkSlots p) (ψ : FibreMember core yG (2 + 2))
    {π : Placement ψ.target (2 + 2)} (hπ : π.NonDangling ψ.data)
    (lab : StablePath (glueDatum ψ.data π) → Fin (p + 1 + 1 + 1)) : Prop where
  inj : ∀ z z' : NonDanglingEdge (refine₃ ψ.data π),
    lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) =
      lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z') →
    CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z =
      CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z'
  merge : ∀ z : NonDanglingEdge (refine₃ ψ.data π),
    mergeOne s.first (mergeOne s.second (mergeOne s.third
      (lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z)))) =
        ψ.ident.row (parentND₃ z).stablePath
  old : ∀ (z : NonDanglingEdge (refine₃ ψ.data π)) (b : BranchVertex ψ.data),
    incidenceCount (glueDatum ψ.data π) (π.oldSourceVertex ψ.data b.1)
        (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) =
      coreIncidence (markedCore core s) (mOld (ψ.ident.vertex b))
        (lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z))
  mark : ∀ (z : NonDanglingEdge (refine₃ ψ.data π)) (k : Fin 3),
    incidenceCount (glueDatum ψ.data π) (π.markSourceVertex ψ.data k)
        (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) =
      coreIncidence (markedCore core s) (markVertex n k)
        (lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z))

/-! ## 1. The branch vertices -/

section Vertices

variable {ψ : FibreMember core yG (2 + 2)} {π : Placement ψ.target (2 + 2)}
  (hπ : π.NonDangling ψ.data)

/-- An old branch vertex, as a branch vertex of the glued datum. -/
def oldBV (b : BranchVertex ψ.data) : BranchVertex (glueDatum ψ.data π) :=
  ⟨π.oldSourceVertex ψ.data b.1, by
    rw [oldSourceVertex_eq, nonDanglingValency_oldVertex₃ ψ.data π ψ.fullDim.valid.1
      ψ.fullDim.targetConnected hπ]
    have h := CutPaths.nonDanglingValency_lift₃V (π := π) ψ.fullDim.valid.1 b.1
    have hb := b.2
    change 3 ≤ nonDanglingValency (refine₃ ψ.data π) (CutPaths.lift₃V ψ.data π b.1) + _
    omega⟩

/-- Mark `k`, as a branch vertex of the glued datum. -/
def markBV (k : Fin 3) : BranchVertex (glueDatum ψ.data π) :=
  ⟨π.markSourceVertex ψ.data k, by
    rw [markSourceVertex_eq, nonDanglingValency_oldVertex₃ ψ.data π ψ.fullDim.valid.1
      ψ.fullDim.targetConnected hπ, sum_mark_eq_one, markR₃,
      π.nonDanglingValency_markR₃ ψ.data ψ.fullDim.valid.1 hπ k]⟩

omit hπ in
/-- **The new sheet has a branch vertex**, the median of the three mark images. -/
theorem exists_centre :
    ∃ u, 3 ≤ nonDanglingValency (glueDatum ψ.data π) (newVertex ψ.data π u) := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hT0 := ψ.fullDim.targetGenus
  have hG := glueDatum_connected ψ.data π hD hT
  have hX : ∀ u ∉ π.markSet, tCount (NewSurvives ψ.data π) u ≠ 1 := by
    intro u hu
    have h := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
      (newVertex ψ.data π u)
    rw [nonDanglingValency_newVertex ψ.data π hD hT, π.sum_markVertex_eq, if_neg hu,
      add_zero] at h
    exact h
  have hXM : ∀ u ∈ π.markSet, tCount (NewSurvives ψ.data π) u ≠ 0 := by
    intro u hu
    have h := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
      (newVertex ψ.data π u)
    rw [nonDanglingValency_newVertex ψ.data π hD hT, π.sum_markVertex_eq, if_pos hu] at h
    omega
  have h := card_branch_eq_one (π.T₃_connected hT) (π.T₃_genus hT0) π.markSet π.card_markSet
    (NewSurvives ψ.data π) hX hXM
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [h]; norm_num)
  refine ⟨u, ?_⟩
  rw [nonDanglingValency_newVertex ψ.data π hD hT, π.sum_markVertex_eq]
  exact (Finset.mem_filter.mp hu).2

/-- The centre: the branch vertex of the new sheet. -/
def centreU : π.T₃.V := Classical.choose (exists_centre (ψ := ψ) (π := π))

/-- The centre, as a branch vertex of the glued datum. -/
def centreBV : BranchVertex (glueDatum ψ.data π) :=
  ⟨newVertex ψ.data π centreU, Classical.choose_spec (exists_centre (ψ := ψ) (π := π))⟩

/-- The branch vertex with a given label of `Γ̃`: an old vertex, a mark, or the centre. -/
def vinv (L : Fin (n + 1 + 1 + 1 + 1)) : BranchVertex (glueDatum ψ.data π) :=
  if h : L.val < n then oldBV hπ (ψ.ident.vertex.symm ⟨L.val, h⟩)
  else if h' : L.val < n + 3 then markBV hπ ⟨L.val - n, by omega⟩ else centreBV

theorem vinv_oldLabel (v : Fin n) : vinv hπ (oldLabel v) = oldBV hπ (ψ.ident.vertex.symm v) := by
  unfold vinv
  rw [dif_pos (by simp [oldLabel])]
  rfl

theorem vinv_tripodMark (k : Fin 3) : vinv hπ (tripodMark n k) = markBV hπ k := by
  unfold vinv
  rw [dif_neg (by simp only [tripodMark, markVertex, Fin.val_castSucc]; omega),
    dif_pos (by simp only [tripodMark, markVertex, Fin.val_castSucc]; omega)]
  congr 1
  exact Fin.ext (by simp only [tripodMark, markVertex, Fin.val_castSucc]; omega)

theorem vinv_centre : vinv hπ (centre n) = centreBV := by
  unfold vinv
  rw [dif_neg (by simp only [centre, Fin.val_last]; omega),
    dif_neg (by simp only [centre, Fin.val_last]; omega)]

theorem oldSV₃_injective : Function.Injective (oldSV₃ ψ.data π) := fun _ _ h ↦
  Refine.oldSV_injective _ _ (Refine.oldSV_injective _ _ (Refine.oldSV_injective _ _ h))

theorem oldSourceVertex_injective : Function.Injective (π.oldSourceVertex ψ.data) := fun _ _ h ↦
  oldSV₃_injective (oldVertex₃_injective ψ.data π h)

theorem vinv_cases (L : Fin (n + 1 + 1 + 1 + 1)) :
    (∃ v, L = oldLabel v) ∨ (∃ k, L = tripodMark n k) ∨ L = centre n := by
  by_cases h : L.val < n
  · exact Or.inl ⟨⟨L.val, h⟩, Fin.ext rfl⟩
  · by_cases h' : L.val < n + 3
    · exact Or.inr (Or.inl ⟨⟨L.val - n, by omega⟩,
        Fin.ext (by simp only [tripodMark, markVertex, Fin.val_castSucc]; omega)⟩)
    · exact Or.inr (Or.inr (Fin.ext (by simp only [centre, Fin.val_last]; omega)))

theorem vinv_injective : Function.Injective (vinv hπ) := by
  intro L L' h
  have hv : (vinv hπ L).1 = (vinv hπ L').1 := congrArg Subtype.val h
  rcases vinv_cases L with ⟨v, rfl⟩ | ⟨k, rfl⟩ | rfl <;>
    rcases vinv_cases L' with ⟨v', rfl⟩ | ⟨k', rfl⟩ | rfl <;>
    simp only [vinv_oldLabel, vinv_tripodMark, vinv_centre, oldBV, markBV, centreBV,
      oldSourceVertex_eq, markSourceVertex_eq] at hv
  · have h1 := oldSV₃_injective (oldVertex₃_injective ψ.data π hv)
    have h2 : ψ.ident.vertex.symm v = ψ.ident.vertex.symm v' := Subtype.ext h1
    rw [ψ.ident.vertex.symm.injective h2]
  · exact absurd (oldVertex₃_injective ψ.data π hv)
      (CutPaths.lift₃V_ne_markR₃ ψ.fullDim.valid.1 hπ _ k')
  · exact absurd hv (oldVertex₃_ne_newVertex ψ.data π _ _)
  · exact absurd (oldVertex₃_injective ψ.data π hv).symm
      (CutPaths.lift₃V_ne_markR₃ ψ.fullDim.valid.1 hπ _ k)
  · rw [markR₃_injective ψ.data π (oldVertex₃_injective ψ.data π hv)]
  · exact absurd hv (oldVertex₃_ne_newVertex ψ.data π _ _)
  · exact absurd hv.symm (oldVertex₃_ne_newVertex ψ.data π _ _)
  · exact absurd hv.symm (oldVertex₃_ne_newVertex ψ.data π _ _)
  · rfl

theorem vinv_surjective : Function.Surjective (vinv hπ) := by
  intro b
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hT0 := ψ.fullDim.targetGenus
  have hb := b.2
  rcases sourceVertex_cases_glue ψ.data π b.1 with ⟨x, hx⟩ | ⟨u, hu⟩ | ⟨k, j, hkj⟩
  · rw [hx, nonDanglingValency_oldVertex₃ ψ.data π hD hT hπ] at hb
    by_cases hm : ∃ k, x = markR₃ ψ.data π k
    · obtain ⟨k, rfl⟩ := hm
      refine ⟨tripodMark n k, ?_⟩
      rw [vinv_tripodMark]
      apply Subtype.ext
      rw [hx]
      exact (markSourceVertex_eq ψ.data π k)
    · push Not at hm
      rw [sum_mark_eq_zero ψ.data π hm, add_zero] at hb
      rcases Onto.lift₃V_or_le_two hD x with ⟨v, rfl⟩ | hle
      · have hv : 3 ≤ nonDanglingValency ψ.data v := by
          rwa [CutPaths.nonDanglingValency_lift₃V hD] at hb
        obtain ⟨b₀, hb₀⟩ : ∃ b₀ : BranchVertex ψ.data, b₀.1 = v := ⟨⟨v, hv⟩, rfl⟩
        refine ⟨oldLabel (ψ.ident.vertex b₀), ?_⟩
        rw [vinv_oldLabel, Equiv.symm_apply_apply]
        apply Subtype.ext
        rw [hx, ← hb₀]
        rfl
      · omega
  · rw [hu] at hb
    refine ⟨centre n, ?_⟩
    rw [vinv_centre]
    apply Subtype.ext
    rw [hu]
    show newVertex ψ.data π centreU = _
    rw [show (centreU : π.T₃.V) = u from Onto.newVertex_eq_of_three_le hD hT hT0
      (Classical.choose_spec (exists_centre (ψ := ψ) (π := π))) hb]
  · rw [hkj] at hb
    have := nonDanglingValency_tip_le ψ.data π hD hT k j
    omega

theorem vinv_bijective : Function.Bijective (vinv hπ) :=
  ⟨vinv_injective hπ, vinv_surjective hπ⟩

end Vertices

/-! ## 2. The stable paths -/

section Rows

variable {ψ : FibreMember core yG (2 + 2)} {π : Placement ψ.target (2 + 2)}
  (hπ : π.NonDangling ψ.data) {lab : StablePath (glueDatum ψ.data π) → Fin (p + 1 + 1 + 1)}
  (hl : PieceLabels s ψ hπ lab)

/-- The leg of mark `k`: the stable path of its hairpin. -/
def hp (ψ : FibreMember core yG (2 + 2)) (π : Placement ψ.target (2 + 2)) (k : Fin 3) :
    StablePath (glueDatum ψ.data π) :=
  (Onto.legND (π := π) ψ.fullDim.valid.1 ψ.fullDim.targetConnected k).stablePath

include hl in
theorem lab_surjective (i : Fin (p + 1 + 1 + 1)) :
    ∃ z, lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) = i := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hcard := CutPaths.card_image_gluedPath hD hT hπ ψ.fullDim.targetGenus ψ.fullDim.trivalent
    ψ.fullDim.pathEnds
  have hP : Fintype.card (StablePath ψ.data) = p := by
    rw [Fintype.card_congr ψ.ident.row, Fintype.card_fin]
  have himg : (Finset.univ.image fun z ↦
      lab (CutPaths.gluedPath ψ.data π hD hT hπ z)).card = p + 1 + 1 + 1 := by
    have himg' : (Finset.univ.image fun z ↦ lab (CutPaths.gluedPath ψ.data π hD hT hπ z)) =
        (Finset.univ.image (CutPaths.gluedPath ψ.data π hD hT hπ)).image lab := by
      rw [Finset.image_image]; rfl
    rw [himg', Finset.card_image_of_injOn, hcard, hP]
    rintro _ hQ _ hQ' h
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨z', -, rfl⟩ := Finset.mem_image.mp hQ'
    exact hl.inj z z' h
  have huniv := Finset.eq_univ_of_card _ (himg.trans (Fintype.card_fin _).symm)
  have hi : i ∈ Finset.univ.image fun z ↦ lab (CutPaths.gluedPath ψ.data π hD hT hπ z) := by
    rw [huniv]; exact Finset.mem_univ i
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hi
  exact ⟨z, hz⟩

/-- The glued old path labelled `i`. -/
def zOf (i : Fin (p + 1 + 1 + 1)) : NonDanglingEdge (refine₃ ψ.data π) :=
  Classical.choose (lab_surjective hπ hl i)

theorem lab_zOf (i : Fin (p + 1 + 1 + 1)) :
    lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ
      (zOf hπ hl i)) = i :=
  Classical.choose_spec (lab_surjective hπ hl i)

/-- The stable path with a given label of `Γ̃`: a glued old path, or a leg. -/
def rinv (j : Fin (p + 1 + 1 + 1 + 3)) : StablePath (glueDatum ψ.data π) :=
  Fin.addCases (fun i ↦ CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ
    (zOf hπ hl i)) (fun k ↦ hp ψ π k) j

theorem rinv_castAdd (i : Fin (p + 1 + 1 + 1)) :
    rinv hπ hl (Fin.castAdd 3 i) =
      CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ (zOf hπ hl i) := by
  unfold rinv
  rw [Fin.addCases_left]

theorem rinv_legSlot (k : Fin 3) : rinv hπ hl (legSlot p k) = hp ψ π k := by
  unfold rinv legSlot
  rw [Fin.addCases_right]

include hπ in
theorem hp_injective : Function.Injective (hp ψ π) := fun _ _ h ↦
  hairpinPath_injective ψ π hπ (fun k ↦ (hairpin_not_isDangling_glueDatum ψ π k).1) h

theorem gluedPath_ne_hp (z : NonDanglingEdge (refine₃ ψ.data π)) (k : Fin 3) :
    CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z ≠ hp ψ π k :=
  CutPaths.gluedPath_ne_hairpin ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z k

theorem rinv_injective : Function.Injective (rinv hπ hl) := by
  intro j j' h
  induction j using Fin.addCases with
  | left i =>
    induction j' using Fin.addCases with
    | left i' =>
      rw [rinv_castAdd, rinv_castAdd] at h
      have := congrArg lab h
      rw [lab_zOf hπ hl i, lab_zOf hπ hl i'] at this
      rw [this]
    | right k' =>
      rw [rinv_castAdd, show Fin.natAdd (p + 1 + 1 + 1) k' = legSlot p k' from rfl,
        rinv_legSlot] at h
      exact absurd h (gluedPath_ne_hp hπ _ k')
  | right k =>
    induction j' using Fin.addCases with
    | left i' =>
      rw [rinv_castAdd, show Fin.natAdd (p + 1 + 1 + 1) k = legSlot p k from rfl,
        rinv_legSlot] at h
      exact absurd h.symm (gluedPath_ne_hp hπ _ k)
    | right k' =>
      rw [show Fin.natAdd (p + 1 + 1 + 1) k = legSlot p k from rfl,
        show Fin.natAdd (p + 1 + 1 + 1) k' = legSlot p k' from rfl, rinv_legSlot,
        rinv_legSlot] at h
      rw [hp_injective hπ h]

theorem rinv_bijective : Function.Bijective (rinv hπ hl) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨rinv_injective hπ hl, ?_⟩
  rw [Fintype.card_fin, card_stablePath_glueDatum ψ π hπ]

end Rows

/-! ## 3. The incidences -/

section Incidence

variable {ψ : FibreMember core yG (2 + 2)} {π : Placement ψ.target (2 + 2)}
  (hπ : π.NonDangling ψ.data) {lab : StablePath (glueDatum ψ.data π) → Fin (p + 1 + 1 + 1)}
  (hl : PieceLabels s ψ hπ lab)

theorem coreIncidence_castSucc_castAdd (u : Fin (n + 1 + 1 + 1)) (i : Fin (p + 1 + 1 + 1)) :
    coreIncidence (tripodCore core s) u.castSucc (Fin.castAdd 3 i) =
      coreIncidence (markedCore core s) u i := by
  unfold coreIncidence
  rw [Dichotomy.tripodCore_tail_castAdd, Dichotomy.tripodCore_head_castAdd]
  simp only [Fin.castSucc_inj]

theorem coreIncidence_centre_castAdd (i : Fin (p + 1 + 1 + 1)) :
    coreIncidence (tripodCore core s) (centre n) (Fin.castAdd 3 i) = 0 := by
  unfold coreIncidence
  have h1 : ((markedCore core s).tail i).castSucc ≠ centre n := (Fin.castSucc_lt_last _).ne
  have h2 : ((markedCore core s).head i).castSucc ≠ centre n := (Fin.castSucc_lt_last _).ne
  rw [Dichotomy.tripodCore_tail_castAdd, Dichotomy.tripodCore_head_castAdd, if_neg h1, if_neg h2]

theorem incidenceCount_eq_zero_of {S : CFGraph} {k : ℕ} {E : GluingDatum S k} {v : E.SourceVertex}
    {Q : StablePath E}
    (h : ∀ x : NonDanglingEdge E, Incident E x.1 v → x.stablePath = Q → False) :
    incidenceCount E v Q = 0 := by
  unfold incidenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hxQ
  exact h x ((StablePathCount.mem_incidentEdges _ _ _).mp hx) hxQ

/-- A glued old path does not meet the new sheet. -/
theorem incidenceCount_gluedPath_newVertex (z : NonDanglingEdge (refine₃ ψ.data π)) (u : π.T₃.V) :
    incidenceCount (glueDatum ψ.data π) (newVertex ψ.data π u)
      (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) = 0 := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  refine incidenceCount_eq_zero_of fun x hx hxQ ↦ ?_
  obtain ⟨z', hz'⟩ := (CutPaths.isOld_iff_of_stablePath_eq hD hT hπ hxQ).mpr
    (CutPaths.isOld_liftND hD hT hπ z)
  rw [hz'] at hx
  exact not_incident_liftSE_newVertex ψ.data π z' u hx

include hπ in
/-- A surviving edge on a leg is not old. -/
theorem not_isOld_of_hp {x : NonDanglingEdge (glueDatum ψ.data π)} {k : Fin 3}
    (hx : x.stablePath = hp ψ π k) : ¬ CutPaths.IsOld ψ.data π x := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  intro hold
  obtain ⟨z, rfl⟩ := CutPaths.eq_liftND_of_isOld hD hT hπ hold
  exact gluedPath_ne_hp hπ z k hx

include hπ in
/-- A leg does not meet an old branch vertex. -/
theorem incidenceCount_hp_old (b : BranchVertex ψ.data) (k : Fin 3) :
    incidenceCount (glueDatum ψ.data π) (π.oldSourceVertex ψ.data b.1) (hp ψ π k) = 0 := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  refine incidenceCount_eq_zero_of fun x hx hxQ ↦ ?_
  rw [oldSourceVertex_eq] at hx
  rcases Onto.isOld_or_arm_of_incident_oldVertex₃ hD hT x hx with hold | ⟨k', hk', -⟩
  · exact not_isOld_of_hp hπ hxQ hold
  · exact CutPaths.lift₃V_ne_markR₃ hD hπ _ k' hk'

include hπ in
/-- **A leg meets a mark once, at its own mark** (by its arm). -/
theorem incidenceCount_hp_mark (k k' : Fin 3) :
    incidenceCount (glueDatum ψ.data π) (π.markSourceVertex ψ.data k') (hp ψ π k) =
      if k' = k then 1 else 0 := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hmem : ∀ x : NonDanglingEdge (glueDatum ψ.data π),
      x ∈ (StablePathCount.incidentEdges _ (π.markSourceVertex ψ.data k')).filter
        (fun e ↦ e.stablePath = hp ψ π k) ↔
        x = Onto.legND (π := π) hD hT k' ∧ k' = k := by
    intro x
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges, markSourceVertex_eq]
    constructor
    · rintro ⟨hx, hxQ⟩
      rcases Onto.isOld_or_arm_of_incident_oldVertex₃ hD hT x hx with hold | ⟨k'', hk'', harm⟩
      · exact absurd hold (not_isOld_of_hp hπ hxQ)
      · have hkk : k' = k'' := markR₃_injective ψ.data π hk''
        subst hkk
        have hxe : x = Onto.legND (π := π) hD hT k' := Subtype.ext harm
        refine ⟨hxe, hp_injective hπ ?_⟩
        rw [← hxQ, hxe]
        rfl
    · rintro ⟨rfl, rfl⟩
      refine ⟨?_, rfl⟩
      rw [← markSourceVertex_eq]
      exact armSourceEdge_incident ψ.data π k'
  unfold incidenceCount
  split_ifs with hkk
  · subst hkk
    rw [Finset.card_eq_one]
    exact ⟨Onto.legND (π := π) hD hT k', Finset.ext fun x ↦ by
      rw [hmem, Finset.mem_singleton]; exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, rfl⟩⟩⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    exact hkk ((hmem x).mp hx).2

include hπ in
/-- **A leg meets the centre once**: it has two ends, one at its mark. -/
theorem incidenceCount_hp_centre (k : Fin 3) :
    incidenceCount (glueDatum ψ.data π) (centreBV (ψ := ψ) (π := π)).1 (hp ψ π k) = 1 := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hG := glueDatum_connected ψ.data π hD hT
  have hne1 := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
  have hEnds := StablePathCount.endCount_eq_two _ hne1 (hasPathEnds_glueDatum ψ π hπ) (hp ψ π k)
  unfold StablePathCount.endCount at hEnds
  have hmk : (markBV hπ k).1 ≠ (centreBV (ψ := ψ) (π := π)).1 := by
    show π.markSourceVertex ψ.data k ≠ newVertex ψ.data π centreU
    rw [markSourceVertex_eq]
    exact oldVertex₃_ne_newVertex ψ.data π _ _
  have hle : ∀ v, incidenceCount (glueDatum ψ.data π) v (hp ψ π k) ≤
      nonDanglingValency (glueDatum ψ.data π) v := by
    intro v
    rw [← StablePathCount.card_incidentEdges]
    exact Finset.card_filter_le _ _
  rw [Finset.sum_eq_add (markBV hπ k).1 (centreBV (ψ := ψ) (π := π)).1 hmk] at hEnds
  · have h1 : incidenceCount (glueDatum ψ.data π) (markBV hπ k).1 (hp ψ π k) = 1 := by
      show incidenceCount _ (π.markSourceVertex ψ.data k) _ = 1
      rw [incidenceCount_hp_mark hπ, if_pos rfl]
    omega
  · intro c hc ⟨hc1, hc2⟩
    have hval := (Finset.mem_filter.mp hc).2
    by_cases h0 : nonDanglingValency (glueDatum ψ.data π) c = 0
    · have := hle c; omega
    have h3 : 3 ≤ nonDanglingValency (glueDatum ψ.data π) c := by
      have := hne1 c; omega
    obtain ⟨L, hL⟩ := vinv_surjective hπ ⟨c, h3⟩
    have hcL : c = (vinv hπ L).1 := by rw [hL]
    rcases vinv_cases L with ⟨v, rfl⟩ | ⟨k', rfl⟩ | rfl
    · rw [vinv_oldLabel] at hcL
      rw [hcL]
      exact incidenceCount_hp_old hπ _ k
    · rw [vinv_tripodMark] at hcL
      rw [hcL]
      show incidenceCount _ (π.markSourceVertex ψ.data k') _ = 0
      rw [incidenceCount_hp_mark hπ, if_neg]
      rintro rfl
      exact hc1 hcL
    · rw [vinv_centre] at hcL
      exact absurd hcL hc2
  · intro h
    exfalso
    apply h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have := (markBV hπ k).2
    omega
  · intro h
    exfalso
    apply h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have := (centreBV (ψ := ψ) (π := π)).2
    omega

include hl in
/-- **The incidences of `Γ̃` are those of the glued datum**, at every label. -/
theorem incidence_vinv_rinv (L : Fin (n + 1 + 1 + 1 + 1)) (j : Fin (p + 1 + 1 + 1 + 3)) :
    incidenceCount (glueDatum ψ.data π) (vinv hπ L).1 (rinv hπ hl j) =
      coreIncidence (tripodCore core s) L j := by
  induction j using Fin.addCases with
  | left i =>
    rw [rinv_castAdd]
    rcases vinv_cases L with ⟨v, rfl⟩ | ⟨k, rfl⟩ | rfl
    · rw [vinv_oldLabel]
      show incidenceCount _ (π.oldSourceVertex ψ.data (ψ.ident.vertex.symm v).1) _ = _
      rw [hl.old, lab_zOf hπ hl i, Equiv.apply_symm_apply]
      exact (coreIncidence_castSucc_castAdd (mOld v) i).symm
    · rw [vinv_tripodMark]
      show incidenceCount _ (π.markSourceVertex ψ.data k) _ = _
      rw [hl.mark, lab_zOf hπ hl i]
      exact (coreIncidence_castSucc_castAdd (markVertex n k) i).symm
    · rw [vinv_centre, coreIncidence_centre_castAdd]
      exact incidenceCount_gluedPath_newVertex hπ _ _
  | right k =>
    rw [show Fin.natAdd (p + 1 + 1 + 1) k = legSlot p k from rfl, rinv_legSlot]
    unfold coreIncidence
    rw [Dichotomy.tripodCore_tail_legSlot, Dichotomy.tripodCore_head_legSlot]
    rcases vinv_cases L with ⟨v, rfl⟩ | ⟨k', rfl⟩ | rfl
    · rw [vinv_oldLabel, if_neg, if_neg]
      · exact incidenceCount_hp_old hπ _ k
      · intro h
        have := congrArg Fin.val h
        simp only [tripodMark, markVertex, oldLabel, Fin.val_castSucc] at this
        omega
      · intro h
        have := congrArg Fin.val h
        simp only [centre, oldLabel, Fin.val_castSucc, Fin.val_last] at this
        omega
    · rw [vinv_tripodMark, if_neg (Dichotomy.centre_ne_tripodMark k')]
      show incidenceCount _ (π.markSourceVertex ψ.data k') _ = _
      rw [incidenceCount_hp_mark hπ]
      by_cases hkk : k' = k
      · rw [if_pos hkk, if_pos (by rw [hkk])]
      · rw [if_neg hkk, if_neg (fun h ↦ hkk (Dichotomy.tripodMark_injective h).symm)]
    · rw [vinv_centre, if_pos rfl, if_neg (Dichotomy.centre_ne_tripodMark k).symm]
      exact incidenceCount_hp_centre hπ k

end Incidence

/-! ## 4. The core identification -/

section Ident

variable {ψ : FibreMember core yG (2 + 2)} {π : Placement ψ.target (2 + 2)}
  (hπ : π.NonDangling ψ.data) {lab : StablePath (glueDatum ψ.data π) → Fin (p + 1 + 1 + 1)}
  (hl : PieceLabels s ψ hπ lab)

/-- **The core identification from the piece labels.** -/
def identOf : CoreIdentification (tripodCore core s) (glueDatum ψ.data π) where
  vertex := (Equiv.ofBijective (vinv hπ) (vinv_bijective hπ)).symm
  row := (Equiv.ofBijective (rinv hπ hl) (rinv_bijective hπ hl)).symm
  incidence b j := by
    rw [Equiv.symm_symm, Equiv.ofBijective_apply]
    obtain ⟨L, rfl⟩ := vinv_surjective hπ b
    have hL : (Equiv.ofBijective (vinv hπ) (vinv_bijective hπ)).symm (vinv hπ L) = L :=
      (Equiv.ofBijective (vinv hπ) (vinv_bijective hπ)).symm_apply_apply L
    rw [hL]
    exact incidence_vinv_rinv hπ hl L j

theorem identOf_vertex_symm (L : Fin (n + 1 + 1 + 1 + 1)) :
    (identOf hπ hl).vertex.symm L = vinv hπ L := rfl

theorem identOf_row_gluedPath (z : NonDanglingEdge (refine₃ ψ.data π)) :
    (identOf hπ hl).row
        (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) =
      Fin.castAdd 3 (lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1
        ψ.fullDim.targetConnected hπ z)) := by
  show (Equiv.ofBijective (rinv hπ hl) (rinv_bijective hπ hl)).symm _ = _
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, rinv_castAdd]
  exact (hl.inj (zOf hπ hl _) z (lab_zOf hπ hl _)).symm

theorem identOf_row_hp (k : Fin 3) : (identOf hπ hl).row (hp ψ π k) = legSlot p k := by
  show (Equiv.ofBijective (rinv hπ hl) (rinv_bijective hπ hl)).symm _ = _
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, rinv_legSlot]

theorem refl_sourceVertexEquiv {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (x : E.SourceVertex) :
    (GeometricDatumIso.refl E).sourceVertexEquiv x = x := Subtype.ext rfl

theorem refl_sourceEdgeEquiv {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (x : E.SourceEdge) :
    (GeometricDatumIso.refl E).sourceEdgeEquiv x = x := Subtype.ext rfl

include hl in
/-- **The glued labels** of the identification from the piece labels. -/
theorem gluedLabels_identOf :
    GluedLabels s ψ π (identOf hπ hl) (GeometricDatumIso.refl _) := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  refine ⟨fun b ↦ ?_, fun k ↦ ?_, ?_, fun e ↦ ?_, fun k ↦ ?_⟩
  · rw [identOf_vertex_symm, refl_sourceVertexEquiv, vinv_oldLabel, Equiv.symm_apply_apply]
    rfl
  · rw [identOf_vertex_symm, refl_sourceVertexEquiv, vinv_tripodMark]
    rfl
  · rw [identOf_vertex_symm, vinv_centre]
    have : (GeometricDatumIso.refl (glueDatum ψ.data π)).sourceVertexEquiv.symm
        (centreBV (ψ := ψ) (π := π)).1 = (centreBV (ψ := ψ) (π := π)).1 := by
      rw [Equiv.symm_apply_eq, refl_sourceVertexEquiv]
    rw [this]
    exact congrArg Prod.snd (newVertex_val ψ.data π _)
  · let z₀ : NonDanglingEdge (refine₃ ψ.data π) := ⟨firstPiece₃ ψ.data π e.1, by
      rw [isDangling_iff₃ ψ.data π hD, parentSE₃_firstPiece₃]; exact e.2⟩
    refine ⟨gluedND hπ z₀, ?_, ?_⟩
    · rw [refl_sourceEdgeEquiv]
      exact liftSE_firstPiece₃ ψ.data π e.1
    · show mergeSlot s ((identOf hπ hl).row
        (CutPaths.gluedPath ψ.data π hD hT hπ z₀)) = _
      rw [identOf_row_gluedPath, mergeSlot_castAdd, hl.merge]
      have hp₀ : parentND₃ z₀ = e := Subtype.ext (parentSE₃_firstPiece₃ ψ.data π e.1)
      rw [hp₀]
  · refine ⟨Onto.legND (π := π) hD hT k, ?_, identOf_row_hp hπ hl k⟩
    rw [refl_sourceEdgeEquiv]
    rfl

include hl in
/-- **The core identification with the glued labels, from the piece labels**, carrying each glued
old path to its label. -/
theorem exists_ident_of_pieceLabels :
    ∃ ident : CoreIdentification (tripodCore core s) (glueDatum ψ.data π),
      GluedLabels s ψ π ident (GeometricDatumIso.refl _) ∧
      ∀ z, ident.row
          (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z) =
        Fin.castAdd 3 (lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1
          ψ.fullDim.targetConnected hπ z)) :=
  ⟨identOf hπ hl, gluedLabels_identOf hπ hl, identOf_row_gluedPath hπ hl⟩

end Ident

end PieceIdent

end GenusSixExistence.Tripod.Gluing

end
