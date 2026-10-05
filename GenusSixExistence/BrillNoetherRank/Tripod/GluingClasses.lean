module

public import GenusSixExistence.BrillNoetherRank.Tripod.Gluing
public import GenusSixExistence.BrillNoetherRank.Tripod.GluingExtend
public import GenusSixExistence.BrillNoetherRank.Tripod.GluingOnto
public import GenusSixExistence.BrillNoetherRank.Tripod.GluingWellDefined
public import GenusSixExistence.BrillNoetherRank.Tripod.GluingPositivity

@[expose] public section

/-!
# The gluing bijection on classes

The class-level half of the gluing bijection: the labelled identification `exists_gluedIdent`,
(b) a gluing is glued, (c) the multiplicity, (d)/(e) and well-definedness, (f) the bijection on
classes, and (g) `exists_gluing`, the statement `Classification.exists_gluing` consumes. The
letters are those of the table in `Gluing.lean`. Prose proof:
`Research/genus-six-brill-noether-rank.md`, §5.2 (Positivity and change-minimality) and §5.5 (The
bijection); section and statement numbers in this file refer to that note.

## The lemmas

| lemma | content | from |
|---|---|---|
| `exists_gluedIdent_closed` | the glued labels at the actual placement, coordinates `≥ 0` at `y` | `GluingPositivity.exists_pieceLabels` (in `GluingLayout`/`GluingLayoutStages`: the actual positions, labels of the glued old paths by the pieces of the marked core with their ends, and the geometric lengths of `T₃` on the old rows); the core identification (`GluingPieceIdent`), the legs, the arms and long legs |
| `exists_gluedIdent` | the same, open at `y` | the line above and `hgen` (no glued frame has a zero coordinate) |
| `nonempty_iso_of_isGluingOf_self` | the placement is forced: open gluings of one member over a loopless `G̃` are isomorphic | `GluingWellDefined.placement_forced` (when no mark sits on a loop slot of `G̃`, the placements differ only by sheets in one block), with the change of sheet and the comparison at one placement there. Looplessness of `G̃` (`hloop`, from `TripodModel.loopless`) is a hypothesis up to `exists_gluing` |
| `nonempty_iso_of_isGluingOf` | well defined on classes | the line above and `GluingExtend.exists_gluing_transport` |
| `nonempty_iso_of_isGluingOf_iso` | injective on classes | `GluingInjective.nonempty_memberIso_of_glued` |
| `exists_isGluingOf_of_memberIsGlued` | onto the open glued classes | `GluingOnto.exists_glueShape` (the shape) and `GluingOnto.exists_isGluingOf_of_shape` (the deletion) |

The two class-level inputs rest on three modules: `GluingPositivity` (coordinates from lengths;
the legs, the arms and their positivity), `GluingPieceIdent` (the core identification of a glued
datum from labels of its pieces) and `GluingWellDefined` (a change of sheet within a block; two
gluings at one placement agree).

The machinery is in six modules. `GluingRestrict` restricts an isomorphism of glued data that
fixes the arms and the new sheet to the old sheets (`restrict₃`) and un-refines it at the marks
(`exists_unrefine₃`). `GluingInjective` reads the labels: the arms go to the arms because mark `k`
meets leg `k` once, the new sheet goes to the new sheet from the centre, and every piece of an old
edge carries the merged label of its parent (`pieceLabel_eq`). `GluingExtend` goes the other way:
an isomorphism `D ≅ D'` extends through the three stages of `glueDatum` (`glueIso`), and a gluing
moves along an isomorphism of members (`exists_gluing_transport`). `GluingOnto`,
`GluingOntoIdent` and `GluingOntoOpen` are the onto direction: from the shape of a gluing, the
deleted datum is a member (full-dimensional, identified with `G̃` with the glued labels, open).
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count (IsLeafVertex leafVertices leafCount)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion


section Bijection

open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph} {d : ℕ}

/-- **The glued labels, closed at `y`** (§5.2, positivity; §5.5, well-definedness; without the
genericity): the placement at the actual positions of the marks, and the core identification
with `Γ̃`; the coordinates of the glued frame at `y` are the geometric lengths, so they are
non-negative. -/
theorem exists_gluedIdent_closed {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (hlong : LongLegs s y) (ψ : FibreMember core (baseRequest s y) (2 + 2)) (hψ : ψ.Open) :
    ∃ π : Placement ψ.target (2 + 2), π.NonDangling ψ.data ∧
      ∃ ident : CoreIdentification (tripodCore core s) (glueDatum ψ.data π),
        GluedLabels s ψ π ident (GeometricDatumIso.refl _) ∧
        ∀ (fd : FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)))
          (col : Fin (p + 1 + 1 + 1 + 3)),
          0 ≤ (⟨_, _, fd, ident⟩ : Frame (tripodCore core s) (3 + 2)).coordsAt y col := by
  -- §5.2, in `GluingPositivity`: the coordinates of every glued frame are any
  -- target lengths realising `y` along its stable paths (`coordsAt_eq_of_realises`). The
  -- lengths are the geometric lengths of the edges of `T₃` at the actual placement
  -- (`exists_pieceLabels`, in `GluingLayoutStages`: the actual positions of the marks,
  -- and the labels of the glued old paths by the pieces of the marked core), with the glued labels
  -- (`PieceIdent.exists_ident_of_pieceLabels`), extended to the arms by the leg rows
  -- (`pathSum_hairpinPath`); the arms are positive by long legs: a leg at zero arm length
  -- is at most the length of `T₃`, which is at most `4 L(G̃)` (`pathSum_hairpinPath_le`,
  -- `sum_w₃_le`, `sum_g_le`).
  exact Positivity.exists_gluedIdent_closed hpos hlong ψ hψ

/-- **The glued labels, open at `y`** (§5.2, positivity; §5.5, well-definedness): the
placement at the actual positions of the marks, and the core identification with `Γ̃`. The
coordinates are non-negative (`exists_gluedIdent_closed`) and, `y` being general for `Γ̃`, none is
zero (module docstring of `Gluing.lean`, (g)). -/
theorem exists_gluedIdent {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (hgen : StepSupplyReduction.GeneralRequest (tripodCore core s) (3 + 2) y)
    (hlong : LongLegs s y) (ψ : FibreMember core (baseRequest s y) (2 + 2)) (hψ : ψ.Open) :
    ∃ π : Placement ψ.target (2 + 2), π.NonDangling ψ.data ∧
      ∃ ident : CoreIdentification (tripodCore core s) (glueDatum ψ.data π),
        GluedLabels s ψ π ident (GeometricDatumIso.refl _) ∧
        ∀ fd : FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3)),
          Frame.OpenAt (⟨_, _, fd, ident⟩ : Frame (tripodCore core s) (3 + 2)) y := by
  obtain ⟨π, hπ, ident, hL, hclosed⟩ := exists_gluedIdent_closed hpos hlong ψ hψ
  exact ⟨π, hπ, ident, hL, fun fd col ↦ lt_of_le_of_ne (hclosed fd col) (Ne.symm (hgen _ col))⟩

/-- **(a): every open member over `G̃` has an open gluing** at an admissible request. -/
theorem exists_open_isGluingOf {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (hgen : StepSupplyReduction.GeneralRequest (tripodCore core s) (3 + 2) y)
    (hlong : LongLegs s y) (ψ : FibreMember core (baseRequest s y) (2 + 2)) (hψ : ψ.Open) :
    ∃ φ : FibreMember (tripodCore core s) y (3 + 2), φ.Open ∧ IsGluingOf s ψ φ := by
  obtain ⟨π, hπ, ident, hLabels, hOpen⟩ := exists_gluedIdent hpos hgen hlong ψ hψ
  obtain ⟨fd⟩ := nonempty_fullDim_glueDatum ψ π hπ
  refine ⟨Frame.member ⟨_, _, fd, ident⟩ y, hOpen fd, π, hπ, GeometricDatumIso.refl _, hLabels⟩

/-! ## (b) A gluing is glued -/

/-- **(b): a gluing is glued** (§3.3): the leg at each mark starts up its arm, a leaf edge
of the target. Read off the glued labels: the arm in the sheet of the mark lies on leg `k`, is
incident to the mark, and ends at a tip of valency one. -/
theorem memberIsGlued_of_isGluingOf {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    {ψ : FibreMember core (baseRequest s y) (2 + 2)}
    {φ : FibreMember (tripodCore core s) y (3 + 2)} (h : IsGluingOf s ψ φ) :
    MemberIsGlued φ := by
  obtain ⟨π, -, iso, hL⟩ := h
  intro k
  obtain ⟨e, he, hrow⟩ := hL.leg k
  refine ⟨e, hrow, ?_, ?_⟩
  · show Incident φ.data e.1 (φ.ident.vertex.symm (tripodMark n k)).1
    rw [he, hL.mark k, iso.incident_map_iff]
    left
    refine (sourceEnds_sourceEdge_fst _ _ _).trans ?_
    exact congrArg (fun v ↦ (glueDatum ψ.data π).sourceEndpoint v (π.sheet k).castSucc)
      (congrArg Prod.fst (π.armEdge_ends k))
  · show IsLeafEdge φ.target e.1.1.1
    rw [he]
    refine (isLeafEdge_map iso (π.armEdge k)).mpr (Or.inr ?_)
    exact (congrArg (vertex_degree π.T₆) (congrArg Prod.snd (π.armEdge_ends k))).trans
      (π.vertex_degree_tipTarget k)

/-! ## (c) The multiplicity -/

/-- **(c): the gluing preserves `|Mult|`** (§5.4):
`D_ψ ∏ a_k · 8 |det A_ψ| / ∏ a_k / 2^(l(T)+3) = D_ψ |det A_ψ| / 2^l(T)`. -/
theorem fdAbsMult_glueDatum {yG : Fin p → ℚ} (ψ : FibreMember core yG (2 + 2))
    (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
    (fd : FullDimensionalSourcePresentation (glueDatum ψ.data π) (Fin (p + 1 + 1 + 1 + 3))) :
    fdAbsMult fd = fdAbsMult ψ.fullDim := by
  have h1 := abs_det_glueDatum ψ π hπ fd
  have h2 := denominatorProduct_glueDatum ψ π hπ fd
  show |signedMult fd.labelling.presentation| = |signedMult ψ.fullDim.labelling.presentation|
  unfold signedMult
  rw [h2, π.leafCount_T₆, abs_mul, abs_mul, abs_div, abs_div, Nat.abs_cast, Nat.abs_cast,
    abs_pow, abs_pow, abs_two]
  rw [FibreMember.matrix] at h1
  push_cast
  rw [pow_add, show ((2 : ℚ) ^ 3) = 8 by norm_num]
  calc (denominatorProduct ψ.fullDim.labelling.presentation : ℚ) *
          (∏ k, (π.markIndex ψ.data k : ℚ)) / (2 ^ leafCount ψ.target * 8) *
        |(GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).det| =
        (denominatorProduct ψ.fullDim.labelling.presentation : ℚ) / 2 ^ leafCount ψ.target *
          ((|(GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).det| *
            ∏ k, (π.markIndex ψ.data k : ℚ)) / 8) := by ring
    _ = _ := by rw [h1]; ring

/-- The multiplicity of a gluing, as the natural number `multNat` reads. -/
theorem oddMult_eq_of_isGluingOf {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    {ψ : FibreMember core (baseRequest s y) (2 + 2)}
    {φ : FibreMember (tripodCore core s) y (3 + 2)} (h : IsGluingOf s ψ φ) :
    φ.oddMult = ψ.oddMult := by
  obtain ⟨π, hπ, iso, -⟩ := h
  have hAbs : φ.absMult = ψ.absMult := by
    show fdAbsMult φ.fullDim = fdAbsMult ψ.fullDim
    rw [GeometricMultiplicity.fdAbsMult_eq_of_datumIso iso
      (GeometricMultiplicity.transportFullDim iso.symm φ.fullDim) φ.fullDim]
    exact fdAbsMult_glueDatum ψ π hπ _
  rw [FibreMember.absMult_eq_oddMult, FibreMember.absMult_eq_oddMult] at hAbs
  exact_mod_cast hAbs

/-! ## (d), (e) and well-definedness -/

/-- **The placement is forced** (§5.5, well-definedness): two open gluings of one member over
`G̃` are isomorphic over `Γ̃`. This is the content of well-definedness; the transport along
`ψ ≅ ψ'` is `GluingExtend.exists_gluing_transport`. -/
theorem nonempty_iso_of_isGluingOf_self (hloop : ∀ i, core.tail i ≠ core.head i)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} {ψ : FibreMember core (baseRequest s y) (2 + 2)}
    {φ φ' : FibreMember (tripodCore core s) y (3 + 2)} (hφ : φ.Open) (hφ' : φ'.Open)
    (h : IsGluingOf s ψ φ) (h' : IsGluingOf s ψ φ') : Nonempty (GeometricMemberIso φ φ') := by
  -- §5.5, in `GluingWellDefined`: when no mark sits on
  -- a loop slot of `G̃` the placements agree up to a change of sheet in the block of each mark's
  -- source edge (`placement_forced`, in `GluingLayoutStages`), which moves the glued labels
  -- along an isomorphism of glued data (`gluedLabels_sheetIso`); two gluings at one
  -- placement are then isomorphic over `Γ̃` (`nonempty_iso_of_samePlacement`: the glued
  -- labels pin every vertex label, every leg, and every G-slot through its merged label and its
  -- ends). No mark sits on a loop slot, `G̃` being loopless (`marksOffLoops_of_loopless`).
  exact WellDefined.nonempty_iso_of_isGluingOf_self hloop hφ hφ' h h'

/-- **Well defined on classes**: gluings of isomorphic members over `G̃` are isomorphic over `Γ̃`,
when open. -/
theorem nonempty_iso_of_isGluingOf (hloop : ∀ i, core.tail i ≠ core.head i)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} {ψ ψ' : FibreMember core (baseRequest s y) (2 + 2)}
    {φ φ' : FibreMember (tripodCore core s) y (3 + 2)} (hφ : φ.Open) (hφ' : φ'.Open)
    (h : IsGluingOf s ψ φ) (h' : IsGluingOf s ψ' φ')
    (hψ : Nonempty (GeometricMemberIso ψ ψ')) : Nonempty (GeometricMemberIso φ φ') := by
  -- §5.5: move the gluing of `ψ'` to a gluing of `ψ` along
  -- `ψ ≅ ψ'` (`GluingExtend.exists_gluing_transport`: push the placement forward, compose with the
  -- glued isomorphism `glueIso`), then the placement is forced (`nonempty_iso_of_isGluingOf_self`).
  obtain ⟨m⟩ := hψ
  obtain ⟨π', hπ', iso', hL'⟩ := h'
  exact nonempty_iso_of_isGluingOf_self hloop hφ hφ' h
    (exists_gluing_transport (d := 2 + 2) m.symm hπ' iso' hL')

/-- **(d): injective on classes**: if two gluings are isomorphic over `Γ̃`, the members they glue
are isomorphic over `G̃`. -/
theorem nonempty_iso_of_isGluingOf_iso {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
    {ψ ψ' : FibreMember core (baseRequest s y) (2 + 2)}
    {φ φ' : FibreMember (tripodCore core s) y (3 + 2)}
    (h : IsGluingOf s ψ φ) (h' : IsGluingOf s ψ' φ')
    (hφ : Nonempty (GeometricMemberIso φ φ')) : Nonempty (GeometricMemberIso ψ ψ') := by
  -- §5.5: restrict the composite isomorphism of glued data to the old
  -- sheets and un-refine at the marks (`GluingInjective.nonempty_memberIso_of_glued`).
  obtain ⟨π, hπ, iso, hL⟩ := h
  obtain ⟨π', hπ', iso', hL'⟩ := h'
  obtain ⟨m⟩ := hφ
  exact nonempty_memberIso_of_glued (d := 2 + 2) hπ hπ' iso iso' hL hL' m

/-- **(e): onto the open glued classes**: every open glued member over `Γ̃`, at long legs, is the
gluing of an open member over `G̃`. -/
theorem exists_isGluingOf_of_memberIsGlued (hcubic : core.Cubic) (hconn : core.Connected)
    (hgenus : p + 1 - n = 6) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (hlong : LongLegs s y) (φ : FibreMember (tripodCore core s) y (3 + 2)) (hφ : φ.Open)
    (hGlued : MemberIsGlued φ) :
    ∃ ψ : FibreMember core (baseRequest s y) (2 + 2), ψ.Open ∧ IsGluingOf s ψ φ := by
  -- §5.5, the onto step, in two steps (`GluingOnto`): the
  -- shape, `φ ≅ glue(D, π)` with the marks, the centre and the legs in place
  -- (`Onto.exists_glueShape`), and the deletion, `D` is the datum of an open member over `G̃`
  -- whose gluing is `φ` (`Onto.exists_isGluingOf_of_shape`).
  obtain ⟨T, D, π, hD, hπ, Ξ, hS⟩ := Onto.exists_glueShape hcubic hconn hgenus hpos hlong φ hφ hGlued
  exact Onto.exists_isGluingOf_of_shape hcubic hconn hφ D π hD hπ Ξ hS

/-! ## (f) The bijection on classes -/

/-- **(f): the gluing bijection at one admissible request**, from (a)--(e). Choose a
representative of each open class over `G̃` and an open gluing of it; the class of the gluing is
open and glued (b), has the same multiplicity (c), depends only on the class (well defined),
determines it (d), and every open glued class arises (e). -/
theorem exists_gluingEquiv (hcubic : core.Cubic) (hconn : core.Connected)
    (hloop : ∀ i, core.tail i ≠ core.head i) (hgenus : p + 1 - n = 6) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (hgen : StepSupplyReduction.GeneralRequest (tripodCore core s) (3 + 2) y)
    (hlong : LongLegs s y) :
    ∃ e : {c : GeometricFibre core (baseRequest s y) (2 + 2) // c.Open} ≃
        {c : GeometricFibre (tripodCore core s) y (3 + 2) // c.Open ∧ ClassIsGlued c},
      ∀ c, (e c).1.multNat = c.1.multNat := by
  classical
  -- a representative of each class over `G̃`
  have hrep (c : GeometricFibre core (baseRequest s y) (2 + 2)) :
      ∃ ψ, GeometricFibre.cls ψ = c := GeometricFibre.cls_surjective c
  choose rep hrep using hrep
  have hglue (c : {c : GeometricFibre core (baseRequest s y) (2 + 2) // c.Open}) :
      ∃ φ : FibreMember (tripodCore core s) y (3 + 2), φ.Open ∧ IsGluingOf s (rep c.1) φ := by
    refine exists_open_isGluingOf hpos hgen hlong (rep c.1) ?_
    have := c.2
    rw [← hrep c.1] at this
    exact this
  choose glue hglueOpen hglueRel using hglue
  let F : {c : GeometricFibre core (baseRequest s y) (2 + 2) // c.Open} →
      {c : GeometricFibre (tripodCore core s) y (3 + 2) // c.Open ∧ ClassIsGlued c} :=
    fun c ↦ ⟨GeometricFibre.cls (glue c), hglueOpen c,
      glue c, rfl, memberIsGlued_of_isGluingOf (hglueRel c)⟩
  have hinj : Function.Injective F := by
    intro c₁ c₂ hF
    have hcls : GeometricFibre.cls (glue c₁) = GeometricFibre.cls (glue c₂) :=
      congrArg Subtype.val hF
    have hiso := nonempty_iso_of_isGluingOf_iso (hglueRel c₁) (hglueRel c₂)
      (GeometricFibre.cls_eq_cls_iff.mp hcls)
    apply Subtype.ext
    rw [← hrep c₁.1, ← hrep c₂.1]
    exact GeometricFibre.cls_eq_cls_iff.mpr hiso
  have hsurj : Function.Surjective F := by
    rintro ⟨c', hOpen, φ, hφc, hφGlued⟩
    subst hφc
    have hφOpen : φ.Open := hOpen
    obtain ⟨ψ, hψOpen, hψφ⟩ :=
      exists_isGluingOf_of_memberIsGlued hcubic hconn hgenus hpos hlong φ hφOpen hφGlued
    refine ⟨⟨GeometricFibre.cls ψ, hψOpen⟩, ?_⟩
    apply Subtype.ext
    show GeometricFibre.cls (glue ⟨GeometricFibre.cls ψ, hψOpen⟩) = GeometricFibre.cls φ
    have hrepψ : Nonempty (GeometricMemberIso (rep (GeometricFibre.cls ψ)) ψ) :=
      GeometricFibre.cls_eq_cls_iff.mp (hrep _)
    exact GeometricFibre.cls_eq_cls_iff.mpr (nonempty_iso_of_isGluingOf hloop
      (hglueOpen _) hφOpen (hglueRel _) hψφ hrepψ)
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun c ↦ ?_⟩
  show (GeometricFibre.cls (glue c)).multNat = c.1.multNat
  have hc := congrArg GeometricFibre.multNat (hrep c.1)
  rw [GeometricFibre.multNat_cls] at hc
  rw [GeometricFibre.multNat_cls, oddMult_eq_of_isGluingOf (hglueRel c), hc]

/-! ## (g) The family `B` -/

/-- **The gluing bijection** (Theorem 5.1; §3.3), in the
form of `Classification.exists_gluing`. The family `B` is empty: the mark condition (iv) of
§6.3 is implied by the generality (ii) for `Γ̃` (module docstring, (g)). -/
theorem exists_gluing (hcubic : core.Cubic) (hconn : core.Connected)
    (hloop : ∀ i, core.tail i ≠ core.head i) (hgenus : p + 1 - n = 6) (s : MarkSlots p) :
    ∃ B : Finset (Fin (p + 1 + 1 + 1 + 3) → ℚ), (∀ w ∈ B, w ≠ 0) ∧
      ∀ y, Admissible core s B y →
        ∃ e : {c : GeometricFibre core (baseRequest s y) (2 + 2) // c.Open} ≃
            {c : GeometricFibre (tripodCore core s) y (3 + 2) // c.Open ∧ ClassIsGlued c},
          ∀ c, (e c).1.multNat = c.1.multNat :=
  ⟨∅, by simp, fun _ hy ↦ exists_gluingEquiv hcubic hconn hloop hgenus hy.1 hy.2.1 hy.2.2.2.2⟩

end Bijection

end GenusSixExistence.Tripod.Gluing

end
