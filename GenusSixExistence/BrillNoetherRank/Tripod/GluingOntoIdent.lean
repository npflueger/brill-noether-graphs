module

public import GenusSixExistence.BrillNoetherRank.Tripod.GluingExtend

@[expose] public section

/-!
# The core identification of the deletion

The proof of `GluingOnto.exists_ident_of_shape`: given
a connected datum `D` and a placement `π` on its core, and an isomorphism
`Ξ : glueDatum D π ≅ φ.data` to a member over `Γ̃` that carries the marks, the centre and the legs
(`ShapeLabels`), the stable graph of `D` is identified with `G̃`, with the glued labels
(`exists_ident_of_shape_aux`). Prose proof: `Research/genus-six-brill-noether-rank.md`, §5.5
(The bijection, the onto step, "Identification"). Numbered sections below are those of this file.

* **Walking** (section 1, `anc_stablePath_eq_of_gluedPath_eq`): the ancestors of two old edges on
  one glued path lie on one stable path of `D`. Through a passage of the glued datum off the marks
  the two edges are consecutive in `refine₃ D π`, and through a passage of a refinement the
  parents are consecutive or equal. This direction needs no count.
* **The vertices of the glued datum** (section 3): a surviving edge at an old vertex is old or the
  arm at a mark; a new edge meets a branch vertex only at a mark (by its arm) or in the new sheet;
  the new sheet has one branch vertex, the centre (section 5, `newVertex_eq_centre`).
* **Merged labels** (section 4, `glabel`): the slot of `G̃` of a glued path. The two glued halves at
  a mark carry one merged label (`glabel_eq_of_mark`, as in `GluingInjective`), so merging back at
  the marks keeps it (`glabel_cut₀_anc`); a glued old path is never a leg
  (`exists_glabel_eq_some`), and every G-slot of `Γ̃` is a glued old path
  (`exists_gluedPath_eq_gSlot`).
* **Path ends** (section 6, `hasPathEnds_of_shape`, for connected `G̃`): an endless stable path of
  `D` would have its glued pieces ending only at marks on it, and those marks would be cut off from
  the rest of the connected marked core.
* **Rows, vertices, incidences** (sections 7--10): the row label `prow` is onto and, by the
  stable-path count of the glued datum, a bijection; the vertex label `vmap` is a bijection onto the
  old vertices of `Γ̃`; and the incidences match (`incidenceCount_eq`) by an injection into the
  edges of `φ` with the merged label, both sides summing to three (`sum_mergeSlot_coreIncidence`:
  the pieces of a slot meet an old vertex as the slot does).
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

namespace Onto

section Shape

variable {n p : ℕ} {core : Core n p}

/-- **The clauses of `GluedLabels` that do not mention the member being glued**: through `iso`,
mark `k` is the source vertex of the glued datum over its mark image in the sheet of the mark,
the centre lies in the new sheet, and the arm of leg `k` in the sheet of mark `k` lies on leg
`k`. For a member `ψ` with `ψ.data = D` these are the fields `mark`, `centre` and `leg` of
`GluedLabels s ψ π ident' iso`. -/
structure ShapeLabels (s : MarkSlots p) {T : CFGraph} {d : ℕ} (D : GluingDatum T d)
    (π : Placement T d) {target' : CFGraph.{0}} {data' : GluingDatum target' (d + 1)}
    (ident' : CoreIdentification (tripodCore core s) data')
    (iso : GeometricDatumIso (glueDatum D π) data') : Prop where
  mark : ∀ k, (ident'.vertex.symm (tripodMark n k)).1 =
    iso.sourceVertexEquiv (π.markSourceVertex D k)
  centre : (iso.sourceVertexEquiv.symm (ident'.vertex.symm (centre n)).1).1.2 = Fin.last d
  leg : ∀ k, ∃ e' : NonDanglingEdge data',
    e'.1 = iso.sourceEdgeEquiv (π.armSourceEdge D k) ∧ ident'.row e'.stablePath = legSlot p k

end Shape

/-! ## 1. Walking along a glued path -/

section Walk

variable {T : CFGraph} {d : ℕ}

/-- **Through a passage of a refinement the parents lie on one stable path**: at an old vertex they
are consecutive (or equal), at a fresh vertex they are equal. -/
theorem parent_stablePath_eq_of_consecutive (D : GluingDatum T d) (t : T.edges) (hD : D.Connected)
    {y y' : NonDanglingEdge (refineDatum D t)} (h : Consecutive (refineDatum D t) y y') :
    (Refine.parentND D t hD y).stablePath = (Refine.parentND D t hD y').stablePath := by
  obtain ⟨-, u, hy, hy', hval⟩ := h
  rcases Refine.sourceVertex_cases D t u with ⟨v, rfl⟩ | ⟨i, hi, rfl⟩
  · have hv : nonDanglingValency D v = 2 := by
      rwa [Refine.nonDanglingValency_oldSV D t hD] at hval
    have h1 := ((Refine.incident_oldSV_iff D t y.1 v).mp hy).1
    have h2 := ((Refine.incident_oldSV_iff D t y'.1 v).mp hy').1
    by_cases heq : Refine.parentND D t hD y = Refine.parentND D t hD y'
    · rw [heq]
    · exact stablePath_eq_of_consecutive ⟨heq, v, h1, h2, hv⟩
  · have hp : ∀ w : (refineDatum D t).SourceEdge, Incident _ w (Refine.freshSV D t i hi) →
        Refine.parentSE D t w = ⟨(t, i), hi⟩ := by
      intro w hw
      rcases (Refine.incident_freshSV_iff D t i hi w).mp hw with rfl | rfl
      · exact Refine.parentSE_halfNone D t i hi
      · exact Refine.parentSE_halfSome D t i hi
    have heq : Refine.parentND D t hD y = Refine.parentND D t hD y' :=
      Subtype.ext ((hp _ hy).trans (hp _ hy').symm)
    rw [heq]

/-- **One stable path of a refinement lies over one stable path of `D`.** -/
theorem parent_stablePath_eq (D : GluingDatum T d) (t : T.edges) (hD : D.Connected)
    {y y' : NonDanglingEdge (refineDatum D t)} (h : y.stablePath = y'.stablePath) :
    (Refine.parentND D t hD y).stablePath = (Refine.parentND D t hD y').stablePath := by
  have := (eqvGen_iff_of_closed (property := fun w ↦
      (Refine.parentND D t hD w).stablePath = (Refine.parentND D t hD y).stablePath)
    (fun a b hab ha ↦ (parent_stablePath_eq_of_consecutive D t hD hab).symm.trans ha)
    ((stablePath_eq_iff _ _).mp h)).mp rfl
  exact this.symm

/-- The ancestors of two edges on one stable path of `refine₃ D π` lie on one stable path of
`D`. -/
theorem anc_stablePath_eq (D : GluingDatum T d) (π : Placement T d) (hD : D.Connected)
    {z z' : NonDanglingEdge (refine₃ D π)} (h : z.stablePath = z'.stablePath) :
    (CutPaths.anc D π hD z).stablePath = (CutPaths.anc D π hD z').stablePath :=
  parent_stablePath_eq D π.edge₀ hD (parent_stablePath_eq _ π.edge₁ (π.refine₁_connected D hD)
    (parent_stablePath_eq _ π.edge₂ (π.refine₂_connected D hD) h))

variable {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D)
include hD hT hπ

/-- The surviving edges of the glued datum at an old vertex of valency two, off the marks, are the
copies of consecutive edges of `refine₃ D π`. -/
theorem consecutive_of_liftND {z z' : NonDanglingEdge (refine₃ D π)}
    (h : Consecutive (glueDatum D π) (CutPaths.liftND D π hD hT hπ z)
      (CutPaths.liftND D π hD hT hπ z')) :
    Consecutive (refine₃ D π) z z' := by
  obtain ⟨hne, w, hw, hw', hval⟩ := h
  rcases sourceVertex_cases_glue D π w with ⟨x, rfl⟩ | ⟨u, rfl⟩ | ⟨k, j, rfl⟩
  · refine ⟨fun h' ↦ hne (by rw [h']), x, (incident_liftSE_oldVertex₃ D π _ x).mp hw,
      (incident_liftSE_oldVertex₃ D π _ x).mp hw', ?_⟩
    rw [nonDanglingValency_oldVertex₃ D π hD hT hπ] at hval
    by_cases hm : ∃ k, x = markR₃ D π k
    · obtain ⟨k, rfl⟩ := hm
      rw [sum_mark_eq_one, markR₃, π.nonDanglingValency_markR₃ D hD hπ k] at hval
      omega
    · push Not at hm
      rw [sum_mark_eq_zero D π hm, add_zero] at hval
      exact hval
  · exact absurd hw (not_incident_liftSE_newVertex D π z.1 u)
  · exact absurd hw (not_incident_liftSE_tip D π z.1 k j)

/-- **Two old edges on one glued path lie on one stable path of `refine₃ D π`.** -/
theorem stablePath_eq_of_gluedPath_eq {z z' : NonDanglingEdge (refine₃ D π)}
    (h : CutPaths.gluedPath D π hD hT hπ z = CutPaths.gluedPath D π hD hT hπ z') :
    z.stablePath = z'.stablePath := by
  let Pr : NonDanglingEdge (glueDatum D π) → Prop := fun a ↦
    ∀ za, a = CutPaths.liftND D π hD hT hπ za → za.stablePath = z.stablePath
  have hclosed : ∀ a b : NonDanglingEdge (glueDatum D π), Consecutive _ a b → Pr a → Pr b := by
    intro a b hab ha zb hb
    have haOld : CutPaths.IsOld D π a :=
      CutPaths.isOld_of_consecutive hD hT hπ (consecutive_symm hab) ⟨zb.1, by rw [hb]; rfl⟩
    obtain ⟨za, rfl⟩ := CutPaths.eq_liftND_of_isOld hD hT hπ haOld
    rw [hb] at hab
    exact (stablePath_eq_of_consecutive (consecutive_of_liftND hD hT hπ hab)).symm.trans
      (ha za rfl)
  have h0 : Pr (CutPaths.liftND D π hD hT hπ z) := fun za hza ↦ by
    rw [CutPaths.liftND_injective D π hD hT hπ hza]
  exact ((eqvGen_iff_of_closed hclosed ((stablePath_eq_iff _ _).mp h)).mp h0 z' rfl).symm

/-- **Walking**: the ancestors of two old edges on one glued path lie on one stable path of
`D`. -/
theorem anc_stablePath_eq_of_gluedPath_eq {z z' : NonDanglingEdge (refine₃ D π)}
    (h : CutPaths.gluedPath D π hD hT hπ z = CutPaths.gluedPath D π hD hT hπ z') :
    (CutPaths.anc D π hD z).stablePath = (CutPaths.anc D π hD z').stablePath :=
  anc_stablePath_eq D π hD (stablePath_eq_of_gluedPath_eq hD hT hπ h)

end Walk

/-! ## 2. Vertices of `refine₃ D π` -/

section Refine₃

variable {T : CFGraph} {d : ℕ} {D : GluingDatum T d} {π : Placement T d}

/-- A vertex of `refine₃ D π` is an old vertex of `D`, or has valency at most two. -/
theorem lift₃V_or_le_two (hD : D.Connected) (x : (refine₃ D π).SourceVertex) :
    (∃ v, x = CutPaths.lift₃V D π v) ∨ nonDanglingValency (refine₃ D π) x ≤ 2 := by
  classical
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  rcases Refine.sourceVertex_cases _ π.edge₂ x with ⟨x₂, rfl⟩ | ⟨i, hi, rfl⟩
  · rcases Refine.sourceVertex_cases _ π.edge₁ x₂ with ⟨x₁, rfl⟩ | ⟨i, hi, rfl⟩
    · rcases Refine.sourceVertex_cases D π.edge₀ x₁ with ⟨v, rfl⟩ | ⟨i, hi, rfl⟩
      · exact Or.inl ⟨v, rfl⟩
      · right
        rw [Refine.nonDanglingValency_oldSV _ _ h₂, Refine.nonDanglingValency_oldSV _ _ h₁,
          Refine.nonDanglingValency_freshSV D _ hD]
        split_ifs <;> omega
    · right
      rw [Refine.nonDanglingValency_oldSV _ _ h₂, Refine.nonDanglingValency_freshSV _ _ h₁]
      split_ifs <;> omega
  · right
    rw [Refine.nonDanglingValency_freshSV _ _ h₂]
    split_ifs <;> omega

/-- An edge of `refine₃ D π` at an old vertex of `D` has its ancestor at that vertex. -/
theorem incident_anc_of_incident_lift₃V (hD : D.Connected) {z : NonDanglingEdge (refine₃ D π)}
    {v : D.SourceVertex} (h : Incident (refine₃ D π) z.1 (CutPaths.lift₃V D π v)) :
    Incident D (CutPaths.anc D π hD z).1 v :=
  ((Refine.incident_oldSV_iff D π.edge₀ _ v).mp ((Refine.incident_oldSV_iff _ π.edge₁ _ _).mp
    ((Refine.incident_oldSV_iff _ π.edge₂ _ _).mp h).1).1).1

/-- The parent of an edge at the fresh vertex of `x` is `x`. -/
theorem parentSE_of_incident_freshOf {t : T.edges} {x : D.SourceEdge} (hx : x.1.1 = t)
    {y : (refineDatum D t).SourceEdge} (h : Incident _ y (Refine.freshOf D t x hx)) :
    Refine.parentSE D t y = x := by
  rcases (Refine.incident_freshSV_iff D t _ _ y).mp h with rfl | rfl
  · rw [Refine.parentSE_halfNone]
    exact Subtype.ext (Prod.ext hx.symm rfl)
  · rw [Refine.parentSE_halfSome]
    exact Subtype.ext (Prod.ext hx.symm rfl)

/-- **The edges at a mark are pieces of the mark's edge.** -/
theorem anc_of_incident_markR₃ (hD : D.Connected) (hπ : π.NonDangling D) {k : Fin 3}
    {z : NonDanglingEdge (refine₃ D π)} (h : Incident (refine₃ D π) z.1 (markR₃ D π k)) :
    (CutPaths.anc D π hD z).1 = D.sourceEdge (π.parentEdge k) (π.sheet k) := by
  show Refine.parentSE D π.edge₀ (Refine.parentSE _ π.edge₁ (Refine.parentSE _ π.edge₂ z.1)) = _
  match k with
  | 0 =>
    rw [π.markR₃_zero_eq D hπ] at h
    have h1 := ((Refine.incident_oldSV_iff _ π.edge₁ _ _).mp
      ((Refine.incident_oldSV_iff _ π.edge₂ _ _).mp h).1).1
    exact parentSE_of_incident_freshOf _ h1
  | 1 =>
    rw [π.markR₃_one_eq D hD hπ] at h
    have h1 := ((Refine.incident_oldSV_iff _ π.edge₂ _ _).mp h).1
    rw [parentSE_of_incident_freshOf _ h1]
    exact Refine.parentSE_sourceEdge D π.edge₀ _ _
  | 2 =>
    rw [π.markR₃_two_eq D hD hπ] at h
    rw [parentSE_of_incident_freshOf _ h]
    show Refine.parentSE D π.edge₀ (Refine.parentSE _ π.edge₁
      ((refineDatum (refineDatum D π.edge₀) π.edge₁).sourceEdge π.edge₂ (π.sheet 2))) = _
    rw [Refine.parentSE_sourceEdge, Refine.parentSE_sourceEdge]
    rfl

end Refine₃

/-! ## 3. The vertices of the glued datum -/

section GlueVertices

variable {T : CFGraph} {d : ℕ} {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected)
  (hT : graph_connected T) (hπ : π.NonDangling D)
include hD hT

/-- **A surviving edge at an old vertex of the glued datum is old, or the arm at a mark.** -/
theorem isOld_or_arm_of_incident_oldVertex₃ (a : NonDanglingEdge (glueDatum D π))
    {x : (refine₃ D π).SourceVertex} (h : Incident (glueDatum D π) a.1 (oldVertex₃ D π x)) :
    CutPaths.IsOld D π a ∨ ∃ k, x = markR₃ D π k ∧ a.1 = π.armSourceEdge D k := by
  rcases sourceEdge_cases_glue D π a.1 with ⟨z', hz'⟩ | ⟨ε, hε⟩ | ⟨k, j, hkj⟩
  · exact Or.inl ⟨z', hz'⟩
  · rw [hε] at h
    exact absurd h (not_incident_newSE_oldVertex₃ D π ε x)
  · right
    have hnd := a.2
    rw [hkj] at hnd h
    obtain ⟨hk, i', hi', hrel⟩ := (incident_arm_oldVertex₃_iff D π k j x).mp h
    rcases ((hairpinShaped_nonDangling D π hD hT) k j).mp hnd with hj | hj
    · rw [hj] at hi'
      have hii : i' = π.sheet k := (Fin.castSucc_injective _ hi').symm
      rw [hii] at hrel
      refine ⟨k, (eq_markR₃_iff D π x k).mpr ⟨hk, hrel⟩, ?_⟩
      rw [hkj, hj]
      rfl
    · rw [hj] at hi'
      exact absurd hi'.symm (Fin.castSucc_lt_last i').ne

/-- **A new surviving edge meets a branch vertex only at a mark, as its arm, or in the new
sheet.** -/
theorem eq_mark_or_newVertex_of_not_isOld {a : NonDanglingEdge (glueDatum D π)}
    (ha : ¬ CutPaths.IsOld D π a) {w : (glueDatum D π).SourceVertex}
    (h : Incident (glueDatum D π) a.1 w) (h3 : 3 ≤ nonDanglingValency (glueDatum D π) w) :
    (∃ k, w = π.markSourceVertex D k ∧ a.1 = π.armSourceEdge D k) ∨
      ∃ u, w = newVertex D π u := by
  rcases sourceVertex_cases_glue D π w with ⟨x, rfl⟩ | ⟨u, rfl⟩ | ⟨k, j, rfl⟩
  · rcases isOld_or_arm_of_incident_oldVertex₃ hD hT a h with hold | ⟨k, rfl, hk⟩
    · exact absurd hold ha
    · exact Or.inl ⟨k, (markSourceVertex_eq D π k).symm, hk⟩
  · exact Or.inr ⟨u, rfl⟩
  · have := nonDanglingValency_tip_le D π hD hT k j
    omega

omit hD hT in
/-- An old vertex of the glued datum is not in the new sheet. -/
theorem oldVertex₃_sheet_ne_last (x : (refine₃ D π).SourceVertex) :
    (oldVertex₃ D π x).1.2 ≠ Fin.last d := by
  rw [oldVertex₃_val]
  exact (Fin.castSucc_lt_last _).ne

/-- **The new sheet has one branch vertex**, the median of the three mark images
(`card_branch_eq_one`). -/
theorem newVertex_eq_of_three_le (hT0 : genus T = 0) {u u' : π.T₃.V}
    (hu : 3 ≤ nonDanglingValency (glueDatum D π) (newVertex D π u))
    (hu' : 3 ≤ nonDanglingValency (glueDatum D π) (newVertex D π u')) : u = u' := by
  classical
  have hG := glueDatum_connected D π hD hT
  have hX : ∀ v ∉ π.markSet, tCount (NewSurvives D π) v ≠ 1 := by
    intro v hv
    have h := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
      (newVertex D π v)
    rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq, ite_eq_right hv, add_zero] at h
    exact h
  have hXM : ∀ v ∈ π.markSet, tCount (NewSurvives D π) v ≠ 0 := by
    intro v hv
    have h := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hG
      (newVertex D π v)
    rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq, ite_eq_left hv] at h
    omega
  have h := card_branch_eq_one (π.T₃_connected hT) (π.T₃_genus hT0) π.markSet π.card_markSet
    (NewSurvives D π) hX hXM
  have hmem : ∀ v, 3 ≤ nonDanglingValency (glueDatum D π) (newVertex D π v) →
      v ∈ Finset.univ.filter fun v ↦ 3 ≤ tCount (NewSurvives D π) v +
        (if v ∈ π.markSet then 1 else 0) := by
    intro v hv
    rw [nonDanglingValency_newVertex D π hD hT, π.sum_markVertex_eq] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  exact Finset.card_le_one.mp h.le _ (hmem u hu) _ (hmem u' hu')

end GlueVertices


/-! ## 4. The merged labels of the glued paths -/

section Labels

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph.{0}} {d : ℕ}
  {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {φ : FibreMember (tripodCore core s) y (d + 1)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data)

/-- **The merged label of a glued stable path**: the slot of `G̃` its slot of `Γ̃` merges to, read
through `Ξ` and `φ.ident` (`none` on a leg). -/
def glabel (Q : StablePath (glueDatum D π)) : Option (Fin p) :=
  mergeSlot s (φ.ident.row (Ξ.stablePathEquiv (glueDatum_connected D π hD hT) Q))

/-- The arm of leg `k` in the sheet of mark `k`, as a surviving edge. -/
def legND (k : Fin 3) : NonDanglingEdge (glueDatum D π) :=
  ⟨_, (hairpin_not_isDangling D π hD hT k).1⟩

theorem legND_val (k : Fin 3) : (legND hD hT k).1 = π.armSourceEdge D k := rfl

variable (hS : ShapeLabels s D π φ.ident Ξ)

include hS in
/-- The arm of leg `k` lies on leg `k`. -/
theorem row_legND (k : Fin 3) :
    φ.ident.row (Ξ.nonDanglingEdgeEquiv (glueDatum_connected D π hD hT) (legND hD hT k)).stablePath =
      legSlot p k := by
  obtain ⟨e', he', hr⟩ := hS.leg k
  have : e' = Ξ.nonDanglingEdgeEquiv (glueDatum_connected D π hD hT) (legND hD hT k) :=
    Subtype.ext he'
  rw [← this, hr]

include hS hπ in
/-- **At mark `k`, a glued old edge lies on a G-slot of `Γ̃` at mark `k`**, not on leg `k` (mark
`k` meets leg `k` once, by its arm). -/
theorem key_mark {k : Fin 3} {z : NonDanglingEdge (refine₃ D π)}
    (hz : Incident (refine₃ D π) z.1 (markR₃ D π k)) :
    ((tripodCore core s).tail (φ.ident.row (Ξ.nonDanglingEdgeEquiv (glueDatum_connected D π hD hT)
        (CutPaths.liftND D π hD hT hπ z)).stablePath) = tripodMark n k ∨
      (tripodCore core s).head (φ.ident.row (Ξ.nonDanglingEdgeEquiv
        (glueDatum_connected D π hD hT) (CutPaths.liftND D π hD hT hπ z)).stablePath) =
          tripodMark n k) ∧
      φ.ident.row (Ξ.nonDanglingEdgeEquiv (glueDatum_connected D π hD hT)
        (CutPaths.liftND D π hD hT hπ z)).stablePath ≠ legSlot p k := by
  have hinc : Incident φ.data (Ξ.nonDanglingEdgeEquiv (glueDatum_connected D π hD hT)
      (CutPaths.liftND D π hD hT hπ z)).1 (φ.ident.vertex.symm (tripodMark n k)).1 := by
    rw [hS.mark k, markSourceVertex_eq]
    exact (Ξ.incident_map_iff _ _).mpr ((incident_liftSE_oldVertex₃ _ _ _ _).mpr hz)
  refine ⟨Dichotomy.end_of_incident_vertex (Frame.of φ) (tripodMark n k) _ hinc,
    fun hleg ↦ ?_⟩
  obtain ⟨e₁, he₁, hr₁⟩ := hS.leg k
  have hinc₁ : Incident φ.data e₁.1 (φ.ident.vertex.symm (tripodMark n k)).1 := by
    rw [he₁, hS.mark k]
    exact (Ξ.incident_map_iff _ _).mpr (armSourceEdge_incident _ _ k)
  have heq := Dichotomy.legEdge_unique_at_mark (Frame.of φ) k hinc hinc₁ hleg hr₁
  have h' : liftSE D π z.1 = π.armSourceEdge D k := by
    apply Ξ.sourceEdgeEquiv.injective
    rw [← he₁]
    exact congrArg Subtype.val heq
  exact liftSE_ne_arm D π z.1 k (π.sheet k).castSucc h'

include hS in
/-- Two glued old edges at one mark carry one merged label. -/
theorem glabel_eq_of_mark {k : Fin 3} {z z' : NonDanglingEdge (refine₃ D π)}
    (hz : Incident (refine₃ D π) z.1 (markR₃ D π k))
    (hz' : Incident (refine₃ D π) z'.1 (markR₃ D π k)) :
    glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ z) =
      glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ z') := by
  obtain ⟨a₁, b₁⟩ := key_mark hD hT hπ Ξ hS hz
  obtain ⟨a₂, b₂⟩ := key_mark hD hT hπ Ξ hS hz'
  exact mergeSlot_eq_of_incident_mark core s k a₁ a₂ b₁ b₂

omit hπ in
theorem glabel_mergeFn {S N : StablePath (glueDatum D π)}
    (h : glabel hD hT Ξ S = glabel hD hT Ξ N) (P : StablePath (glueDatum D π)) :
    glabel hD hT Ξ (Merge.mergeFn S N P) = glabel hD hT Ξ P := by
  unfold Merge.mergeFn
  split_ifs with hP
  · rw [h, hP]
  · rfl

include hS in
/-- The merge at mark `2` keeps the merged labels. -/
theorem glabel_merge₂ :
    glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ
        (Refine.someHalfND _ _ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ))) =
      glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ
        (Refine.noneHalfND _ _ (π.refine₂_connected D hD) (π.markEdge₂ D hD hπ))) := by
  obtain ⟨hs, hn⟩ := Refine.incident_halves _ π.edge₂ (π.refine₂_connected D hD)
    (x := π.markEdge₂ D hD hπ) rfl
  exact glabel_eq_of_mark hD hT hπ Ξ hS (k := 2) hs hn

include hS in
/-- The merge at mark `1` keeps the merged labels. -/
theorem glabel_merge₁ :
    glabel hD hT Ξ (CutPaths.cut₂ D π hD hT hπ
        (Refine.someHalfND _ _ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ))) =
      glabel hD hT Ξ (CutPaths.cut₂ D π hD hT hπ
        (Refine.noneHalfND _ _ (π.refine₁_connected D hD) (π.markEdge₁ D hD hπ))) := by
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  obtain ⟨hs, hn⟩ := Refine.incident_halves _ π.edge₁ h₁ (x := π.markEdge₁ D hD hπ) rfl
  obtain ⟨-, hz, hz'⟩ := Refine.pieceND_pair _ π.edge₂ h₂
    (Refine.someHalfND_ne_noneHalfND _ _ h₁ (x := π.markEdge₁ D hD hπ) rfl) hs hn
  set u := Refine.freshOf _ π.edge₁ (π.markEdge₁ D hD hπ).1 rfl
  have e1 := CutPaths.cut₂_parentND hD hT hπ
    (Refine.pieceND _ π.edge₂ h₂ u (Refine.someHalfND _ _ h₁ (π.markEdge₁ D hD hπ)))
  have e2 := CutPaths.cut₂_parentND hD hT hπ
    (Refine.pieceND _ π.edge₂ h₂ u (Refine.noneHalfND _ _ h₁ (π.markEdge₁ D hD hπ)))
  rw [Refine.parentND_pieceND] at e1 e2
  rw [e1, e2, glabel_mergeFn hD hT Ξ (glabel_merge₂ hD hT hπ Ξ hS),
    glabel_mergeFn hD hT Ξ (glabel_merge₂ hD hT hπ Ξ hS)]
  exact glabel_eq_of_mark hD hT hπ Ξ hS (k := 1) hz hz'

include hS in
/-- The merge at mark `0` keeps the merged labels. -/
theorem glabel_merge₀ :
    glabel hD hT Ξ (CutPaths.cut₁ D π hD hT hπ (Refine.someHalfND _ _ hD (π.markEdge₀ D hπ))) =
      glabel hD hT Ξ (CutPaths.cut₁ D π hD hT hπ
        (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ))) := by
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  obtain ⟨hs, hn⟩ := Refine.incident_halves D π.edge₀ hD (x := π.markEdge₀ D hπ) rfl
  obtain ⟨hww, hw, hw'⟩ := Refine.pieceND_pair _ π.edge₁ h₁
    (Refine.someHalfND_ne_noneHalfND _ _ hD (x := π.markEdge₀ D hπ) rfl) hs hn
  obtain ⟨-, hz, hz'⟩ := Refine.pieceND_pair _ π.edge₂ h₂ hww hw hw'
  set u := Refine.freshOf D π.edge₀ (π.markEdge₀ D hπ).1 rfl
  set u' := Refine.oldSV _ π.edge₁ u
  have e1 := CutPaths.cut₁_parentND hD hT hπ
    (Refine.pieceND _ π.edge₁ h₁ u (Refine.someHalfND _ _ hD (π.markEdge₀ D hπ)))
  have e2 := CutPaths.cut₁_parentND hD hT hπ
    (Refine.pieceND _ π.edge₁ h₁ u (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ)))
  rw [Refine.parentND_pieceND] at e1 e2
  have e3 := CutPaths.cut₂_parentND hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u'
    (Refine.pieceND _ π.edge₁ h₁ u (Refine.someHalfND _ _ hD (π.markEdge₀ D hπ))))
  have e4 := CutPaths.cut₂_parentND hD hT hπ (Refine.pieceND _ π.edge₂ h₂ u'
    (Refine.pieceND _ π.edge₁ h₁ u (Refine.noneHalfND _ _ hD (π.markEdge₀ D hπ))))
  rw [Refine.parentND_pieceND] at e3 e4
  rw [e1, e2, glabel_mergeFn hD hT Ξ (glabel_merge₁ hD hT hπ Ξ hS),
    glabel_mergeFn hD hT Ξ (glabel_merge₁ hD hT hπ Ξ hS), e3, e4,
    glabel_mergeFn hD hT Ξ (glabel_merge₂ hD hT hπ Ξ hS),
    glabel_mergeFn hD hT Ξ (glabel_merge₂ hD hT hπ Ξ hS)]
  exact glabel_eq_of_mark hD hT hπ Ξ hS (k := 0) hz hz'

include hS in
/-- **Merging back at the marks keeps the merged labels.** -/
theorem glabel_cut₀_anc (z : NonDanglingEdge (refine₃ D π)) :
    glabel hD hT Ξ (CutPaths.cut₀ D π hD hT hπ (CutPaths.anc D π hD z)) =
      glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ z) := by
  rw [CutPaths.cut₀_anc hD hT hπ]
  unfold CutPaths.stage₀ CutPaths.stage₁ CutPaths.stage₂
  rw [glabel_mergeFn hD hT Ξ (glabel_merge₀ hD hT hπ Ξ hS),
    glabel_mergeFn hD hT Ξ (glabel_merge₁ hD hT hπ Ξ hS),
    glabel_mergeFn hD hT Ξ (glabel_merge₂ hD hT hπ Ξ hS)]

/-- A G-slot of `Γ̃` merges to some slot of `G̃`. -/
theorem mergeSlot_isSome_of_isGSlot {j : Fin (p + 1 + 1 + 1 + 3)} (hj : IsGSlot j) :
    ∃ i, mergeSlot s j = some i := by
  unfold mergeSlot
  rw [dite_eq_left (show (j : ℕ) < p + 1 + 1 + 1 from hj)]
  exact ⟨_, rfl⟩

include hS in
/-- **A glued old path is not a leg**: its merged label is a slot of `G̃`. -/
theorem exists_glabel_eq_some (z : NonDanglingEdge (refine₃ D π)) :
    ∃ i, glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ z) = some i := by
  have hG := glueDatum_connected D π hD hT
  rcases Dichotomy.isGSlot_or_eq_legSlot (φ.ident.row (Ξ.stablePathEquiv hG
      (CutPaths.gluedPath D π hD hT hπ z))) with hj | ⟨k, hk⟩
  · exact mergeSlot_isSome_of_isGSlot hj
  · exfalso
    rw [← row_legND hD hT Ξ hS k] at hk
    have h := φ.ident.row.injective hk
    rw [CutPaths.gluedPath, GeometricDatumIso.stablePathEquiv_mk,
      ← GeometricDatumIso.stablePathEquiv_mk] at h
    exact CutPaths.gluedPath_ne_hairpin hD hT hπ z k ((Ξ.stablePathEquiv hG).injective h)

end Labels


/-! ## 5. The G-slots of `Γ̃` are glued old paths -/

section GSlots

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph.{0}} {d : ℕ}
  {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D) (hT0 : genus T = 0) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {φ : FibreMember (tripodCore core s) y (d + 1)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ)
include hD hT

omit hπ in
/-- A branch vertex of `φ` comes from a vertex of valency at least three of the glued datum. -/
theorem three_le_symm (b : BranchVertex φ.data) :
    3 ≤ nonDanglingValency (glueDatum D π) (Ξ.sourceVertexEquiv.symm b.1) := by
  rw [← Ξ.nonDanglingValency_map (glueDatum_connected D π hD hT), Equiv.apply_symm_apply]
  exact b.2

omit hπ in
include hS in
/-- **The centre is in the new sheet**, over a vertex of `T₃`. -/
theorem exists_centre_eq_newVertex :
    ∃ u, Ξ.sourceVertexEquiv.symm (φ.ident.vertex.symm (centre n)).1 = newVertex D π u := by
  have h3 := three_le_symm hD hT Ξ (φ.ident.vertex.symm (centre n))
  have hc := hS.centre
  rcases sourceVertex_cases_glue D π (Ξ.sourceVertexEquiv.symm (φ.ident.vertex.symm (centre n)).1)
    with ⟨x, hx⟩ | ⟨u, hu⟩ | ⟨k, j, hkj⟩
  · rw [hx] at hc
    exact absurd hc (oldVertex₃_sheet_ne_last x)
  · exact ⟨u, hu⟩
  · rw [hkj] at h3
    have := nonDanglingValency_tip_le D π hD hT k j
    omega

include hS hT0 in
/-- **The only branch vertex of the new sheet is the centre.** -/
theorem newVertex_eq_centre {u : π.T₃.V}
    (hu : 3 ≤ nonDanglingValency (glueDatum D π) (newVertex D π u)) :
    newVertex D π u = Ξ.sourceVertexEquiv.symm (φ.ident.vertex.symm (centre n)).1 := by
  obtain ⟨uc, huc⟩ := exists_centre_eq_newVertex hD hT Ξ hS
  have h3 := three_le_symm hD hT Ξ (φ.ident.vertex.symm (centre n))
  rw [huc] at h3 ⊢
  rw [newVertex_eq_of_three_le hD hT hT0 hu h3]

include hS hπ hT0 in
/-- **Every G-slot of `Γ̃` is a glued old path** (the row list of §5.3): a new surviving edge
meets a branch vertex only at a mark, as the arm there, which lies on a leg, or at the centre,
which no G-slot meets. -/
theorem exists_gluedPath_eq_gSlot (i : Fin (p + 1 + 1 + 1)) :
    ∃ z, Ξ.stablePathEquiv (glueDatum_connected D π hD hT) (CutPaths.gluedPath D π hD hT hπ z) =
      φ.ident.row.symm (Fin.castAdd 3 i) := by
  have hG := glueDatum_connected D π hD hT
  set ℓ := ((markedCore core s).tail i).castSucc with hℓ
  obtain ⟨aφ, hinc₀, hpath₀⟩ := Dichotomy.exists_incident_of_end (Frame.of φ) (Fin.castAdd 3 i) ℓ
    (Or.inl (Dichotomy.tripodCore_tail_castAdd i))
  have hinc : Incident φ.data aφ.1 (φ.ident.vertex.symm ℓ).1 := hinc₀
  have hpath : @NonDanglingEdge.stablePath _ _ φ.data aφ = φ.ident.row.symm (Fin.castAdd 3 i) :=
    hpath₀
  set a := (Ξ.nonDanglingEdgeEquiv hG).symm aφ with ha
  have haφ : Ξ.nonDanglingEdgeEquiv hG a = aφ := Equiv.apply_symm_apply _ _
  by_cases hold : CutPaths.IsOld D π a
  · obtain ⟨z, hz⟩ := CutPaths.eq_liftND_of_isOld hD hT hπ hold
    refine ⟨z, ?_⟩
    rw [CutPaths.gluedPath, ← hz, GeometricDatumIso.stablePathEquiv_mk, haφ]
    exact hpath
  · exfalso
    set w := Ξ.sourceVertexEquiv.symm (φ.ident.vertex.symm ℓ).1 with hw
    have hincw : Incident (glueDatum D π) a.1 w := by
      rw [← Ξ.incident_map_iff, hw, Equiv.apply_symm_apply]
      rw [← haφ] at hinc
      exact hinc
    have h3 : 3 ≤ nonDanglingValency (glueDatum D π) w := three_le_symm hD hT Ξ _
    rcases eq_mark_or_newVertex_of_not_isOld hD hT hold hincw h3 with ⟨k, -, harm⟩ | ⟨u, hu⟩
    · -- the arm at mark `k` is on leg `k`
      have hk : a = legND hD hT k := Subtype.ext harm
      have hrow := row_legND hD hT Ξ hS k
      rw [← hk, haφ, hpath, Equiv.apply_symm_apply] at hrow
      have := congrArg Fin.val hrow
      simp only [Fin.val_castAdd, legSlot, Fin.val_natAdd] at this
      omega
    · -- a new-sheet branch vertex is the centre, which no G-slot meets
      rw [hu] at h3
      have hc := newVertex_eq_centre hD hT hT0 Ξ hS h3
      rw [← hu, hw] at hc
      have hℓc : ℓ = centre n := by
        have := Ξ.sourceVertexEquiv.symm.injective hc
        exact φ.ident.vertex.symm.injective (Subtype.ext this)
      exact (Fin.castSucc_lt_last _).ne hℓc

include hS hπ hT0 in
/-- **Every slot of `G̃` is the merged label of a glued old path.** -/
theorem exists_glabel_eq (j : Fin p) :
    ∃ z, glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ z) = some j := by
  obtain ⟨z, hz⟩ := exists_gluedPath_eq_gSlot hD hT hπ hT0 Ξ hS j.castSucc.castSucc.castSucc
  refine ⟨z, ?_⟩
  unfold glabel
  rw [hz, Equiv.apply_symm_apply, mergeSlot_castAdd, mergeOne_castSucc, mergeOne_castSucc,
    mergeOne_castSucc]

end GSlots


/-! ## 6. Path ends of `D`

A stable path `P` of `D` without an end has its glued pieces ending only at marks on `P`
(`mark_of_end`). If no mark lies on `P`, a glued piece has no end, against the path ends of the
glued datum; otherwise the marks on `P` would be cut off from the rest of the connected marked core
(`hasPathEnds_of_shape`). -/

section PathEndsD

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph.{0}} {d : ℕ}
  {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D) (hT0 : genus T = 0) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {φ : FibreMember (tripodCore core s) y (d + 1)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ)

omit hD in
/-- The surviving edge of `D` under mark `k`. -/
def markND (hπ : π.NonDangling D) (k : Fin 3) : NonDanglingEdge D :=
  ⟨D.sourceEdge (π.parentEdge k) (π.sheet k), hπ k⟩

include hD hT hπ in
/-- **The ends of the glued pieces of an endless stable path are marks on it.** -/
theorem mark_of_end {P : StablePath D}
    (hno : ∀ (x : NonDanglingEdge D) (v : D.SourceVertex), x.stablePath = P →
      ¬ IsPathEnd D x.1 v)
    {z : NonDanglingEdge (refine₃ D π)} (hz : (CutPaths.anc D π hD z).stablePath = P)
    {a : NonDanglingEdge (glueDatum D π)} {w : (glueDatum D π).SourceVertex}
    (ha : a.stablePath = CutPaths.gluedPath D π hD hT hπ z) (hinc : Incident _ a.1 w)
    (hval : nonDanglingValency (glueDatum D π) w ≠ 2) :
    ∃ k, w = π.markSourceVertex D k ∧ (markND hπ k).stablePath = P := by
  have haOld : CutPaths.IsOld D π a :=
    (CutPaths.isOld_iff_of_stablePath_eq hD hT hπ ha).mpr (CutPaths.isOld_liftND hD hT hπ z)
  obtain ⟨za, rfl⟩ := CutPaths.eq_liftND_of_isOld hD hT hπ haOld
  have hP : (CutPaths.anc D π hD za).stablePath = P :=
    (anc_stablePath_eq_of_gluedPath_eq hD hT hπ ha).trans hz
  rcases sourceVertex_cases_glue D π w with ⟨xw, rfl⟩ | ⟨u, rfl⟩ | ⟨k, j, rfl⟩
  · have hza := (incident_liftSE_oldVertex₃ D π za.1 xw).mp hinc
    by_cases hm : ∃ k, xw = markR₃ D π k
    · obtain ⟨k, rfl⟩ := hm
      refine ⟨k, (markSourceVertex_eq D π k).symm, ?_⟩
      have h1 : CutPaths.anc D π hD za = markND hπ k :=
        Subtype.ext (anc_of_incident_markR₃ hD hπ hza)
      rw [← h1, hP]
    · exfalso
      push Not at hm
      rw [nonDanglingValency_oldVertex₃ D π hD hT hπ, sum_mark_eq_zero D π hm, add_zero] at hval
      have hpos : 0 < nonDanglingValency (refine₃ D π) xw := by
        rw [← StablePathCount.card_incidentEdges]
        exact Finset.card_pos.mpr ⟨za, (StablePathCount.mem_incidentEdges _ _ _).mpr hza⟩
      have hne1 := NonDanglingValency.nonDanglingValency_ne_one (refine₃ D π)
        (π.refine₃_connected D hD) xw
      rcases lift₃V_or_le_two hD xw with ⟨v, rfl⟩ | hle
      · rw [CutPaths.nonDanglingValency_lift₃V hD] at hval
        exact hno _ v hP ⟨incident_anc_of_incident_lift₃V hD hza, hval⟩
      · omega
  · exact absurd hinc (not_incident_liftSE_newVertex D π za.1 u)
  · exact absurd hinc (not_incident_liftSE_tip D π za.1 k j)

include hD hT hπ hS in
/-- **The slot of `Γ̃` of a glued piece of an endless stable path ends only at marks on it.** -/
theorem end_mark_of_gSlot {P : StablePath D}
    (hno : ∀ (x : NonDanglingEdge D) (v : D.SourceVertex), x.stablePath = P →
      ¬ IsPathEnd D x.1 v)
    {z : NonDanglingEdge (refine₃ D π)} (hz : (CutPaths.anc D π hD z).stablePath = P)
    {j : Fin (p + 1 + 1 + 1 + 3)}
    (hj : Ξ.stablePathEquiv (glueDatum_connected D π hD hT) (CutPaths.gluedPath D π hD hT hπ z) =
      φ.ident.row.symm j)
    {ℓ : Fin (n + 1 + 1 + 1 + 1)}
    (hℓ : (tripodCore core s).tail j = ℓ ∨ (tripodCore core s).head j = ℓ) :
    ∃ k, ℓ = tripodMark n k ∧ (markND hπ k).stablePath = P := by
  have hG := glueDatum_connected D π hD hT
  obtain ⟨bφ, hinc₀, hpath₀⟩ := Dichotomy.exists_incident_of_end (Frame.of φ) j ℓ hℓ
  have hinc : Incident φ.data bφ.1 (φ.ident.vertex.symm ℓ).1 := hinc₀
  have hpath : @NonDanglingEdge.stablePath _ _ φ.data bφ = φ.ident.row.symm j := hpath₀
  set b := (Ξ.nonDanglingEdgeEquiv hG).symm bφ with hbdef
  have hbφ : Ξ.nonDanglingEdgeEquiv hG b = bφ := Equiv.apply_symm_apply _ _
  set w := Ξ.sourceVertexEquiv.symm (φ.ident.vertex.symm ℓ).1 with hw
  have hincw : Incident (glueDatum D π) b.1 w := by
    rw [← Ξ.incident_map_iff, hw, Equiv.apply_symm_apply]
    rw [← hbφ] at hinc
    exact hinc
  have h3 : 3 ≤ nonDanglingValency (glueDatum D π) w := three_le_symm hD hT Ξ _
  have hb : b.stablePath = CutPaths.gluedPath D π hD hT hπ z := by
    apply (Ξ.stablePathEquiv hG).injective
    rw [GeometricDatumIso.stablePathEquiv_mk, hbφ, hpath, hj]
  obtain ⟨k, hwk, hk⟩ := mark_of_end hD hT hπ hno hz hb hincw (by omega)
  refine ⟨k, ?_, hk⟩
  have h1 : (φ.ident.vertex.symm ℓ).1 = (φ.ident.vertex.symm (tripodMark n k)).1 := by
    rw [hS.mark k, ← hwk, hw, Equiv.apply_symm_apply]
  exact φ.ident.vertex.symm.injective (Subtype.ext h1)

include hD hT hπ hS in
/-- **`D` has path ends** (for connected `G̃`): an endless stable path of `D` would carry marks
cut off from the rest of the connected marked core, or none, and then a glued piece of it would
have no end. -/
theorem hasPathEnds_of_shape (hconn : core.Connected) (hEndsG : HasPathEnds (glueDatum D π)) :
    HasPathEnds D := by
  classical
  intro x
  by_contra hno₀
  set P := x.stablePath with hP
  have hno : ∀ (x' : NonDanglingEdge D) (v : D.SourceVertex), x'.stablePath = P →
      ¬ IsPathEnd D x'.1 v := fun x' v hx' hend ↦ hno₀ ⟨x', v, hx', hend⟩
  have hG := glueDatum_connected D π hD hT
  set z₀ := Refine.someHalfND _ π.edge₂ (π.refine₂_connected D hD)
    (Refine.someHalfND _ π.edge₁ (π.refine₁_connected D hD) (Refine.someHalfND D π.edge₀ hD x))
    with hz₀def
  have hz₀ : CutPaths.anc D π hD z₀ = x := by
    rw [hz₀def, CutPaths.anc, Refine.parentND_someHalfND, Refine.parentND_someHalfND,
      Refine.parentND_someHalfND]
  have hz₀P : (CutPaths.anc D π hD z₀).stablePath = P := by rw [hz₀]
  by_cases hM : ∃ k, (markND hπ k).stablePath = P
  · obtain ⟨k₀, hk₀⟩ := hM
    let S : Finset (Fin (n + 1 + 1 + 1)) := Finset.univ.filter fun v ↦
      ∃ k, v = markVertex n k ∧ (markND hπ k).stablePath = P
    have hmem : ∀ v, v ∈ S ↔ ∃ k, v = markVertex n k ∧ (markND hπ k).stablePath = P :=
      fun v ↦ by simp [S]
    have hold : (core.tail s.first).castSucc.castSucc.castSucc ∉ S := by
      rw [hmem]
      rintro ⟨k, hk, -⟩
      have h1 := congrArg Fin.val hk
      simp only [Fin.val_castSucc, markVertex] at h1
      have := (core.tail s.first).isLt
      omega
    obtain ⟨i, hi⟩ := Dichotomy.markedCore_connected hconn S
      ⟨_, _, (hmem _).mpr ⟨k₀, rfl, hk₀⟩, hold⟩
    have key : ∀ k, (markND hπ k).stablePath = P →
        ((markedCore core s).tail i = markVertex n k ∨
          (markedCore core s).head i = markVertex n k) →
        (markedCore core s).tail i ∈ S ∧ (markedCore core s).head i ∈ S := by
      intro k hk hik
      obtain ⟨aφ, hinc₀, hpath₀⟩ := Dichotomy.exists_incident_of_end (Frame.of φ)
        (Fin.castAdd 3 i) (tripodMark n k) (by
          rcases hik with h | h
          · exact Or.inl (by rw [Dichotomy.tripodCore_tail_castAdd, h]; rfl)
          · exact Or.inr (by rw [Dichotomy.tripodCore_head_castAdd, h]; rfl))
      have hinc : Incident φ.data aφ.1 (φ.ident.vertex.symm (tripodMark n k)).1 := hinc₀
      have hpath : @NonDanglingEdge.stablePath _ _ φ.data aφ =
          φ.ident.row.symm (Fin.castAdd 3 i) := hpath₀
      set a := (Ξ.nonDanglingEdgeEquiv hG).symm aφ with ha
      have haφ : Ξ.nonDanglingEdgeEquiv hG a = aφ := Equiv.apply_symm_apply _ _
      have hinca : Incident (glueDatum D π) a.1 (oldVertex₃ D π (markR₃ D π k)) := by
        rw [← markSourceVertex_eq, ← Ξ.incident_map_iff, ← hS.mark k]
        rw [← haφ] at hinc
        exact hinc
      rcases isOld_or_arm_of_incident_oldVertex₃ hD hT a hinca with haOld | ⟨k', -, harm⟩
      · obtain ⟨za, hza⟩ := CutPaths.eq_liftND_of_isOld hD hT hπ haOld
        have hzinc : Incident (refine₃ D π) za.1 (markR₃ D π k) := by
          rw [← incident_liftSE_oldVertex₃]
          rw [hza] at hinca
          exact hinca
        have hzP : (CutPaths.anc D π hD za).stablePath = P := by
          rw [show CutPaths.anc D π hD za = markND hπ k from
            Subtype.ext (anc_of_incident_markR₃ hD hπ hzinc)]
          exact hk
        have hj : Ξ.stablePathEquiv hG (CutPaths.gluedPath D π hD hT hπ za) =
            φ.ident.row.symm (Fin.castAdd 3 i) := by
          rw [CutPaths.gluedPath, ← hza, GeometricDatumIso.stablePathEquiv_mk, haφ, hpath]
        obtain ⟨k₁, h₁, hk₁⟩ := end_mark_of_gSlot hD hT hπ Ξ hS hno hzP hj (Or.inl rfl)
        obtain ⟨k₂, h₂, hk₂⟩ := end_mark_of_gSlot hD hT hπ Ξ hS hno hzP hj (Or.inr rfl)
        rw [Dichotomy.tripodCore_tail_castAdd] at h₁
        rw [Dichotomy.tripodCore_head_castAdd] at h₂
        exact ⟨(hmem _).mpr ⟨k₁, Fin.castSucc_injective _ h₁, hk₁⟩,
          (hmem _).mpr ⟨k₂, Fin.castSucc_injective _ h₂, hk₂⟩⟩
      · exfalso
        have hk' : a = legND hD hT k' := Subtype.ext harm
        have hrow := row_legND hD hT Ξ hS k'
        rw [← hk', haφ, hpath, Equiv.apply_symm_apply] at hrow
        have := congrArg Fin.val hrow
        simp only [Fin.val_castAdd, legSlot, Fin.val_natAdd] at this
        omega
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨k, hk, hkP⟩ := (hmem _).mp h1
      exact h2 (key k hkP (Or.inl hk)).2
    · obtain ⟨k, hk, hkP⟩ := (hmem _).mp h1
      exact h2 (key k hkP (Or.inr hk)).1
  · push Not at hM
    obtain ⟨a, w, ha, hend⟩ := hEndsG (CutPaths.liftND D π hD hT hπ z₀)
    obtain ⟨k, -, hk⟩ := mark_of_end hD hT hπ hno hz₀P ha hend.1 hend.2
    exact hM k hk

end PathEndsD


/-! ## 7. The rows of `D` -/

section Rows

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph.{0}} {d : ℕ}
  {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D) (hT0 : genus T = 0) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {φ : FibreMember (tripodCore core s) y (d + 1)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ)

/-- The merged label of a surviving edge of `D`: that of its glued pieces, merged back at the
marks. -/
def dlabel (x : NonDanglingEdge D) : Option (Fin p) :=
  glabel hD hT Ξ (CutPaths.cut₀ D π hD hT hπ x)

/-- The merged label of a stable path of `D` (`CutPaths.cut₀_eq_of_consecutive`). -/
def plabel : StablePath D → Option (Fin p) :=
  Quot.lift (dlabel hD hT hπ Ξ) fun _ _ h ↦
    congrArg (glabel hD hT Ξ) (CutPaths.cut₀_eq_of_consecutive hD hT hπ h)

theorem plabel_mk (x : NonDanglingEdge D) : plabel hD hT hπ Ξ x.stablePath = dlabel hD hT hπ Ξ x :=
  rfl

include hS in
theorem dlabel_anc (z : NonDanglingEdge (refine₃ D π)) :
    dlabel hD hT hπ Ξ (CutPaths.anc D π hD z) = glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ z) :=
  glabel_cut₀_anc hD hT hπ Ξ hS z

omit hT in
/-- The first piece of a surviving edge of `D`, surviving in `refine₃ D π`. -/
def firstND (x : NonDanglingEdge D) : NonDanglingEdge (refine₃ D π) :=
  ⟨firstPiece₃ D π x.1, by rw [isDangling_iff₃ D π hD, parentSE₃_firstPiece₃]; exact x.2⟩

omit hT in
theorem anc_firstND (x : NonDanglingEdge D) : CutPaths.anc D π hD (firstND hD x) = x :=
  Subtype.ext (parentSE₃_firstPiece₃ D π x.1)

include hS in
theorem exists_plabel_eq_some (P : StablePath D) : ∃ j, plabel hD hT hπ Ξ P = some j := by
  obtain ⟨x, rfl⟩ := Quot.exists_rep P
  have h := dlabel_anc hD hT hπ Ξ hS (firstND hD x)
  rw [anc_firstND] at h
  show ∃ j, dlabel hD hT hπ Ξ x = some j
  rw [h]
  exact exists_glabel_eq_some hD hT hπ Ξ hS _

/-- **The row label of a stable path of `D`.** -/
def prow (P : StablePath D) : Fin p := Classical.choose (exists_plabel_eq_some hD hT hπ Ξ hS P)

theorem plabel_eq_prow (P : StablePath D) :
    plabel hD hT hπ Ξ P = some (prow hD hT hπ Ξ hS P) :=
  Classical.choose_spec (exists_plabel_eq_some hD hT hπ Ξ hS P)

include hT0 in
theorem prow_surjective : Function.Surjective (prow hD hT hπ Ξ hS) := by
  intro j
  obtain ⟨z, hz⟩ := exists_glabel_eq hD hT hπ hT0 Ξ hS j
  refine ⟨(CutPaths.anc D π hD z).stablePath, Option.some_injective _ ?_⟩
  rw [← plabel_eq_prow, plabel_mk, dlabel_anc hD hT hπ Ξ hS, hz]

include hD hT hπ hT0 Ξ in
theorem card_stablePath_of_shape (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D) :
    Fintype.card (StablePath D) = p := by
  have h := card_stablePath_glue D π hD hT hT0 hπ h3 hEnds
  have hG : Fintype.card (StablePath (glueDatum D π)) = p + 1 + 1 + 1 + 3 := by
    rw [Fintype.card_congr ((Ξ.stablePathEquiv (glueDatum_connected D π hD hT)).trans
      φ.ident.row), Fintype.card_fin]
  omega

include hT0 in
theorem prow_bijective (h3 : ∀ x, nonDanglingValency D x ≤ 3) (hEnds : HasPathEnds D) :
    Function.Bijective (prow hD hT hπ Ξ hS) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨prow_surjective hD hT hπ hT0 Ξ hS, ?_⟩
  rw [card_stablePath_of_shape hD hT hπ hT0 Ξ h3 hEnds, Fintype.card_fin]

end Rows

/-! ## 8. The branch vertices of `D` -/

section Vertices

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph.{0}} {d : ℕ}
  {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D) (hT0 : genus T = 0) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {φ : FibreMember (tripodCore core s) y (d + 1)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ)

include hD hT hπ in
/-- An old branch vertex of `D` is a branch vertex of the glued datum. -/
theorem three_le_oldSourceVertex (b : BranchVertex D) :
    3 ≤ nonDanglingValency φ.data (Ξ.sourceVertexEquiv (π.oldSourceVertex D b.1)) := by
  rw [Ξ.nonDanglingValency_map (glueDatum_connected D π hD hT), oldSourceVertex_eq,
    show oldSV₃ D π b.1 = CutPaths.lift₃V D π b.1 from rfl,
    nonDanglingValency_oldVertex₃ D π hD hT hπ,
    sum_mark_eq_zero D π (fun k ↦ CutPaths.lift₃V_ne_markR₃ hD hπ b.1 k), add_zero,
    CutPaths.nonDanglingValency_lift₃V hD]
  exact b.2

/-- The branch vertex of `φ` of an old branch vertex of `D`. -/
def bvφ (b : BranchVertex D) : BranchVertex φ.data :=
  ⟨Ξ.sourceVertexEquiv (π.oldSourceVertex D b.1), three_le_oldSourceVertex hD hT hπ Ξ b⟩

include hS in
/-- **An old branch vertex is labelled by an old vertex of `Γ̃`**: it is neither a mark nor the
centre. -/
theorem vlabel_lt (b : BranchVertex D) : (φ.ident.vertex (bvφ hD hT hπ Ξ b)).val < n := by
  set ℓ := φ.ident.vertex (bvφ hD hT hπ Ξ b) with hℓ
  have hsymm : φ.ident.vertex.symm ℓ = bvφ hD hT hπ Ξ b := Equiv.symm_apply_apply _ _
  have hm : ∀ k, ℓ ≠ tripodMark n k := by
    intro k hk
    have h1 := hS.mark k
    rw [← hk, hsymm] at h1
    have h2 := Ξ.sourceVertexEquiv.injective h1
    rw [oldSourceVertex_eq, markSourceVertex_eq] at h2
    exact CutPaths.lift₃V_ne_markR₃ hD hπ b.1 k (oldVertex₃_injective D π h2)
  have hc : ℓ ≠ centre n := by
    intro hk
    have h1 := hS.centre
    rw [← hk, hsymm] at h1
    simp only [bvφ, Equiv.symm_apply_apply, oldSourceVertex_eq] at h1
    exact oldVertex₃_sheet_ne_last _ h1
  have hv : ∀ k : Fin 3, ℓ.val ≠ n + k.val := fun k h ↦ hm k (Fin.ext (by rw [h]; rfl))
  have hcv : ℓ.val ≠ n + 1 + 1 + 1 := fun h ↦ hc (Fin.ext (by rw [h]; rfl))
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  change ℓ.val ≠ n + 0 at h0
  change ℓ.val ≠ n + 1 at h1
  change ℓ.val ≠ n + 2 at h2
  have := ℓ.isLt
  omega

/-- **The vertex label of an old branch vertex.** -/
def vmap (b : BranchVertex D) : Fin n :=
  ⟨(φ.ident.vertex (bvφ hD hT hπ Ξ b)).val, vlabel_lt hD hT hπ Ξ hS b⟩

theorem oldLabel_vmap (b : BranchVertex D) :
    oldLabel (vmap hD hT hπ Ξ hS b) = φ.ident.vertex (bvφ hD hT hπ Ξ b) :=
  Fin.ext rfl

theorem vmap_injective : Function.Injective (vmap hD hT hπ Ξ hS) := by
  intro b b' h
  have h1 : φ.ident.vertex (bvφ hD hT hπ Ξ b) = φ.ident.vertex (bvφ hD hT hπ Ξ b') := by
    rw [← oldLabel_vmap hD hT hπ Ξ hS b, ← oldLabel_vmap hD hT hπ Ξ hS b', h]
  have h2 : Ξ.sourceVertexEquiv (π.oldSourceVertex D b.1) =
      Ξ.sourceVertexEquiv (π.oldSourceVertex D b'.1) :=
    congrArg Subtype.val (φ.ident.vertex.injective h1)
  have h3 := Ξ.sourceVertexEquiv.injective h2
  rw [oldSourceVertex_eq, oldSourceVertex_eq] at h3
  have h4 := oldVertex₃_injective D π h3
  unfold oldSV₃ at h4
  exact Subtype.ext (Refine.oldSV_injective D π.edge₀ (Refine.oldSV_injective _ π.edge₁
    (Refine.oldSV_injective _ π.edge₂ h4)))

include hT0 in
theorem vmap_surjective : Function.Surjective (vmap hD hT hπ Ξ hS) := by
  intro v
  set B := φ.ident.vertex.symm (oldLabel v) with hB
  set u := Ξ.sourceVertexEquiv.symm B.1 with hu
  have h3 : 3 ≤ nonDanglingValency (glueDatum D π) u := three_le_symm hD hT Ξ B
  have hlabel : ∀ b : BranchVertex D, Ξ.sourceVertexEquiv (π.oldSourceVertex D b.1) = B.1 →
      vmap hD hT hπ Ξ hS b = v := by
    intro b hb
    apply Fin.ext
    show (φ.ident.vertex (bvφ hD hT hπ Ξ b)).val = v.val
    have : bvφ hD hT hπ Ξ b = B := Subtype.ext hb
    rw [this, hB, Equiv.apply_symm_apply]
    rfl
  rcases sourceVertex_cases_glue D π u with ⟨x, hx⟩ | ⟨u', hu'⟩ | ⟨k, j, hkj⟩
  · by_cases hm : ∃ k, x = markR₃ D π k
    · exfalso
      obtain ⟨k, rfl⟩ := hm
      have h1 : B.1 = (φ.ident.vertex.symm (tripodMark n k)).1 := by
        rw [hS.mark k, markSourceVertex_eq, ← hx, hu, Equiv.apply_symm_apply]
      have h2 : oldLabel v = tripodMark n k := φ.ident.vertex.symm.injective (Subtype.ext h1)
      have h4 := congrArg Fin.val h2
      change v.val = n + k.val at h4
      have := v.isLt
      omega
    · push Not at hm
      rw [hx, nonDanglingValency_oldVertex₃ D π hD hT hπ, sum_mark_eq_zero D π hm, add_zero] at h3
      rcases lift₃V_or_le_two hD x with ⟨b0, rfl⟩ | hle
      · rw [CutPaths.nonDanglingValency_lift₃V hD] at h3
        refine ⟨⟨b0, h3⟩, hlabel _ ?_⟩
        rw [oldSourceVertex_eq]
        show Ξ.sourceVertexEquiv (oldVertex₃ D π (CutPaths.lift₃V D π b0)) = B.1
        rw [← hx, hu, Equiv.apply_symm_apply]
      · omega
  · exfalso
    rw [hu'] at h3
    have hc := newVertex_eq_centre hD hT hT0 Ξ hS h3
    rw [← hu', hu] at hc
    have h2 : oldLabel v = centre n :=
      φ.ident.vertex.symm.injective (Subtype.ext (Ξ.sourceVertexEquiv.symm.injective hc))
    have h4 := congrArg Fin.val h2
    change v.val = n + 1 + 1 + 1 at h4
    have := v.isLt
    omega
  · exfalso
    rw [hkj] at h3
    have := nonDanglingValency_tip_le D π hD hT k j
    omega

end Vertices

/-! ## 9. Incidences of the marked core, summed over the pieces of a slot -/

section CoreMerge

theorem coreIncidence_subdivide_castSucc {m q : ℕ} (C : Core m q) (e i : Fin q) (u : Fin m) :
    coreIncidence (subdivide C e) u.castSucc i.castSucc +
        (if i = e ∧ C.head e = u then 1 else 0) = coreIncidence C u i := by
  unfold coreIncidence
  rw [subdivide_tail_castSucc, subdivide_head_castSucc]
  by_cases hi : i = e
  · subst hi
    by_cases hh : C.head i = u <;> simp [hh, (Fin.castSucc_lt_last u).ne', Fin.castSucc_inj]
  · simp [hi, Fin.castSucc_inj]

theorem coreIncidence_subdivide_last {m q : ℕ} (C : Core m q) (e : Fin q) (u : Fin m) :
    coreIncidence (subdivide C e) u.castSucc (Fin.last q) = if C.head e = u then 1 else 0 := by
  unfold coreIncidence
  rw [subdivide_tail_last, subdivide_head_last]
  simp [(Fin.castSucc_lt_last u).ne', Fin.castSucc_inj]

/-- **One subdivision, summed over the pieces**: the two pieces of `e` meet an old vertex as often
as `e` does. -/
theorem sum_mergeOne_mul {m q : ℕ} (C : Core m q) (e : Fin q) (u : Fin m) (W : Fin q → ℕ) :
    ∑ i : Fin (q + 1), W (mergeOne e i) * coreIncidence (subdivide C e) u.castSucc i =
      ∑ i : Fin q, W i * coreIncidence C u i := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [mergeOne_castSucc, mergeOne_last, coreIncidence_subdivide_last]
  have h : ∀ i : Fin q, W i * coreIncidence C u i =
      W i * coreIncidence (subdivide C e) u.castSucc i.castSucc +
        (if i = e then W e * (if C.head e = u then 1 else 0) else 0) := by
    intro i
    rw [← coreIncidence_subdivide_castSucc C e i u]
    by_cases hi : i = e
    · subst hi
      by_cases hh : C.head i = u <;> simp [hh, mul_add]
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- **Three subdivisions, summed over the pieces.** -/
theorem sum_merge₃_mul {n p : ℕ} (core : Core n p) (s : MarkSlots p) (u : Fin n)
    (W : Fin p → ℕ) :
    ∑ i : Fin (p + 1 + 1 + 1), W (mergeOne s.first (mergeOne s.second (mergeOne s.third i))) *
        coreIncidence (markedCore core s) u.castSucc.castSucc.castSucc i =
      ∑ j : Fin p, W j * coreIncidence core u j := by
  unfold markedCore
  have h3 := sum_mergeOne_mul (subdivide (subdivide core s.first) s.second) s.third
    u.castSucc.castSucc (fun i₂ ↦ W (mergeOne s.first (mergeOne s.second i₂)))
  have h2 := sum_mergeOne_mul (subdivide core s.first) s.second u.castSucc
    (fun i₁ ↦ W (mergeOne s.first i₁))
  have h1 := sum_mergeOne_mul core s.first u W
  exact h3.trans (h2.trans h1)

/-- **The slots of `Γ̃` merging to `j` meet an old vertex as often as `j` does in `G̃`.** -/
theorem sum_mergeSlot_coreIncidence {n p : ℕ} (core : Core n p) (s : MarkSlots p) (u : Fin n)
    (j : Fin p) :
    (∑ i : Fin (p + 1 + 1 + 1 + 3),
        if mergeSlot s i = some j then coreIncidence (tripodCore core s) (oldLabel u) i else 0) =
      coreIncidence core u j := by
  classical
  rw [Fin.sum_univ_add]
  have hleg : ∀ k : Fin 3, mergeSlot s (Fin.natAdd (p + 1 + 1 + 1) k) = none := by
    intro k
    unfold mergeSlot
    rw [dite_eq_right (by simp only [Fin.val_natAdd]; omega)]
  have hc : ∀ i : Fin (p + 1 + 1 + 1),
      coreIncidence (tripodCore core s) (oldLabel u) (Fin.castAdd 3 i) =
        coreIncidence (markedCore core s) u.castSucc.castSucc.castSucc i := by
    intro i
    unfold coreIncidence
    rw [Dichotomy.tripodCore_tail_castAdd, Dichotomy.tripodCore_head_castAdd]
    simp only [oldLabel, Fin.castSucc_inj]
  simp only [hleg, reduceCtorEq, ite_false, Finset.sum_const_zero, add_zero, mergeSlot_castAdd,
    Option.some_inj, hc]
  have := sum_merge₃_mul core s u (fun j' ↦ if j' = j then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at this
  exact this.trans (by simp)

end CoreMerge


/-! ## 10. The incidences, and the core identification -/

section Assemble

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {T : CFGraph.{0}} {d : ℕ}
  {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected) (hT : graph_connected T)
  (hπ : π.NonDangling D) (hT0 : genus T = 0) {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {φ : FibreMember (tripodCore core s) y (d + 1)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ)

omit hT in
/-- The piece of a surviving edge of `D` at an old vertex, in `refine₃ D π`. -/
def piece₃ (b : D.SourceVertex) (x : NonDanglingEdge D) : NonDanglingEdge (refine₃ D π) :=
  Refine.pieceND _ π.edge₂ (π.refine₂_connected D hD)
    (Refine.oldSV _ π.edge₁ (Refine.oldSV D π.edge₀ b))
    (Refine.pieceND _ π.edge₁ (π.refine₁_connected D hD) (Refine.oldSV D π.edge₀ b)
      (Refine.pieceND D π.edge₀ hD b x))

omit hT in
theorem anc_piece₃ (b : D.SourceVertex) (x : NonDanglingEdge D) :
    CutPaths.anc D π hD (piece₃ hD b x) = x := by
  unfold piece₃ CutPaths.anc
  rw [Refine.parentND_pieceND, Refine.parentND_pieceND, Refine.parentND_pieceND]

omit hT in
theorem incident_piece₃ {b : D.SourceVertex} {x : NonDanglingEdge D} (h : Incident D x.1 b) :
    Incident (refine₃ D π) (piece₃ hD b x).1 (CutPaths.lift₃V D π b) :=
  Refine.incident_piece _ _ (Refine.incident_piece _ _ (Refine.incident_piece _ _ h))

/-- The surviving edges of `φ` at the old vertex of `b` whose slot merges to `j`. -/
def cSet (b : BranchVertex D) (j : Fin p) : Finset (NonDanglingEdge φ.data) :=
  (StablePathCount.incidentEdges φ.data (Ξ.sourceVertexEquiv (π.oldSourceVertex D b.1))).filter
    fun a ↦ mergeSlot s (φ.ident.row a.stablePath) = some j

/-- **The edges of `φ` at an old branch vertex with merged label `j`** number as the incidences of
the vertex of `G̃` with `j` (`φ.ident.incidence`, summed over the pieces of `j`). -/
theorem card_cSet (b : BranchVertex D) (j : Fin p) :
    (cSet Ξ b j).card = coreIncidence core (vmap hD hT hπ Ξ hS b) j := by
  classical
  have hV : Ξ.sourceVertexEquiv (π.oldSourceVertex D b.1) =
      (φ.ident.vertex.symm (oldLabel (vmap hD hT hπ Ξ hS b))).1 := by
    rw [oldLabel_vmap, Equiv.symm_apply_apply]
    rfl
  rw [← sum_mergeSlot_coreIncidence core s (vmap hD hT hπ Ξ hS b) j,
    Finset.card_eq_sum_card_fiberwise (f := fun a ↦ φ.ident.row a.stablePath)
      (t := Finset.univ.filter fun i ↦ mergeSlot s i = some j) (by
        intro a ha
        simp only [cSet, Finset.coe_filter, Set.mem_ofPred_eq] at ha
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        exact ha.2),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs with hi
  · have hinc := φ.ident.incidence (φ.ident.vertex.symm (oldLabel (vmap hD hT hπ Ξ hS b))) i
    rw [Equiv.apply_symm_apply] at hinc
    rw [← hinc]
    unfold incidenceCount
    congr 1
    ext a
    simp only [cSet, Finset.mem_filter, StablePathCount.mem_incidentEdges]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨hV ▸ h1, by rw [← h2, Equiv.symm_apply_apply]⟩
    · rintro ⟨h1, h2⟩
      have h2' : φ.ident.row a.stablePath = i := by rw [h2, Equiv.apply_symm_apply]
      exact ⟨⟨hV ▸ h1, by rw [h2']; exact hi⟩, h2'⟩
  · rfl

/-- The incidences of `b` with `P` inject into the edges of `φ` at `b` with the label of `P`. -/
theorem incidenceCount_le_card_cSet (b : BranchVertex D) (P : StablePath D) :
    incidenceCount D b.1 P ≤ (cSet Ξ b (prow hD hT hπ Ξ hS P)).card := by
  classical
  have hG := glueDatum_connected D π hD hT
  unfold incidenceCount
  refine Finset.card_le_card_of_injOn (fun x ↦ Ξ.nonDanglingEdgeEquiv hG
    (CutPaths.liftND D π hD hT hπ (piece₃ hD b.1 x))) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, StablePathCount.mem_incidentEdges] at hx
    obtain ⟨hxb, hxP⟩ := hx
    simp only [cSet, Finset.coe_filter, Set.mem_ofPred_eq, StablePathCount.mem_incidentEdges]
    refine ⟨?_, ?_⟩
    · rw [GeometricDatumIso.nonDanglingEdgeEquiv_val, Ξ.incident_map_iff, oldSourceVertex_eq]
      exact (incident_liftSE_oldVertex₃ D π _ _).mpr (incident_piece₃ hD hxb)
    · rw [← GeometricDatumIso.stablePathEquiv_mk]
      show glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ (piece₃ hD b.1 x)) =
        some (prow hD hT hπ Ξ hS P)
      rw [← dlabel_anc hD hT hπ Ξ hS, anc_piece₃, ← plabel_mk, hxP, plabel_eq_prow]
  · intro x _ x' _ h
    have h' := CutPaths.liftND_injective D π hD hT hπ ((Ξ.nonDanglingEdgeEquiv hG).injective h)
    rw [← anc_piece₃ hD b.1 x, ← anc_piece₃ hD b.1 x']
    exact congrArg (CutPaths.anc D π hD) h'

include hT0 in
/-- **The incidence multiplicities match** (§5.5): termwise inequality, and both sides
sum to three. -/
theorem incidenceCount_eq (hcubic : core.Cubic) (h3 : ∀ x, nonDanglingValency D x ≤ 3)
    (hEnds : HasPathEnds D) (b : BranchVertex D) (P : StablePath D) :
    incidenceCount D b.1 P = coreIncidence core (vmap hD hT hπ Ξ hS b) (prow hD hT hπ Ξ hS P) := by
  classical
  have hle : ∀ P, incidenceCount D b.1 P ≤
      coreIncidence core (vmap hD hT hπ Ξ hS b) (prow hD hT hπ Ξ hS P) := fun P ↦
    (incidenceCount_le_card_cSet hD hT hπ Ξ hS b P).trans_eq (card_cSet hD hT hπ Ξ hS b _)
  have hsumA : ∑ P, incidenceCount D b.1 P = 3 := by
    rw [StablePathCount.sum_incidenceCount_vertex]
    exact le_antisymm (h3 _) b.2
  have hsumC : ∑ P, coreIncidence core (vmap hD hT hπ Ξ hS b) (prow hD hT hπ Ξ hS P) = 3 := by
    rw [Fintype.sum_bijective _ (prow_bijective hD hT hπ hT0 Ξ hS h3 hEnds) _
      (fun j ↦ coreIncidence core (vmap hD hT hπ Ξ hS b) j) fun _ ↦ rfl]
    exact hcubic (vmap hD hT hπ Ξ hS b)
  exact ((Finset.sum_eq_sum_iff_of_le fun P _ ↦ hle P).mp (hsumA.trans hsumC.symm)) P
    (Finset.mem_univ _)

include hD hT hπ hT0 hS in
/-- **The core identification of the deletion, with the glued labels** (`exists_ident_of_shape`
for a datum whose trivalence and path ends are known). -/
theorem exists_ident_of_shape_aux (hcubic : core.Cubic) (h3 : ∀ x, nonDanglingValency D x ≤ 3)
    (hEnds : HasPathEnds D) :
    ∃ ident : CoreIdentification core D,
      (∀ b : BranchVertex D, (φ.ident.vertex.symm (oldLabel (ident.vertex b))).1 =
        Ξ.sourceVertexEquiv (π.oldSourceVertex D b.1)) ∧
      ∀ e : NonDanglingEdge D, ∃ e' : NonDanglingEdge φ.data,
        e'.1 = Ξ.sourceEdgeEquiv (π.oldSourceEdge D e.1) ∧
          mergeSlot s (φ.ident.row e'.stablePath) = some (ident.row e.stablePath) := by
  have hG := glueDatum_connected D π hD hT
  let rowE : StablePath D ≃ Fin p :=
    Equiv.ofBijective _ (prow_bijective hD hT hπ hT0 Ξ hS h3 hEnds)
  let vertE : BranchVertex D ≃ Fin n :=
    Equiv.ofBijective _ ⟨vmap_injective hD hT hπ Ξ hS, vmap_surjective hD hT hπ hT0 Ξ hS⟩
  refine ⟨⟨vertE, rowE, fun b j ↦ ?_⟩, fun b ↦ ?_, fun e ↦ ?_⟩
  · have h := incidenceCount_eq hD hT hπ hT0 Ξ hS hcubic h3 hEnds b (rowE.symm j)
    have hj : prow hD hT hπ Ξ hS (rowE.symm j) = j := rowE.apply_symm_apply j
    rw [hj] at h
    exact h
  · show (φ.ident.vertex.symm (oldLabel (vmap hD hT hπ Ξ hS b))).1 = _
    rw [oldLabel_vmap, Equiv.symm_apply_apply]
    rfl
  · refine ⟨Ξ.nonDanglingEdgeEquiv hG (CutPaths.liftND D π hD hT hπ (firstND hD e)), ?_, ?_⟩
    · show Ξ.sourceEdgeEquiv (liftSE D π (firstPiece₃ D π e.1)) = _
      rw [liftSE_firstPiece₃]
    · rw [← GeometricDatumIso.stablePathEquiv_mk]
      show glabel hD hT Ξ (CutPaths.gluedPath D π hD hT hπ (firstND hD e)) =
        some (prow hD hT hπ Ξ hS e.stablePath)
      rw [← dlabel_anc hD hT hπ Ξ hS, anc_firstND, ← plabel_mk, plabel_eq_prow]

end Assemble

end Onto

end GenusSixExistence.Tripod.Gluing

end
