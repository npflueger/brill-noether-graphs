import DraismaVargasCount.GeometricFibre
import DraismaVargasCount.Star
import DraismaVargasCount.RowGeodesic

/-!
# Geometric frame transport and constancy between walls

The geometric count uses the frames of `SegmentWalls` and their affine
coordinate walls, but the orientation-independent over-core relation. This
module ports the request-fibre equivalence and open odd count constancy to
`GeometricFibre`; it does not identify geometric counts with strict counts.
-/

namespace DraismaVargas.Count.GeometricSegmentWalls

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)
open SegmentWalls (Frame)

variable {n p degree : ℕ} {core : Core n p}

/-- Geometric frame isomorphism over the identity of the source core.
The induced dictionaries, rather than arbitrary bijections, preserve labels. -/
structure FrameIso (first second : Frame core degree) where
  datum : GeometricDatumIso first.data second.data
  overCore_vertex : ∀ branch : BranchVertex first.data,
    second.ident.vertex (datum.branchVertexEquiv first.fullDim.valid.1 branch) =
      first.ident.vertex branch
  overCore_row : ∀ path : StablePath first.data,
    second.ident.row (datum.stablePathEquiv first.fullDim.valid.1 path) =
      first.ident.row path

namespace FrameIso

variable {first second third : Frame core degree}

def toMemberIso (iso : FrameIso first second) (y : Fin p → ℚ) :
    GeometricMemberIso (first.member y) (second.member y) :=
  ⟨iso.datum, iso.overCore_vertex, iso.overCore_row⟩

def ofMemberIso {y : Fin p → ℚ}
    (iso : GeometricMemberIso (first.member y) (second.member y)) : FrameIso first second :=
  ⟨iso.datum, iso.overCore_vertex, iso.overCore_row⟩

noncomputable def refl (frame : Frame core degree) : FrameIso frame frame :=
  ofMemberIso (GeometricMemberIso.refl (frame.member (fun _ ↦ 0)))

noncomputable def symm (iso : FrameIso first second) : FrameIso second first :=
  ofMemberIso (iso.toMemberIso (fun _ ↦ 0)).symm

noncomputable def trans (left : FrameIso first second) (right : FrameIso second third) :
    FrameIso first third :=
  ofMemberIso ((left.toMemberIso (fun _ ↦ 0)).trans (right.toMemberIso (fun _ ↦ 0)))

def ofStrict (iso : SegmentWalls.FrameIso first second) : FrameIso first second :=
  ⟨GeometricDatumIso.ofStrict iso.datum, iso.overCore_vertex, iso.overCore_row⟩

def column (iso : FrameIso first second) : Fin p ≃ Fin p :=
  first.fullDim.labelling.targetEdge.trans
    (iso.datum.targetEdge.trans second.fullDim.labelling.targetEdge.symm)

theorem coordsAt_column (iso : FrameIso first second) (y : Fin p → ℚ) (col : Fin p) :
    second.coordsAt y (iso.column col) = first.coordsAt y col :=
  (iso.toMemberIso y).coords_column col

/-- The coordinate rigidity argument does not need ordered target endpoints. -/
theorem column_eq (left right : FrameIso first second) : left.column = right.column := by
  refine Equiv.ext fun col ↦ ?_
  exact second.col_eq_of_coordsAt_eq
    (fun y ↦ (left.coordsAt_column y col).trans (right.coordsAt_column y col).symm)

theorem column_self (iso : FrameIso first first) (col : Fin p) : iso.column col = col :=
  first.col_eq_of_coordsAt_eq (fun y ↦ iso.coordsAt_column y col)

theorem targetEdge_self (iso : FrameIso first first) (edge : first.target.edges) :
    iso.datum.targetEdge edge = edge := by
  have h := iso.column_self (first.fullDim.labelling.targetEdge.symm edge)
  simp only [column, Equiv.trans_apply, Equiv.apply_symm_apply] at h
  exact first.fullDim.labelling.targetEdge.symm.injective h

/-- Unordered endpoints need a geometric argument: moving a vertex while
fixing every edge would force both endpoints of an edge to be leaves. -/
theorem targetVertex_self (iso : FrameIso first first) (vertex : first.target.V) :
    iso.datum.targetVertex vertex = vertex := by
  classical
  by_contra hMove
  have hNe : vertex ≠ iso.datum.targetVertex vertex := Ne.symm hMove
  have := first.fullDim.nontrivial_target
  obtain ⟨edge, hEdge⟩ :=
    SegmentWalls.exists_incident_occurrence first.fullDim.targetConnected vertex
  have hMem : edge ∈ GluingDatum.incidentEdges vertex := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hEdge
  have hMap (e : first.target.edges) (h : e ∈ GluingDatum.incidentEdges vertex) :
      e ∈ GluingDatum.incidentEdges (iso.datum.targetVertex vertex) := by
    have hm := (iso.datum.mem_incidentEdges_map vertex e).mpr h
    rwa [iso.targetEdge_self] at hm
  have hSingleton : GluingDatum.incidentEdges vertex = {edge} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hMem, fun other hOther ↦ ?_⟩
    exact RowGeodesic.simpleTarget_of_genusZero first.fullDim.targetConnected
      first.fullDim.targetGenus vertex (iso.datum.targetVertex vertex) other edge hNe
      hOther (hMap other hOther) hMem (hMap edge hMem)
  have hLeaf : IsLeafVertex first.target vertex := by
    unfold IsLeafVertex
    rw [hSingleton, Finset.card_singleton]
  have hLeafMap := (iso.datum.isLeafVertex_map vertex).mpr hLeaf
  have hEdgeMap : (edge : first.target.V × first.target.V).1 = iso.datum.targetVertex vertex ∨
      (edge : first.target.V × first.target.V).2 = iso.datum.targetVertex vertex := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      using hMap edge hMem
  have hNoLeaves := noLeafToLeafEdge_of_fullDimensional first.fullDim edge
  rcases hEdge with hLeft | hRight <;> rcases hEdgeMap with hLeftMap | hRightMap
  · exact hNe (hLeft.symm.trans hLeftMap)
  · exact hNoLeaves (hLeft ▸ hLeaf) (hRightMap ▸ hLeafMap)
  · exact hNoLeaves (hLeftMap ▸ hLeafMap) (hRight ▸ hLeaf)
  · exact hNe (hRight.symm.trans hRightMap)

theorem degenerateAt_map (iso : FrameIso first second) {y : Fin p → ℚ} {col : Fin p}
    (h : first.DegenerateAt y col) : second.DegenerateAt y (iso.column col) := by
  constructor
  · rw [iso.coordsAt_column]
    exact h.1
  · intro other hOther
    obtain ⟨old, rfl⟩ := iso.column.surjective other
    rw [iso.coordsAt_column]
    exact h.2 old (fun heq ↦ hOther (congrArg iso.column heq))

theorem crossingTime_eq (iso : FrameIso first second) (y₀ y₁ : Fin p → ℚ) (col : Fin p) :
    (second.coordWall (iso.column col)).crossingTime y₀ y₁ =
      (first.coordWall col).crossingTime y₀ y₁ := by
  simp only [RationalAffineWall.crossingTime, Frame.eval_coordWall, iso.coordsAt_column]

end FrameIso

theorem isoOverCore_member_iff (first second : Frame core degree) (y : Fin p → ℚ) :
    Nonempty (GeometricMemberIso (first.member y) (second.member y)) ↔
      Nonempty (FrameIso first second) :=
  ⟨fun ⟨iso⟩ ↦ ⟨FrameIso.ofMemberIso iso⟩, fun ⟨iso⟩ ↦ ⟨iso.toMemberIso y⟩⟩

/-- The geometric fibre, not just the strict fibre, is request-independent. -/
noncomputable def fibreEquiv (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) :
    GeometricFibre core y degree ≃ GeometricFibre core y' degree :=
  Quotient.congr
    ((Frame.memberEquiv core degree y).symm.trans (Frame.memberEquiv core degree y'))
    (by
      intro a b
      have ha := Frame.member_of a
      have hb := Frame.member_of b
      show Nonempty (GeometricMemberIso a b) ↔
        Nonempty (GeometricMemberIso ((Frame.of a).member y') ((Frame.of b).member y'))
      rw [isoOverCore_member_iff, ← ha, ← hb, isoOverCore_member_iff, Frame.of_member,
        Frame.of_member])

@[simp] theorem fibreEquiv_cls (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (member : FibreMember core y degree) :
    fibreEquiv core degree y y' (GeometricFibre.cls member) =
      GeometricFibre.cls ((Frame.of member).member y') := rfl

theorem open_fibreEquiv_iff_of_no_wall (core : Core n p) (degree : ℕ)
    (y₀ y₁ : Fin p → ℚ) (u v : ℚ)
    (hno : ∀ (k : Frame core degree) (col : Fin p) (t : ℚ), min u v ≤ t → t ≤ max u v →
      ¬ k.IsWallParam y₀ y₁ col t)
    (c : GeometricFibre core (RationalAffineWall.segment y₀ y₁ u) degree) :
    (fibreEquiv core degree (RationalAffineWall.segment y₀ y₁ u)
        (RationalAffineWall.segment y₀ y₁ v) c).Open ↔ c.Open := by
  obtain ⟨member, rfl⟩ := GeometricFibre.cls_surjective c
  rw [fibreEquiv_cls, GeometricFibre.open_cls, GeometricFibre.open_cls]
  have h := (Frame.of member).openAt_segment_iff_of_no_wall y₀ y₁ u v
    fun col t ↦ hno (Frame.of member) col t
  constructor
  · intro hv
    have h2 : ((Frame.of member).member (RationalAffineWall.segment y₀ y₁ u)).Open := h.mpr hv
    rwa [Frame.member_of] at h2
  · intro hu
    refine h.mp ?_
    show ((Frame.of member).member (RationalAffineWall.segment y₀ y₁ u)).Open
    rw [Frame.member_of]
    exact hu

theorem isOdd_fibreEquiv (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (c : GeometricFibre core y degree) :
    (fibreEquiv core degree y y' c).IsOdd ↔ c.IsOdd := by
  obtain ⟨member, rfl⟩ := GeometricFibre.cls_surjective c
  rw [fibreEquiv_cls, GeometricFibre.isOdd_cls_iff, GeometricFibre.isOdd_cls_iff]
  exact Iff.rfl

theorem oddCount_eq (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) :
    GeometricFibre.oddCount core y degree = GeometricFibre.oddCount core y' degree :=
  Nat.card_congr (Equiv.subtypeEquiv (fibreEquiv core degree y y')
    fun c ↦ (isOdd_fibreEquiv core degree y y' c).symm)

/-- The open odd count, the one the genus-six assembly uses, is constant on a wall-free
interval of requests, on the geometric quotient itself. -/
theorem openOddCount_eq_of_no_wall (core : Core n p) (degree : ℕ)
    (y₀ y₁ : Fin p → ℚ) (u v : ℚ)
    (hno : ∀ (k : Frame core degree) (col : Fin p) (t : ℚ), min u v ≤ t → t ≤ max u v →
      ¬ k.IsWallParam y₀ y₁ col t) :
    GeometricFibre.openOddCount core (RationalAffineWall.segment y₀ y₁ u) degree =
      GeometricFibre.openOddCount core (RationalAffineWall.segment y₀ y₁ v) degree :=
  Nat.card_congr (Equiv.subtypeEquiv
    (fibreEquiv core degree (RationalAffineWall.segment y₀ y₁ u)
      (RationalAffineWall.segment y₀ y₁ v))
    fun c ↦ and_congr
      (open_fibreEquiv_iff_of_no_wall core degree y₀ y₁ u v hno c).symm
      (isOdd_fibreEquiv core degree _ _ c).symm)

end DraismaVargas.Count.GeometricSegmentWalls
