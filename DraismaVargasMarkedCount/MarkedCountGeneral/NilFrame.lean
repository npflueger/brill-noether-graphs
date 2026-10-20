module

public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame
public import DraismaVargasCount.IntegerCount.WeightedCount

@[expose] public section

/-!
# Mark sets with the same members, and frames with no marks

**Mark sets with the same members** (§1). The marked notions of the ramification-one marked
count (`MarkedStablePath`,
`MarkedBranchVertex`, `markedIncidenceCount`, `HasMarkedPathEnds`, `MarkedLabelling`) depend on
a `Finset` of marks only through membership. Two mark sets with the same members give the same
marked rows, with the identity on representatives (`markedStablePathCongr`, which is `rfl` on
`markedRow`), so every marked receipt can be moved between them without a cast. The relabelling
of the marks in the drop lemma (module `DropRelabel`) needs this, because permuting the marks
changes `markSet markSource` only up to equality of members.

**No marks** (§2--§4). With no marks the marked notions are the unmarked ones (the
ramification-one `markedStablePathEmptyEquiv`, here for any mark set with no member). A typed
frame with `k = 0` is a `Frame` of the integer count (`TypedFrame.toFrame`, `ofFrame`), their
isomorphisms correspond, and the multiplicities and coordinates agree. Hence
**`typedCount_nil_eq_openMultCount'`**, the content of `Agreement.typedCount_nil_eq_openMultCount`.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Mark sets with the same members -/

section MarkCongr

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {M M' : Finset data.SourceVertex}

/-- Marked consecutiveness reads the marks only through membership. -/
theorem markedConsecutive_congr (h : ∀ v, v ∈ M ↔ v ∈ M') (first second : NonDanglingEdge data) :
    MarkedConsecutive data M first second ↔ MarkedConsecutive data M' first second := by
  simp only [MarkedConsecutive, h]

/-- **The marked rows of two mark sets with the same members**, identity on representatives. -/
def markedStablePathCongr (h : ∀ v, v ∈ M ↔ v ∈ M') :
    MarkedStablePath data M ≃ MarkedStablePath data M' :=
  Quot.congr (Equiv.refl _) fun first second ↦ markedConsecutive_congr h first second

@[simp] theorem markedStablePathCongr_markedRow (h : ∀ v, v ∈ M ↔ v ∈ M')
    (edge : NonDanglingEdge data) :
    markedStablePathCongr h (markedRow M edge) = markedRow M' edge := rfl

@[simp] theorem markedStablePathCongr_symm_markedRow (h : ∀ v, v ∈ M ↔ v ∈ M')
    (edge : NonDanglingEdge data) :
    (markedStablePathCongr h).symm (markedRow M' edge) = markedRow M edge := rfl

/-- The marked vertices of two mark sets with the same members. -/
def markedBranchVertexCongr (h : ∀ v, v ∈ M ↔ v ∈ M') :
    MarkedBranchVertex data M ≃ MarkedBranchVertex data M' :=
  Equiv.subtypeEquivRight fun v ↦ or_congr_right (h v)

/-- The incidence counts agree along `markedStablePathCongr`. -/
theorem markedIncidenceCount_congr (h : ∀ v, v ∈ M ↔ v ∈ M') (vertex : data.SourceVertex)
    (path : MarkedStablePath data M) :
    markedIncidenceCount data M' vertex (markedStablePathCongr h path) =
      markedIncidenceCount data M vertex path := by
  classical
  unfold markedIncidenceCount
  congr 1
  refine Finset.filter_congr fun edge _ ↦ ?_
  rw [← markedStablePathCongr_markedRow h edge]
  exact (markedStablePathCongr h).apply_eq_iff_eq

/-- Marked path ends read the marks only through membership. -/
theorem hasMarkedPathEnds_congr (h : ∀ v, v ∈ M ↔ v ∈ M') (hEnds : HasMarkedPathEnds data M) :
    HasMarkedPathEnds data M' := by
  intro edge
  obtain ⟨first, vertex, hRow, hIncident, hEnd⟩ := hEnds edge
  exact ⟨first, vertex, congrArg (markedStablePathCongr h) hRow, hIncident,
    hEnd.imp_right (h vertex).mp⟩

/-- A marked labelling, moved to a mark set with the same members. -/
def labellingCongrMarks {coordinate : Type*} (h : ∀ v, v ∈ M ↔ v ∈ M')
    (labelling : MarkedLabelling data M coordinate) : MarkedLabelling data M' coordinate :=
  ⟨labelling.targetEdge, (markedStablePathCongr h).symm.trans labelling.row⟩

/-- The presentation (hence the marked matrix) does not move. -/
theorem presentation_labellingCongrMarks {coordinate : Type*} (h : ∀ v, v ∈ M ↔ v ∈ M')
    (labelling : MarkedLabelling data M coordinate) :
    (labellingCongrMarks h labelling).presentation = labelling.presentation := rfl

/-- Marked full-dimensionality, moved to a mark set with the same members (and an equal
excess). -/
def _root_.DraismaVargas.Count.MarkedCount.MarkedFullDim.congrMarks {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    {excess excess' : ℤ} (h : ∀ v, v ∈ M ↔ v ∈ M') (hExcess : excess = excess')
    (fd : MarkedFullDim data M coordinate excess) : MarkedFullDim data M' coordinate excess' where
  valid := fd.valid
  targetConnected := fd.targetConnected
  targetGenus := fd.targetGenus
  saturated := by rw [← hExcess]; exact fd.saturated
  labelling := labellingCongrMarks h fd.labelling
  det_ne_zero := fd.det_ne_zero
  trivalent := fd.trivalent
  markValency v hv := fd.markValency v ((h v).mpr hv)
  pathEnds := hasMarkedPathEnds_congr h fd.pathEnds

end MarkCongr

/-! ## 2.  No marks: the marked notions are the unmarked ones -/

section Nil

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {M : Finset data.SourceVertex}

/-- With no member, marked consecutiveness is consecutiveness. -/
theorem markedConsecutive_nil_iff (h : ∀ v, v ∉ M) (first second : NonDanglingEdge data) :
    MarkedConsecutive data M first second ↔ Consecutive data first second := by
  simp only [MarkedConsecutive, Consecutive, h, not_false_eq_true, and_true]

/-- **With no member, the marked rows are the stable paths** (the
ramification-one `markedStablePathEmptyEquiv`, for any mark set with no member). -/
def markedStablePathNil (h : ∀ v, v ∉ M) : MarkedStablePath data M ≃ StablePath data :=
  Quot.congr (Equiv.refl _) fun first second ↦ markedConsecutive_nil_iff h first second

@[simp] theorem markedStablePathNil_markedRow (h : ∀ v, v ∉ M) (edge : NonDanglingEdge data) :
    markedStablePathNil h (markedRow M edge) = edge.stablePath := rfl

@[simp] theorem markedStablePathNil_symm_stablePath (h : ∀ v, v ∉ M)
    (edge : NonDanglingEdge data) :
    (markedStablePathNil h).symm edge.stablePath = markedRow M edge := rfl

/-- With no member, the marked vertices are the branch vertices. -/
def markedBranchVertexNil (h : ∀ v, v ∉ M) : MarkedBranchVertex data M ≃ BranchVertex data :=
  Equiv.subtypeEquivRight fun v ↦ by simp [h]

/-- With no member, the marked incidence counts are the stable-path incidence counts. -/
theorem markedIncidenceCount_nil (h : ∀ v, v ∉ M) (vertex : data.SourceVertex)
    (path : MarkedStablePath data M) :
    markedIncidenceCount data M vertex path =
      StablePathCount.incidenceCount data vertex (markedStablePathNil h path) := by
  classical
  unfold markedIncidenceCount StablePathCount.incidenceCount
  congr 1
  refine Finset.filter_congr fun edge _ ↦ ?_
  rw [← markedStablePathNil_markedRow h edge]
  exact (markedStablePathNil h).apply_eq_iff_eq.symm

theorem hasPathEnds_of_nil (h : ∀ v, v ∉ M) (hEnds : HasMarkedPathEnds data M) :
    HasPathEnds data := by
  intro edge
  obtain ⟨first, vertex, hRow, hIncident, hEnd⟩ := hEnds edge
  exact ⟨first, vertex, congrArg (markedStablePathNil h) hRow, hIncident,
    hEnd.resolve_right (h vertex)⟩

theorem hasMarkedPathEnds_of_nil (h : ∀ v, v ∉ M) (hEnds : HasPathEnds data) :
    HasMarkedPathEnds data M := by
  intro edge
  obtain ⟨first, vertex, hRow, hIncident, hEnd⟩ := hEnds edge
  exact ⟨first, vertex, (markedStablePathNil h).injective hRow, hIncident, Or.inl hEnd⟩

/-- A marked labelling with no mark is a stable labelling, with the same presentation. -/
def labellingToStable {coordinate : Type*} (h : ∀ v, v ∉ M)
    (labelling : MarkedLabelling data M coordinate) :
    StableLengthMatrixLabelling data coordinate :=
  ⟨labelling.targetEdge, (markedStablePathNil h).symm.trans labelling.row⟩

/-- A stable labelling as a marked labelling with no mark, with the same presentation. -/
def labellingToMarked {coordinate : Type*} (h : ∀ v, v ∉ M)
    (labelling : StableLengthMatrixLabelling data coordinate) :
    MarkedLabelling data M coordinate :=
  ⟨labelling.targetEdge, (markedStablePathNil h).trans labelling.row⟩

/-- The two literal presentations agree. They are not definitionally equal: the stable one
decides membership of a row with `DecidableEq coordinate`, the marked one classically. -/
theorem presentation_labellingToStable {coordinate : Type*} [DecidableEq coordinate]
    (h : ∀ v, v ∉ M) (labelling : MarkedLabelling data M coordinate) :
    (labellingToStable h labelling).presentation = labelling.presentation := by
  unfold StableLengthMatrixLabelling.presentation MarkedLabelling.presentation
  congr 1
  funext row
  unfold StableLengthMatrixLabelling.path MarkedLabelling.path
  exact List.filter_congr fun _ _ ↦ decide_eq_decide.mpr Iff.rfl

theorem presentation_labellingToMarked {coordinate : Type*} [DecidableEq coordinate]
    (h : ∀ v, v ∉ M) (labelling : StableLengthMatrixLabelling data coordinate) :
    (labellingToMarked h labelling).presentation = labelling.presentation := by
  unfold StableLengthMatrixLabelling.presentation MarkedLabelling.presentation
  congr 1
  funext row
  unfold StableLengthMatrixLabelling.path MarkedLabelling.path
  exact List.filter_congr fun _ _ ↦ decide_eq_decide.mpr Iff.rfl

end Nil

/-! ## 3.  Typed frames with no marks are the frames of the integer count -/

variable {n p degree : ℕ} {core : Core n p} {mark : Fin 0 → Fin n} {types : Fin 0 → ℕ}

theorem not_mem_markSet_nil {target : CFGraph} {data : GluingDatum target degree}
    (markSource : Fin 0 → data.SourceVertex) (v : data.SourceVertex) :
    v ∉ markSet markSource := by
  simp [markSet]

theorem typeExcess_nil (types : Fin 0 → ℕ) : typeExcess types = 0 := by
  simp [typeExcess]

namespace TypedFrame

/-- **A typed frame with no marks, as a frame of the integer count.** -/
def toFrame (κ : TypedFrame core mark types degree) : Frame core degree where
  target := κ.target
  data := κ.data
  fullDim :=
    { valid := κ.fullDim.valid
      targetConnected := κ.fullDim.targetConnected
      targetGenus := κ.fullDim.targetGenus
      saturated := by
        have h := κ.fullDim.saturated
        have h0 := typeExcess_nil types
        omega
      labelling := labellingToStable (not_mem_markSet_nil κ.markSource) κ.fullDim.labelling
      det_ne_zero := by rw [presentation_labellingToStable]; exact κ.fullDim.det_ne_zero
      trivalent := κ.fullDim.trivalent
      pathEnds := hasPathEnds_of_nil (not_mem_markSet_nil κ.markSource) κ.fullDim.pathEnds }
  ident :=
    { vertex := (markedBranchVertexNil (not_mem_markSet_nil κ.markSource)).symm.trans
        κ.ident.vertex
      row := (markedStablePathNil (not_mem_markSet_nil κ.markSource)).symm.trans κ.ident.row
      incidence := fun branch slot ↦ by
        have h := κ.ident.incidence
          ((markedBranchVertexNil (not_mem_markSet_nil κ.markSource)).symm branch) slot
        rw [markedIncidenceCount_nil (not_mem_markSet_nil κ.markSource)] at h
        exact h }

theorem toFrame_slot (κ : TypedFrame core mark types degree) (row : Fin p) :
    κ.toFrame.slot row = κ.slot row := by
  simp [Frame.slot, MarkedFrameBase.slot, toFrame, labellingToStable]

theorem toFrame_matrix (κ : TypedFrame core mark types degree) :
    κ.toFrame.matrix = κ.matrix :=
  congrArg GluingDatum.LengthMatrixPresentation.matrix (presentation_labellingToStable _ _)

theorem coordsAt_toFrame (κ : TypedFrame core mark types degree) (y : Fin p → ℚ) :
    κ.toFrame.coordsAt y = κ.coordsAt y := by
  unfold Frame.coordsAt MarkedFrameBase.coordsAt
  simp only [toFrame_slot, toFrame_matrix]

theorem openAt_toFrame_iff (κ : TypedFrame core mark types degree) (y : Fin p → ℚ) :
    κ.toFrame.OpenAt y ↔ κ.OpenAt y := by
  unfold Frame.OpenAt MarkedFrameBase.OpenAt
  rw [coordsAt_toFrame]

theorem ramifiedLeafImages_nil (κ : TypedFrame core mark types degree) :
    κ.ramifiedLeafImages = ∅ := by
  unfold ramifiedLeafImages
  simp

/-- **The multiplicities agree**: with no mark, `l* = l` and the typed formula is Part II's. -/
theorem absMult_toFrame (κ : TypedFrame core mark types degree) :
    κ.toFrame.absMult = κ.typedAbsMult := by
  rw [typedAbsMult, typedSignedMult_eq, ramifiedLeafImages_nil, Finset.card_empty, pow_zero,
    one_mul]
  change |Count.signedMult (labellingToStable _ κ.fullDim.labelling).presentation| = _
  rw [presentation_labellingToStable]

end TypedFrame

/-- **A frame of the integer count as a typed frame with no marks.** -/
def ofFrame (mark : Fin 0 → Fin n) (types : Fin 0 → ℕ) (f : Frame core degree) :
    TypedFrame core mark types degree where
  target := f.target
  data := f.data
  markSource := fun j ↦ j.elim0
  fullDim :=
    { valid := f.fullDim.valid
      targetConnected := f.fullDim.targetConnected
      targetGenus := f.fullDim.targetGenus
      saturated := by rw [typeExcess_nil, add_zero]; exact f.fullDim.saturated
      labelling := labellingToMarked (not_mem_markSet_nil _) f.fullDim.labelling
      det_ne_zero := by rw [presentation_labellingToMarked]; exact f.fullDim.det_ne_zero
      trivalent := f.fullDim.trivalent
      markValency := fun v hv ↦ absurd hv (not_mem_markSet_nil _ v)
      pathEnds := hasMarkedPathEnds_of_nil (not_mem_markSet_nil _) f.fullDim.pathEnds }
  ident :=
    { vertex := (markedBranchVertexNil (not_mem_markSet_nil _)).trans f.ident.vertex
      row := (markedStablePathNil (not_mem_markSet_nil _)).trans f.ident.row
      incidence := fun branch slot ↦ by
        rw [markedIncidenceCount_nil (not_mem_markSet_nil _)]
        simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
        exact f.ident.incidence (markedBranchVertexNil (not_mem_markSet_nil _) branch) slot
      vertex_mark := fun j ↦ j.elim0 }
  typed j := j.elim0

/-! ## 4.  Isomorphisms correspond, and the round trips -/

/-- A typed isomorphism with no marks is a frame isomorphism. -/
def TypedFrameIso.toFrameIso {κ κ' : TypedFrame core mark types degree}
    (iso : TypedFrameIso κ κ') :
    GeometricSegmentWalls.FrameIso κ.toFrame κ'.toFrame where
  datum := iso.datum
  overCore_vertex branch :=
    iso.overCore_vertex ⟨branch.1, Or.inl branch.2⟩ (Or.inl (by
      rw [iso.datum.nonDanglingValency_map κ.fullDim.valid.1]
      exact branch.2))
  overCore_row path := by
    induction path using Quot.ind with
    | mk edge => exact iso.overCore_row edge

/-- A frame isomorphism is a typed isomorphism of the frames with no marks. -/
def ofFrameIso (mark : Fin 0 → Fin n) (types : Fin 0 → ℕ) {f f' : Frame core degree}
    (iso : GeometricSegmentWalls.FrameIso f f') :
    TypedFrameIso (ofFrame mark types f) (ofFrame mark types f') where
  datum := iso.datum
  mark j := j.elim0
  overCore_vertex vertex _ :=
    iso.overCore_vertex ⟨vertex.1, vertex.2.resolve_right (not_mem_markSet_nil _ _)⟩
  overCore_row edge := iso.overCore_row edge.stablePath

/-- The round trip through frames, on typed frames, up to isomorphism. -/
def ofFrame_toFrameIso (κ : TypedFrame core mark types degree) :
    TypedFrameIso (ofFrame mark types κ.toFrame) κ where
  datum := GeometricDatumIso.refl κ.data
  mark j := j.elim0
  overCore_vertex _ _ := rfl
  overCore_row _ := rfl

/-- The round trip through typed frames, on frames, up to isomorphism. -/
def toFrame_ofFrameIso (f : Frame core degree) :
    GeometricSegmentWalls.FrameIso (ofFrame mark types f).toFrame f where
  datum := GeometricDatumIso.refl f.data
  overCore_vertex _ := rfl
  overCore_row path := by
    induction path using Quot.ind with
    | mk _ => rfl

/-! ## 5.  The count -/

/-- **Typed frame classes with no marks are the frame classes of the integer count.** -/
noncomputable def nilClassEquiv (mark : Fin 0 → Fin n) (types : Fin 0 → ℕ) :
    TypedFrameClass core mark types degree ≃ CrossCoreTransport.FrameClass core degree where
  toFun := Quot.lift (fun κ ↦ CrossCoreTransport.FrameClass.mk κ.toFrame) fun _ _ h ↦
    h.elim fun iso ↦ CrossCoreTransport.FrameClass.mk_eq_mk_iff.mpr ⟨iso.toFrameIso⟩
  invFun := Quotient.lift (fun f ↦ TypedFrameClass.mk (ofFrame mark types f)) fun _ _ h ↦
    h.elim fun iso ↦ TypedFrameClass.mk_eq_mk_of_iso ⟨ofFrameIso mark types iso⟩
  left_inv x := by
    induction x using Quot.ind with
    | mk κ => exact TypedFrameClass.mk_eq_mk_of_iso ⟨ofFrame_toFrameIso κ⟩
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h f => exact CrossCoreTransport.FrameClass.mk_eq_mk_iff.mpr ⟨toFrame_ofFrameIso f⟩

/-- **With no marks, the typed count is the weighted count of the integer count.** -/
theorem typedCount_nil_eq_openMultCount' (core : Core n p) (mark : Fin 0 → Fin n)
    (types : Fin 0 → ℕ) (y : Fin p → ℚ) (degree : ℕ) :
    typedCount core mark types y degree =
      (IntegerCount.openMultCount core y degree : ℚ) := by
  rw [IntegerCount.openMultCount_cast_eq_frameSum]
  let e : TypedFibre core mark types y degree ≃
      {x : CrossCoreTransport.FrameClass core degree // x.OpenAt y} :=
    (nilClassEquiv mark types).subtypeEquiv fun x ↦ by
      induction x using Quot.ind with
      | mk κ => exact (κ.openAt_toFrame_iff y).symm
  unfold typedCount
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun x ↦ ?_
  obtain ⟨x, hx⟩ := x
  induction x using Quot.ind with
  | mk κ => exact κ.absMult_toFrame.symm

end DraismaVargas.Count.MarkedCountGeneral
