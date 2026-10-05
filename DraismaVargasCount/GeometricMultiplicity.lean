module

public import DraismaVargasCount.GeometricStableTransport
public import DraismaVargasCount.GeometricValidityTransport
public import DraismaVargasCount.TransportMultiplicity

@[expose] public section

/-!
# Multiplicity and coordinates under orientation-independent transport

The actual geometric incidence dictionaries preserve the presentation matrix,
its row denominators and target leaf normalization. Thus absolute multiplicity
is invariant even when stored endpoint orientations change. Coordinates follow
from matrix invertibility and preservation of the core's row labels; they are
not an additional isomorphism hypothesis.

This extends the strict transport proofs to the geometric dictionaries.
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GluingDatum.LengthMatrixPresentation
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource

variable {target₁ target₂ : CFGraph} {degree : ℕ}

namespace GeometricDatumIso

variable {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

theorem isLeafVertex_map (iso : GeometricDatumIso first second) (vertex : target₁.V) :
    IsLeafVertex target₂ (iso.targetVertex vertex) ↔ IsLeafVertex target₁ vertex := by
  unfold IsLeafVertex
  rw [iso.incidentEdges_card_map]

/-- The number of leaves of the target is preserved, so the normalisation
`2^{l(T)}` of the multiplicity is the same on both sides. -/
theorem leafCount_map (iso : GeometricDatumIso first second) : leafCount target₂ = leafCount target₁ := by
  classical
  unfold leafCount leafVertices
  refine (Finset.card_bij (fun vertex _ ↦ iso.targetVertex vertex) ?_ ?_ ?_).symm
  · intro vertex hVertex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hVertex ⊢
    exact (iso.isLeafVertex_map vertex).mpr hVertex
  · exact fun _ _ _ _ h ↦ iso.targetVertex.injective h
  · intro vertex hVertex
    refine ⟨iso.targetVertex.symm vertex, ?_, iso.targetVertex.apply_symm_apply vertex⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hVertex ⊢
    refine (iso.isLeafVertex_map _).mp ?_
    rwa [Equiv.apply_symm_apply]

end GeometricDatumIso

namespace GeometricMultiplicity

/-! ## The transported presentation -/

section Presentation

variable {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The transported stable labelling**: the rows follow the induced
dictionary of stable paths, the columns the target relabelling. -/
noncomputable def transportLabelling (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (labelling : StableLengthMatrixLabelling first coordinate) :
    StableLengthMatrixLabelling second coordinate where
  targetEdge := labelling.targetEdge.trans iso.targetEdge
  row := (iso.stablePathEquiv hConnected).symm.trans labelling.row

/-- **The length matrix is literally unchanged.**  Both presentations use the
same coordinate type, and the transported labelling matches row `i` with row
`i` and column `t` with column `t`. -/
theorem matrix_transportLabelling (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (labelling : StableLengthMatrixLabelling first coordinate) :
    matrix (transportLabelling iso hConnected labelling).presentation =
      matrix labelling.presentation := by
  funext sourceRow column
  rw [StableSourceMatrix.labelling_matrix_eq, StableSourceMatrix.labelling_matrix_eq]
  exact iso.matrix_map hConnected _ _

theorem denominatorProduct_transportLabelling (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (labelling : StableLengthMatrixLabelling first coordinate) :
    denominatorProduct (transportLabelling iso hConnected labelling).presentation =
      denominatorProduct labelling.presentation := by
  unfold denominatorProduct rowDenominator
  rw [matrix_transportLabelling]

/-- **The multiplicity is preserved by the transport.** -/
theorem absMult_transportLabelling (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (labelling : StableLengthMatrixLabelling first coordinate) :
    absMult (transportLabelling iso hConnected labelling).presentation =
      absMult labelling.presentation := by
  unfold absMult signedMult
  rw [matrix_transportLabelling, denominatorProduct_transportLabelling,
    iso.leafCount_map]

/-- **Multiplicity is an isomorphism invariant, at the level of gluing data.**  Any two honest stable
labellings of isomorphic gluing data, on one coordinate type, give the same
multiplicity.  No full-dimensionality, no integrality, and no relation between
the two labellings is required. -/
theorem absMult_eq_of_datumIso (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    (source : StableLengthMatrixLabelling first coordinate)
    (image : StableLengthMatrixLabelling second coordinate) :
    absMult image.presentation = absMult source.presentation :=
  (absMult_labelling_indep image (transportLabelling iso hConnected source)).trans
    (absMult_transportLabelling iso hConnected source)

/-- **The transported full-dimensional presentation.** -/
noncomputable def transportFullDim (iso : GeometricDatumIso first second)
    (fd : FullDimensionalSourcePresentation first coordinate) :
    FullDimensionalSourcePresentation second coordinate where
  valid := iso.valid_map fd.valid
  targetConnected := iso.targetConnected_map fd.targetConnected
  targetGenus := by rw [iso.targetGenus_map]; exact fd.targetGenus
  saturated := by
    rw [iso.targetEdgeCard_map, iso.sourceGenus_map]
    exact fd.saturated
  labelling := transportLabelling iso fd.valid.1 fd.labelling
  det_ne_zero := by
    rw [matrix_transportLabelling]
    exact fd.det_ne_zero
  trivalent := iso.trivalent_map fd.valid.1 fd.trivalent
  pathEnds := iso.hasPathEnds_map fd.valid.1 fd.pathEnds

@[simp] theorem transportFullDim_labelling (iso : GeometricDatumIso first second)
    (fd : FullDimensionalSourcePresentation first coordinate) :
    (transportFullDim iso fd).labelling = transportLabelling iso fd.valid.1 fd.labelling := rfl

theorem fdAbsMult_transportFullDim (iso : GeometricDatumIso first second)
    (fd : FullDimensionalSourcePresentation first coordinate) :
    fdAbsMult (transportFullDim iso fd) = fdAbsMult fd :=
  absMult_transportLabelling iso fd.valid.1 fd.labelling

/-- **Multiplicity is an isomorphism invariant, on full-dimensional presentations.**  Isomorphic gluing
data have equal multiplicity, whatever presentations they carry. -/
theorem fdAbsMult_eq_of_datumIso (iso : GeometricDatumIso first second)
    (source : FullDimensionalSourcePresentation first coordinate)
    (image : FullDimensionalSourcePresentation second coordinate) :
    fdAbsMult image = fdAbsMult source :=
  absMult_eq_of_datumIso iso source.valid.1 source.labelling image.labelling

end Presentation

/-! ## Transport of a labelled fibre member -/

section Member

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)

variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}

/-- **The transported core identification.**  The label of the stable graph
travels along the induced dictionaries, so the transported datum carries the
same request. -/
noncomputable def transportIdent {target₁ target₂ : CFGraph.{0}}
    {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
    (iso : GeometricDatumIso first second) (hConnected : first.Connected)
    (ident : CoreIdentification core first) : CoreIdentification core second where
  vertex := (iso.branchVertexEquiv hConnected).symm.trans ident.vertex
  row := (iso.stablePathEquiv hConnected).symm.trans ident.row
  incidence branch slot := by
    have hBase := ident.incidence ((iso.branchVertexEquiv hConnected).symm branch)
      slot
    have hMap := iso.incidenceCount_map hConnected
      (((iso.branchVertexEquiv hConnected).symm branch) : BranchVertex first).1
      (ident.row.symm slot)
    have hVertex : iso.sourceVertexEquiv
        (((iso.branchVertexEquiv hConnected).symm branch) : BranchVertex first).1 =
        branch.1 := congrArg Subtype.val
          ((iso.branchVertexEquiv hConnected).apply_symm_apply branch)
    rw [hVertex] at hMap
    rw [show ((iso.stablePathEquiv hConnected).symm.trans ident.row).symm slot =
        iso.stablePathEquiv hConnected (ident.row.symm slot) from rfl, ← hMap]
    exact hBase

/-- **The transported member.**  Its coordinates are literally those of the
original: the length matrix is unchanged and the requested lengths are read
through the same row dictionary. -/
noncomputable def transportMember (member : FibreMember core y degree)
    {target₂ : CFGraph.{0}} {second : GluingDatum target₂ degree}
    (iso : GeometricDatumIso member.data second) : FibreMember core y degree where
  target := target₂
  data := second
  fullDim := transportFullDim iso member.fullDim
  ident := transportIdent iso member.fullDim.valid.1 member.ident
  coords := member.coords
  realizes := by
    have hMatrix := matrix_transportLabelling iso member.fullDim.valid.1
      member.fullDim.labelling
    show (GluingDatum.LengthMatrixPresentation.matrix
      (transportFullDim iso member.fullDim).labelling.presentation).mulVec
      member.coords = _
    rw [transportFullDim_labelling, hMatrix]
    refine member.realizes.trans ?_
    funext row
    simp [transportIdent, transportLabelling]

@[simp] theorem transportMember_absMult (member : FibreMember core y degree)
    {target₂ : CFGraph.{0}} {second : GluingDatum target₂ degree}
    (iso : GeometricDatumIso member.data second) :
    (transportMember member iso).absMult = member.absMult :=
  fdAbsMult_transportFullDim iso member.fullDim

end Member

section Coordinates

open Utilities.Certificate.ExplicitPotential (Core)
variable {n p : ℕ} {core : Core n p} {y : Fin p → ℚ}
variable {first second : FibreMember core y degree}

/-- The requested lengths and induced stable-row dictionary force target
coordinates to agree, with no coordinate receipt. -/
theorem coords_eq_of_datumIso_member (iso : GeometricDatumIso first.data second.data)
    (hRow : ∀ path : StablePath first.data,
      second.ident.row (iso.stablePathEquiv first.fullDim.valid.1 path) =
        first.ident.row path)
    (column : Fin p) :
    second.coords (second.fullDim.labelling.targetEdge.symm
        (iso.targetEdge (first.fullDim.labelling.targetEdge column))) =
      first.coords column := by
  classical
  set transported := transportLabelling iso first.fullDim.valid.1 first.fullDim.labelling
    with htrans
  set ρ : Fin p ≃ Fin p := second.fullDim.labelling.row.symm.trans transported.row with hρ
  set γ : Fin p ≃ Fin p :=
    second.fullDim.labelling.targetEdge.trans transported.targetEdge.symm with hγ
  have hsub : second.matrix = first.matrix.submatrix ρ γ := by
    show matrix second.fullDim.labelling.presentation =
      (matrix first.fullDim.labelling.presentation).submatrix ρ γ
    rw [matrix_labelling_submatrix second.fullDim.labelling transported, hρ, hγ,
      matrix_transportLabelling iso first.fullDim.valid.1 first.fullDim.labelling]
  have hslot : ∀ r : Fin p,
      second.ident.row (second.fullDim.labelling.row.symm r) =
        first.ident.row (first.fullDim.labelling.row.symm (ρ r)) := by
    intro r
    have h := hRow ((iso.stablePathEquiv first.fullDim.valid.1).symm
      (second.fullDim.labelling.row.symm r))
    rw [Equiv.apply_symm_apply] at h
    have hrowsym : first.fullDim.labelling.row.symm (ρ r) =
        (iso.stablePathEquiv first.fullDim.valid.1).symm
          (second.fullDim.labelling.row.symm r) := by
      rw [hρ, htrans]
      simp [transportLabelling]
    rw [hrowsym]
    exact h
  have hrow : ∀ r : Fin p, second.matrix.mulVec (fun c ↦ first.coords (γ c)) r =
      first.matrix.mulVec first.coords (ρ r) := by
    intro r
    rw [hsub]
    show ∑ c, first.matrix (ρ r) (γ c) * first.coords (γ c) =
      ∑ c, first.matrix (ρ r) c * first.coords c
    exact Fintype.sum_equiv γ _ _ fun c ↦ by simp
  have hsolve : second.matrix.mulVec (fun c ↦ first.coords (γ c)) =
      fun row ↦ y (second.ident.row (second.fullDim.labelling.row.symm row)) := by
    funext r
    rw [hslot r, hrow r]
    exact congrFun first.realizes (ρ r)
  have huniq : (fun c ↦ first.coords (γ c)) = second.coords := second.coords_unique _ hsolve
  have hgamma : γ (second.fullDim.labelling.targetEdge.symm
      (iso.targetEdge (first.fullDim.labelling.targetEdge column))) = column := by
    rw [hγ, htrans]
    simp [transportLabelling]
  rw [← huniq]
  show first.coords (γ (second.fullDim.labelling.targetEdge.symm
    (iso.targetEdge (first.fullDim.labelling.targetEdge column)))) = first.coords column
  rw [hgamma]

end Coordinates
end GeometricMultiplicity
end DraismaVargas.Count
