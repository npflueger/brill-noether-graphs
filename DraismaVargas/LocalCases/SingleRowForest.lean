import DraismaVargas.LocalCases.NonTrivalentWallSetup
import DraismaVargas.LocalCases.CycleRows
import DraismaVargas.LocalCases.StableGraphIncidence

/-!
# A single non-loop stable row may collapse without losing genus

The wall crossing of Vargas, Part II contracts a non-loop edge of the stable
source. At its open facet every other stable row retains positive length. The
source-fibre forest theorem of `SourceFibreForest` requires *all* rows to be
nonzero and therefore does not apply.

The occurrence proof is direct. A minimal cycle contains every stable path
it touches. Every such path must be the sole possibly-zero row. A non-loop
row has an end at which exactly one of its occurrences is incident, whereas
a minimal cycle supplies two distinct occurrences there: a contradiction.

`HasSimpleEnd` states that non-loop fact on the actual stable source and is
preserved by the incidence dictionaries. This file does not produce
the dictionary identifying a requested Whitehead edge with the row.
-/

namespace DraismaVargas.LocalCases.SingleRowForest

open DraismaVargas.Infrastructure
open W4StableSource StablePathCount StableGraphIncidence
open ZeroForestBridge ZeroForestPreservation
open PresentationDecomposition
open Utilities.Certificate ContractionForestCensusGeneral
open Finset (univ)
open TerminalForestReceipt
  (exists_minimal_not_isForest exists_ne_slotAt_of_minimal notMem_of_separated)
open ZeroFreeTerminalFace (isForest_empty)

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- A non-loop stable edge has an actual branch end at which it occurs once.
The count is occurrence-sensitive: a stable loop would occur twice. -/
def HasSimpleEnd (data : GluingDatum target degree) (path : StablePath data) : Prop :=
  ∃ vertex : BranchVertex data, incidenceCount data vertex.1 path = 1

/-- Two distinct actual branch ends provide the simple end. The fact that a
stable path has only two ends is the proved stable-path count, not a receipt. -/
theorem hasSimpleEnd_of_distinct_ends (hConnected : data.Connected)
    (hEnds : HasPathEnds data) (path : StablePath data)
    (first second : BranchVertex data) (hNe : first ≠ second)
    (hFirst : 0 < incidenceCount data first.1 path)
    (hSecond : 0 < incidenceCount data second.1 path) :
    HasSimpleEnd data path := by
  classical
  have hNeVertex : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hSubset : ({first.1, second.1} : Finset data.SourceVertex) ⊆
      univ.filter (fun v ↦ nonDanglingValency data v ≠ 2) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := first.2; omega⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := second.2; omega⟩
  have hBound := Finset.sum_le_sum_of_subset
    (f := fun v ↦ incidenceCount data v path) hSubset
  rw [Finset.sum_pair hNeVertex] at hBound
  change incidenceCount data first.1 path + incidenceCount data second.1 path ≤
    endCount data path at hBound
  rw [endCount_eq_two data
    (NonDanglingValency.nonDanglingValency_ne_one data hConnected) hEnds] at hBound
  exact ⟨first, by omega⟩

/-- Source graph dictionaries preserve the non-loop condition used here. -/
theorem hasSimpleEnd_transport {target' : CFGraph.{0}} {degree' : ℕ}
    {other : GluingDatum target' degree'} (certificate : Equivalence data other)
    {path : StablePath data} (h : HasSimpleEnd data path) :
    HasSimpleEnd other (certificate.row path) := by
  obtain ⟨vertex, hVertex⟩ := h
  exact ⟨certificate.vertex vertex, (certificate.incidence vertex path).symm.trans hVertex⟩

/-- Minimal cycles are saturated under the literal stable-path equivalence. -/
theorem mem_cycle_iff_of_stablePath_eq
    (realization : data.NonnegativeIntegralRealization)
    {C : Finset (Fin data.sourceGraph.edges.card)}
    (hNot : ¬ IsForest (UnitSubdivisionPresentation.core data.sourceGraph) C)
    (hMin : ∀ drop ∈ C,
      IsForest (UnitSubdivisionPresentation.core data.sourceGraph) (C.erase drop))
    (hSurvive : ∀ slot ∈ C, ¬ IsDangling data (realization.sourceEdgeAt slot))
    {first second : NonDanglingEdge data}
    (hPath : first.stablePath = second.stablePath) :
    slotOf data realization first.1 ∈ C ↔ slotOf data realization second.1 ∈ C := by
  have hChain := (stablePath_eq_iff first second).mp hPath
  clear hPath
  induction hChain with
  | rel first second hStep =>
    obtain ⟨_, vertex, hFirst, hSecond, hValency⟩ := hStep
    exact ⟨CycleRows.mem_of_meetsAt realization hNot hMin hSurvive first.2 second.2
        ⟨vertex, hFirst, hSecond, hValency⟩,
      CycleRows.mem_of_meetsAt realization hNot hMin hSurvive second.2 first.2
        ⟨vertex, hSecond, hFirst, hValency⟩⟩
  | refl edge => rfl
  | symm first second _ ih => exact ih.symm
  | trans first middle last _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Fintype coordinate] in
/-- All rows except one retain a nonzero occurrence; the remaining row has
a simple end. Then the full zero subgraph, including dangling edges, is a
census forest. No forest receipt is taken as input. -/
theorem isForest_of_single_row
    (labelling : StableLengthMatrixLabelling data coordinate)
    (realization : data.NonnegativeIntegralRealization) (facet : coordinate)
    (hRows : ∀ row, row ≠ facet → ∃ edge ∈ labelling.presentation.path row,
      realization.sourceLength edge ≠ 0)
    (hEnd : HasSimpleEnd data (labelling.row.symm facet)) :
    IsForest (UnitSubdivisionPresentation.core data.sourceGraph)
      realization.sourceZeroSet := by
  classical
  by_contra hNotForest
  obtain ⟨C, hSubset, hNot, hMin⟩ := exists_minimal_not_isForest
    (UnitSubdivisionPresentation.core data.sourceGraph) realization.sourceZeroSet hNotForest
  have hSurvive : ∀ slot ∈ C, ¬ IsDangling data (realization.sourceEdgeAt slot) := by
    intro slot hSlot hDangling
    exact notMem_of_separated _ hNot hMin
      (fun F ↦ CycleRows.not_reachIn_of_isDangling data realization hDangling F rfl) hSlot
  have hZero {edge : data.SourceEdge} (hMem : slotOf data realization edge ∈ C) :
      realization.sourceLength edge = 0 := by
    have h := (realization.mem_sourceZeroSet _).mp (hSubset hMem)
    simpa only [sourceEdgeAt_slotOf] using h
  have hClass (slot : Fin data.sourceGraph.edges.card) (hSlot : slot ∈ C) :
      labelling.row (NonDanglingEdge.stablePath
        (⟨realization.sourceEdgeAt slot, hSurvive slot hSlot⟩ : NonDanglingEdge data)) = facet := by
    let edge : NonDanglingEdge data := ⟨realization.sourceEdgeAt slot, hSurvive slot hSlot⟩
    by_contra hNe
    obtain ⟨other, hOther, hPositive⟩ := hRows (labelling.row edge.stablePath) hNe
    obtain ⟨hOtherSurvive, hRow⟩ := (mem_presentation_path_iff labelling _ other).mp hOther
    have hPath := labelling.row.injective hRow
    have hMem := (mem_cycle_iff_of_stablePath_eq realization hNot hMin hSurvive hPath).mpr
      (show slotOf data realization edge.1 ∈ C by simpa [edge] using hSlot)
    exact hPositive (hZero hMem)
  obtain ⟨start, hStart⟩ : C.Nonempty := by
    rcases C.eq_empty_or_nonempty with hEmpty | hNonempty
    · subst C
      exact (hNot (isForest_empty _)).elim
    · exact hNonempty
  obtain ⟨vertex, hCount⟩ := hEnd
  obtain ⟨edge, hIncident, hPath⟩ := (incidenceCount_pos_iff data vertex.1
    (labelling.row.symm facet)).mp (by omega)
  have hStartPath : NonDanglingEdge.stablePath
      (⟨realization.sourceEdgeAt start, hSurvive start hStart⟩ : NonDanglingEdge data) =
      labelling.row.symm facet :=
    labelling.row.injective (by simpa using hClass start hStart)
  have hMem : slotOf data realization edge.1 ∈ C :=
    (mem_cycle_iff_of_stablePath_eq realization hNot hMin hSurvive
      (hPath.trans hStartPath.symm)).mpr (by simpa using hStart)
  let label := (sourceVertexEquiv data).symm vertex.1
  have hVertex : sourceVertexOf data label = vertex.1 := by
    exact (sourceVertexEquiv data).apply_symm_apply vertex.1
  have hAt : TerminalForestReceipt.SlotAt (UnitSubdivisionPresentation.core data.sourceGraph)
      (slotOf data realization edge.1) label := by
    rw [CycleRows.slotAt_iff_incident data realization, sourceEdgeAt_slotOf, hVertex]
    exact hIncident
  obtain ⟨other, hOther, hOtherNe, hOtherAt⟩ := exists_ne_slotAt_of_minimal _
    hNot hMin (CycleRows.core_loopless data) hMem hAt
  rw [CycleRows.slotAt_iff_incident data realization, hVertex] at hOtherAt
  let otherEdge : NonDanglingEdge data := ⟨realization.sourceEdgeAt other, hSurvive other hOther⟩
  have hOtherPath : otherEdge.stablePath = labelling.row.symm facet :=
    labelling.row.injective (by simpa [otherEdge] using hClass other hOther)
  have hEqual : edge = otherEdge := by
    apply (Finset.card_le_one.mp (show ((incidentEdges data vertex.1).filter
      (fun e ↦ e.stablePath = labelling.row.symm facet)).card ≤ 1 from hCount.le))
    · exact Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hIncident, hPath⟩
    · exact Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hOtherAt, hOtherPath⟩
  apply hOtherNe
  have hEdgeEq := congrArg Subtype.val hEqual
  have hSlotEq := congrArg (slotOf data realization) hEdgeEq
  simpa only [otherEdge, slotOf_sourceEdgeAt] using hSlotEq.symm

/-- Metric form at a Part II open facet. Only the selected non-loop row may
vanish. Its actual source zero set is proved to be a forest. -/
theorem noContractedCycle_of_single_row
    (labelling : StableLengthMatrixLabelling data coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : HasSimpleEnd data (labelling.row.symm facet)) :
    NonTrivalentWallSetup.NoContractedCycle labelling.presentation coordinates hNonnegative := by
  apply isForest_of_single_row labelling
    (NonTrivalentWallSetup.wallRealization labelling.presentation coordinates hNonnegative)
    facet ?_ hEnd
  intro row hNe
  by_contra hNone
  push Not at hNone
  apply hRows row hNe
  rw [GluingDatum.LengthMatrixPresentation.matrix_mulVec]
  unfold GluingDatum.sourcePathLength
  apply List.sum_eq_zero
  intro term hTerm
  obtain ⟨edge, hEdge, rfl⟩ := List.mem_map.mp hTerm
  have hZero := (GluingDatum.NonnegativeIntegralRealization.ofNonnegativeRational_sourceLength_eq_zero_iff
    data (fun edge ↦ coordinates (labelling.presentation.targetEdge.symm edge))
    (fun edge ↦ hNonnegative (labelling.presentation.targetEdge.symm edge)) edge).mp (hNone edge hEdge)
  simp only [GluingDatum.sourceEdgeLength, hZero, zero_div]

/-- Feed the single-row argument directly to the contraction validity
interface used by the Part II wall setup. -/
theorem contractionForest_of_single_row
    (labelling : StableLengthMatrixLabelling data coordinate)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (facet : coordinate)
    (hRows : ∀ row, row ≠ facet →
      (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).mulVec
        coordinates row ≠ 0)
    (hEnd : HasSimpleEnd data (labelling.row.symm facet))
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b))
    (hZero : coordinates (labelling.targetEdge.symm contracted) = 0) :
    ContractionRamification.ContractionForest data a b contracted :=
  NonTrivalentWallSetup.contractionForest_of_noContractedCycle labelling.presentation
    coordinates hNonnegative
    (noContractedCycle_of_single_row labelling coordinates hNonnegative facet hRows hEnd)
    hc hZero

end DraismaVargas.LocalCases.SingleRowForest
