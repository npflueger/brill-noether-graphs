import DraismaVargas.LocalCases.InteriorGraphTracking
import DraismaVargas.LocalCases.M11HonestGaugeFamily
import DraismaVargas.LocalCases.W3ShiftGraphTracking
import DraismaVargas.LocalCases.IncomingSourceCases
import DraismaVargas.LocalCases.M11FullDimensional
import DraismaVargas.LocalCases.M11IncomingMatching

/-!
# Same-candidate graph and row tracking for Figure 32

Source: Draisma--Vargas Part I, §5.2 (compatible labellings and the
limit-matrix lemma) and case `{w2-r2-nd3-M-11}` (Figure 32 and Equation (6)).
The three actual M-11 members already carry literal stable-row equivalences
(`M11StableGraphs.equivalence`, the remote branch swap included). Their
member-to-member row formula is read directly off the outgoing labelling
definitions, which is what lets a selected member receive its
full-dimensional presentation and its `Tracks` witness under one binder.

What is proved here: the row equation `outgoingLabelling_row`; the tracked
incoming normalization `exists_matched_tracking`, which retains the actual
stable-incidence certificate together with its recovered row equation;
`base_valid`, the validity of the base datum of each Figure 32 position; and
`exists_w2M11_payload`, which reads the case's occurrence profile off the
`w2M11` tag of `IncomingSourceCases.W2.Classification`.

What is NOT proved here: no new positive exit, determinant balance or
occurrence census. The producer `M11IncomingMatching.exists_matching` is
consumed verbatim. The standing hypotheses are explicit: the incoming datum
with its full-dimensional presentation, the contraction forest, dangling
compatibility, the two-star and its wall input. Full-dimensionality of an
outgoing member is only ever obtained at a member whose own honest determinant
is nonzero. Matrix equality is never used to identify a graph: every graph
identification below is an actual `StableGraphIncidence.Equivalence`.

Consumers: the tracked march (`TrackedWallProgress`), alongside
`W3Nd2GraphTracking` and `W3ShiftTrackedFinal`. The tracked-exit output shape
is `W3ShiftGraphTracking.TrackedCertifiedExit`, which despite its file name is
general.
-/

namespace DraismaVargas.LocalCases.W2M11GraphTracking

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open W4Assembly W4StableSource W2R1Target SecondEquation
open FullDimensionalSource InteriorGraphTracking
open M11SourceCandidates M11RemoteCandidates M11FullDimensional

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

section Member

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)
  (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation
    (candidates input profile hCard incoming).datum coordinate)

/-- The compatible outgoing labelling names each actual stable row through the
member-to-member incidence dictionary of `M11StableGraphs`. This is read off
the labelling definitions; no row compatibility is assumed. -/
theorem outgoingLabelling_row (outgoing : Fin 3) :
    (outgoingLabelling input profile hCard incoming incomingFD outgoing).row =
      (M11StableGraphs.between input profile hCard incoming outgoing).row.symm.trans
        incomingFD.labelling.row := by
  ext r
  simp [outgoingLabelling, M11CommonBalance.labelling, M11CommonBalance.sourceCoordinates,
    initialLabelling, M11StableGraphs.between, StableGraphIncidence.Equivalence.symm,
    StableGraphIncidence.Equivalence.trans, M11StableGraphs.equivalence_row]

end Member

section Arbitrary

/-! ## The tracked normalization of an arbitrary incoming cover

`M11IncomingMatching.exists_matching` names the identified member by an
equation of gluing data, reached from the incoming datum by one target
relabelling and one sheet relabelling. Both relabellings transport a
full-dimensional presentation literally (`RelabelFullDimensional`) and are
stable-incidence equivalences (`TargetRelabelStable.graphEquivalence`,
`StableGraphIncidence.sheetRelabel`), so the incoming tracked graph travels
with the presentation and the row equation is the composite's. -/

private theorem matched_of_relabel {first second : CFGraph} {size : ℕ}
    {source : GluingDatum first size} (iso : Utilities.CFGraphIso first second)
    (sourceFD : FullDimensionalSourcePresentation source coordinate)
    (sheets : (GluingTransport.transport iso source).SheetRelabeling)
    {member : GluingDatum second size} (hEq : sheets.apply = member)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks sourceFD graph label) :
    ∃ fd : FullDimensionalSourcePresentation member coordinate,
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix sourceFD.labelling.presentation ∧
        fd.labelling.targetEdge =
            sourceFD.labelling.targetEdge.trans (GluingTransport.edgeEquiv iso) ∧
          ∃ certificate : StableGraphIncidence.Equivalence source member,
            fd.labelling.row = certificate.row.symm.trans sourceFD.labelling.row ∧
            Nonempty (Tracks fd graph label) := by
  cases hEq
  have hTargetTracks :
      Tracks (RelabelFullDimensional.targetPresentation iso sourceFD) graph label :=
    throughIncidence current (RelabelFullDimensional.targetPresentation iso sourceFD)
      (TargetRelabelStable.graphEquivalence iso source sourceFD.valid.1) rfl
  refine ⟨RelabelFullDimensional.sheetPresentation sheets
      (RelabelFullDimensional.targetPresentation iso sourceFD), ?_, rfl,
    (TargetRelabelStable.graphEquivalence iso source sourceFD.valid.1).trans
      (StableGraphIncidence.sheetRelabel sheets
        (RelabelFullDimensional.targetPresentation iso sourceFD).valid.1), ?_,
    ⟨throughIncidence hTargetTracks
      (RelabelFullDimensional.sheetPresentation sheets
        (RelabelFullDimensional.targetPresentation iso sourceFD))
      (StableGraphIncidence.sheetRelabel sheets
        (RelabelFullDimensional.targetPresentation iso sourceFD).valid.1) rfl⟩⟩
  · exact (RelabelFullDimensional.sheet_matrix_eq sheets
      (RelabelFullDimensional.targetPresentation iso sourceFD).valid.1
      (RelabelFullDimensional.targetPresentation iso sourceFD).labelling).trans
      (RelabelFullDimensional.target_matrix_eq iso source sourceFD.valid.1 sourceFD.labelling)
  · ext path
    rfl

-- The source-facing certified-family and march interfaces use small graphs.
variable {target : CFGraph.{0}} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (incoming : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  (hCompat : WallDegeneration.DanglingCompatible incoming hc hab hOne)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
  {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum incoming hc hab hOne) star block)
  (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard block.1 = 2)

include hForest hCompat

/-- The identified Figure 32 member carries an honest presentation in exactly
the original coordinates, an actual stable-incidence certificate, the row
equation that certificate forces, and the incoming cover's tracked graph. The
target relabelling and the sheet relabelling each transport the tracking
literally; no family membership is assumed. -/
theorem exists_matched_tracking
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label) :
    ∃ position : Fin 3,
      ∃ fd : FullDimensionalSourcePresentation
          (candidates input profile hCard position).datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          fd.labelling.targetEdge.symm
              (M11CommonBalance.columnEquiv input profile hCard position none) =
            fullDim.labelling.targetEdge.symm contracted ∧
          ∃ certificate : StableGraphIncidence.Equivalence incoming
              (candidates input profile hCard position).datum,
            fd.labelling.row = certificate.row.symm.trans fullDim.labelling.row ∧
            Nonempty (Tracks fd graph label) := by
  classical
  obtain ⟨position, iso, sheets, hEq, hColumns, _rows, _hRowMk, _hNatural⟩ :=
    M11IncomingMatching.exists_matching incoming hc hab hOne fullDim hForest hCompat
      input profile hCard
  obtain ⟨fd, hMatrix, hEdge, certificate, hRows, hTrack⟩ :=
    matched_of_relabel iso fullDim sheets hEq current
  refine ⟨position, fd, hMatrix, ?_, certificate, hRows, hTrack⟩
  rw [hEdge]
  change fullDim.labelling.targetEdge.symm
    ((GluingTransport.edgeEquiv iso).symm
      (M11CommonBalance.columnEquiv input profile hCard position none)) = _
  rw [← hColumns none, Equiv.symm_apply_apply]
  rfl

/-! ## Retaining the actual Candidate and its base stage -/

omit hForest hCompat in
/-- The base datum of each Figure 32 position is valid: positions `0` and `2`
sit over the wall datum itself and position `1` over the branch-swapped copy,
whose validity is the sheet relabelling's. -/
theorem base_valid (hValid : (contractDatum incoming hc hab hOne).Valid) (i : Fin 3) :
    (M11HonestGaugeFamily.base profile hCard i).Valid := by
  match i with
  | 0 => exact hValid
  | 1 => exact ResolutionM11.wallBranchSwap_preserves_valid _ hValid _ _ _ _ _ _
  | 2 => exact hValid

end Arbitrary

section Classified

-- The source-facing certified-family and march interfaces use small graphs.
variable {target : CFGraph.{0}} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (incoming : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  (hCompat : WallDegeneration.DanglingCompatible incoming hc hab hOne)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W2SourceInput (contractDatum incoming hc hab hOne) star)

/-- The `w2M11` tag names the `m11` constructor, and that constructor already
carries the case's occurrence profile together with its two-sheet wall block.
No profile, family membership or graph/row compatibility is supplied. -/
theorem exists_w2M11_payload
    (classification : IncomingSourceCases.W2.Classification
      (contractDatum incoming hc hab hOne) star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w2M11) :
    ∃ wallBlock : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩,
      ∃ _sourceProfile : W2R2SourceProfile.SourceProfile
          (contractDatum incoming hc hab hOne) star wallBlock,
        ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard
          wallBlock.1 = 2 := by
  cases classification with
  | m11 wallBlock sourceProfile _ _ _ _ _ _ _ hBlockCard =>
      exact ⟨wallBlock, sourceProfile, hBlockCard⟩
  | m1k _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | mkk _ _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | p _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | r1 _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag

end Classified

end DraismaVargas.LocalCases.W2M11GraphTracking
