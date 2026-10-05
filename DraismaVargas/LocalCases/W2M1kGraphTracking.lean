module

public import DraismaVargas.LocalCases.W3InteriorGraphTracking
public import DraismaVargas.LocalCases.W3ShiftGraphTracking
public import DraismaVargas.LocalCases.W2M1kClosureUnconditional
public import DraismaVargas.LocalCases.W2M1kGaugeFamily
public import DraismaVargas.LocalCases.IncomingSourceCases
public import DraismaVargas.LocalCases.W2M1kArbitraryExit

@[expose] public section

/-!
# Same-candidate graph and row tracking for Figure 33

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7), with the factor of two in the second bracket of Equation (7)
explained in `W2M1kCommonBalance`.

`W2M1kCommonBalance.LimitColumns` builds every member's honest labelling out of
`LimitMember.row`, so the member-to-member row equation is between the
receipt's own row bijections. The five per-member stable-incidence dictionaries
that `W2M1kArbitraryExit` discharges read exactly those rows
(`alignedOrientationDictionary_row`, `separatedOrientationDictionary_row`, both
`rfl` position by position, the remote branch swap included, because
`SheetRelabelIncidence.equivalence` and `LimitChainCore.Gauge.ofSheetRelabeling`
take their rows from the same `SheetRelabelStable.stablePathEquiv`). The row
formula therefore holds with no new hypothesis, and the incoming cover's tracked
row-labelled graph travels to the selected outgoing member, under the SAME
full-dimensional presentation that carries the metric segment and the cleared
pencil.

Both orientations are covered: Base I.a (`alignedOrientation`, position `1`
remote) and Base II.2.2.M (`separatedOrientation`, position `0` remote).

What is proved here: the row equation `labelling_row`; the tracked member exit
in the incoming cover's own coordinates; the tracked incoming normalization
`exists_matched_tracking`, which retains the actual stable-incidence certificate
together with its recovered row equation; the three unconditional Figure 33
headlines in tracked form; and the source-facing
`exists_tracked_exit_of_classification`, whose only classification input is the
`w2M1k` tag of `IncomingSourceCases.W2.Classification`.

What is NOT proved here: no new determinant balance, occurrence census or
positive exit. `W2M1kArbitraryExit.exists_positive_exit_with_presentation`,
`W2M1kSelectedCensus`, `W2M1kLeafBackground` and
`W2M1kClosureUnconditional.headline_cases` are consumed verbatim. The standing
hypotheses remain explicit at the source-facing producer: the incoming datum
with its full-dimensional presentation, the contraction forest, the two-star,
its wall input and the positivity data of the exit. Full-dimensionality of an
outgoing member is only ever obtained at a member whose own honest determinant
is nonzero. Matrix equality is never used to identify a graph.

Used by: the tracked successor packaging of the march
(`InteriorBridgesDivalent`), alongside `W2M11GraphTracking`,
`W3Nd2GraphTracking` and `W3ShiftTrackedFinal`. The output proposition is
`W3ShiftGraphTracking.TrackedCertifiedExit`, which despite its file name is the
general tracked-exit output shape.
-/

namespace DraismaVargas.LocalCases.W2M1kGraphTracking

open DraismaVargas.Infrastructure
open TargetExpansion
open GraphContraction GluingContraction ContractionRamification WallDegeneration
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource InteriorGraphTracking
open W2M1kSourceCandidates
open W2M1kCommonBalance (LimitMember LimitColumns)
open W2M1kLimitColumns (alignedOrientation separatedOrientation)

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

section Member

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}
  {shape : Shape profile}

/-- The receipt's own row bijections give the member-to-member row equation
whenever the per-position dictionaries read the receipt's rows. Nothing is
assumed about the outgoing member beyond that. -/
theorem labelling_row (limit : LimitColumns profile shape)
    (dictionary : ∀ position : Fin 3,
      StableGraphIncidence.Equivalence data (limit.member position).datum)
    (hDictionaryRow : ∀ position : Fin 3,
      (dictionary position).row = (limit.member position).row)
    (incoming outgoing : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate) :
    (limit.labelling (W2M1kArbitraryExit.initialLabelling limit incoming incomingFD)
        outgoing).row =
      ((dictionary incoming).symm.trans (dictionary outgoing)).row.symm.trans
        incomingFD.labelling.row := by
  ext path
  simp [LimitColumns.labelling, LimitColumns.sourceCoordinates,
    W2M1kArbitraryExit.initialLabelling, hDictionaryRow,
    StableGraphIncidence.Equivalence.symm, StableGraphIncidence.Equivalence.trans]

/-- **The tracked Figure 33 member exit**, stated against the incoming cover's
own length matrix and its own contracted column, as the M-1k producers are.
The member-to-member incidence dictionary, the tracked row-labelled graph, the
metric segment and the cleared pencil all sit under the SAME outgoing
full-dimensional presentation. -/
theorem exists_tracked_member_exit (limit : LimitColumns profile shape)
    (input : W2SourceInput data star)
    (dictionary : ∀ position : Fin 3,
      StableGraphIncidence.Equivalence data (limit.member position).datum)
    (hDictionaryRow : ∀ position : Fin 3,
      (dictionary position).row = (limit.member position).row)
    (sourceGenus : ∀ position : Fin 3,
      genus (limit.member position).datum.sourceGraph = genus data.sourceGraph)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation (limit.member incoming).datum coordinate)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks incomingFD graph label)
    (originalMatrix : Matrix coordinate coordinate ℚ)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
      originalMatrix)
    (originalWallColumn : coordinate)
    (hWall : incomingFD.labelling.targetEdge.symm
      (occurrenceEquiv target wall (limit.member incoming).right none) = originalWallColumn)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z originalWallColumn = 0)
    (hzpos : ∀ i, i ≠ originalWallColumn → 0 < z i)
    (hDirection : incomingVelocity originalWallColumn < 0) :
    ∃ outgoing : Fin 3,
      ∃ outgoingFD : FullDimensionalSourcePresentation (limit.member outgoing).datum coordinate,
        Nonempty (StableGraphIncidence.Equivalence (limit.member incoming).datum
          (limit.member outgoing).datum) ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        originalMatrix.det *
          (GluingDatum.LengthMatrixPresentation.matrix
            outgoingFD.labelling.presentation).det < 0 ∧
        ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • velocity) i) ∧
          (GluingDatum.LengthMatrixPresentation.matrix
              outgoingFD.labelling.presentation).mulVec (z + t • velocity) =
            originalMatrix.mulVec z + t • originalMatrix.mulVec incomingVelocity ∧
          ∃ realization : (limit.member outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) * (z + t • velocity) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  have hWallColumn :
      limit.wallColumn (W2M1kArbitraryExit.initialLabelling limit incoming incomingFD) =
        originalWallColumn :=
    (W2M1kArbitraryExit.wallColumn_initialLabelling limit incoming incomingFD).trans hWall
  have hIncomingMatrix :
      limit.squareMatrix (W2M1kArbitraryExit.initialLabelling limit incoming incomingFD)
          incoming = originalMatrix :=
    (W2M1kArbitraryExit.squareMatrix_self limit incoming incomingFD).trans hMatrix
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, δ, hδ, hStep⟩ :=
    W2M1kArbitraryExit.exists_positive_exit_with_presentation limit input dictionary sourceGenus
      (W2M1kArbitraryExit.initialLabelling limit incoming incomingFD) hConnected hGenus incoming
      incomingFD (W2M1kArbitraryExit.squareMatrix_self_ne_zero limit incoming incomingFD)
      z incomingVelocity (hWallColumn ▸ hz) (hWallColumn ▸ hzpos) (hWallColumn ▸ hDirection)
  have hOutMatrix : GluingDatum.LengthMatrixPresentation.matrix
      outgoingFD.labelling.presentation =
      limit.squareMatrix (W2M1kArbitraryExit.initialLabelling limit incoming incomingFD)
        outgoing := by
    rw [hLabelling]
    rfl
  have hTrack : Tracks outgoingFD graph label := by
    refine throughIncidence current outgoingFD
      ((dictionary incoming).symm.trans (dictionary outgoing)) ?_
    rw [hLabelling]
    exact labelling_row limit dictionary hDictionaryRow incoming outgoing incomingFD
  refine ⟨outgoing, outgoingFD, ⟨(dictionary incoming).symm.trans (dictionary outgoing)⟩,
    ⟨hTrack⟩, ?_,
    W2M1kArbitraryExit.outgoingVelocity limit
      (W2M1kArbitraryExit.initialLabelling limit incoming incomingFD) incoming
      incomingVelocity outgoing, δ, hδ, ?_⟩
  · rw [hOutMatrix, ← hIncomingMatrix]
    exact hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, hPencil⟩ := hStep t ht htδ
    refine ⟨hPositive, ?_, ?_⟩
    · rw [hOutMatrix, ← hIncomingMatrix]
      exact hMetric
    · rw [hLabelling]
      exact hPencil

end Member

section Orientations

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- Base I.a's three discharged dictionaries read the receipt's own rows. The
remote position is `rfl` too: `SheetRelabelIncidence.equivalence` and
`LimitChainCore.Gauge.ofSheetRelabeling` take their row maps from the same
`SheetRelabelStable.stablePathEquiv`. -/
theorem alignedOrientationDictionary_row (input : W2SourceInput data star) (shape : Shape profile)
    (hTargetConnected : graph_connected target) (hGenus : genus target = 0)
    (pair : LeafPair profile) (position : Fin 3) :
    (W2M1kArbitraryExit.alignedOrientationDictionary input shape hTargetConnected hGenus pair
        position).row =
      ((alignedOrientation input shape pair hTargetConnected hGenus).member position).row := by
  fin_cases position <;> rfl

/-- Base II.2.2.M's three discharged dictionaries read the receipt's own rows. -/
theorem separatedOrientationDictionary_row (input : W2SourceInput data star)
    (shape : Shape profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) (divided : DividedData profile) (position : Fin 3) :
    (W2M1kArbitraryExit.separatedOrientationDictionary input shape hTargetConnected hGenus
        divided position).row =
      ((separatedOrientation input shape divided hTargetConnected hGenus).member
        position).row := by
  fin_cases position <;> rfl

end Orientations

section Matched

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- **One tracked incoming normalization, shared by the three Figure 33
members.** Its two `SameBlocks` inputs are exactly what
`W2M1kIncomingMatching.leaf_sameBlocks`, `divided_sameBlocks` and
`joined_sameBlocks` produce, and the three headlines below discharge them.
`W3Nd2IncomingMemberMatching.normalizedAgainst` supplies the honest presentation
in the original coordinates and `W3InteriorGraphTracking.matched_tracking_of_normalized`
recovers its geometric row equation from the actual natural matrices, so the
incoming cover's tracked graph travels with it. The column identity is
`IncomingMatchingCore.memberTargetIso_occurrence` at `none`. -/
theorem exists_matched_tracking
    (incoming : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (fullDim : FullDimensionalSourcePresentation incoming coordinate)
    (member : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum incoming hc hab hOne) ⟨a, hab⟩)
    (hPlacement : IncomingMatchingCore.Placement hc hab hOne member.right)
    (hVertices : ∀ vertex,
      ((GluingTransport.transport
          (IncomingMatchingCore.memberTargetIso incoming hc hab hOne member hPlacement)
          incoming).vertexPartition vertex).SameBlocks (member.datum.vertexPartition vertex))
    (hEdges : ∀ edge,
      ((GluingTransport.transport
          (IncomingMatchingCore.memberTargetIso incoming hc hab hOne member hPlacement)
          incoming).edgePartition edge).SameBlocks (member.datum.edgePartition edge))
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label) :
    ∃ fd : FullDimensionalSourcePresentation member.datum coordinate,
      GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
          GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
        fd.labelling.targetEdge.symm
            (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ member.right none) =
          fullDim.labelling.targetEdge.symm contracted ∧
        ∃ certificate : StableGraphIncidence.Equivalence incoming member.datum,
          fd.labelling.row = certificate.row.symm.trans fullDim.labelling.row ∧
          Nonempty (Tracks fd graph label) := by
  classical
  have hNorm := W3Nd2IncomingMemberMatching.normalizedAgainst incoming fullDim
    (IncomingMatchingCore.memberTargetIso incoming hc hab hOne member hPlacement)
    member.datum hVertices hEdges
  obtain ⟨fd, hMatrix, hEdge, hRows, hTrack⟩ :=
    W3InteriorGraphTracking.matched_tracking_of_normalized incoming fullDim current hNorm
  refine ⟨fd, hMatrix, ?_, _, hRows, hTrack⟩
  rw [hEdge]
  change fullDim.labelling.targetEdge.symm
    ((GluingTransport.edgeEquiv
        (IncomingMatchingCore.memberTargetIso incoming hc hab hOne member hPlacement)).symm
      (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ member.right none)) = _
  rw [← IncomingMatchingCore.memberTargetIso_occurrence incoming hc hab hOne member hPlacement
    fullDim.targetConnected fullDim.targetGenus none, Equiv.symm_apply_apply]
  rfl

end Matched

section Certified

-- The source-facing certified-family and march interfaces use small graphs.
variable {degree : ℕ}
  {incomingTarget : CFGraph.{0}} {a b : incomingTarget.V} {contracted : incomingTarget.edges}
  (incoming : GluingDatum incomingTarget degree)
  (hc : (contracted : incomingTarget.V × incomingTarget.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges incomingTarget a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  {wallStar : TwoStar (contract incomingTarget hab hOne) ⟨a, hab⟩}
  (wallInput : W2SourceInput (contractDatum incoming hc hab hOne) wallStar)
  {wallBlock : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
  (wallProfile : W2R2SourceProfile.SourceProfile (contractDatum incoming hc hab hOne)
    wallStar wallBlock)
  (wallShape : Shape wallProfile)

include fullDim wallInput

/-- Base I.a: the tracked exit from an identified position of the aligned
orientation, retaining the actual `BalancedGlobal.Candidate` and its valid
connected genus-zero base stage. Position `1` is remote, so its base is the
branch-swapped copy and its validity is the relabelling's. -/
theorem trackedCertifiedExit_of_aligned (pair : LeafPair wallProfile) (position : Fin 3)
    (fd : FullDimensionalSourcePresentation
      ((alignedOrientation wallInput wallShape pair
        (graph_connected_contract incomingTarget hab hOne fullDim.targetConnected)
        ((genus_contract incomingTarget hab hOne).trans
          fullDim.targetGenus)).member position).datum coordinate)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation)
    (hWall : fd.labelling.targetEdge.symm
      (occurrenceEquiv (contract incomingTarget hab hOne) ⟨a, hab⟩
        ((alignedOrientation wallInput wallShape pair
          (graph_connected_contract incomingTarget hab hOne fullDim.targetConnected)
          ((genus_contract incomingTarget hab hOne).trans
            fullDim.targetGenus)).member position).right none) =
      fullDim.labelling.targetEdge.symm contracted)
    (certificate : StableGraphIncidence.Equivalence incoming
      ((alignedOrientation wallInput wallShape pair
        (graph_connected_contract incomingTarget hab hOne fullDim.targetConnected)
        ((genus_contract incomingTarget hab hOne).trans
          fullDim.targetGenus)).member position).datum)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  have hConnected := graph_connected_contract incomingTarget hab hOne fullDim.targetConnected
  have hGenus := (genus_contract incomingTarget hab hOne).trans fullDim.targetGenus
  obtain ⟨outgoing, outgoingFD, hBetween, hTrack, hSign, velocity, δ, hδ, hStep⟩ :=
    exists_tracked_member_exit
      (alignedOrientation wallInput wallShape pair hConnected hGenus) wallInput
      (W2M1kArbitraryExit.alignedOrientationDictionary wallInput wallShape hConnected hGenus pair)
      (alignedOrientationDictionary_row wallInput wallShape hConnected hGenus pair)
      (W2M1kArbitraryExit.alignedOrientationSourceGenus wallInput wallShape hConnected hGenus
        pair)
      hConnected hGenus position fd current _ hMatrix _ hWall z incomingVelocity hz hzpos
      hDirection
  fin_cases outgoing
  · exact ⟨_, W2M1kGaugeFamily.alignedBase pair 0, ⟨a, hab⟩,
      W2M1kGaugeFamily.alignedCandidate wallInput wallShape pair hConnected hGenus 0,
      wallInput.valid, hConnected, hGenus, outgoingFD.valid,
      Nonempty.map (fun e ↦ certificate.trans e) hBetween, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩
  · exact ⟨_, W2M1kGaugeFamily.alignedBase pair 1, ⟨a, hab⟩,
      W2M1kGaugeFamily.alignedCandidate wallInput wallShape pair hConnected hGenus 1,
      (W2M1kTransport.swapRelabeling wallProfile pair.second pair.rel_second).valid
        wallInput.valid,
      hConnected, hGenus, outgoingFD.valid,
      Nonempty.map (fun e ↦ certificate.trans e) hBetween, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩
  · exact ⟨_, W2M1kGaugeFamily.alignedBase pair 2, ⟨a, hab⟩,
      W2M1kGaugeFamily.alignedCandidate wallInput wallShape pair hConnected hGenus 2,
      wallInput.valid, hConnected, hGenus, outgoingFD.valid,
      Nonempty.map (fun e ↦ certificate.trans e) hBetween, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩

/-- Base II.2.2.M: the same from an identified position of the separated
orientation, where position `0` is the remote one. -/
theorem trackedCertifiedExit_of_separated (divided : DividedData wallProfile) (position : Fin 3)
    (fd : FullDimensionalSourcePresentation
      ((separatedOrientation wallInput wallShape divided
        (graph_connected_contract incomingTarget hab hOne fullDim.targetConnected)
        ((genus_contract incomingTarget hab hOne).trans
          fullDim.targetGenus)).member position).datum coordinate)
    (hMatrix : GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation)
    (hWall : fd.labelling.targetEdge.symm
      (occurrenceEquiv (contract incomingTarget hab hOne) ⟨a, hab⟩
        ((separatedOrientation wallInput wallShape divided
          (graph_connected_contract incomingTarget hab hOne fullDim.targetConnected)
          ((genus_contract incomingTarget hab hOne).trans
            fullDim.targetGenus)).member position).right none) =
      fullDim.labelling.targetEdge.symm contracted)
    (certificate : StableGraphIncidence.Equivalence incoming
      ((separatedOrientation wallInput wallShape divided
        (graph_connected_contract incomingTarget hab hOne fullDim.targetConnected)
        ((genus_contract incomingTarget hab hOne).trans
          fullDim.targetGenus)).member position).datum)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  have hConnected := graph_connected_contract incomingTarget hab hOne fullDim.targetConnected
  have hGenus := (genus_contract incomingTarget hab hOne).trans fullDim.targetGenus
  obtain ⟨outgoing, outgoingFD, hBetween, hTrack, hSign, velocity, δ, hδ, hStep⟩ :=
    exists_tracked_member_exit
      (separatedOrientation wallInput wallShape divided hConnected hGenus) wallInput
      (W2M1kArbitraryExit.separatedOrientationDictionary wallInput wallShape hConnected hGenus
        divided)
      (separatedOrientationDictionary_row wallInput wallShape hConnected hGenus divided)
      (W2M1kArbitraryExit.separatedOrientationSourceGenus wallInput wallShape hConnected hGenus
        divided)
      hConnected hGenus position fd current _ hMatrix _ hWall z incomingVelocity hz hzpos
      hDirection
  fin_cases outgoing
  · exact ⟨_, W2M1kGaugeFamily.separatedBase wallProfile 0, ⟨a, hab⟩,
      W2M1kGaugeFamily.separatedCandidate wallInput wallShape divided hConnected hGenus 0,
      (W2M1kTransport.swapRelabeling wallProfile (pinSheet wallProfile 1)
        (W2SourceTransport.alignedTogether wallProfile)).valid wallInput.valid,
      hConnected, hGenus, outgoingFD.valid,
      Nonempty.map (fun e ↦ certificate.trans e) hBetween, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩
  · exact ⟨_, W2M1kGaugeFamily.separatedBase wallProfile 1, ⟨a, hab⟩,
      W2M1kGaugeFamily.separatedCandidate wallInput wallShape divided hConnected hGenus 1,
      wallInput.valid, hConnected, hGenus, outgoingFD.valid,
      Nonempty.map (fun e ↦ certificate.trans e) hBetween, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩
  · exact ⟨_, W2M1kGaugeFamily.separatedBase wallProfile 2, ⟨a, hab⟩,
      W2M1kGaugeFamily.separatedCandidate wallInput wallShape divided hConnected hGenus 2,
      wallInput.valid, hConnected, hGenus, outgoingFD.valid,
      Nonempty.map (fun e ↦ certificate.trans e) hBetween, outgoingFD, hTrack,
      hSign, velocity, δ, hδ, hStep⟩

include hForest wallProfile wallShape

/-- **Figure 33, Base I.a, tracked and unconditional.** The leaf pair and its
selected-class census are produced, not assumed; the `(1,3)` background census
is `W2M1kLeafBackground.leafBackgroundCensus`. -/
theorem exists_tracked_exit_of_incoming_leaf
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  obtain ⟨pair, selected⟩ := W2M1kSelectedCensus.exists_selectedCensus_leaf incoming hc hab
    hOne fullDim wallProfile wallShape hLeaf
  obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.leaf_sameBlocks incoming hc hab hOne
    fullDim wallInput wallProfile wallShape pair hLeaf selected
    (W2M1kLeafBackground.leafBackgroundCensus incoming hc hab hOne fullDim hForest wallInput
      wallProfile hLeaf)
  obtain ⟨fd, hMatrix, hWall, certificate, _hRows, ⟨hTrack⟩⟩ :=
    exists_matched_tracking incoming hc hab hOne fullDim
      (LeafPair.candidate wallInput wallShape pair)
      (W2M1kIncomingMatching.leafPlacement incoming hc hab hOne wallInput wallProfile wallShape
        pair hLeaf)
      hVertices hEdges current
  exact trackedCertifiedExit_of_aligned incoming hc hab hOne fullDim wallInput wallProfile
    wallShape pair 0 fd hMatrix hWall certificate hTrack z incomingVelocity hz hzpos
    hDirection

/-- **Figure 33, Base II.1.M over an aligned datum, tracked and unconditional.** The
incoming cover is `M⁽³⁾`, at position `2` of the aligned orientation. -/
theorem exists_tracked_exit_of_incoming_joined_aligned (pair : LeafPair wallProfile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.joined_sameBlocks incoming hc hab hOne
    fullDim hForest wallInput wallProfile
    (W2M1kClosureUnconditional.wall_background incoming hc hab hOne wallInput wallProfile)
    hLeftCard hRightCard (pair.geometry wallShape)
    (W2M1kSelectedCensus.selectedCensus_of_aligned incoming hc hab hOne fullDim hForest
      wallProfile wallShape pair.aligned hLeftCard hRightCard)
  obtain ⟨fd, hMatrix, hWall, certificate, _hRows, ⟨hTrack⟩⟩ :=
    exists_matched_tracking incoming hc hab hOne fullDim
      (joinedCandidate wallStar (pair.geometry wallShape))
      (W2M1kIncomingMatching.joinedPlacement incoming hc hab hOne (pair.geometry wallShape)
        hLeftCard hRightCard)
      hVertices hEdges current
  exact trackedCertifiedExit_of_aligned incoming hc hab hOne fullDim wallInput wallProfile
    wallShape pair 2 fd hMatrix hWall certificate hTrack z incomingVelocity hz hzpos
    hDirection

/-- **Figure 33, Base II over a separated datum, tracked and unconditional.**
The census dichotomy of Part I's Base II (case `{w2-r2}`) puts the incoming
cover at position `1` (`M⁽²⁾`) or
position `2` (`M⁽³⁾`) of the separated orientation; both land here. -/
theorem exists_tracked_exit_of_incoming_separated (divided : DividedData wallProfile)
    (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
    (hRightCard : (GluingDatum.incidentEdges b).card = 2)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  have hBackground :=
    W2M1kClosureUnconditional.wall_background incoming hc hab hOne wallInput wallProfile
  rcases W2M1kSelectedCensus.selectedCensus_dichotomy_of_dividedData incoming hc hab hOne
    fullDim hForest wallProfile wallShape divided hLeftCard hRightCard with selected | selected
  · obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.divided_sameBlocks incoming hc hab hOne
      fullDim hForest wallInput wallProfile hBackground hLeftCard hRightCard wallShape divided
      selected
    obtain ⟨fd, hMatrix, hWall, certificate, _hRows, ⟨hTrack⟩⟩ :=
      exists_matched_tracking incoming hc hab hOne fullDim
        (DividedData.candidate wallShape divided)
        (W2M1kIncomingMatching.dividedPlacement incoming hc hab hOne wallProfile wallShape
          divided hLeftCard hRightCard)
        hVertices hEdges current
    exact trackedCertifiedExit_of_separated incoming hc hab hOne fullDim wallInput wallProfile
      wallShape divided 1 fd hMatrix hWall certificate hTrack z incomingVelocity hz hzpos
      hDirection
  · obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.joined_sameBlocks incoming hc hab hOne
      fullDim hForest wallInput wallProfile hBackground hLeftCard hRightCard
      (divided.geometry wallShape) selected
    obtain ⟨fd, hMatrix, hWall, certificate, _hRows, ⟨hTrack⟩⟩ :=
      exists_matched_tracking incoming hc hab hOne fullDim
        (joinedCandidate wallStar (divided.geometry wallShape))
        (W2M1kIncomingMatching.joinedPlacement incoming hc hab hOne
          (divided.geometry wallShape) hLeftCard hRightCard)
        hVertices hEdges current
    exact trackedCertifiedExit_of_separated incoming hc hab hOne fullDim wallInput wallProfile
      wallShape divided 2 fd hMatrix hWall certificate hTrack z incomingVelocity hz hzpos
      hDirection

end Certified

section Classified

-- The source-facing certified-family and march interfaces use small graphs.
variable {degree : ℕ}
  {incomingTarget : CFGraph.{0}} {a b : incomingTarget.V} {contracted : incomingTarget.edges}
  (incoming : GluingDatum incomingTarget degree)
  (hc : (contracted : incomingTarget.V × incomingTarget.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges incomingTarget a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  (wallStar : TwoStar (contract incomingTarget hab hOne) ⟨a, hab⟩)
  (wallInput : W2SourceInput (contractDatum incoming hc hab hOne) wallStar)

/-- The `w2M1k` tag names the `m1k` constructor, whose `unit_large` disjunction
is exactly the M-1k `Shape` on the profile or on its exchange
(`W2M1kIncomingCensus.exists_shape_of_m1k`). Both are profiles of the same wall
block, so one existential covers them. -/
theorem exists_w2M1k_payload
    (classification : IncomingSourceCases.W2.Classification
      (contractDatum incoming hc hab hOne) wallStar wallInput)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w2M1k) :
    ∃ block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩,
      ∃ sourceProfile : W2R2SourceProfile.SourceProfile
          (contractDatum incoming hc hab hOne) wallStar block,
        Nonempty (Shape sourceProfile) := by
  cases classification with
  | m11 _ _ _ _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | m1k sourceBlock sourceProfile hDeleted _ _ _ hUnitLarge =>
      rcases W2M1kIncomingCensus.exists_shape_of_m1k sourceProfile hDeleted hUnitLarge with
        hShape | hShape
      · exact ⟨sourceBlock, sourceProfile, hShape⟩
      · exact ⟨sourceBlock, W2M1kIncomingCensus.exchange sourceProfile, hShape⟩
  | mkk _ _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | p _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | r1 _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag

include fullDim hForest wallInput in
/-- **The tracked exit at a wall the classifier tags `w2M1k`.** No profile,
shape, orientation, census or family membership is supplied: the classification
carries the profile, `W2M1kIncomingCensus.exists_shape_of_m1k` the shape and
`W2M1kClosureUnconditional.headline_cases` the three surviving
(source witness, target type) pairs. The outgoing `BalancedGlobal.Candidate`,
its valid connected genus-zero base stage, its full-dimensional presentation,
the tracked row-labelled graph, the metric segment and the cleared pencil are
all returned under one binder. -/
theorem exists_tracked_exit_of_classification
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (classification : IncomingSourceCases.W2.Classification
      (contractDatum incoming hc hab hOne) wallStar wallInput)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w2M1k)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  obtain ⟨_, wallProfile, ⟨wallShape⟩⟩ :=
    exists_w2M1k_payload incoming hc hab hOne wallStar wallInput classification hTag
  rcases W2M1kClosureUnconditional.headline_cases incoming hc hab hOne fullDim wallProfile
      wallShape with
    ⟨_, hLeaf⟩ | ⟨⟨pair⟩, hLeftCard, hRightCard⟩ | ⟨⟨divided⟩, hLeftCard, hRightCard⟩
  · exact exists_tracked_exit_of_incoming_leaf incoming hc hab hOne fullDim hForest wallInput
      wallProfile wallShape hLeaf current z incomingVelocity hz hzpos hDirection
  · exact exists_tracked_exit_of_incoming_joined_aligned incoming hc hab hOne fullDim hForest
      wallInput wallProfile wallShape pair hLeftCard hRightCard current z incomingVelocity hz
      hzpos hDirection
  · exact exists_tracked_exit_of_incoming_separated incoming hc hab hOne fullDim hForest
      wallInput wallProfile wallShape divided hLeftCard hRightCard current z incomingVelocity
      hz hzpos hDirection

end Classified

end DraismaVargas.LocalCases.W2M1kGraphTracking
