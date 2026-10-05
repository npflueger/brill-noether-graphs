module

public import DraismaVargas.LocalCases.W3InteriorGraphTracking
public import DraismaVargas.LocalCases.W3ShiftGraphTracking
public import DraismaVargas.LocalCases.W2R1ArbitraryIncomingExit

@[expose] public section

/-!
# Same-candidate graph and row tracking for Equation (10)

Source: Draisma--Vargas Part I, Case {w2-r1}, Equation (10) and the two
distinct ramification-one wall blocks it resolves.

The two actual `{w2-r1}` members carry literal stable-row equivalences
(`W2R1GraphData.equivalence`, whose row map is the limit matrices' own row map
by `equivalence_row` and `W2R1LimitMatrix.limitColumns_row`). Their
member-to-member row formula is therefore read directly off the outgoing
labelling definitions, so the same selected member receives its
full-dimensional presentation, `Tracks` witness, metric segment and cleared
pencil under one binder.

What is proved here: the dictionary row equation `between_row`; the labelling
row equation `outgoingLabelling_row`; the tracked member exit
`exists_tracked_member_exit`; the tracked incoming normalization
`exists_matched_tracking`, which retains the actual stable-incidence
certificate together with its recovered row equation; the tracked exit in the
incoming cover's own coordinates; and the source-facing
`exists_tracked_exit_of_classification`, whose only classification input is the
`w2R1` tag of `IncomingSourceCases.W2.Classification`.

What is NOT proved here: no new positive exit, determinant balance or occurrence
census. `W2R1ArbitraryIncomingExit.exists_member_positive_exit_with_pencil`,
`W2R1IncomingMatching.exists_member_normalization` and
`W2R1ArbitraryIncomingExit.exists_w2R1_payload` are consumed verbatim. The
standing hypotheses remain explicit at the source-facing producer: the incoming
datum with its full-dimensional presentation, the contraction forest, the
two-star, its wall input and the positivity data of the exit.
Full-dimensionality of an outgoing member is only ever obtained at a member
whose own honest determinant is nonzero: a singular member of the balanced pair
is never required nonsingular. Matrix equality is never used to identify a
graph -- every graph identification below is an actual
`StableGraphIncidence.Equivalence`.

Consumers: the tracked successor packaging of the march, alongside
`W2M11GraphTracking`, `W2M1kGraphTracking`, `W2MkkGraphTracking`,
`W2PGraphTracking` and `W3Nd2GraphTracking`. The output proposition is
`W3ShiftGraphTracking.TrackedCertifiedExit`, which despite its file name is the
general tracked-exit output shape.
-/

namespace DraismaVargas.LocalCases.W2R1GraphTracking

open DraismaVargas.Infrastructure
open TargetExpansion
open GraphContraction GluingContraction ContractionRamification WallDegeneration
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource InteriorGraphTracking
open W2R1SourceCandidates
open W2R1ArbitraryIncomingExit

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- Going out through one occurrence dictionary and back through another
cancels, read backwards at the wall column. This is the `Equiv` algebra
`W2R1ArbitraryIncomingExit` keeps private; it mentions no gluing data. -/
private theorem symm_trans_cancel {α β γ ε : Type*} (e : α ≃ β) (A : γ ≃ β) (B : γ ≃ ε)
    (x : γ) : ((e.trans (A.symm.trans B)).trans B.symm).symm x = e.symm (A x) := by
  simp

section Member

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (pair : Pair data star) (hValid : data.Valid) (incoming : Fin 2)
  (incomingFD : FullDimensionalSourcePresentation (pair.candidate incoming).datum coordinate)

/-- The member-to-member dictionary's row map is the limit matrices' own row
map on both sides. `W2R1GraphData.equivalence_row` is the only input. -/
theorem between_row (first second : Fin 2) :
    (W2R1GraphData.between pair hValid first second).row =
      ((W2R1LimitMatrix.limitColumns pair hValid).row first).symm.trans
        ((W2R1LimitMatrix.limitColumns pair hValid).row second) := by
  rw [W2R1LimitMatrix.limitColumns_row, W2R1LimitMatrix.limitColumns_row]
  change (W2R1GraphData.equivalence pair hValid first).row.symm.trans
    (W2R1GraphData.equivalence pair hValid second).row = _
  rw [W2R1GraphData.equivalence_row, W2R1GraphData.equivalence_row]

/-- The compatible outgoing labelling names each actual stable row through the
member-to-member incidence dictionary of `W2R1GraphData`. This is read off the
labelling definitions; no row compatibility is assumed. -/
theorem outgoingLabelling_row (outgoing : Fin 2) :
    (W2R1GraphData.outgoingLabelling pair hValid incoming incomingFD outgoing).row =
      (W2R1GraphData.between pair hValid incoming outgoing).row.symm.trans
        incomingFD.labelling.row := by
  ext path
  simp only [W2R1GraphData.outgoingLabelling, W2R1CommonBalance.LimitColumns.labelling,
    W2R1CommonBalance.LimitColumns.sourceCoordinates, W2R1GraphData.initialLabelling,
    between_row, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    Equiv.symm_symm]

/-- The actual Equation (10) member exit, with a row-labelled graph on the SAME
selected member that carries the full-dimensional presentation, the metric
segment and the cleared pencil. -/
theorem exists_tracked_member_exit
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks incomingFD graph label)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn pair hValid incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn pair hValid incoming incomingFD → 0 < z i)
    (hIncomingDirection : incomingVelocity (wallColumn pair hValid incoming incomingFD) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (pair.candidate outgoing).datum coordinate,
        outgoingFD.labelling =
            W2R1GraphData.outgoingLabelling pair hValid incoming incomingFD outgoing ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        (memberMatrix pair hValid incoming incomingFD incoming).det *
            (memberMatrix pair hValid incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity pair hValid incoming incomingFD
            incomingVelocity outgoing) i) ∧
          (memberMatrix pair hValid incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity pair hValid incoming incomingFD
                incomingVelocity outgoing) =
            (memberMatrix pair hValid incoming incomingFD incoming).mulVec z +
              t • (memberMatrix pair hValid incoming incomingFD
                incoming).mulVec incomingVelocity ∧
          ∃ realization : (pair.candidate outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) *
                    (z + t • outgoingVelocity pair hValid incoming incomingFD
                      incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, hStep⟩ :=
    exists_member_positive_exit_with_pencil pair hValid incoming incomingFD hConnected hGenus
      z incomingVelocity hz hzpos hIncomingDirection
  refine ⟨outgoing, outgoingFD, hLabelling, ⟨throughIncidence current outgoingFD
    (W2R1GraphData.between pair hValid incoming outgoing) ?_⟩, hSign, hStep⟩
  rw [hLabelling]
  exact outgoingLabelling_row pair hValid incoming incomingFD outgoing

end Member

section Arbitrary

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W2SourceInput (contractDatum data hc hab hOne) star)
  (pair : Pair (contractDatum data hc hab hOne) star)

include fullDim hForest pair

/-- **The tracked incoming normalization.** `W2R1IncomingMatching`'s own receipt
names the Equation (10) position the incoming cover occupies, and
`W3InteriorGraphTracking.matched_tracking_of_normalized` recovers that
normalization's geometric row equation from the actual natural matrices, so the
incoming cover's tracked row-labelled graph travels with the presentation. The
column identity at `none` is the receipt's own `Option` dictionary. -/
theorem exists_matched_tracking
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label) :
    ∃ position : Fin 2,
      ∃ fd : FullDimensionalSourcePresentation (pair.candidate position).datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          fd.labelling.targetEdge.symm
              (W2R1CommonBalance.columnEquiv pair position none) =
            fullDim.labelling.targetEdge.symm contracted ∧
          ∃ certificate : StableGraphIncidence.Equivalence data
              (pair.candidate position).datum,
            fd.labelling.row = certificate.row.symm.trans fullDim.labelling.row ∧
            Nonempty (Tracks fd graph label) := by
  classical
  obtain ⟨position, _hSelector, hColumns, hNorm⟩ :=
    W2R1IncomingMatching.exists_member_normalization data hc hab hOne fullDim hForest star pair
  obtain ⟨fd, hMatrix, hEdge, hRows, hTrack⟩ :=
    W3InteriorGraphTracking.matched_tracking_of_normalized data fullDim current hNorm
  refine ⟨position, fd, hMatrix, ?_, _, hRows, hTrack⟩
  rw [hEdge]
  change fullDim.labelling.targetEdge.symm
    ((GluingTransport.edgeEquiv (IncomingMatchingCore.memberTargetIso data hc hab hOne
        (pair.candidate position)
        (W2R1IncomingCensus.members_placement data hc hab hOne fullDim star pair
          position))).symm
      (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (pair.candidate position).right none)) = _
  rw [← hColumns none, Equiv.symm_apply_apply]
  rfl

include input in
/-- The tracked exit against the incoming cover's own length matrix and its own
contracted column. The outgoing member's graph, row map, metric segment and
cleared pencil all sit under the SAME full-dimensional presentation. -/
theorem exists_tracked_exit_with_pencil
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    ∃ outgoing : Fin 2,
      ∃ outgoingFD : FullDimensionalSourcePresentation
          (pair.candidate outgoing).datum coordinate,
        Nonempty (StableGraphIncidence.Equivalence data (pair.candidate outgoing).datum) ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        (GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation).det *
            (GluingDatum.LengthMatrixPresentation.matrix
              outgoingFD.labelling.presentation).det < 0 ∧
        ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧
          ∀ t : ℚ, 0 < t → t ≤ δ →
            (∀ i, 0 < (z + t • velocity) i) ∧
            (GluingDatum.LengthMatrixPresentation.matrix
                outgoingFD.labelling.presentation).mulVec (z + t • velocity) =
              (GluingDatum.LengthMatrixPresentation.matrix
                  fullDim.labelling.presentation).mulVec z +
                t • (GluingDatum.LengthMatrixPresentation.matrix
                  fullDim.labelling.presentation).mulVec incomingVelocity ∧
            ∃ realization : (pair.candidate outgoing).datum.IntegralRealization,
              ∃ scale : ℕ, 0 < scale ∧
                (∀ column,
                  (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                    (scale : ℚ) * (z + t • velocity) column) ∧
                Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨position, fd, hMatrix, hWall, hGraph, _hRows, ⟨hTrack⟩⟩ :=
    exists_matched_tracking data hc hab hOne fullDim hForest star pair current
  have hWall' : wallColumn pair input.valid position fd =
      fullDim.labelling.targetEdge.symm contracted :=
    (symm_trans_cancel _ _ _ none).trans hWall
  have hSelf : memberMatrix pair input.valid position fd position =
      GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation := by
    unfold memberMatrix
    rw [W2R1GraphData.outgoingLabelling_self pair input.valid position fd]
    exact hMatrix
  obtain ⟨outgoing, outgoingFD, hLabelling, hOutTrack, hSign, δ, hδ, hStep⟩ :=
    exists_tracked_member_exit pair input.valid position fd hTrack
      (graph_connected_contract target hab hOne fullDim.targetConnected)
      ((genus_contract target hab hOne).trans fullDim.targetGenus)
      z incomingVelocity (hWall' ▸ hz) (hWall' ▸ hzpos) (hWall' ▸ hDirection)
  have hOutMatrix : memberMatrix pair input.valid position fd outgoing =
      GluingDatum.LengthMatrixPresentation.matrix outgoingFD.labelling.presentation := by
    unfold memberMatrix
    rw [hLabelling]
  refine ⟨outgoing, outgoingFD,
    ⟨hGraph.trans (W2R1GraphData.between pair input.valid position outgoing)⟩, hOutTrack,
    ?_, outgoingVelocity pair input.valid position fd incomingVelocity outgoing, δ, hδ, ?_⟩
  · simpa only [hSelf, hOutMatrix] using hSign
  · intro t ht htδ
    obtain ⟨hPositive, hMetric, hPencil⟩ := hStep t ht htδ
    exact ⟨hPositive, by simpa only [hSelf, hOutMatrix] using hMetric, hPencil⟩

include input in
/-- The two Equation (10) member names identify the actual
`BalancedGlobal.Candidate` before forgetting the family index. Both members sit
over the wall datum itself, so its validity is the wall input's. Its valid
connected genus-zero base stage, full presentation, tracking, metric segment and
pencil stay together in the march-facing package. -/
theorem exists_tracked_certified_exit
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  obtain ⟨outgoing, outgoingFD, hGraph, hTrack, hSign, velocity, δ, hδ, hStep⟩ :=
    exists_tracked_exit_with_pencil data hc hab hOne fullDim hForest star input pair
      (graph := graph) (label := label) current z incomingVelocity hz hzpos hDirection
  exact ⟨_, contractDatum data hc hab hOne, ⟨a, hab⟩, pair.candidate outgoing, input.valid,
    graph_connected_contract target hab hOne fullDim.targetConnected,
    (genus_contract target hab hOne).trans fullDim.targetGenus,
    outgoingFD.valid, hGraph, outgoingFD, hTrack, hSign, velocity, δ, hδ, hStep⟩

end Arbitrary

section Classified

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)
  (input : W2SourceInput (contractDatum data hc hab hOne) star)

include fullDim hForest input in
/-- **The tracked exit at a wall the classifier tags `w2R1`.** No pair is
supplied: `W2R1ArbitraryIncomingExit.exists_w2R1_payload` rebuilds it field for
field from the `r1` constructor's two distinct blocks, their two profiles and
the background clause. The outgoing `BalancedGlobal.Candidate`, its valid
connected genus-zero base stage, its full-dimensional presentation, the tracked
row-labelled graph, the metric segment and the cleared pencil are all returned
under one binder. -/
theorem exists_tracked_exit_of_classification
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label)
    (classification : IncomingSourceCases.W2.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w2R1)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim graph label z incomingVelocity := by
  classical
  obtain ⟨pair⟩ := exists_w2R1_payload data hc hab hOne star input classification hTag
  exact exists_tracked_certified_exit data hc hab hOne fullDim hForest star input pair current
    z incomingVelocity hz hzpos hDirection

include hForest in
/-- **Non-vacuity of the tracked input.** The incoming cover's own constructed
row-labelled graph tracks it (`InteriorGraphTracking.Tracks.self`), so the
classified producer applies with no external graph or labelling receipt at all:
this is the tracked `w2R1` exit of a bare full-dimensional incoming cover. -/
theorem exists_tracked_exit_of_classification_self
    (classification : IncomingSourceCases.W2.Classification
      (contractDatum data hc hab hOne) star input)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w2R1)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (fullDim.labelling.targetEdge.symm contracted) = 0)
    (hzpos : ∀ i, i ≠ fullDim.labelling.targetEdge.symm contracted → 0 < z i)
    (hDirection : incomingVelocity (fullDim.labelling.targetEdge.symm contracted) < 0) :
    W3ShiftGraphTracking.TrackedCertifiedExit fullDim
      (StableSourceDarts.ofDatum data fullDim.connected fullDim.trivalent fullDim.pathEnds)
      (fun d ↦ fullDim.labelling.row (StableSourceDarts.row data d)) z incomingVelocity :=
  exists_tracked_exit_of_classification data hc hab hOne fullDim hForest star input
    (Tracks.self fullDim) classification hTag z incomingVelocity hz hzpos hDirection

end Classified

end DraismaVargas.LocalCases.W2R1GraphTracking
