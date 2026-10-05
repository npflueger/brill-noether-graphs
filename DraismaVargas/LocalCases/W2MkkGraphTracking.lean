module

public import DraismaVargas.LocalCases.W3InteriorGraphTracking
public import DraismaVargas.LocalCases.W3ShiftGraphTracking
public import DraismaVargas.LocalCases.IncomingSourceCases
public import DraismaVargas.LocalCases.W2MkkArbitraryExit

@[expose] public section

/-!
# Same-candidate graph and row tracking for Figure 34

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).

`W2MkkCommonBalance.LimitColumns.labelling` builds every member's honest
labelling out of `LimitMember.row`, so the member-to-member row equation is
between the receipt's own row bijections. Both orientations' three
stable-incidence dictionaries read exactly those rows, the remote branch swap
included: the remote dictionary is `StableGraphIncidence.sheetRelabel` at the
same relabelling from which `W2MkkTransport.swapGauge` is
`LimitChainCore.Gauge.ofSheetRelabeling`, and both take their row maps from
`SheetRelabelStable.stablePathEquiv`. The row formula therefore holds with no
new hypothesis, and the incoming cover's tracked row-labelled graph travels to
the selected outgoing member, under the SAME full-dimensional presentation that
carries the metric segment and the cleared pencil.

Both orientations are covered: Base II.2.1.M (`firstOrientation`, position `1`
remote) and Base II.2.2.M (`secondOrientation`, position `0` remote).

What is proved here: the row equation `labelling_row`; the tracked exit in the
incoming cover's own coordinates, `exists_tracked_exit_in_original_coordinates`,
with its member-level form `exists_tracked_member_exit`; the tracked incoming
normalization `exists_matched_tracking`, which retains the actual
stable-incidence certificate together with its recovered row equation; and
`exists_w2Mkk_payload`, which reads the case's data off the `w2Mkk` tag of
`IncomingSourceCases.W2.Classification`.

What is NOT proved here: no new determinant balance, occurrence census or
positive exit. `W2MkkArbitraryExit.exists_positive_exit_with_presentation` and
`W2MkkSelectedCensus.selectedCensus_dichotomy`/`divalent_endpoints` are consumed
verbatim. The standing hypotheses are explicit: the incoming datum with its
full-dimensional presentation, the contraction forest, the two-star, its wall
input, a distinguished sheet for `M⁽³⁾` and the positivity data of the exit.
Full-dimensionality of an outgoing member is only ever obtained at a member
whose own honest determinant is nonzero: Figure 34's singular members are never
required nonsingular. Matrix equality is never used to identify a graph --
every graph identification below is an actual
`StableGraphIncidence.Equivalence`.

Consumers: the tracked march, alongside `W2M11GraphTracking`,
`W2M1kGraphTracking`, `W3Nd2GraphTracking` and `W3ShiftTrackedFinal`. The output
proposition is `W3ShiftGraphTracking.TrackedCertifiedExit`, which despite its
file name is the general tracked-exit output shape.
-/

namespace DraismaVargas.LocalCases.W2MkkGraphTracking

open DraismaVargas.Infrastructure
open TargetExpansion
open GraphContraction GluingContraction ContractionRamification WallDegeneration
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource InteriorGraphTracking
open W2MkkSourceCandidates
open W2MkkCommonBalance (LimitMember LimitColumns)
open W2MkkLimitColumns (firstOrientation secondOrientation)

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
    (limit.labelling (W2MkkArbitraryExit.initialLabelling limit incoming incomingFD)
        outgoing).row =
      ((dictionary incoming).symm.trans (dictionary outgoing)).row.symm.trans
        incomingFD.labelling.row := by
  ext path
  simp [LimitColumns.labelling, LimitColumns.sourceCoordinates,
    W2MkkArbitraryExit.initialLabelling, hDictionaryRow,
    StableGraphIncidence.Equivalence.symm, StableGraphIncidence.Equivalence.trans]

/-- The tracked Figure 34 exit against the incoming cover's own length matrix
and its own contracted column. The outgoing member's graph, row map, metric
segment and cleared pencil all sit under the SAME full-dimensional
presentation. -/
theorem exists_tracked_exit_in_original_coordinates (limit : LimitColumns profile shape)
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
      limit.wallColumn (W2MkkArbitraryExit.initialLabelling limit incoming incomingFD) =
        originalWallColumn :=
    (W2MkkArbitraryExit.wallColumn_initialLabelling limit incoming incomingFD).trans hWall
  have hIncomingMatrix :
      limit.squareMatrix (W2MkkArbitraryExit.initialLabelling limit incoming incomingFD)
          incoming = originalMatrix :=
    (W2MkkArbitraryExit.squareMatrix_self limit incoming incomingFD).trans hMatrix
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, δ, hδ, hStep⟩ :=
    W2MkkArbitraryExit.exists_positive_exit_with_presentation limit input dictionary sourceGenus
      (W2MkkArbitraryExit.initialLabelling limit incoming incomingFD) hConnected hGenus incoming
      incomingFD (W2MkkArbitraryExit.squareMatrix_self_ne_zero limit incoming incomingFD)
      z incomingVelocity (hWallColumn ▸ hz) (hWallColumn ▸ hzpos) (hWallColumn ▸ hDirection)
  have hOutMatrix : GluingDatum.LengthMatrixPresentation.matrix
      outgoingFD.labelling.presentation =
      limit.squareMatrix (W2MkkArbitraryExit.initialLabelling limit incoming incomingFD)
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
    W2MkkArbitraryExit.outgoingVelocity limit
      (W2MkkArbitraryExit.initialLabelling limit incoming incomingFD) incoming
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

/-- **The tracked Figure 34 member exit in the identified member's own
coordinates.** This is `exists_tracked_exit_in_original_coordinates` at the
identity bridge: the member's own honest length matrix and its own regrown wall
column. Nothing new is proved; it is the member-level form the other family
adapters state directly. -/
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
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (incomingFD.labelling.targetEdge.symm
      (occurrenceEquiv target wall (limit.member incoming).right none)) = 0)
    (hzpos : ∀ i, i ≠ incomingFD.labelling.targetEdge.symm
      (occurrenceEquiv target wall (limit.member incoming).right none) → 0 < z i)
    (hDirection : incomingVelocity (incomingFD.labelling.targetEdge.symm
      (occurrenceEquiv target wall (limit.member incoming).right none)) < 0) :
    ∃ outgoing : Fin 3,
      ∃ outgoingFD : FullDimensionalSourcePresentation (limit.member outgoing).datum coordinate,
        Nonempty (StableGraphIncidence.Equivalence (limit.member incoming).datum
          (limit.member outgoing).datum) ∧
        Nonempty (Tracks outgoingFD graph label) ∧
        (GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation).det *
          (GluingDatum.LengthMatrixPresentation.matrix
            outgoingFD.labelling.presentation).det < 0 ∧
        ∃ velocity : coordinate → ℚ, ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • velocity) i) ∧
          (GluingDatum.LengthMatrixPresentation.matrix
              outgoingFD.labelling.presentation).mulVec (z + t • velocity) =
            (GluingDatum.LengthMatrixPresentation.matrix
                incomingFD.labelling.presentation).mulVec z +
              t • (GluingDatum.LengthMatrixPresentation.matrix
                incomingFD.labelling.presentation).mulVec incomingVelocity ∧
          ∃ realization : (limit.member outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) * (z + t • velocity) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree :=
  exists_tracked_exit_in_original_coordinates limit input dictionary hDictionaryRow sourceGenus
    hConnected hGenus incoming incomingFD current _ rfl _ rfl z incomingVelocity hz hzpos
    hDirection

end Member

section Matched

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (incoming : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  {wallStar : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (wallInput : W2SourceInput (contractDatum incoming hc hab hOne) wallStar)
  {wallBlock : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
  (wallProfile : W2R2SourceProfile.SourceProfile (contractDatum incoming hc hab hOne)
    wallStar wallBlock)
  (hBackground : ∀ other : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩,
    other ≠ wallBlock →
      (contractDatum incoming hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
  (hLeftCard : (GluingDatum.incidentEdges a).card = 2)
  (hRightCard : (GluingDatum.incidentEdges b).card = 2)
  (wallShape : Shape wallProfile) (detach : DetachData wallProfile) (distinguished : Fin degree)

include fullDim hForest wallInput hBackground hLeftCard hRightCard

/-- **The tracked incoming normalization.** `W2MkkIncomingMatching`'s own
dichotomy receipt names the Figure 34 position the incoming cover occupies, and
`W3InteriorGraphTracking.matched_tracking_of_normalized` recovers that
normalization's geometric row equation from the actual natural matrices, so the
incoming cover's tracked row-labelled graph travels with the presentation. The
column identity at `none` is the receipt's own `Option` dictionary. No family
membership and no matrix identification of graphs is used. -/
theorem exists_matched_tracking
    (hCensus : W2MkkIncomingMatching.DetachCensus incoming hc hab hOne wallProfile detach ∨
      W2MkkIncomingMatching.JoinedCensus incoming hc hab hOne wallProfile)
    {graph : CubicDarts.CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fullDim graph label) :
    ∃ position : Fin 2,
      ∃ fd : FullDimensionalSourcePresentation
          (W2MkkIncomingMatching.members incoming hc hab hOne wallProfile wallShape detach
            distinguished position).datum coordinate,
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation =
            GluingDatum.LengthMatrixPresentation.matrix fullDim.labelling.presentation ∧
          fd.labelling.targetEdge.symm
              (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
                (W2MkkIncomingMatching.members incoming hc hab hOne wallProfile wallShape detach
                  distinguished position).right none) =
            fullDim.labelling.targetEdge.symm contracted ∧
          ∃ certificate : StableGraphIncidence.Equivalence incoming
              (W2MkkIncomingMatching.members incoming hc hab hOne wallProfile wallShape detach
                distinguished position).datum,
            fd.labelling.row = certificate.row.symm.trans fullDim.labelling.row ∧
            Nonempty (Tracks fd graph label) := by
  classical
  obtain ⟨index, hColumns, _hVertices, _hEdges, hNorm⟩ :=
    W2MkkIncomingMatching.exists_member_normalization_of_dichotomy incoming hc hab hOne fullDim
      hForest wallInput wallProfile hBackground hLeftCard hRightCard wallShape detach
      distinguished hCensus
  obtain ⟨fd, hMatrix, hEdge, hRows, hTrack⟩ :=
    W3InteriorGraphTracking.matched_tracking_of_normalized incoming fullDim current hNorm
  refine ⟨index, fd, hMatrix, ?_, _, hRows, hTrack⟩
  rw [hEdge]
  change fullDim.labelling.targetEdge.symm
    ((GluingTransport.edgeEquiv (IncomingMatchingCore.memberTargetIso incoming hc hab hOne
        (W2MkkIncomingMatching.members incoming hc hab hOne wallProfile wallShape detach
          distinguished index)
        (W2MkkIncomingMatching.members_placement incoming hc hab hOne wallProfile wallShape
          detach distinguished index hLeftCard hRightCard))).symm
      (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
        (W2MkkIncomingMatching.members incoming hc hab hOne wallProfile wallShape detach
          distinguished index).right none)) = _
  rw [← hColumns none, Equiv.symm_apply_apply]
  rfl

end Matched

section Classified

variable {degree : ℕ}
  {incomingTarget : CFGraph} {a b : incomingTarget.V} {contracted : incomingTarget.edges}
  (incoming : GluingDatum incomingTarget degree)
  (hc : (contracted : incomingTarget.V × incomingTarget.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges incomingTarget a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  (wallStar : TwoStar (contract incomingTarget hab hOne) ⟨a, hab⟩)
  (wallInput : W2SourceInput (contractDatum incoming hc hab hOne) wallStar)

/-- The `w2Mkk` tag names the `mkk` constructor, whose `deleted_target`,
`first_two_le` and `second_two_le` fields are literally
`W2MkkSourceCandidates.Shape` (`W2MkkIncomingCensus.shape_of_mkk`) and whose
`background` field is the `r = 0` census. Nothing else of the constructor is
used. -/
theorem exists_w2Mkk_payload
    (classification : IncomingSourceCases.W2.Classification
      (contractDatum incoming hc hab hOne) wallStar wallInput)
    (hTag : classification.sourceCase = ClassifiedContinuation.SourceCase.w2Mkk) :
    ∃ block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩,
      ∃ sourceProfile : W2R2SourceProfile.SourceProfile
          (contractDatum incoming hc hab hOne) wallStar block,
        ∃ _ : Shape sourceProfile,
          ∀ other : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩,
            other ≠ block →
              (contractDatum incoming hc hab hOne).localRamification ⟨a, hab⟩ other = 0 := by
  cases classification with
  | m11 _ _ _ _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | m1k _ _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | mkk block sourceProfile hDeleted _ _ hBackground hFirst hSecond =>
      exact ⟨block, sourceProfile,
        W2MkkIncomingCensus.shape_of_mkk incoming hc hab hOne sourceProfile hDeleted hFirst
          hSecond, hBackground⟩
  | p _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag
  | r1 _ _ _ _ _ _ =>
      simp [IncomingSourceCases.W2.Classification.sourceCase] at hTag

end Classified

end DraismaVargas.LocalCases.W2MkkGraphTracking
