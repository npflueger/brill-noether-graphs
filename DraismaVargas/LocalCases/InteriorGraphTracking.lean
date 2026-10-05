module

public import DraismaVargas.LocalCases.StableSourceDartsTransport
public import DraismaVargas.LocalCases.W4PositiveExit

@[expose] public section

/-!
# Same-candidate graph tracking at an interior exit of Case {w4}

Vargas, Part II (in the proofs of its main theorems) separates crossings
inside one trivalent cone from genuine type changes.  The former preserve the
row-labelled source graph.  This file checks that preservation at the exit of
Draisma--Vargas Part I, Case {w4} (a four-valent wall vertex), without changing
`State`, `CarriesClearedPencil`, or `PresentedProgress`.

`Tracks fd graph label` binds its actual dart Iso to precisely the datum and
labelling of `fd`. It is the incoming invariant, not an assertion that every
cover presents an arbitrary graph. `exists_matched_tracking` consumes actual
target/sheet matching to transport it from an arbitrary incoming cover to
the selected Case {w4} member. `exists_tracked_w4_member_exit` consumes the real
positive exit and retains tracking on the very outgoing member carrying the
full-dimensional presentation, metric segment, and pencil. The needed row
compatibility is proved from the geometric labelling definitions.

Tracking is not part of the march state here.  The existential
candidate/fullDim binder of `SemanticAtlasMarch.CarriesClearedPencil` has no
tracking field, and `PresentedProgress` carries only
fullDimAt/fullDimPresentation, not a map from that opened incoming witness.  A
separate existential graph witness at the same matrix would not suffice, since
it need not be attached to the same source.  Making tracking a march invariant
would put `Tracks` under that same binder and thread the selected exit's
tracking through successor construction.  The original-coordinate Case {w4}
exit also discards its matched row equality (as `_hRow`); the two consumers
here show how to retain it locally.

The file establishes tracking at this one exit only; it does not make tracking
an invariant of the march, and it does not construct the type-changing exits
of Part II.
-/

namespace DraismaVargas.LocalCases.InteriorGraphTracking

open DraismaVargas.Infrastructure CubicDarts CubicDartGraph
open W4StableSource StableSourceDarts StableGraphIncidence FullDimensionalSource

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- A graph and its coordinate labels attached to this very full-dimensional
source, not to another witness realizing the same matrix. -/
structure Tracks (fd : FullDimensionalSourcePresentation data coordinate)
    (graph : CubicDartGraph D V) (label : D → coordinate) where
  iso : Iso (ofDatum data fd.connected fd.trivalent fd.pathEnds) graph
  row_map : ∀ d : Dart data, label (iso.dart d) = fd.labelling.row (row data d)

/-- Every actual full-dimensional source starts with its own constructed
graph and literal row labels, without an external graph receipt. -/
noncomputable def Tracks.self (fd : FullDimensionalSourcePresentation data coordinate) :
    Tracks fd (ofDatum data fd.connected fd.trivalent fd.pathEnds)
      (fun d ↦ fd.labelling.row (row data d)) where
  iso := Iso.refl _
  row_map _ := rfl

/-- The non-loop edge of the current Whitehead type is the corresponding
actual stable row of this same cover. Interior crossings may change the
cover; its tracked isomorphism, not the original seed's graph, supplies this. -/
theorem Tracks.hasSimpleEnd
    {fd : FullDimensionalSourcePresentation data coordinate}
    {graph : CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label) (d : D) (hNonloop : ¬ graph.IsLoopDart d) :
    SingleRowForest.HasSimpleEnd data (fd.labelling.row.symm (label d)) := by
  have hRow : fd.labelling.row.symm (label d) = row data (current.iso.dart.symm d) := by
    apply fd.labelling.row.injective
    simpa only [Equiv.apply_symm_apply] using
      current.row_map (current.iso.dart.symm d)
  rw [hRow]
  apply hasSimpleEnd_of_not_isLoopDart data fd.connected fd.trivalent fd.pathEnds
    (current.iso.dart.symm d)
  intro hLoop
  apply hNonloop
  have h : graph.vert (graph.op (current.iso.dart (current.iso.dart.symm d))) =
      graph.vert (current.iso.dart (current.iso.dart.symm d)) := by
    rw [current.iso.op_map, current.iso.vert_map, current.iso.vert_map]
    exact congrArg current.iso.vtx hLoop
  simpa only [IsLoopDart, Equiv.apply_symm_apply] using h

/-- An actual tracked non-loop move supplies the no-cycle condition at its
one-row boundary. No independent forest or simple-end receipt is assumed. -/
theorem Tracks.noContractedCycle
    {target : CFGraph.{0}} {data : GluingDatum target degree}
    {fd : FullDimensionalSourcePresentation data coordinate}
    {graph : CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks fd graph label) (d : D) (hNonloop : ¬ graph.IsLoopDart d)
    (coordinates : coordinate → ℚ) (hNonnegative : ∀ column, 0 ≤ coordinates column)
    (hRows : ∀ r, r ≠ label d →
      (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation).mulVec
        coordinates r ≠ 0) :
    NonTrivalentWallSetup.NoContractedCycle (data := data) fd.labelling.presentation coordinates
      hNonnegative :=
  SingleRowForest.noContractedCycle_of_single_row (target := target) (degree := degree)
    (data := data) (coordinate := coordinate) fd.labelling coordinates
    hNonnegative (label d) hRows
    (Tracks.hasSimpleEnd (fd := fd) (graph := graph) (label := label) current d hNonloop)

variable {target' : CFGraph} {degree' : ℕ} {other : GluingDatum target' degree'}

/-- This local composition is used below with an actual Case {w4} exit and its
proved row equality. Neither outgoing compatibility nor existence is assumed
at the final Case {w4} boundary. -/
noncomputable def throughIncidence
    {fd : FullDimensionalSourcePresentation data coordinate}
    {graph : CubicDartGraph D V} {label : D → coordinate} (current : Tracks fd graph label)
    (outFD : FullDimensionalSourcePresentation other coordinate)
    (certificate : Equivalence data other)
    (hRows : outFD.labelling.row = certificate.row.symm.trans fd.labelling.row) :
    Tracks outFD graph label where
  iso := (isoOfIncidenceEquivalence other outFD.connected outFD.trivalent outFD.pathEnds
    fd.connected fd.trivalent fd.pathEnds certificate.symm).trans current.iso
  row_map d := by
    change label (current.iso.dart (dartEquiv other certificate.symm d)) = _
    rw [current.row_map, hRows]
    exact congrArg fd.labelling.row (dartEquiv_row other certificate.symm d)

open W4TargetPairings W4SourceClassification W4OutgoingStableRows W4PositiveExit

variable {wall : target.V} {star : FourStar target wall} [DecidableEq target.edges]
  (input : AuxR0SourceInput data star) (incoming : Fin 3)
  (incomingFD : FullDimensionalSourcePresentation (member input incoming).datum coordinate)

/-- Actual Case {w4} outgoing row labels are the incoming labels through the actual
member-to-member incidence map. This is proved from the geometric definitions. -/
theorem outgoingLabelling_row (outgoing : Fin 3) :
    (outgoingLabelling input incoming incomingFD outgoing).row =
      (between input incoming outgoing).row.symm.trans incomingFD.labelling.row := by
  ext r
  simp [outgoingLabelling, W4CommonBalance.labelling, W4CommonBalance.sourceCoordinates,
    initialLabelling, between, StableGraphIncidence.Equivalence.symm,
    StableGraphIncidence.Equivalence.trans, equivalence]

/-- The full positive Case {w4} member exit, with a row-labelled graph on the SAME
selected member that carries its full-dimensional presentation and pencil. -/
theorem exists_tracked_w4_member_exit
    {graph : CubicDartGraph D V} {label : D → coordinate}
    (current : Tracks incomingFD graph label)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (root : target.V)
    (z incomingVelocity : coordinate → ℚ)
    (hz : z (wallColumn input incoming incomingFD) = 0)
    (hzpos : ∀ i, i ≠ wallColumn input incoming incomingFD → 0 < z i)
    (hDirection : incomingVelocity (wallColumn input incoming incomingFD) < 0) :
    ∃ outgoing : Fin 3,
      ∃ outgoingFD : FullDimensionalSourcePresentation (member input outgoing).datum coordinate,
        Nonempty (Tracks outgoingFD graph label) ∧
        outgoingFD.labelling = outgoingLabelling input incoming incomingFD outgoing ∧
        (memberMatrix input incoming incomingFD incoming).det *
            (memberMatrix input incoming incomingFD outgoing).det < 0 ∧
        ∃ δ : ℚ, 0 < δ ∧ ∀ t : ℚ, 0 < t → t ≤ δ →
          (∀ i, 0 < (z + t • outgoingVelocity input incoming incomingFD incomingVelocity outgoing) i) ∧
          (memberMatrix input incoming incomingFD outgoing).mulVec
              (z + t • outgoingVelocity input incoming incomingFD incomingVelocity outgoing) =
            (memberMatrix input incoming incomingFD incoming).mulVec z +
              t • (memberMatrix input incoming incomingFD incoming).mulVec incomingVelocity ∧
          ∃ realization : (member input outgoing).datum.IntegralRealization,
            ∃ scale : ℕ, 0 < scale ∧
              (∀ column,
                (realization.targetLength (outgoingFD.labelling.targetEdge column) : ℚ) =
                  (scale : ℚ) * (z + t • outgoingVelocity input incoming incomingFD
                    incomingVelocity outgoing) column) ∧
              Utilities.BNExists realization.sourceSpec.graph 1 degree := by
  obtain ⟨outgoing, outgoingFD, hLabelling, hSign, hMetric⟩ :=
    exists_member_positive_exit_with_pencil input incoming incomingFD hConnected hGenus root
      z incomingVelocity hz hzpos hDirection
  refine ⟨outgoing, outgoingFD, ⟨throughIncidence current outgoingFD
    (between input incoming outgoing) ?_⟩, hLabelling, hSign, hMetric⟩
  rw [hLabelling]
  exact outgoingLabelling_row input incoming incomingFD outgoing

open GraphContraction GluingContraction ContractionRamification WallDegeneration

omit [DecidableEq target.edges] in
/-- Original incoming covers enter the checked member exit through actual
target/sheet matching. The graph and row dictionary travel with the exact
matched presentation; family membership is not an input. -/
theorem exists_matched_tracking
    (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
    {graph : CubicDartGraph D V} {label : D → coordinate} (current : Tracks fd graph label)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    [DecidableEq (contract target hab hOne).edges]
    (input : AuxR0SourceInput (contractDatum data hc hab hOne) star) :
    ∃ matched : FullDimensionalSourcePresentation
        (member input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)).datum coordinate,
      Nonempty (Tracks matched graph label) ∧
      GluingDatum.LengthMatrixPresentation.matrix matched.labelling.presentation =
        GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation ∧
      matched.labelling.targetEdge =
        fd.labelling.targetEdge.trans (GluingTransport.edgeEquiv
          (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)) ∧
      matched.labelling.targetEdge.symm
          (TargetExpansion.occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
            (member input (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)).right none) =
        fd.labelling.targetEdge.symm contracted := by
  obtain ⟨matched, hMatrix, hTarget, hWall, certificate, hRows⟩ :=
    W4PositiveExit.exists_matchedPresentation data fd hc hab hOne star hForest hCompat input
  exact ⟨matched, ⟨throughIncidence current matched certificate hRows⟩, hMatrix, hTarget, hWall⟩

end DraismaVargas.LocalCases.InteriorGraphTracking
