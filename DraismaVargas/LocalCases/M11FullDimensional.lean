module

public import DraismaVargas.LocalCases.M11StableGraphs
public import DraismaVargas.LocalCases.M11SourceGenus
public import DraismaVargas.LocalCases.StableGraphFullDimensional

@[expose] public section

/-!
# Full-dimensionality of an actual M11 family member

Starting from a full-dimensional presentation of one of the three actual
source-derived M11 candidates, stable-incidence transport rebuilds such a
presentation on any chosen member whose compatible length matrix is
nonsingular.  In particular, the contracted wall datum is never assumed to
be full-dimensional.
-/

namespace DraismaVargas.LocalCases.M11FullDimensional

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource W2R1Target SecondEquation
open FullDimensionalSource
open M11SourceCandidates M11RemoteCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  (input : W2SourceInput data star) {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wall).blockCard block.1 = 2)

/-! The geometric receipts for every concrete member are consequences of
splitting one target vertex. -/

theorem candidate_targetConnected (hConnected : graph_connected target)
    (position : Fin 3) :
    graph_connected (candidates input profile hCard position).outgoingTarget := by
  fin_cases position
  · change graph_connected (TargetExpansion.graph target wall _)
    exact TargetExpansion.graph_connected target wall _ hConnected
  · change graph_connected (TargetExpansion.graph target wall _)
    exact TargetExpansion.graph_connected target wall _ hConnected
  · change graph_connected (TargetExpansion.graph target wall _)
    exact TargetExpansion.graph_connected target wall _ hConnected

theorem candidate_targetGenus (hGenus : genus target = 0) (position : Fin 3) :
    genus (candidates input profile hCard position).outgoingTarget = 0 := by
  fin_cases position
  · change genus (TargetExpansion.graph target wall _) = 0
    simpa using hGenus
  · change genus (TargetExpansion.graph target wall _) = 0
    simpa using hGenus
  · change genus (TargetExpansion.graph target wall _) = 0
    simpa using hGenus

theorem candidate_targetEdgeCard (position : Fin 3) :
    (candidates input profile hCard position).outgoingTarget.edges.card =
      target.edges.card + 1 := by
  fin_cases position
  · change (TargetExpansion.graph target wall _).edges.card = _
    simp
  · change (TargetExpansion.graph target wall _).edges.card = _
    simp
  · change (TargetExpansion.graph target wall _).edges.card = _
    simp

/-! Turn the incoming member's coordinate order into the initial order used
by the common M11 family.  The target columns pass through the canonical
old-or-new occurrence coordinates. -/

noncomputable def initialLabelling
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (candidates input profile hCard incoming).datum coordinate) :
    StableLengthMatrixLabelling
      (candidates input profile hCard 0).datum coordinate where
  row := (M11StableGraphs.between input profile hCard 0 incoming).row.trans
    incomingFD.labelling.row
  targetEdge := incomingFD.labelling.targetEdge.trans
    ((M11CommonBalance.columnEquiv input profile hCard incoming).symm.trans
      (M11CommonBalance.columnEquiv input profile hCard 0))

/-- The compatible honest labelling on any chosen outgoing family member. -/
noncomputable def outgoingLabelling
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (candidates input profile hCard incoming).datum coordinate)
    (outgoing : Fin 3) :
    StableLengthMatrixLabelling
      (candidates input profile hCard outgoing).datum coordinate :=
  M11CommonBalance.labelling input profile hCard
    (initialLabelling input profile hCard incoming incomingFD) outgoing

/-- Transfer a full-dimensional presentation between two actual M11 family
members.  Only the chosen outgoing compatible matrix is required to be
nonsingular. -/
noncomputable def outgoingPresentation
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming outgoing : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      (candidates input profile hCard incoming).datum coordinate)
    (outgoingDet :
      (GluingDatum.LengthMatrixPresentation.matrix
        (outgoingLabelling input profile hCard incoming incomingFD outgoing).presentation).det ≠ 0) :
    FullDimensionalSourcePresentation
      (candidates input profile hCard outgoing).datum coordinate :=
  StableGraphFullDimensional.presentationOfEquivalence incomingFD
    (M11StableGraphs.between input profile hCard incoming outgoing)
    (candidates_valid input profile hCard outgoing)
    (candidate_targetConnected input profile hCard hConnected outgoing)
    (candidate_targetGenus input profile hCard hGenus outgoing)
    ((candidate_targetEdgeCard input profile hCard outgoing).trans
      (candidate_targetEdgeCard input profile hCard incoming).symm)
    ((M11SourceGenus.candidates_sourceGenus input profile hCard outgoing).trans
      (M11SourceGenus.candidates_sourceGenus input profile hCard incoming).symm)
    (outgoingLabelling input profile hCard incoming incomingFD outgoing)
    outgoingDet

end DraismaVargas.LocalCases.M11FullDimensional
