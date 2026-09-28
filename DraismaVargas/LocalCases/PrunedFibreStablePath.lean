import DraismaVargas.LocalCases.PrunedFibreTree

/-!
# Stable-path transport through a divalent pruned fibre

The pruned-fibre Euler argument supplies a physical valency statement: over
a divalent wall vertex, every active incoming constituent is divalent. This
module consumes that proved statement and pruned connectivity to construct
the canonical stable-path lift through an actual forest contraction. Only
connectedness and the established occurrencewise dangling compatibility are
needed in addition to the forest; no quotient-row equivalence is assumed.
-/

namespace DraismaVargas.LocalCases.PrunedFibreStablePath

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre
open W4StableSource PrunedContractionFibre StableLocalProperties ClassInjectivity
open WallDegeneration

variable {target : CFGraph} {degree : ℕ}

theorem stablePath_eq_of_incident_divalent (data : GluingDatum target degree)
    (first second : NonDanglingEdge data) (vertex : data.SourceVertex)
    (hFirst : Incident data first.1 vertex) (hSecond : Incident data second.1 vertex)
    (hValency : nonDanglingValency data vertex = 2) : first.stablePath = second.stablePath := by
  by_cases hSame : first = second
  · rw [hSame]
  · exact stablePath_eq_of_consecutive ⟨hSame, vertex, hFirst, hSecond, hValency⟩

theorem sourceVertexMap_eq_of_surviving_walk (data : GluingDatum target degree)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) {first second : data.SourceVertex}
    (hWalk : Relation.ReflTransGen (SurvivingFibreStep data contracted) first second) :
    sourceVertexMap data hc hab hOne first = sourceVertexMap data hc hab hOne second := by
  apply (sourceVertexMap_eq_iff data hc hab hOne first second).mpr
  induction hWalk with
  | refl => exact ReachThroughContracted.refl data contracted first
  | tail _ hStep ih => exact ih.trans hStep.fibreStep.reachThroughContracted

/-- Actual surviving occurrences incident anywhere in a connected divalent
pruned fibre lie on one incoming stable path. The hypothesis concerns literal
source vertices and is precisely what the source's pruned Euler count gives. -/
theorem stablePath_eq_of_divalent_fibre (data : GluingDatum target degree)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hDivalent : ∀ constituent : data.SourceVertex,
      sourceVertexMap data hc hab hOne constituent = vertex →
      nonDanglingValency data constituent ≠ 0 → nonDanglingValency data constituent = 2)
    (first second : NonDanglingEdge data) (left right : data.SourceVertex)
    (hFirst : Incident data first.1 left) (hSecond : Incident data second.1 right)
    (hLeft : sourceVertexMap data hc hab hOne left = vertex)
    (hRight : sourceVertexMap data hc hab hOne right = vertex) :
    first.stablePath = second.stablePath := by
  have hLeftActive := nonDanglingValency_ne_zero_of_incident data first.2 hFirst
  have hRightActive := nonDanglingValency_ne_zero_of_incident data second.2 hSecond
  have hWalk := (sourceVertexMap_eq_iff_surviving_walk data hc hab hOne
    hLeftActive hRightActive).mp (hLeft.trans hRight.symm)
  clear hRightActive hLeftActive hRight
  induction hWalk generalizing second with
  | refl =>
    exact stablePath_eq_of_incident_divalent data first second left hFirst hSecond
      (hDivalent left hLeft (nonDanglingValency_ne_zero_of_incident data first.2 hFirst))
  | @tail previous last hWalk hStep ih =>
    obtain ⟨edge, hTarget, hSurvives, hEnds⟩ := hStep
    let middle : NonDanglingEdge data := ⟨edge, hSurvives⟩
    have hMiddlePrevious : Incident data middle.1 previous := by
      rcases hEnds with h | h
      · exact Or.inl (congrArg Prod.fst h)
      · exact Or.inr (congrArg Prod.snd h)
    have hMiddleLast : Incident data middle.1 last := by
      rcases hEnds with h | h
      · exact Or.inr (congrArg Prod.snd h)
      · exact Or.inl (congrArg Prod.fst h)
    have hLast : sourceVertexMap data hc hab hOne last = vertex :=
      (sourceVertexMap_eq_of_surviving_walk data hc hab hOne
        (hWalk.tail ⟨edge, hTarget, hSurvives, hEnds⟩)).symm.trans hLeft
    exact (ih middle hMiddlePrevious).trans
      (stablePath_eq_of_incident_divalent data middle second last hMiddleLast hSecond
        (hDivalent last hLast
          (nonDanglingValency_ne_zero_of_incident data second.2 hSecond)))

/-- A wall incidence lifts to an actual incident endpoint somewhere in its
source-vertex fibre. This uses the literal occurrence bijection. -/
theorem exists_incident_sourceEdgeEmbedding (data : GluingDatum target degree)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (edge : (contractDatum data hc hab hOne).SourceEdge)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hIncident : Incident (contractDatum data hc hab hOne) edge vertex) :
    ∃ constituent : data.SourceVertex,
      Incident data (sourceEdgeEmbedding data hc hab hOne edge) constituent ∧
      sourceVertexMap data hc hab hOne constituent = vertex := by
  let preimage := (sourceEdgeEquiv data hc hab hOne).symm edge
  have hMap : sourceEdgeMap data hc hab hOne preimage = edge :=
    (sourceEdgeEquiv data hc hab hOne).apply_symm_apply edge
  have hEnds := sourceEnds_sourceEdgeMap data hc hab hOne preimage
  rw [hMap] at hEnds
  rcases hIncident with hFirst | hSecond
  · exact ⟨(data.sourceEnds preimage.1).1, Or.inl rfl,
      (congrArg Prod.fst hEnds).symm.trans hFirst⟩
  · exact ⟨(data.sourceEnds preimage.1).2, Or.inr rfl,
      (congrArg Prod.snd hEnds).symm.trans hSecond⟩

/-- Genuine row compatibility through the pruned fibre, stated on the
established surviving-occurrence embedding. Once the fibre's Euler count
proves its active vertices divalent, no other topology hypothesis is needed. -/
theorem stablePath_nonDanglingEmbedding_eq_of_divalent_fibre
    (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hPreserved : DanglingPreserved data hc hab hOne)
    (vertex : (contractDatum data hc hab hOne).SourceVertex)
    (hDivalent : ∀ constituent : data.SourceVertex,
      sourceVertexMap data hc hab hOne constituent = vertex →
      nonDanglingValency data constituent ≠ 0 → nonDanglingValency data constituent = 2)
    (first second : NonDanglingEdge (contractDatum data hc hab hOne))
    (hFirst : Incident (contractDatum data hc hab hOne) first.1 vertex)
    (hSecond : Incident (contractDatum data hc hab hOne) second.1 vertex) :
    (nonDanglingEmbedding data hPreserved first).stablePath =
      (nonDanglingEmbedding data hPreserved second).stablePath := by
  obtain ⟨left, hLeftInc, hLeft⟩ :=
    exists_incident_sourceEdgeEmbedding data hc hab hOne first.1 vertex hFirst
  obtain ⟨right, hRightInc, hRight⟩ :=
    exists_incident_sourceEdgeEmbedding data hc hab hOne second.1 vertex hSecond
  exact stablePath_eq_of_divalent_fibre data hc hab hOne vertex hDivalent
    (nonDanglingEmbedding data hPreserved first) (nonDanglingEmbedding data hPreserved second)
    left right hLeftInc hRightInc hLeft hRight

section Lift

variable (data : GluingDatum target degree) {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1) (hConnected : graph_connected data.sourceGraph)
  (hCompat : DanglingCompatible data hc hab hOne)
  (hForest : ContractionRamification.ContractionForest data a b contracted)

include hConnected hForest in
/-- Stable adjacency at the actual limit lifts through the actual pruned
fibre. The constituent valencies are derived from the source's Euler formula,
not supplied as an additional hypothesis. -/
theorem stablePath_nonDanglingEmbedding_eq_of_consecutive
    (first second : NonDanglingEdge (contractDatum data hc hab hOne))
    (hConsecutive : Consecutive (contractDatum data hc hab hOne) first second) :
    (nonDanglingEmbedding data hCompat.1 first).stablePath =
      (nonDanglingEmbedding data hCompat.1 second).stablePath := by
  obtain ⟨_, vertex, hFirst, hSecond, hTwo⟩ := hConsecutive
  exact stablePath_nonDanglingEmbedding_eq_of_divalent_fibre data hc hab hOne hCompat.1
    vertex (PrunedFibreTree.nonDanglingValency_eq_two_of_sourceVertexMap_eq
      data hc hab hOne hConnected hCompat hForest vertex hTwo) first second hFirst hSecond

/-- The canonical map from limit stable paths to incoming stable paths,
defined by the actual surviving-occurrence embedding. No free row equivalence
or requested graph dictionary enters this construction. -/
noncomputable def stablePathLift :
    StablePath (contractDatum data hc hab hOne) → StablePath data :=
  Quot.lift (fun edge ↦ (nonDanglingEmbedding data hCompat.1 edge).stablePath)
    (stablePath_nonDanglingEmbedding_eq_of_consecutive data hc hab hOne hConnected hCompat hForest)

@[simp] theorem stablePathLift_mk
    (edge : NonDanglingEdge (contractDatum data hc hab hOne)) :
    stablePathLift data hc hab hOne hConnected hCompat hForest edge.stablePath =
      (nonDanglingEmbedding data hCompat.1 edge).stablePath := rfl

end Lift

end DraismaVargas.LocalCases.PrunedFibreStablePath
