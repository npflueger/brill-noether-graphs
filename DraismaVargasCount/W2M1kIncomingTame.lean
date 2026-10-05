module

public import DraismaVargasCount.W2M1kRowTransport
public import DraismaVargasCount.OutgoingRowCalculus
public import DraismaVargasCount.W2M1kCountBalance

@[expose] public section

/-!
# Incoming M-1k row tameness from a full-dimensional resolution

This file concerns the case `{w2-r2-nd3-M-1k}` of Draisma–Vargas Part I (Figure 33,
Equation (7)).
The incoming wall datum is rectangular and is not change-minimal at the wall.
Its unique ramification-two block has surviving valency three, so every
interior row vertex above the wall is unramified. Away from the wall, a
full-dimensional resolution supplies change-minimality. Retaining a row with
an index greater than one in that resolution proves leaf avoidance, hence
ramification at most one also away from the wall.

The statements use a full-dimensional *member*, never a full-dimensional
presentation of the incoming wall. The final producers apply to the divided
and joined members and to the branch-swapped divided member.  They discharge the
tameness hypothesis of `W2M1kCountBalance.sum_signedMult_eq_zero_of_conditional_tame`,
which gives the balance of Equation (7) (`sum_signedMult_eq_zero`).
-/

namespace DraismaVargas.Count.W2M1kIncomingTame

open DraismaVargas.Infrastructure
open GluingDatum TargetExpansion
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableLocalProperties
open W2R1Target SecondEquation ResolutionM11 ResolutionM1k
open W2M1kSourceCandidates W2M1kLeaves W2M1kStableLift W2M1kCommonBalance
open FullDimensionalSource
open DraismaVargas.Count.RowWalk

variable {target : CFGraph.{0}} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- Change-minimality of a resolution is inherited away from its split vertex. -/
theorem changeMinimalAt_away
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (fd : FullDimensionalSourcePresentation candidate.datum coordinate)
    (vertex : target.V) (hAway : vertex ≠ wall) : data.ChangeMinimalAt vertex := by
  have h := fd.changeMinimal (oldVertex target vertex)
  exact (GlobalResolution.targetExcess_old_of_ne data wall vertex candidate.right
    (LocalResolution.paste _ candidate.resolution candidate.contracts)
    (GlobalAssembly.blockwiseCompatible data wall candidate.right
      candidate.resolution candidate.contracts candidate.exterior) hAway).symm.trans h

/-- A ramified incoming row avoids leaves when its retained occurrences lie
on one row of a full-dimensional resolution. -/
theorem rowAvoidsLeaves_of_retained
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (fd : FullDimensionalSourcePresentation candidate.datum coordinate)
    (hWall : (incidentEdges wall).card ≠ 1)
    {path : StablePath data} {memberRow : StablePath candidate.datum}
    (hRetained : ∀ edge, OnRow data path edge →
      OnRow candidate.datum memberRow (candidate.oldSourceEdge edge))
    {witness : data.SourceEdge} (hWitness : OnRow data path witness)
    (hIndex : data.sourceEdgeIndex witness ≠ 1) : RowAvoidsLeaves data path := by
  have hAvoid := OutgoingRowCalculus.rowAvoidsLeaves_of_index_ne_one fd
    (hRetained witness hWitness)
    (by simpa only [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge] using hIndex)
  intro edge hEdge vertex hLeaf hIncident
  have hAway : vertex ≠ wall := fun h ↦ hWall (h ▸ hLeaf)
  apply hAvoid (candidate.oldSourceEdge edge) (hRetained edge hEdge)
    (oldVertex target vertex)
  · change (incidentEdges (target := TargetExpansion.graph target wall candidate.right)
      (oldVertex target vertex)).card = 1
    rw [GlobalResolution.incidentEdges_card_old_of_ne wall vertex candidate.right hAway]
    exact hLeaf
  · change occurrenceEquiv target wall candidate.right (some edge.1.1) ∈ _
    exact (GlobalResolution.oldOccurrence_mem_incidentEdges_old_iff
      wall vertex candidate.right hAway edge.1.1).mpr hIncident

variable {star : TwoStar target wall} {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- At an M-1k wall, the ramification-two block is a branch vertex, so every
surviving valency-two vertex over the wall has zero ramification. -/
theorem ramification_eq_zero_at_wall (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (vertex : data.SourceVertex) (hWall : vertex.1.1 = wall)
    (hValency : nonDanglingValency data vertex = 2) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 := by
  rcases vertex with ⟨⟨place, sheet⟩, hSheet⟩
  dsimp at hWall
  subst place
  apply W2RankObstructions.other_localRamification_eq_zero input block
    profile.ramification ⟨sheet, hSheet⟩
  intro hEqual
  have hVertex : (⟨(wall, sheet), hSheet⟩ : data.SourceVertex) =
      WallBlock.sourceVertex data wall block := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (congrArg Subtype.val hEqual).trans block.2.symm
  rw [hVertex, profile.valency] at hValency
  omega

/-- Tameness on the rectangular wall from leaf avoidance and the off-wall change
budget (change-minimality away from the wall). The ramification-two wall is handled
separately. -/
theorem rowRamificationAtMostOne_of_away_changeMinimal
    (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hMinimal : ∀ vertex, vertex ≠ wall → data.ChangeMinimalAt vertex)
    {path : StablePath data} (hAvoid : RowAvoidsLeaves data path) :
    RowRamificationAtMostOne data path := by
  intro vertex edge hEdge hIncident hValency
  by_cases hWall : vertex.1.1 = wall
  · exact Or.inl (ramification_eq_zero_at_wall input profile vertex hWall hValency)
  · have hMem := IndexPattern.target_mem_of_incident hIncident
    have hPos : 0 < (incidentEdges vertex.1.1).card :=
      Finset.card_pos.mpr ⟨edge.1.1, hMem⟩
    have hNotLeaf : (incidentEdges vertex.1.1).card ≠ 1 :=
      fun h ↦ hAvoid edge hEdge vertex.1.1 h hMem
    have hNonneg := data.localRamification_nonneg vertex.1.1
      (input.valid.2 vertex.1.1) ⟨vertex.1.2, vertex.2⟩
    have hLe : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ ≤
        data.targetChange vertex.1.1 :=
      Finset.single_le_sum
        (fun item _ ↦ data.localRamification_nonneg vertex.1.1
          (input.valid.2 vertex.1.1) item) (Finset.mem_univ _)
    have hChange : data.targetChange vertex.1.1 +
        ((incidentEdges vertex.1.1).card : ℤ) - 3 = 0 := hMinimal vertex.1.1 hWall
    omega

/-- A full-dimensional member with the geometric row lift supplies incoming
tameness for every row carrying an occurrence of index different from one. -/
theorem rowRamificationAtMostOne_of_lift
    (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (lift : LimitChainCore.LiftData data wall)
    (fd : FullDimensionalSourcePresentation lift.candidate.datum coordinate)
    {path : StablePath data} {edge : data.SourceEdge}
    (hEdge : OnRow data path edge) (hIndex : data.sourceEdgeIndex edge ≠ 1) :
    RowRamificationAtMostOne data path := by
  apply rowRamificationAtMostOne_of_away_changeMinimal input profile
    (changeMinimalAt_away lift.candidate fd)
  exact rowAvoidsLeaves_of_retained lift.candidate fd
    (by rw [star.card_incidentEdges]; decide)
    (fun _ h ↦ W2M1kRowTransport.onRow_oldSourceEdge lift h) hEdge hIndex

/-- The local divided member discharges incoming second-row tameness. -/
theorem secondRow_tame_of_divided (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (fd : FullDimensionalSourcePresentation
      (DividedData.candidate shape divided).datum coordinate) :
    RowRamificationAtMostOne data (secondRow profile) :=
  rowRamificationAtMostOne_of_lift input profile (dividedLiftData input shape divided)
    fd ⟨profile.second_survives, rfl⟩
    (by rw [shape.second_index]; have := shape.one_lt_k; omega)

/-- The joined member also discharges incoming second-row tameness: the lift
retains every row, not only the member's perturbed third row. -/
theorem secondRow_tame_of_joined (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall)
    (fd : FullDimensionalSourcePresentation (joinedCandidate star geometry).datum coordinate) :
    RowRamificationAtMostOne data (secondRow profile) :=
  rowRamificationAtMostOne_of_lift input profile (joinedLiftData input profile geometry)
    fd ⟨profile.second_survives, rfl⟩
    (by rw [shape.second_index]; have := shape.one_lt_k; omega)

open W2M1kTransport

/-- Leaf avoidance is preserved when the occurrence gauge lies over
the identity of the target. -/
theorem rowAvoidsLeaves_of_gauge {base : GluingDatum target degree}
    (gauge : LimitChainCore.Gauge data base wall) {path : StablePath data}
    (hAvoid : RowAvoidsLeaves base (gauge.row path)) : RowAvoidsLeaves data path := by
  intro edge hEdge vertex hLeaf hIncident
  apply hAvoid (gauge.edge edge) (W2M1kRowTransport.onRow_gauge gauge hEdge)
    vertex hLeaf
  simpa only [gauge.target_eq] using hIncident

/-- The branch-swapped divided member discharges tameness on the original
incoming second row. Leaf avoidance descends through the occurrence gauge;
the off-wall change budget descends by relabelling invariance. -/
theorem secondRow_tame_of_remote_divided (input : W2SourceInput data star)
    (shape : Shape profile) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (divided : DividedData (swapProfile profile input.valid.1 other hOther))
    (fd : FullDimensionalSourcePresentation
      (DividedData.candidate (swapShape shape input.valid.1 other hOther) divided).datum
        coordinate) :
    RowRamificationAtMostOne data (secondRow profile) := by
  let relabeling := swapRelabeling profile other hOther
  let gauge := swapGauge profile input.valid.1 other hOther
  let lift := dividedLiftData (swapInput input other hOther)
    (swapShape shape input.valid.1 other hOther) divided
  apply rowRamificationAtMostOne_of_away_changeMinimal input profile
  · intro vertex hAway
    have hMinimal := changeMinimalAt_away lift.candidate fd vertex hAway
    exact (W2SourceTransport.targetExcess_relabel relabeling vertex).symm.trans hMinimal
  · apply rowAvoidsLeaves_of_gauge gauge
    exact rowAvoidsLeaves_of_retained lift.candidate fd
      (by rw [star.card_incidentEdges]; decide)
      (fun _ h ↦ W2M1kRowTransport.onRow_oldSourceEdge lift h)
      (W2M1kRowTransport.onRow_gauge gauge
        (show OnRow data (secondRow profile) profile.second.1 from
          ⟨profile.second_survives, rfl⟩))
      (by rw [gauge.index_eq, shape.second_index]; have := shape.one_lt_k; omega)

open W2M1kLimitColumns

/-- A full-dimensional position-one member gives incoming tameness in both
pin orientations. -/
theorem secondRow_tame_of_member_one (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (fd : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member 1).datum coordinate) :
    RowRamificationAtMostOne data (secondRow profile) := by
  classical
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [limitColumns_eq_alignedOrientation input shape hConnected hGenus hAligned,
      alignedOrientation_member_one] at fd
    let pair := (exists_leafPair shape hAligned).some
    exact secondRow_tame_of_remote_divided input shape pair.second pair.rel_second
      (remoteDivided input shape pair hConnected hGenus) fd
  · rw [limitColumns_eq_separatedOrientation input shape hConnected hGenus hAligned,
      separatedOrientation_member_one] at fd
    exact secondRow_tame_of_divided input shape (exists_dividedData shape hAligned).some fd

/-- A full-dimensional position-two member also gives incoming tameness. -/
theorem secondRow_tame_of_member_two (input : W2SourceInput data star)
    (shape : Shape profile) (hConnected : graph_connected target) (hGenus : genus target = 0)
    (fd : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member 2).datum coordinate) :
    RowRamificationAtMostOne data (secondRow profile) := by
  classical
  by_cases hAligned : pinSheet profile 0 = pinSheet profile 1
  · rw [limitColumns_eq_alignedOrientation input shape hConnected hGenus hAligned,
      alignedOrientation_member_two] at fd
    exact secondRow_tame_of_joined input shape
      ((exists_leafPair shape hAligned).some.geometry shape) fd
  · rw [limitColumns_eq_separatedOrientation input shape hConnected hGenus hAligned,
      separatedOrientation_member_two] at fd
    exact secondRow_tame_of_joined input shape
      ((exists_dividedData shape hAligned).some.geometry shape) fd

/-- **Part I, Equation (7): the signed multiplicity balance on the M-1k family.**
All row, index, denominator, siting and transport hypotheses are discharged. The
only full-dimensional input is the chart the deformation already carries: a
full-dimensional presentation `incomingFD` of the member at any one position.
If both perturbed members are singular their contributions vanish outright;
otherwise one of them supplies incoming tameness. -/
theorem sum_signedMult_eq_zero
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (initial : StableLengthMatrixLabelling
      ((limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member incoming).datum coordinate) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape hConnected hGenus).labelling initial position).presentation =
        0 := by
  apply W2M1kCountBalance.sum_signedMult_eq_zero_of_conditional_tame
    input shape hConnected hGenus incoming initial incomingFD
  rintro (hOne | hTwo)
  · exact secondRow_tame_of_member_one input shape hConnected hGenus
      (W2M1kMemberBalance.memberPresentation input shape hConnected hGenus
        incoming 1 initial incomingFD hOne)
  · exact secondRow_tame_of_member_two input shape hConnected hGenus
      (W2M1kMemberBalance.memberPresentation input shape hConnected hGenus
        incoming 2 initial incomingFD hTwo)

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance : DecidableEq (Option target.edges) := Classical.decEq _

/-- The same balance in canonical coordinates. -/
theorem sum_signedMult_canonical_eq_zero
    (input : W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSourcePresentation
      ((limitColumns input shape hConnected hGenus).member incoming).datum
        (Option target.edges)) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape hConnected hGenus).labelling
        ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input)
          position).presentation = 0 :=
  sum_signedMult_eq_zero input shape hConnected hGenus incoming _ incomingFD

end DraismaVargas.Count.W2M1kIncomingTame
