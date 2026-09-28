import DraismaVargasCount.RowRegrowth
import DraismaVargas.LocalCases.W2M1kRowDescent

/-!
# Retained occurrence transport for the two perturbed M-1k rows

This is the occurrence transport `hTransport` of
`RowRegrowth.forall_index_eq_of_transport` on the members of case `{w2-r2-nd3-M-1k}`
(Draisma--Vargas Part I, arXiv:1909.12924, Figure 33).  The map is the literal
`Candidate.oldSourceEdge`, not a choice of a member occurrence with a matching
index.  The geometric stable
lift already proves that retaining an occurrence respects its row.  Retained
occurrences preserve their dilation index, are injective, and avoid every
regrown occurrence because their target edges are different.

`rowOccurrenceEmbedding` packages these facts for any `LimitChainCore.LiftData`.
`transport_divided_secondRow` and `transport_joined_thirdRow` have exactly the
`hTransport` conclusion of `RowRegrowth.forall_index_eq_of_transport` on the
members constructed by Figure 33.  No full-dimensionality, index constancy,
or transition hypothesis is used here.  The divided statement also applies
to the branch-swapped datum by substitution, as in `W2M1kStableLift`.
-/

namespace DraismaVargas.Count.W2M1kRowTransport

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open W4Assembly W4StableSource StableLocalProperties
open W2R1Target SecondEquation ResolutionM1k
open W2M1kSourceCandidates W2M1kLeaves W2M1kStableLift W2M1kCommonBalance
open DraismaVargas.Count.RowWalk

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

/-- Retention carries every incoming occurrence onto its geometric lifted row. -/
theorem onRow_oldSourceEdge (lift : LimitChainCore.LiftData data wall)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    OnRow lift.candidate.datum (lift.stablePathLift path)
      (lift.candidate.oldSourceEdge edge) := by
  obtain ⟨hSurvives, hRow⟩ := hEdge
  exact ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ lift.valid.1 _ hSurvives,
    congrArg lift.stablePathLift hRow⟩

/-- The actual injection of incoming row occurrences into member occurrences
off a specified regrown edge.  In fact the image avoids every new edge. -/
noncomputable def rowOccurrenceEmbedding (lift : LimitChainCore.LiftData data wall)
    (path : StablePath data) (sheet : Fin degree) :
    {edge : data.SourceEdge // OnRow data path edge} ↪
      {edge : lift.candidate.datum.SourceEdge //
        OnRow lift.candidate.datum (lift.stablePathLift path) edge ∧
          edge ≠ lift.candidate.newSourceEdge sheet} where
  toFun edge := ⟨lift.candidate.oldSourceEdge edge.1,
    onRow_oldSourceEdge lift edge.2,
    LimitChainCore.oldSourceEdge_ne_newSourceEdge edge.1 sheet⟩
  inj' := by
    intro first second hEqual
    exact Subtype.ext (ResolutionCut.oldSourceEdge_injective lift.candidate
      (congrArg Subtype.val hEqual))

/-- The occurrence injection preserves dilation indices exactly. -/
theorem rowOccurrenceEmbedding_index (lift : LimitChainCore.LiftData data wall)
    (path : StablePath data) (sheet : Fin degree)
    (edge : {edge : data.SourceEdge // OnRow data path edge}) :
    lift.candidate.datum.sourceEdgeIndex (rowOccurrenceEmbedding lift path sheet edge).1 =
      data.sourceEdgeIndex edge.1 :=
  BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _

/-- The existential form consumed by the regrowth argument. -/
theorem transport (lift : LimitChainCore.LiftData data wall)
    (path : StablePath data) (sheet : Fin degree) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : lift.candidate.datum.SourceEdge,
        OnRow lift.candidate.datum (lift.stablePathLift path) image ∧
          image ≠ lift.candidate.newSourceEdge sheet ∧
          lift.candidate.datum.sourceEdgeIndex image = data.sourceEdgeIndex edge := by
  intro edge hEdge
  let occurrence := rowOccurrenceEmbedding lift path sheet
    ⟨edge, (onRow_iff_mem_incomingRowEdges path edge).mpr hEdge⟩
  exact ⟨occurrence.1, occurrence.2.1, occurrence.2.2,
    BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _⟩

/-- A branch gauge carries the literal occurrence onto its corresponding row. -/
theorem onRow_gauge {base : GluingDatum target degree}
    (gauge : LimitChainCore.Gauge data base wall)
    {path : StablePath data} {edge : data.SourceEdge} (hEdge : OnRow data path edge) :
    OnRow base (gauge.row path) (gauge.edge edge) := by
  obtain ⟨hSurvives, hRow⟩ := hEdge
  exact ⟨fun hDangling ↦ hSurvives ((gauge.isDangling_iff edge).mp hDangling),
    (gauge.row_mk edge hSurvives).symm.trans (congrArg gauge.row hRow)⟩

/-- For a member constructed after a branch swap, first carry each occurrence
through the gauge and then retain it.  Both maps are actual injections. -/
noncomputable def rowOccurrenceEmbeddingOfGauge {base : GluingDatum target degree}
    (gauge : LimitChainCore.Gauge data base wall)
    (lift : LimitChainCore.LiftData base wall) (path : StablePath data) (sheet : Fin degree) :
    {edge : data.SourceEdge // OnRow data path edge} ↪
      {edge : lift.candidate.datum.SourceEdge //
        OnRow lift.candidate.datum (lift.stablePathLift (gauge.row path)) edge ∧
          edge ≠ lift.candidate.newSourceEdge sheet} where
  toFun edge := rowOccurrenceEmbedding lift (gauge.row path) sheet
    ⟨gauge.edge edge.1, onRow_gauge gauge edge.2⟩
  inj' := by
    intro first second hEqual
    exact Subtype.ext (gauge.edge.injective
      (ResolutionCut.oldSourceEdge_injective lift.candidate (congrArg Subtype.val hEqual)))

/-- The gauge-composed occurrence injection preserves dilation indices. -/
theorem rowOccurrenceEmbeddingOfGauge_index {base : GluingDatum target degree}
    (gauge : LimitChainCore.Gauge data base wall)
    (lift : LimitChainCore.LiftData base wall) (path : StablePath data) (sheet : Fin degree)
    (edge : {edge : data.SourceEdge // OnRow data path edge}) :
    lift.candidate.datum.sourceEdgeIndex
        (rowOccurrenceEmbeddingOfGauge gauge lift path sheet edge).1 =
      data.sourceEdgeIndex edge.1 :=
  (BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _).trans (gauge.index_eq edge.1)

/-- `hTransport` for a member over a gauge copy of the incoming datum.  This
is the aligned orientation's remote divided member in Figure 33. -/
theorem transport_of_gauge {base : GluingDatum target degree}
    (gauge : LimitChainCore.Gauge data base wall)
    (lift : LimitChainCore.LiftData base wall) (path : StablePath data) (sheet : Fin degree) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data path,
      ∃ image : lift.candidate.datum.SourceEdge,
        OnRow lift.candidate.datum (lift.stablePathLift (gauge.row path)) image ∧
          image ≠ lift.candidate.newSourceEdge sheet ∧
          lift.candidate.datum.sourceEdgeIndex image = data.sourceEdgeIndex edge := by
  intro edge hEdge
  let occurrence := rowOccurrenceEmbeddingOfGauge gauge lift path sheet
    ⟨edge, (onRow_iff_mem_incomingRowEdges path edge).mpr hEdge⟩
  exact ⟨occurrence.1, occurrence.2.1, occurrence.2.2,
    (BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge _ _).trans (gauge.index_eq edge)⟩

variable {star : TwoStar target wall} {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- The transport for `M⁽²⁾`: every old second-row occurrence survives on the retained
second row, preserves its index, and avoids the residual regrown occurrence. -/
theorem transport_divided_secondRow (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (secondRow profile),
      ∃ image : (DividedData.candidate shape divided).datum.SourceEdge,
        OnRow (DividedData.candidate shape divided).datum
            (NonDanglingEdge.stablePath
              ⟨(DividedData.candidate shape divided).oldSourceEdge profile.second.1,
                ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
                  profile.second_survives⟩) image ∧
          image ≠ (DividedData.candidate shape divided).newSourceEdge divided.third ∧
          (DividedData.candidate shape divided).datum.sourceEdgeIndex image =
            data.sourceEdgeIndex edge :=
  transport (dividedLiftData input shape divided) (secondRow profile) divided.third

/-- The transport for `M⁽³⁾`: the same on the third row, avoiding its single
regrown occurrence over the distinguished wall block. -/
theorem transport_joined_thirdRow (input : W2SourceInput data star)
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (geometry : GlobalM1k.Geometry data wall) :
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (thirdRow profile),
      ∃ image : (joinedCandidate star geometry).datum.SourceEdge,
        OnRow (joinedCandidate star geometry).datum
            (NonDanglingEdge.stablePath
              ⟨(joinedCandidate star geometry).oldSourceEdge profile.third.1,
                ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _
                  profile.third_survives⟩) image ∧
          image ≠ (joinedCandidate star geometry).newSourceEdge block.1 ∧
          (joinedCandidate star geometry).datum.sourceEdgeIndex image =
            data.sourceEdgeIndex edge :=
  transport (joinedLiftData input profile geometry) (thirdRow profile) block.1

open W2M1kTransport W2M1kLimitColumns

/-- The transport in the aligned orientation: transport occurrences of the original
incoming second row to the divided member over the branch-swapped datum.
The named row identity consumes `swapProfile_secondRow`, so the conclusion
is on the retained partner row used by the transition-siting theorem. -/
theorem transport_remote_divided_secondRow (input : W2SourceInput data star)
    (shape : Shape profile) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile 0) other)
    (divided : DividedData (swapProfile profile input.valid.1 other hOther)) :
    let swappedInput := swapInput input other hOther
    let swappedShape := swapShape shape input.valid.1 other hOther
    let swappedProfile := swapProfile profile input.valid.1 other hOther
    let candidate := DividedData.candidate swappedShape divided
    ∀ edge ∈ TrivalentWeight.incomingRowEdges data (secondRow profile),
      ∃ image : candidate.datum.SourceEdge,
        OnRow candidate.datum
            (NonDanglingEdge.stablePath
              ⟨candidate.oldSourceEdge swappedProfile.second.1,
                ResolutionSurvival.not_isDangling_oldSourceEdge _ swappedInput.valid.1 _
                  swappedProfile.second_survives⟩) image ∧
          image ≠ candidate.newSourceEdge divided.third ∧
          candidate.datum.sourceEdgeIndex image = data.sourceEdgeIndex edge := by
  dsimp only
  have hTransport := transport_of_gauge (swapGauge profile input.valid.1 other hOther)
    (dividedLiftData (swapInput input other hOther)
      (swapShape shape input.valid.1 other hOther) divided) (secondRow profile) divided.third
  rw [← swapProfile_secondRow input.valid.1 other hOther] at hTransport
  exact hTransport

end DraismaVargas.Count.W2M1kRowTransport
