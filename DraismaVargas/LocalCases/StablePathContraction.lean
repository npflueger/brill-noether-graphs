import DraismaVargas.LocalCases.WallProgress

/-!
# A checked unramified instance of stable-path transport through contraction

Source: Draisma--Vargas Part I, `lemma-class-union`, the discussion of the
pruned fibre (`lemma-ndval-of-GqA0` and the lemmas after it), and the
unramified auxiliary blocks in Case {w2}.  The general argument needs the
pruned contracted fibre to be a tree.  The `ContractionForest` API proves
the full fibre's Euler count and ramification additivity, but does not itself
construct that pruned tree (see `PrunedFibreTree`).

Here we prove the bounded unramified instance for contraction of an occurrence
between two divalent target vertices.  Ramification zero of the actual merged
block, forest additivity, and nonnegative incoming ramification force the two
incoming endpoint blocks of each sheet to have ramification zero.  Their
source vertices have ordinary degree two.  Consequently the two exterior
occurrences and the contracted occurrence are on the same actual stable path.
The result uses the literal surviving-occurrence embedding, not an assumed
equivalence of stable paths or an arbitrary matrix-row assignment.

This is not the ramification-two fibre theorem needed for the nd2 exclusions.
-/

namespace DraismaVargas.LocalCases.StablePathContraction

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4StableSource StableLocalProperties WallDegeneration

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-- The fine block containing a sheet belongs to the coarse block containing
that same sheet. -/
theorem toBlock_mem_blocksWithin (fine coarse : SheetPartition degree)
    (hRefines : fine.Refines coarse) (sheet : Fin degree) :
    fine.toBlock sheet ∈ SheetPartition.blocksWithin fine coarse (coarse.toBlock sheet) := by
  apply (SheetPartition.mem_blocksWithin fine coarse _ _).mpr
  apply (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse _ _).mpr
  exact (coarse.rel_repr_left sheet).trans (hRefines.rel (fine.rel_repr_left sheet)).symm

/-- A zero-ramification contracted block can contain only zero-ramification
incoming blocks.  This is a direct consequence of the proved forest
ramification formula, not an additional source-profile assumption. -/
theorem endpoint_localRamification_eq_zero (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hForest : ContractionForest data a b contracted) (sheet : Fin degree)
    (hZero : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet = 0) :
    data.localRamification a ((data.vertexPartition a).toBlock sheet) = 0 ∧
      data.localRamification b ((data.vertexPartition b).toBlock sheet) = 0 := by
  classical
  let mergedBlock := (mergedPartition data a b).toBlock sheet
  have hRel : ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
      sheet mergedBlock.1 := by
    rw [contractDatum_vertexPartition_merge]
    exact (mergedPartition data a b).rel_repr_right sheet
  have hZero' : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩
      mergedBlock.1 = 0 :=
    (localRamificationAt_congr _ _ hRel).symm.trans hZero
  have hSum := localRamificationAt_contractDatum_merge data hc hab hOne hForest mergedBlock
  rw [hZero'] at hSum
  have hLeftNonneg := Finset.sum_nonneg (fun block _ ↦
    data.localRamification_nonneg a (hValid.2 a) block)
    (s := SheetPartition.blocksWithin (data.vertexPartition a)
      (mergedPartition data a b) mergedBlock)
  have hRightNonneg := Finset.sum_nonneg (fun block _ ↦
    data.localRamification_nonneg b (hValid.2 b) block)
    (s := SheetPartition.blocksWithin (data.vertexPartition b)
      (mergedPartition data a b) mergedBlock)
  have hLeftLe := Finset.single_le_sum
    (fun block _ ↦ data.localRamification_nonneg a (hValid.2 a) block)
    (toBlock_mem_blocksWithin (data.vertexPartition a) (mergedPartition data a b)
      (vertexPartition_refines_mergedPartition data a b) sheet)
  have hRightLe := Finset.single_le_sum
    (fun block _ ↦ data.localRamification_nonneg b (hValid.2 b) block)
    (toBlock_mem_blocksWithin (data.vertexPartition b) (mergedPartition data a b)
      (vertexPartition_refines_mergedPartition_right data a b) sheet)
  have hLeftZero := data.localRamification_nonneg a (hValid.2 a)
    ((data.vertexPartition a).toBlock sheet)
  have hRightZero := data.localRamification_nonneg b (hValid.2 b)
    ((data.vertexPartition b).toBlock sheet)
  change 0 = _ at hSum
  dsimp only [mergedBlock] at hSum hLeftNonneg hRightNonneg
  constructor <;> omega

/-- Through an unramified fibre of a divalent-divalent contraction, the two
actual exterior occurrences of a sheet belong to the same incoming stable
path.  The intermediate contracted occurrence is proved to survive. -/
theorem stablePath_sourceEdge_eq_of_unramified_divalent
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hForest : ContractionForest data a b contracted)
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    (sheet : Fin degree)
    (hZero : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet = 0)
    (first second : target.edges) (hFirstNe : first ≠ contracted)
    (hSecondNe : second ≠ contracted)
    (hFirst : first ∈ GluingDatum.incidentEdges a)
    (hSecond : second ∈ GluingDatum.incidentEdges b)
    (hFirstSurvives : ¬ IsDangling data (data.sourceEdge first sheet))
    (hSecondSurvives : ¬ IsDangling data (data.sourceEdge second sheet)) :
    NonDanglingEdge.stablePath ⟨data.sourceEdge first sheet, hFirstSurvives⟩ =
      NonDanglingEdge.stablePath ⟨data.sourceEdge second sheet, hSecondSurvives⟩ := by
  obtain ⟨hLeftZero, hRightZero⟩ :=
    endpoint_localRamification_eq_zero data hc hab hOne hValid hForest sheet hZero
  have hContractedLeft := contracted_mem_incidentEdges_left hc
  have hContractedRight := contracted_mem_incidentEdges_right hc
  have hInternalSurvives : ¬ IsDangling data (data.sourceEdge contracted sheet) := by
    intro hDangling
    exact hFirstSurvives ((isDangling_sourceEdge_iff_of_divalent_localRamification_zero
      data a hLeftDivalent sheet hLeftZero hFirstNe hFirst hContractedLeft).mpr hDangling)
  exact (stablePath_sourceEdge_eq_of_divalent_localRamification_zero data a
    hLeftDivalent sheet hLeftZero hFirstNe hFirst hContractedLeft
    hFirstSurvives hInternalSurvives).trans
      (stablePath_sourceEdge_eq_of_divalent_localRamification_zero data b
        hRightDivalent sheet hRightZero hSecondNe.symm hContractedRight hSecond
        hInternalSurvives hSecondSurvives)

/-- On a canonical sheet occurrence, the actual source embedding is exactly
the corresponding canonical incoming occurrence. -/
theorem sourceEdgeEmbedding_sourceEdge_foldEdge
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (edge : target.edges)
    (hEdge : edge ≠ contracted) (sheet : Fin degree) :
    sourceEdgeEmbedding data hc hab hOne
        ((contractDatum data hc hab hOne).sourceEdge (foldEdge hc hab hOne ⟨edge, hEdge⟩) sheet) =
      data.sourceEdge edge sheet := by
  have hAway : (data.sourceEdge edge sheet).1.1 ≠ contracted := hEdge
  have hMap : sourceEdgeMap data hc hab hOne ⟨data.sourceEdge edge sheet, hAway⟩ =
      (contractDatum data hc hab hOne).sourceEdge (foldEdge hc hab hOne ⟨edge, hEdge⟩) sheet := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (data.edgePartition edge).repr sheet =
        ((contractDatum data hc hab hOne).edgePartition
          (foldEdge hc hab hOne ⟨edge, hEdge⟩)).repr sheet
      rw [contractDatum_edgePartition_foldEdge]
  rw [← hMap, sourceEdgeEmbedding_sourceEdgeMap]

/-- The unramified transport theorem on the actual surviving-occurrence
embedding.  Only dangling preservation is needed in this direction; the
vanishing endpoint ramification is derived from validity and the forest. -/
theorem stablePath_nonDanglingEmbedding_eq_of_unramified_divalent
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (hValid : data.Valid)
    (hForest : ContractionForest data a b contracted)
    (hPreserved : DanglingPreserved data hc hab hOne)
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    (sheet : Fin degree)
    (hZero : localRamificationAt (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet = 0)
    (first second : target.edges) (hFirstNe : first ≠ contracted)
    (hSecondNe : second ≠ contracted)
    (hFirst : first ∈ GluingDatum.incidentEdges a)
    (hSecond : second ∈ GluingDatum.incidentEdges b)
    (hFirstSurvives : ¬ IsDangling (contractDatum data hc hab hOne)
      ((contractDatum data hc hab hOne).sourceEdge
        (foldEdge hc hab hOne ⟨first, hFirstNe⟩) sheet))
    (hSecondSurvives : ¬ IsDangling (contractDatum data hc hab hOne)
      ((contractDatum data hc hab hOne).sourceEdge
        (foldEdge hc hab hOne ⟨second, hSecondNe⟩) sheet)) :
    NonDanglingEdge.stablePath (nonDanglingEmbedding data hPreserved
      ⟨(contractDatum data hc hab hOne).sourceEdge
        (foldEdge hc hab hOne ⟨first, hFirstNe⟩) sheet, hFirstSurvives⟩) =
      NonDanglingEdge.stablePath (nonDanglingEmbedding data hPreserved
        ⟨(contractDatum data hc hab hOne).sourceEdge
          (foldEdge hc hab hOne ⟨second, hSecondNe⟩) sheet, hSecondSurvives⟩) := by
  let left : NonDanglingEdge data := nonDanglingEmbedding data hPreserved
    ⟨(contractDatum data hc hab hOne).sourceEdge
      (foldEdge hc hab hOne ⟨first, hFirstNe⟩) sheet, hFirstSurvives⟩
  let right : NonDanglingEdge data := nonDanglingEmbedding data hPreserved
    ⟨(contractDatum data hc hab hOne).sourceEdge
      (foldEdge hc hab hOne ⟨second, hSecondNe⟩) sheet, hSecondSurvives⟩
  have hLeftValue : left.1 = data.sourceEdge first sheet :=
    sourceEdgeEmbedding_sourceEdge_foldEdge data hc hab hOne first hFirstNe sheet
  have hRightValue : right.1 = data.sourceEdge second sheet :=
    sourceEdgeEmbedding_sourceEdge_foldEdge data hc hab hOne second hSecondNe sheet
  have hLeftSurvives : ¬ IsDangling data (data.sourceEdge first sheet) := hLeftValue ▸ left.2
  have hRightSurvives : ¬ IsDangling data (data.sourceEdge second sheet) := hRightValue ▸ right.2
  have hLeftEq : left = (⟨data.sourceEdge first sheet, hLeftSurvives⟩ : NonDanglingEdge data) :=
    Subtype.ext hLeftValue
  have hRightEq : right = (⟨data.sourceEdge second sheet, hRightSurvives⟩ : NonDanglingEdge data) :=
    Subtype.ext hRightValue
  change left.stablePath = right.stablePath
  rw [hLeftEq, hRightEq]
  exact stablePath_sourceEdge_eq_of_unramified_divalent data hc hab hOne hValid hForest
    hLeftDivalent hRightDivalent sheet hZero first second hFirstNe hSecondNe
    hFirst hSecond hLeftSurvives hRightSurvives

/-- Literal occurrence embedding reflects incidence at every unchanged
source vertex. -/
theorem incident_sourceEdgeEmbedding_iff_of_ne
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (edge : (contractDatum data hc hab hOne).SourceEdge) (vertex : data.SourceVertex)
    (hLeft : vertex.1.1 ≠ a) (hRight : vertex.1.1 ≠ b) :
    Incident data (sourceEdgeEmbedding data hc hab hOne edge) vertex ↔
      Incident (contractDatum data hc hab hOne) edge
        (sourceVertexMap data hc hab hOne vertex) := by
  have hMap : sourceEdgeMap data hc hab hOne ((sourceEdgeEquiv data hc hab hOne).symm edge) =
      edge := (sourceEdgeEquiv data hc hab hOne).apply_symm_apply edge
  have hIncident := incident_sourceEdgeMap_iff_of_ne data hc hab hOne
    ((sourceEdgeEquiv data hc hab hOne).symm edge) vertex hLeft hRight
  rw [hMap] at hIncident
  exact hIncident.symm

/-- Stable adjacency at a source vertex away from the merged fibre lifts
under the actual occurrence embedding.  Both dangling directions are used
only through the already-proved equality of the surviving valencies there. -/
theorem consecutive_nonDanglingEmbedding_of_ne
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hCompat : DanglingCompatible data hc hab hOne)
    (first second : NonDanglingEdge (contractDatum data hc hab hOne))
    (hNe : first ≠ second) (vertex : data.SourceVertex)
    (hLeft : vertex.1.1 ≠ a) (hRight : vertex.1.1 ≠ b)
    (hFirst : Incident (contractDatum data hc hab hOne) first.1
      (sourceVertexMap data hc hab hOne vertex))
    (hSecond : Incident (contractDatum data hc hab hOne) second.1
      (sourceVertexMap data hc hab hOne vertex))
    (hValency : nonDanglingValency (contractDatum data hc hab hOne)
      (sourceVertexMap data hc hab hOne vertex) = 2) :
    Consecutive data (nonDanglingEmbedding data hCompat.1 first)
      (nonDanglingEmbedding data hCompat.1 second) := by
  refine ⟨fun hEq ↦ hNe (nonDanglingEmbedding_injective data hCompat.1 hEq),
    vertex, ?_, ?_, ?_⟩
  · exact (incident_sourceEdgeEmbedding_iff_of_ne data hc hab hOne first.1 vertex
      hLeft hRight).mpr hFirst
  · exact (incident_sourceEdgeEmbedding_iff_of_ne data hc hab hOne second.1 vertex
      hLeft hRight).mpr hSecond
  · exact (nonDanglingValency_sourceVertexMap data hCompat vertex hLeft hRight).symm.trans hValency

end DraismaVargas.LocalCases.StablePathContraction
