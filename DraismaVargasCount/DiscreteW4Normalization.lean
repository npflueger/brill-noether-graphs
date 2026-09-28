import DraismaVargasCount.GeometricUniformExpansion
import DraismaVargasCount.DiscreteContraction
import DraismaVargasCount.W4IncomingNormalizedPartitions
import DraismaVargas.LocalCases.IncomingNormalizationRows

/-!
# Every discrete W4 regrowth is an actual uniform expansion

The incoming target normalization already names its precise pairing. When
the contracted wall partition is discrete, all local partitions are forced;
the normalized datum is literally the uniform expansion, not merely a datum
with the same length matrix or block sizes.  `W4WallExhaustion` uses this for
the exhaustion of the star at a discrete four-valent wall (wall type `{w4}` of
Draisma–Vargas Part I, arXiv:1909.12924, Figures 26–27).
-/
namespace DraismaVargas.Count.DiscreteW4Normalization
open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction TargetExpansion
open W4IncomingTargetNormalization W4IncomingNormalizedPartitions

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  (original : GluingDatum target degree)
  (fd : FullDimensionalSource.FullDimensionalSourcePresentation original coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a,b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a,hab⟩)
  (hDiscrete : (contractDatum original hc hab hOne).vertexPartition ⟨a,hab⟩ =
    SheetPartition.discrete degree)

include hDiscrete in
theorem normalized_eq :
    transported original fd hc hab hOne star =
      GeometricUniformExpansion.data (contractDatum original hc hab hOne) ⟨a,hab⟩
        (star.right (pairing original fd hc hab hOne star)) := by
  have hLocal := DiscreteContraction.partitions_discrete original hc hab hOne hDiscrete
  have hEndpoint :
      ((transported original fd hc hab hOne star).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a,hab⟩),
       (transported original fd hc hab hOne star).vertexPartition
        (freshVertex (contract target hab hOne))) =
          (SheetPartition.discrete degree,SheetPartition.discrete degree) := by
    have h := M11IncomingOuterPartitions.transported_endpointPartitions original hc hab hOne
      (star.right (pairing original fd hc hab hOne star))
      (pairing_placement original fd hc hab hOne star)
    rw [hLocal.1,hLocal.2.1] at h
    simpa only [ite_self,transported,W4IncomingTargetNormalization.targetIso] using h
  apply gluingDatum_ext
  · funext vertex
    cases vertex with
    | inl vertex =>
      by_cases h : vertex = ⟨a,hab⟩
      · subst vertex
        exact (congrArg Prod.fst hEndpoint).trans (hDiscrete.symm.trans
          (GeometricUniformExpansion.vertexPartition (contractDatum original hc hab hOne)
            ⟨a,hab⟩ (star.right (pairing original fd hc hab hOne star))
            (oldVertex (contract target hab hOne) ⟨a,hab⟩)).symm)
      · exact (W4IncomingNormalizedPartitions.vertexPartition_of_ne original fd hc hab hOne
          star vertex h).trans (GeometricUniformExpansion.vertexPartition
            (contractDatum original hc hab hOne) ⟨a,hab⟩
            (star.right (pairing original fd hc hab hOne star))
            (oldVertex (contract target hab hOne) vertex)).symm
    | inr vertex =>
      cases vertex
      exact (congrArg Prod.snd hEndpoint).trans (hDiscrete.symm.trans
        (GeometricUniformExpansion.vertexPartition (contractDatum original hc hab hOne)
          ⟨a,hab⟩ (star.right (pairing original fd hc hab hOne star))
          (freshVertex (contract target hab hOne))).symm)
  · funext edge
    obtain ⟨label,rfl⟩ := (occurrenceEquiv (contract target hab hOne) ⟨a,hab⟩
      (star.right (pairing original fd hc hab hOne star))).surjective edge
    cases label with
    | none =>
      exact (W4IncomingNormalizedPartitions.edgePartition_new original fd hc hab hOne star).trans
        (hLocal.2.2.trans (hDiscrete.symm.trans
          (GeometricUniformExpansion.edgePartition_none _ _ _).symm))
    | some edge =>
      exact (W4IncomingNormalizedPartitions.edgePartition_retained original fd hc hab hOne star edge).trans
        (GeometricUniformExpansion.edgePartition_some _ _ _ _).symm

/-- An actual geometric datum isomorphism from the arbitrary incoming
regrowth onto the uniform member selected by its target placement. -/
noncomputable def datumIso : GeometricDatumIso original
    (GeometricUniformExpansion.data (contractDatum original hc hab hOne) ⟨a,hab⟩
      (star.right (pairing original fd hc hab hOne star))) :=
  normalized_eq original fd hc hab hOne star hDiscrete ▸
    GeometricDatumIso.ofTargetIso (targetIso original fd hc hab hOne star) original

private theorem cast_iso_fields {firstTarget secondTarget : CFGraph} {d : ℕ}
    {first : GluingDatum firstTarget d} {middle last : GluingDatum secondTarget d}
    (h : middle = last) (iso : GeometricDatumIso first middle) :
    (h ▸ iso : GeometricDatumIso first last).targetVertex = iso.targetVertex ∧
    (h ▸ iso : GeometricDatumIso first last).targetEdge = iso.targetEdge ∧
    (h ▸ iso : GeometricDatumIso first last).vertexPerm = iso.vertexPerm ∧
    (h ▸ iso : GeometricDatumIso first last).edgePerm = iso.edgePerm := by
  cases h
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem datumIso_targetVertex :
    (datumIso original fd hc hab hOne star hDiscrete).targetVertex =
      (targetIso original fd hc hab hOne star).vertexEquiv :=
  (cast_iso_fields (normalized_eq original fd hc hab hOne star hDiscrete) _).1

theorem datumIso_targetEdge :
    (datumIso original fd hc hab hOne star hDiscrete).targetEdge =
      GluingTransport.edgeEquiv (targetIso original fd hc hab hOne star) :=
  (cast_iso_fields (normalized_eq original fd hc hab hOne star hDiscrete) _).2.1

theorem datumIso_vertexPerm (vertex : target.V) :
    (datumIso original fd hc hab hOne star hDiscrete).vertexPerm vertex = Equiv.refl (Fin degree) :=
  congrFun (cast_iso_fields (normalized_eq original fd hc hab hOne star hDiscrete) _).2.2.1 vertex

theorem datumIso_edgePerm (edge : target.edges) :
    (datumIso original fd hc hab hOne star hDiscrete).edgePerm edge = Equiv.refl (Fin degree) :=
  congrFun (cast_iso_fields (normalized_eq original fd hc hab hOne star hDiscrete) _).2.2.2 edge

theorem datumIso_occurrence (column : Option (contract target hab hOne).edges) :
    (datumIso original fd hc hab hOne star hDiscrete).targetEdge
        (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract target hab hOne) ⟨a,hab⟩
        (star.right (pairing original fd hc hab hOne star)) column := by
  rw [datumIso_targetEdge]
  exact targetIso_occurrence original fd hc hab hOne star column

/-- Every retained source occurrence, including its stored sheet, is
preserved by the normalization isomorphism. -/
theorem retainedSourceEdge_datumIso
    (edge : (contractDatum original hc hab hOne).SourceEdge) :
    (datumIso original fd hc hab hOne star hDiscrete).sourceEdgeEquiv
        (WallDegeneration.sourceEdgeEmbedding original hc hab hOne edge) =
      GeometricUniformExpansion.retainedSourceEdge (contractDatum original hc hab hOne) ⟨a,hab⟩
        (star.right (pairing original fd hc hab hOne star)) edge := by
  apply Subtype.ext
  change ((datumIso original fd hc hab hOne star hDiscrete).targetEdge
      (WallDegeneration.sourceEdgeEmbedding original hc hab hOne edge).1.1,
    (datumIso original fd hc hab hOne star hDiscrete).edgePerm
      (WallDegeneration.sourceEdgeEmbedding original hc hab hOne edge).1.1
      (WallDegeneration.sourceEdgeEmbedding original hc hab hOne edge).1.2) = _
  rw [IncomingNormalizationRows.sourceEdgeEmbedding_val]
  apply Prod.ext
  · exact datumIso_occurrence original fd hc hab hOne star hDiscrete (some edge.1.1)
  · rw [datumIso_edgePerm]
    rfl

/-- Normalizing the two expanded endpoints does not change the literal
contraction to the old target, including the endpoint-swap case. -/
theorem contractVertex_targetIso (vertex : target.V) :
    contractVertex (contract target hab hOne) ⟨a,hab⟩
        ((targetIso original fd hc hab hOne star).vertexEquiv vertex) =
      fold target hab vertex := by
  classical
  have hEndpoints := M11IncomingOuterPartitions.incomingIso_symm_endpoints hc hab hOne
    (star.right (pairing original fd hc hab hOne star))
    (pairing_placement original fd hc hab hOne star)
  have hFoldEndpoints :
      (fold target hab ((targetIso original fd hc hab hOne star).vertexEquiv.symm
        (oldVertex (contract target hab hOne) ⟨a,hab⟩)),
       fold target hab ((targetIso original fd hc hab hOne star).vertexEquiv.symm
        (freshVertex (contract target hab hOne)))) = (⟨a,hab⟩,⟨a,hab⟩) := by
    have h := congrArg (Prod.map (fold target hab) (fold target hab)) hEndpoints
    split_ifs at h <;>
      simpa only [Prod.map,fold_self,fold_of_ne target hab hab,
        W4IncomingTargetNormalization.targetIso] using h
  have hInverse : ∀ v : Vertex (contract target hab hOne),
      contractVertex (contract target hab hOne) ⟨a,hab⟩ v =
        fold target hab ((targetIso original fd hc hab hOne star).vertexEquiv.symm v) := by
    intro v
    cases v with
    | inl v =>
      by_cases h : v = ⟨a,hab⟩
      · subst v
        exact (congrArg Prod.fst hFoldEndpoints).symm
      · have hOld := M11IncomingOuterPartitions.incomingIso_symm_oldVertex hc hab hOne
          (star.right (pairing original fd hc hab hOne star))
          (pairing_placement original fd hc hab hOne star) v h
        change (targetIso original fd hc hab hOne star).vertexEquiv.symm
          (oldVertex (contract target hab hOne) v) = v.1 at hOld
        exact (fold_of_ne target hab v.property).symm.trans
          (congrArg (fold target hab) hOld).symm
    | inr v =>
      cases v
      exact (congrArg Prod.snd hFoldEndpoints).symm
  simpa only [Equiv.symm_apply_apply] using
    hInverse ((targetIso original fd hc hab hOne star).vertexEquiv vertex)

/-- Normalization preserves the actual source contraction as well. The
argument uses the quotient-source endpoint API, so it does not replace
stored representatives by an arbitrary sheet dictionary. -/
theorem contractSourceVertex_datumIso (vertex : original.SourceVertex) :
    sourceVertexMap original hc hab hOne vertex =
      GeometricUniformExpansion.contractSourceVertex (contractDatum original hc hab hOne) ⟨a,hab⟩
        (star.right (pairing original fd hc hab hOne star))
        ((datumIso original fd hc hab hOne star hDiscrete).sourceVertexEquiv vertex) := by
  apply ((contractDatum original hc hab hOne).sourceEndpoint_eq_iff _ _ _).mpr
  constructor
  · change fold target hab vertex.1.1 =
      contractVertex (contract target hab hOne) ⟨a,hab⟩
        ((datumIso original fd hc hab hOne star hDiscrete).targetVertex vertex.1.1)
    rw [datumIso_targetVertex]
    exact (contractVertex_targetIso original fd hc hab hOne star vertex.1.1).symm
  · change ((contractDatum original hc hab hOne).vertexPartition (fold target hab vertex.1.1)).Rel
      vertex.1.2 ((datumIso original fd hc hab hOne star hDiscrete).vertexPerm vertex.1.1 vertex.1.2)
    rw [datumIso_vertexPerm]
    rfl

end DraismaVargas.Count.DiscreteW4Normalization
