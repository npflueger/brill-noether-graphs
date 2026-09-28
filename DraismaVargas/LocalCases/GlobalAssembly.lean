import DraismaVargas.LocalCases.GlobalResolution
import DraismaVargas.LocalCases.ResolutionAssembly

/-!
# Global assembly of blockwise local resolutions

This module carries out the generic passage from independently chosen wall-block
receipts to an actual outgoing gluing datum. Exterior edge partitions are
checked against the selected local endpoint on each wall block. Those
block-local checks imply compatibility with the pasted endpoints, while the
block-restricted
Riemann--Hurwitz receipts assemble to the two full endpoint conditions.
-/

namespace DraismaVargas.LocalCases.GlobalAssembly

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.GlobalResolution

variable {target : CFGraph} {degree : ℕ}

/-- If every old wall occurrence refines the endpoint on each selected wall
block, then it refines the endpoint obtained by pasting those block choices. -/
theorem blockwiseCompatible (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor,
      (resolution anchor).ContractsTo (data.vertexPartition wall))
    (hExterior : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      ∀ anchor, (data.edgePartition edge).RefinesOnBlock
        (if right edge then (resolution anchor).right
          else (resolution anchor).left)
        (data.vertexPartition wall) anchor) :
    OldCompatible data wall right
      (LocalResolution.paste (data.vertexPartition wall) resolution
        hContracts) := by
  apply oldCompatible_of_wall
  intro edge hIncident
  cases hSide : right edge with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      intro first second hRelation
      change (LocalResolution.pasteLeft (data.vertexPartition wall)
        resolution hContracts).Rel first second
      apply ((data.vertexPartition wall).paste_rel_iff
        (fun anchor ↦ (resolution anchor).left)
        (fun anchor ↦ (hContracts anchor).left_refines) first second).mpr
      have hRefines : (data.edgePartition edge).RefinesOnBlock
          (resolution ((data.vertexPartition wall).repr first)).left
          (data.vertexPartition wall)
          ((data.vertexPartition wall).repr first) := by
        simpa [hSide] using
          (hExterior edge hIncident ((data.vertexPartition wall).repr first))
      exact hRefines.rel ((data.vertexPartition wall).rel_repr_left first)
        hRelation
  | true =>
      simp only [if_true]
      intro first second hRelation
      change (LocalResolution.pasteRight (data.vertexPartition wall)
        resolution hContracts).Rel first second
      apply ((data.vertexPartition wall).paste_rel_iff
        (fun anchor ↦ (resolution anchor).right)
        (fun anchor ↦ (hContracts anchor).right_refines) first second).mpr
      have hRefines : (data.edgePartition edge).RefinesOnBlock
          (resolution ((data.vertexPartition wall).repr first)).right
          (data.vertexPartition wall)
          ((data.vertexPartition wall).repr first) := by
        simpa [hSide] using
          (hExterior edge hIncident ((data.vertexPartition wall).repr first))
      exact hRefines.rel ((data.vertexPartition wall).rel_repr_left first)
        hRelation

/-- The occurrence-labelled outgoing datum assembled from one local resolution
choice on every wall block. -/
noncomputable def datum (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor,
      (resolution anchor).ContractsTo (data.vertexPartition wall))
    (hExterior : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      ∀ anchor, (data.edgePartition edge).RefinesOnBlock
        (if right edge then (resolution anchor).right
          else (resolution anchor).left)
        (data.vertexPartition wall) anchor) :
    GluingDatum (TargetExpansion.graph target wall right) degree :=
  GlobalResolution.datum data wall right
    (LocalResolution.paste (data.vertexPartition wall) resolution hContracts)
    (blockwiseCompatible data wall right resolution hContracts hExterior)

/-- Complete blockwise-to-global validity theorem. The named old occurrence
lists may follow the order of the source figure; their multiset equalities
identify the two sides of the expanded target. -/
theorem datum_valid (data : GluingDatum target degree)
    (wall : target.V) (right : target.edges → Bool)
    (resolution : Fin degree → LocalResolution degree)
    (hContracts : ∀ anchor,
      (resolution anchor).ContractsTo (data.vertexPartition wall))
    (hExterior : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      ∀ anchor, (data.edgePartition edge).RefinesOnBlock
        (if right edge then (resolution anchor).right
          else (resolution anchor).left)
        (data.vertexPartition wall) anchor)
    (hValid : data.Valid) (leftEdges rightEdges : List target.edges)
    (hLeftEdges : (leftEdges : Multiset target.edges) =
      (wallEdgesAssigned target wall right false).val)
    (hRightEdges : (rightEdges : Multiset target.edges) =
      (wallEdgesAssigned target wall right true).val)
    (hLeft : ∀ anchor,
      (data.vertexPartition wall).repr anchor = anchor →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution anchor).left
        ((resolution anchor).newEdge ::
          leftEdges.map data.edgePartition) anchor)
    (hRight : ∀ anchor,
      (data.vertexPartition wall).repr anchor = anchor →
      LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
        (resolution anchor).right
        ((resolution anchor).newEdge ::
          rightEdges.map data.edgePartition) anchor) :
    (datum data wall right resolution hContracts hExterior).Valid := by
  refine datum_valid_of_assignedOccurrences data wall right
    (LocalResolution.paste (data.vertexPartition wall) resolution hContracts)
    (blockwiseCompatible data wall right resolution hContracts hExterior)
    (LocalResolution.paste_contracts (data.vertexPartition wall)
      resolution hContracts) hValid leftEdges rightEdges hLeftEdges hRightEdges
      ?_ ?_
  · exact LocalResolution.paste_left_riemannHurwitzAt
      (data.vertexPartition wall) resolution hContracts
      (leftEdges.map data.edgePartition) hLeft
  · exact LocalResolution.paste_right_riemannHurwitzAt
      (data.vertexPartition wall) resolution hContracts
      (rightEdges.map data.edgePartition) hRight

end DraismaVargas.LocalCases.GlobalAssembly
