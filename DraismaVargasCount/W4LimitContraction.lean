module

public import DraismaVargasCount.GeometricTransport
public import DraismaVargas.Infrastructure.GluingContraction
public import DraismaVargas.Infrastructure.SheetJoin
public import DraismaVargas.Infrastructure.TargetExpansion

@[expose] public section

/-!
# Contracting the regrown occurrence of a target expansion

Source: Draisma–Vargas Part I, the definition of the limit of a gluing datum at a
target edge (`def-limit-gluing`), and the regrowing of a wall vertex to an edge
(section "Constructions", subsection "Trees contracting to `T₀`").

## What is proved

Let `expanded` be a gluing datum on the one-vertex expansion
`TargetExpansion.graph target wall right` of a target, and contract its new
occurrence. If

* the two expanded copies of the wall carry partitions whose join is the
  wall partition of `base` (`hMerge`),
* every other old vertex carries the partition `base` gives it (`hOld`), and
* every retained occurrence carries the partition `base` gives it (`hEdge`),

then the contraction is isomorphic to `base` as a geometric gluing datum
(`limitIso`), by an isomorphism whose sheet permutations are all the identity
(`limitIso_vertexPerm`, `limitIso_edgePerm`) and whose dictionaries are the
literal contraction dictionaries (`limitIso_targetVertex`, `limitIso_targetEdge`,
described by `vertexEquiv_fold` and `occurrenceEquiv_edgeEquiv`).  On sources, the
limit dictionary undoes the literal expansion (`sourceVertexEquiv_sourceVertexMap`,
`sourceVertexEquiv_sourceEndpoint`, `sourceEdgeEquiv_val`).

Nothing is assumed about how `expanded` was assembled: the three displayed
conditions are exactly the local resolution data a W4 candidate supplies. The
occurrence contracted is named by an arbitrary `contracted` together with the
proof `hcontract` that it is the canonical new occurrence, so the statement
applies verbatim to `WallStar.Regrowth.limit`, whose contracted occurrence is
`Frame.edgeOf` and only propositionally the canonical one.

## What is NOT proved

Beyond the computation of the induced source dictionaries above, the source-vertex
and source-occurrence dictionaries are not compared here with any other dictionary;
in particular nothing is said about branch vertices, stable rows, or inherited
core labels. Validity of either datum is neither used nor concluded.

## Consumers

`W4WallExhaustion.candDatumIso` (the canonical limit dictionary of a W4 candidate) and
`W4StarParity.limitIso` (the limit of a member of a W4 wall's family is the wall
datum), both of which describe the star of a W4 wall.
-/

namespace DraismaVargas.Count.W4LimitContraction

open DraismaVargas.Infrastructure
open TargetExpansion GraphContraction GluingContraction

variable {target : CFGraph} {degree : ℕ} {wall : target.V} {right : target.edges → Bool}

/-- Occurrences of the target are the expanded occurrences other than the new
one. -/
noncomputable def survivingEquiv {contracted : (graph target wall right).edges}
    (hcontract : contracted = occurrenceEquiv target wall right none) :
    target.edges ≃ {f : (graph target wall right).edges // f ≠ contracted} where
  toFun edge := ⟨occurrenceEquiv target wall right (some edge), by
    rw [hcontract]
    exact fun h ↦ Option.some_ne_none edge ((occurrenceEquiv target wall right).injective h)⟩
  invFun f := ((occurrenceEquiv target wall right).symm f.1).get (by
    rw [Option.isSome_iff_ne_none]
    intro h
    refine f.2 (Eq.trans ?_ hcontract.symm)
    exact ((occurrenceEquiv target wall right).apply_symm_apply f.1).symm.trans
      (congrArg (occurrenceEquiv target wall right) h))
  left_inv edge := by
    simp only [Equiv.symm_apply_apply]
    rfl
  right_inv f := by
    apply Subtype.ext
    exact congrArg (occurrenceEquiv target wall right)
      (Option.some_get _) |>.trans ((occurrenceEquiv target wall right).apply_symm_apply f.1)

@[simp] theorem survivingEquiv_apply {contracted : (graph target wall right).edges}
    (hcontract : contracted = occurrenceEquiv target wall right none) (edge : target.edges) :
    (survivingEquiv hcontract edge).1 = occurrenceEquiv target wall right (some edge) := rfl

section Contraction

variable {a b : (graph target wall right).V} {contracted : (graph target wall right).edges}
  (hc : (contracted : (graph target wall right).V × (graph target wall right).V) = (a, b))
  (hab : a ≠ b) (hOne : num_edges (graph target wall right) a b = 1)
  (hcontract : contracted = occurrenceEquiv target wall right none)

include hc hcontract in
theorem fst_eq : a = oldVertex target wall := by
  have h : ((contracted : (graph target wall right).V × (graph target wall right).V)) =
      newEnds target wall := by
    rw [hcontract]
    exact occurrenceEquiv_none target wall right
  exact (congrArg Prod.fst (hc.symm.trans h))

include hc hcontract in
theorem snd_eq : b = freshVertex target := by
  have h : ((contracted : (graph target wall right).V × (graph target wall right).V)) =
      newEnds target wall := by
    rw [hcontract]
    exact occurrenceEquiv_none target wall right
  exact (congrArg Prod.snd (hc.symm.trans h))

/-- The contracted expanded target is the original target. -/
noncomputable def vertexEquiv :
    (contract (graph target wall right) hab hOne).V ≃ target.V where
  toFun vertex := contractVertex target wall vertex.1
  invFun vertex := ⟨oldVertex target vertex, by
    rw [snd_eq hc hcontract]
    exact Sum.inl_ne_inr⟩
  left_inv := by
    rintro ⟨vertex, hv⟩
    apply Subtype.ext
    cases vertex with
    | inl u => rfl
    | inr u =>
        cases u
        exact absurd (snd_eq hc hcontract).symm hv
  right_inv _ := rfl

@[simp] theorem vertexEquiv_apply (vertex : (contract (graph target wall right) hab hOne).V) :
    vertexEquiv hc hab hOne hcontract vertex = contractVertex target wall vertex.1 := rfl

theorem vertexEquiv_fold (vertex : (graph target wall right).V) :
    vertexEquiv hc hab hOne hcontract (fold (graph target wall right) hab vertex) =
      contractVertex target wall vertex := by
  by_cases hv : vertex = b
  · rw [hv, fold_self]
    change contractVertex target wall a = contractVertex target wall b
    rw [fst_eq hc hcontract, snd_eq hc hcontract]
    rfl
  · rw [fold_of_ne _ hab hv]
    rfl

/-- The occurrences of the contracted expanded target are the occurrences of the
original target. -/
noncomputable def edgeEquiv :
    (contract (graph target wall right) hab hOne).edges ≃ target.edges :=
  (foldEdgeEquiv hc hab hOne).symm.trans (survivingEquiv hcontract).symm

theorem occurrenceEquiv_edgeEquiv (edge : (contract (graph target wall right) hab hOne).edges) :
    occurrenceEquiv target wall right (some (edgeEquiv hc hab hOne hcontract edge)) =
      unfoldEdge hc hab hOne edge := by
  change ((survivingEquiv hcontract) ((survivingEquiv hcontract).symm
    ((foldEdgeEquiv hc hab hOne).symm edge))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

variable (base : GluingDatum target degree) (expanded : GluingDatum (graph target wall right) degree)

theorem ends_edgeEquiv (edge : (contract (graph target wall right) hab hOne).edges) :
    ((edgeEquiv hc hab hOne hcontract edge : target.V × target.V)) =
      (vertexEquiv hc hab hOne hcontract
          (edge : (contract (graph target wall right) hab hOne).V ×
            (contract (graph target wall right) hab hOne).V).1,
        vertexEquiv hc hab hOne hcontract
          (edge : (contract (graph target wall right) hab hOne).V ×
            (contract (graph target wall right) hab hOne).V).2) := by
  have hfold := fold_unfoldEdge hc hab hOne edge
  have hocc : unfoldEdge hc hab hOne edge =
      occurrenceEquiv target wall right (some (edgeEquiv hc hab hOne hcontract edge)) :=
    (occurrenceEquiv_edgeEquiv hc hab hOne hcontract edge).symm
  have hends : ((unfoldEdge hc hab hOne edge :
        (graph target wall right).V × (graph target wall right).V)) =
      oldEnds target wall right (edgeEquiv hc hab hOne hcontract edge) := by
    rw [hocc]
    exact occurrenceEquiv_some target wall right _
  apply Prod.ext
  · rw [← congrArg Prod.fst hfold, vertexEquiv_fold, hends]
    exact (contract_expandedEndpoint target wall right _ _).symm
  · rw [← congrArg Prod.snd hfold, vertexEquiv_fold, hends]
    exact (contract_expandedEndpoint target wall right _ _).symm

theorem vertexPartition_eq
    (hMerge : SheetPartition.join (expanded.vertexPartition (oldVertex target wall))
      (expanded.vertexPartition (freshVertex target)) = base.vertexPartition wall)
    (hOld : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex)
    (vertex : (contract (graph target wall right) hab hOne).V) :
    base.vertexPartition (vertexEquiv hc hab hOne hcontract vertex) =
      (contractDatum expanded hc hab hOne).vertexPartition vertex := by
  rw [contractDatum_vertexPartition]
  by_cases hv : vertex.1 = a
  · have hvertex : vertex = ⟨a, hab⟩ := Subtype.ext hv
    rw [hvertex, contractVertexPartition_merge]
    change base.vertexPartition (contractVertex target wall a) = _
    rw [fst_eq hc hcontract, snd_eq hc hcontract]
    exact hMerge.symm
  · rw [contractVertexPartition_of_ne expanded a b (y := vertex) hv]
    have hvb : vertex.1 ≠ freshVertex target := by
      rw [← snd_eq hc hcontract]
      exact vertex.2
    rw [fst_eq hc hcontract] at hv
    obtain ⟨u, hu⟩ : ∃ u : target.V, vertex.1 = oldVertex target u := by
      rcases hvv : vertex.1 with u | u
      · exact ⟨u, rfl⟩
      · cases u
        exact absurd hvv hvb
    have hune : u ≠ wall := by
      intro hEq
      exact hv (hu.trans (congrArg (oldVertex target) hEq))
    rw [vertexEquiv_apply, hu, contract_oldVertex]
    exact (hOld u hune).symm

theorem edgePartition_eq
    (hEdge : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge)
    (edge : (contract (graph target wall right) hab hOne).edges) :
    base.edgePartition (edgeEquiv hc hab hOne hcontract edge) =
      (contractDatum expanded hc hab hOne).edgePartition edge := by
  rw [contractDatum_edgePartition, ← occurrenceEquiv_edgeEquiv hc hab hOne hcontract edge]
  exact (hEdge _).symm

/-- **The limit of a target expansion at its regrown occurrence is the base
datum.** The dictionaries are the literal contraction dictionaries and every
sheet permutation is the identity. -/
noncomputable def limitIso
    (hMerge : SheetPartition.join (expanded.vertexPartition (oldVertex target wall))
      (expanded.vertexPartition (freshVertex target)) = base.vertexPartition wall)
    (hOld : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex)
    (hEdge : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge) :
    GeometricDatumIso (contractDatum expanded hc hab hOne) base where
  targetVertex := vertexEquiv hc hab hOne hcontract
  targetEdge := edgeEquiv hc hab hOne hcontract
  ends edge := Or.inl (ends_edgeEquiv hc hab hOne hcontract edge)
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition vertex := by
    rw [Transport.DatumIso.relabel_refl]
    exact vertexPartition_eq hc hab hOne hcontract base expanded hMerge hOld vertex
  edgePartition edge := by
    rw [Transport.DatumIso.relabel_refl]
    exact edgePartition_eq hc hab hOne hcontract base expanded hEdge edge
  compatible _ _ _ _ := rfl

@[simp] theorem limitIso_targetVertex (hMerge hOld hEdge) :
    (limitIso hc hab hOne hcontract base expanded hMerge hOld hEdge).targetVertex =
      vertexEquiv hc hab hOne hcontract := rfl

@[simp] theorem limitIso_targetEdge (hMerge hOld hEdge) :
    (limitIso hc hab hOne hcontract base expanded hMerge hOld hEdge).targetEdge =
      edgeEquiv hc hab hOne hcontract := rfl

@[simp] theorem limitIso_vertexPerm (hMerge hOld hEdge)
    (vertex : (contract (graph target wall right) hab hOne).V) :
    (limitIso hc hab hOne hcontract base expanded hMerge hOld hEdge).vertexPerm vertex =
      Equiv.refl (Fin degree) := rfl

@[simp] theorem limitIso_edgePerm (hMerge hOld hEdge)
    (edge : (contract (graph target wall right) hab hOne).edges) :
    (limitIso hc hab hOne hcontract base expanded hMerge hOld hEdge).edgePerm edge =
      Equiv.refl (Fin degree) := rfl

/-! ### The induced source dictionary -/

theorem sourceVertexEquiv_sourceVertexMap
    (hMerge : SheetPartition.join (expanded.vertexPartition (oldVertex target wall))
      (expanded.vertexPartition (freshVertex target)) = base.vertexPartition wall)
    (hOld : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex)
    (hEdge : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge)
    (vertex : expanded.SourceVertex) :
    (limitIso hc hab hOne hcontract base expanded hMerge hOld hEdge).sourceVertexEquiv
        (sourceVertexMap expanded hc hab hOne vertex) =
      base.sourceEndpoint (contractVertex target wall vertex.1.1) vertex.1.2 := by
  apply Subtype.ext
  apply Prod.ext
  · exact vertexEquiv_fold hc hab hOne hcontract vertex.1.1
  · change (Equiv.refl (Fin degree))
      (((contractDatum expanded hc hab hOne).vertexPartition
        (fold (graph target wall right) hab vertex.1.1)).repr vertex.1.2) =
      (base.vertexPartition (contractVertex target wall vertex.1.1)).repr vertex.1.2
    have h := vertexPartition_eq hc hab hOne hcontract base expanded hMerge hOld
      (fold (graph target wall right) hab vertex.1.1)
    rw [vertexEquiv_fold] at h
    rw [← h]
    rfl

/-- **The limit dictionary undoes the literal expansion.** A source vertex of
the expansion over a chosen expanded vertex descends to the source vertex of
`base` it came from, provided its expanded partition refines the one `base`
carries. The sheet is normalized by `sourceEndpoint` on both sides. -/
theorem sourceVertexEquiv_sourceEndpoint
    (hMerge : SheetPartition.join (expanded.vertexPartition (oldVertex target wall))
      (expanded.vertexPartition (freshVertex target)) = base.vertexPartition wall)
    (hOld : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex)
    (hEdge : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge)
    (place : (graph target wall right).V) (vertex : target.V) (sheet : Fin degree)
    (hplace : contractVertex target wall place = vertex)
    (hrefines : (expanded.vertexPartition place).Refines (base.vertexPartition vertex)) :
    (limitIso hc hab hOne hcontract base expanded hMerge hOld hEdge).sourceVertexEquiv
        (sourceVertexMap expanded hc hab hOne (expanded.sourceEndpoint place sheet)) =
      base.sourceEndpoint vertex sheet := by
  rw [sourceVertexEquiv_sourceVertexMap hc hab hOne hcontract base expanded hMerge hOld hEdge]
  change base.sourceEndpoint (contractVertex target wall place)
    ((expanded.vertexPartition place).repr sheet) = _
  rw [hplace]
  apply (base.sourceEndpoint_eq_iff _ _ _).mpr
  refine ⟨rfl, ?_⟩
  change (base.vertexPartition vertex).repr ((expanded.vertexPartition place).repr sheet) =
    (base.vertexPartition vertex).repr ((base.vertexPartition vertex).repr sheet)
  rw [(base.vertexPartition vertex).repr_idem]
  exact hrefines.rel ((expanded.vertexPartition place).rel_repr_left sheet)

theorem sourceEdgeEquiv_val
    (hMerge : SheetPartition.join (expanded.vertexPartition (oldVertex target wall))
      (expanded.vertexPartition (freshVertex target)) = base.vertexPartition wall)
    (hOld : ∀ vertex : target.V, vertex ≠ wall →
      expanded.vertexPartition (oldVertex target vertex) = base.vertexPartition vertex)
    (hEdge : ∀ edge : target.edges,
      expanded.edgePartition (occurrenceEquiv target wall right (some edge)) =
        base.edgePartition edge)
    (edge : (contractDatum expanded hc hab hOne).SourceEdge) :
    ((limitIso hc hab hOne hcontract base expanded hMerge hOld hEdge).sourceEdgeEquiv edge).1 =
      (edgeEquiv hc hab hOne hcontract edge.1.1, edge.1.2) := rfl

end Contraction

/-- The discrete partition is its own join, so a wall with singleton sheet
blocks is recovered from two discrete expanded endpoints. -/
theorem join_discrete_discrete (d : ℕ) :
    SheetPartition.join (SheetPartition.discrete d) (SheetPartition.discrete d) =
      SheetPartition.discrete d := by
  have hRefines : (SheetPartition.join (SheetPartition.discrete d)
      (SheetPartition.discrete d)).Refines (SheetPartition.discrete d) :=
    SheetPartition.IsJoin.least (SheetPartition.isJoin_join _ _)
      (SheetPartition.Refines.refl _) (SheetPartition.Refines.refl _)
  apply SheetPartition.ext_repr
  funext sheet
  exact (SheetPartition.discrete_rel_iff _ _).mp
    (hRefines.rel ((SheetPartition.join (SheetPartition.discrete d)
      (SheetPartition.discrete d)).rel_repr_left sheet))

end DraismaVargas.Count.W4LimitContraction
