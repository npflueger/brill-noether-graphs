module

public import DraismaVargasCount.Star
public import DraismaVargasCount.GeometricValidityTransport

@[expose] public section

/-!
# Geometric contraction is functorial

An actual `GeometricDatumIso` induces an isomorphism after contracting a
corresponding target occurrence. Neither the contracted occurrence nor any
retained occurrence must preserve stored endpoint order. The vertex dictionary
is `fold ∘ targetVertex` on surviving representatives; its inverse uses the
opposite fold. The retained occurrence dictionary is inherited literally.

At the merged vertex, `WallStar.mergePerm` repairs the canonical
representative choice in a partition join. Canonical join commutativity handles
reversal of the contracted occurrence. All sheet compatibility follows from
the given geometric datum isomorphism; no extra receipt is assumed.

This module changes no fibre or star quotient. It reuses the sheet algebra
proved in `DraismaVargasCount.Star`, not that module's strict contraction isomorphism.
-/

namespace DraismaVargas.Count.GeometricContraction

open DraismaVargas.Infrastructure
open GluingContraction GraphContraction SheetPartition
open WallStar

section Vertices
variable {G H : CFGraph} {a b : G.V} {c d : H.V}
  (vertices : G.V ≃ H.V) (hab : a ≠ b) (hcd : c ≠ d)
  (ends : UnorderedEnds vertices (a,b) (c,d))

include ends

theorem fold_images_endpoints :
    fold H hcd (vertices a) = fold H hcd (vertices b) := by
  rcases ends with h | h
  · have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    dsimp only at ha hb
    rw [← ha, ← hb, fold_a, fold_self]
  · have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    dsimp only at ha hb
    rw [← hb, ← ha, fold_self, fold_a]

theorem fold_map_fold (v : G.V) :
    fold H hcd (vertices (fold G hab v).1) = fold H hcd (vertices v) := by
  by_cases hv : v = b
  · subst v
    rw [fold_self]
    exact fold_images_endpoints vertices hcd ends
  · rw [fold_of_ne G hab hv]

def foldEquiv : Vertex G b ≃ Vertex H d where
  toFun x := fold H hcd (vertices x.1)
  invFun y := fold G hab (vertices.symm y.1)
  left_inv x := by
    dsimp only
    rw [fold_map_fold vertices.symm hcd hab ends.symm]
    simp only [Equiv.symm_apply_apply, fold_coe]
  right_inv y := by
    dsimp only
    rw [fold_map_fold vertices hab hcd ends]
    simp only [Equiv.apply_symm_apply, fold_coe]

theorem foldEquiv_fold (v : G.V) :
    foldEquiv vertices hab hcd ends (fold G hab v) =
      fold H hcd (vertices v) :=
  fold_map_fold vertices hab hcd ends v

theorem foldEquiv_merged :
    (foldEquiv vertices hab hcd ends ⟨a,hab⟩).1 = c := by
  change (fold H hcd (vertices a)).1 = c
  rcases ends with h | h
  · have ha := congrArg Prod.fst h
    dsimp only at ha
    rw [← ha, fold_a]
  · have ha := congrArg Prod.snd h
    dsimp only at ha
    rw [← ha, fold_self]

theorem foldEquiv_of_ne (x : Vertex G b) (hx : x.1 ≠ a) :
    (foldEquiv vertices hab hcd ends x).1 = vertices x.1 := by
  have hne : vertices x.1 ≠ d := by
    rcases ends with h | h
    · have hb := congrArg Prod.snd h
      dsimp only at hb
      rw [hb]
      exact fun h ↦ x.2 (vertices.injective h)
    · have hb := congrArg Prod.snd h
      dsimp only at hb
      rw [hb]
      exact fun h ↦ hx (vertices.injective h)
  exact congrArg Subtype.val (fold_of_ne H hcd hne)

theorem foldEquiv_ne_merged (x : Vertex G b) (hx : x.1 ≠ a) :
    (foldEquiv vertices hab hcd ends x).1 ≠ c := by
  intro h
  have heq : foldEquiv vertices hab hcd ends x =
      foldEquiv vertices hab hcd ends ⟨a,hab⟩ :=
    Subtype.ext (h.trans (foldEquiv_merged vertices hab hcd ends).symm)
  exact hx (congrArg Subtype.val ((foldEquiv vertices hab hcd ends).injective heq))
end Vertices

theorem join_comm (Pa Pb : SheetPartition degree) : join Pa Pb = join Pb Pa := by
  apply SheetPartition.ext_repr
  funext i
  have hclasses : joinClass Pa Pb i = joinClass Pb Pa i := by
    ext j
    rw [mem_joinClass, mem_joinClass, ← join_rel_iff, ← join_rel_iff]
    exact join_rel_comm Pa Pb i j
  simp only [join_repr, joinRepr, hclasses]

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

def contractVertexEquiv (iso : GeometricDatumIso first second) (e₁ : target₁.edges) :
    Vertex target₁ ((e₁ : target₁.V × target₁.V)).2 ≃
      Vertex target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 :=
  foldEquiv iso.targetVertex (fst_ne_snd e₁) (fst_ne_snd (iso.targetEdge e₁)) (iso.ends e₁)

theorem contractVertexEquiv_fold (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (v : target₁.V) :
    contractVertexEquiv iso e₁ (fold target₁ (fst_ne_snd e₁) v)
      = fold target₂ (fst_ne_snd (iso.targetEdge e₁)) (iso.targetVertex v) :=
  foldEquiv_fold _ _ _ _ v

noncomputable def contractEdgeEquiv (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (hOne₂ : num_edges target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
      ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 = 1) :
    (contractTarget e₁ hOne₁).edges ≃ (contractTarget (iso.targetEdge e₁) hOne₂).edges :=
  (foldEdgeEquiv rfl (fst_ne_snd e₁) hOne₁).symm.trans
    ((Equiv.subtypeEquiv iso.targetEdge (fun f ↦ by
        simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq])).trans
      (foldEdgeEquiv rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂))

theorem unfoldEdge_contractEdgeEquiv (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (hOne₂ : num_edges target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
      ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 = 1)
    (ê : (contractTarget e₁ hOne₁).edges) :
    unfoldEdge rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂
        (contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê)
      = iso.targetEdge (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) := by
  show ((foldEdgeEquiv rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂).symm
      ((foldEdgeEquiv rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂)
        ((Equiv.subtypeEquiv iso.targetEdge _)
          ((foldEdgeEquiv rfl (fst_ne_snd e₁) hOne₁).symm ê)))).1 = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem contractVertexPartition_of_eq {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (a b : target.V)
    {y : Vertex target b} (h : (y : target.V) = a) :
    contractVertexPartition data a b y
      = join (data.vertexPartition a) (data.vertexPartition b) := ite_eq_left h

/-- The two endpoint sheet permutations of a `GeometricDatumIso` agree modulo the join
of the endpoint partitions of the occurrence, downstairs. -/
theorem joinRel_vertexPerm_symm (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (u : Fin degree) :
    JoinRel (first.vertexPartition ((e₁ : target₁.V × target₁.V)).1)
      (first.vertexPartition ((e₁ : target₁.V × target₁.V)).2)
      ((iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1).symm u)
      ((iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2).symm u) := by
  have h1 := iso.compatible e₁ _ (Or.inl rfl) ((iso.edgePerm e₁).symm u)
  have h2 := iso.compatible e₁ _ (Or.inr rfl) ((iso.edgePerm e₁).symm u)
  rw [Equiv.apply_symm_apply] at h1 h2
  exact (joinRel_of_left h1).trans (joinRel_of_right h2).symm

/-- and upstairs. -/
theorem joinRel_vertexPerm (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (x : Fin degree) :
    JoinRel
      ((first.vertexPartition ((e₁ : target₁.V × target₁.V)).1).relabel
        (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1))
      ((first.vertexPartition ((e₁ : target₁.V × target₁.V)).2).relabel
        (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2))
      (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1 x)
      (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2 x) := by
  have k1 := ((first.vertexPartition ((e₁ : target₁.V × target₁.V)).1).relabel_rel_iff
    (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1)
    ((iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1).symm (iso.edgePerm e₁ x)) x).mpr
      (iso.compatible e₁ _ (Or.inl rfl) x)
  have k2 := ((first.vertexPartition ((e₁ : target₁.V × target₁.V)).2).relabel_rel_iff
    (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2)
    ((iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2).symm (iso.edgePerm e₁ x)) x).mpr
      (iso.compatible e₁ _ (Or.inr rfl) x)
  rw [Equiv.apply_symm_apply] at k1 k2
  exact (joinRel_of_left k1).symm.trans (joinRel_of_right k2)

/-- The sheet permutation the contracted datum carries at the merged vertex. -/
noncomputable def mergedPerm (iso : GeometricDatumIso first second) (e₁ : target₁.edges) :
    Equiv.Perm (Fin degree) :=
  mergePerm (joinRel_vertexPerm iso e₁) (joinRel_vertexPerm_symm iso e₁)

/-- The sheet permutations of the contracted datum. -/
noncomputable def contractVertexPerm (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : Equiv.Perm (Fin degree) :=
  if (x : target₁.V) = ((e₁ : target₁.V × target₁.V)).1 then mergedPerm iso e₁
  else iso.vertexPerm (x : target₁.V)

theorem contractVertexPerm_merged (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    {x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2}
    (hx : (x : target₁.V) = ((e₁ : target₁.V × target₁.V)).1) :
    contractVertexPerm iso e₁ x = mergedPerm iso e₁ := ite_eq_left hx

theorem contractVertexPerm_of_ne (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    {x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2}
    (hx : (x : target₁.V) ≠ ((e₁ : target₁.V × target₁.V)).1) :
    contractVertexPerm iso e₁ x = iso.vertexPerm (x : target₁.V) := ite_eq_right hx

theorem contractGeometricDatumIso_compatible_fst (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (ê : (contractTarget e₁ hOne₁).edges) (s : Fin degree) :
    (contractVertexPartition first ((e₁ : target₁.V × target₁.V)).1
        ((e₁ : target₁.V × target₁.V)).2
        ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).1).Rel
      ((contractVertexPerm iso e₁
          ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).1).symm
        (iso.edgePerm (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) s)) s := by
  have hfst : ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).1
      = fold target₁ (fst_ne_snd e₁)
        ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 :=
    (congrArg Prod.fst (fold_unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê)).symm
  rw [hfst]
  by_cases hv : ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1
      = ((e₁ : target₁.V × target₁.V)).2
  · have hfold : ((fold target₁ (fst_ne_snd e₁)
          ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 :
        Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
        = ((e₁ : target₁.V × target₁.V)).1 := by
      rw [hv, fold_self]
    rw [contractVertexPartition_of_eq _ _ _ hfold, contractVertexPerm_merged iso e₁ hfold,
      mergedPerm]
    refine merged_rel_mergePerm_symm (joinRel_vertexPerm iso e₁)
      (joinRel_vertexPerm_symm iso e₁) (Or.inr ?_)
    have hc := iso.compatible (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) _ (Or.inl rfl) s
    rw [hv] at hc
    exact (join_rel_iff _ _ _ _).mpr (joinRel_of_right hc)
  · have hfoldval : ((fold target₁ (fst_ne_snd e₁)
          ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 :
        Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
        = ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 := by
      rw [fold_of_ne _ _ hv]
    by_cases hva : ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1
        = ((e₁ : target₁.V × target₁.V)).1
    · have hfold := hfoldval.trans hva
      rw [contractVertexPartition_of_eq _ _ _ hfold, contractVertexPerm_merged iso e₁ hfold,
        mergedPerm]
      refine merged_rel_mergePerm_symm (joinRel_vertexPerm iso e₁)
        (joinRel_vertexPerm_symm iso e₁) (Or.inl ?_)
      have hc := iso.compatible (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) _ (Or.inl rfl) s
      rw [hva] at hc
      exact (join_rel_iff _ _ _ _).mpr (joinRel_of_left hc)
    · have hne : ((fold target₁ (fst_ne_snd e₁)
            ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 :
          Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
          ≠ ((e₁ : target₁.V × target₁.V)).1 := by
        rw [hfoldval]; exact hva
      rw [contractVertexPartition_of_ne _ _ _ hne, contractVertexPerm_of_ne iso e₁ hne,
        hfoldval]
      exact iso.compatible _ _ (Or.inl rfl) s

theorem contractGeometricDatumIso_compatible_snd (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (ê : (contractTarget e₁ hOne₁).edges) (s : Fin degree) :
    (contractVertexPartition first ((e₁ : target₁.V × target₁.V)).1
        ((e₁ : target₁.V × target₁.V)).2
        ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).2).Rel
      ((contractVertexPerm iso e₁
          ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).2).symm
        (iso.edgePerm (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) s)) s := by
  have hsnd : ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).2
      = fold target₁ (fst_ne_snd e₁)
        ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 :=
    (congrArg Prod.snd (fold_unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê)).symm
  rw [hsnd]
  by_cases hv : ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2
      = ((e₁ : target₁.V × target₁.V)).2
  · have hfold : ((fold target₁ (fst_ne_snd e₁)
          ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 :
        Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
        = ((e₁ : target₁.V × target₁.V)).1 := by
      rw [hv, fold_self]
    rw [contractVertexPartition_of_eq _ _ _ hfold, contractVertexPerm_merged iso e₁ hfold,
      mergedPerm]
    refine merged_rel_mergePerm_symm (joinRel_vertexPerm iso e₁)
      (joinRel_vertexPerm_symm iso e₁) (Or.inr ?_)
    have hc := iso.compatible (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) _ (Or.inr rfl) s
    rw [hv] at hc
    exact (join_rel_iff _ _ _ _).mpr (joinRel_of_right hc)
  · have hfoldval : ((fold target₁ (fst_ne_snd e₁)
          ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 :
        Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
        = ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 := by
      rw [fold_of_ne _ _ hv]
    by_cases hva : ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2
        = ((e₁ : target₁.V × target₁.V)).1
    · have hfold := hfoldval.trans hva
      rw [contractVertexPartition_of_eq _ _ _ hfold, contractVertexPerm_merged iso e₁ hfold,
        mergedPerm]
      refine merged_rel_mergePerm_symm (joinRel_vertexPerm iso e₁)
        (joinRel_vertexPerm_symm iso e₁) (Or.inl ?_)
      have hc := iso.compatible (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) _ (Or.inr rfl) s
      rw [hva] at hc
      exact (join_rel_iff _ _ _ _).mpr (joinRel_of_left hc)
    · have hne : ((fold target₁ (fst_ne_snd e₁)
            ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 :
          Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
          ≠ ((e₁ : target₁.V × target₁.V)).1 := by
        rw [hfoldval]; exact hva
      rw [contractVertexPartition_of_ne _ _ _ hne, contractVertexPerm_of_ne iso e₁ hne,
        hfoldval]
      exact iso.compatible _ _ (Or.inr rfl) s

theorem contractDatumIso_vertexPartition (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) :
    contractVertexPartition second ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
        ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 (contractVertexEquiv iso e₁ x)
      = (contractVertexPartition first ((e₁ : target₁.V × target₁.V)).1
          ((e₁ : target₁.V × target₁.V)).2 x).relabel (contractVertexPerm iso e₁ x) := by
  by_cases hx : (x : target₁.V) = ((e₁ : target₁.V × target₁.V)).1
  · have hx2 : (contractVertexEquiv iso e₁ x).1 =
        ((iso.targetEdge e₁ : target₂.V × target₂.V)).1 := by
      have heq : x = ⟨_, fst_ne_snd e₁⟩ := Subtype.ext hx
      rw [heq]
      exact foldEquiv_merged _ _ _ _
    rw [contractVertexPartition_of_eq _ _ _ hx2, contractVertexPartition_of_eq _ _ _ hx,
      contractVertexPerm_merged iso e₁ hx, mergedPerm, relabel_mergePerm]
    rcases iso.ends e₁ with h | h
    · rw [show (iso.targetEdge e₁ : target₂.V × target₂.V) = _ from h]
      rw [iso.vertexPartition, iso.vertexPartition]
    · rw [show (iso.targetEdge e₁ : target₂.V × target₂.V) = _ from h]
      rw [iso.vertexPartition, iso.vertexPartition, join_comm]
  · have hx2 : (contractVertexEquiv iso e₁ x).1 ≠
        ((iso.targetEdge e₁ : target₂.V × target₂.V)).1 :=
      foldEquiv_ne_merged _ _ _ _ x hx
    have hval : (contractVertexEquiv iso e₁ x).1 = iso.targetVertex x.1 :=
      foldEquiv_of_ne _ _ _ _ x hx
    rw [contractVertexPartition_of_ne _ _ _ hx2, contractVertexPartition_of_ne _ _ _ hx,
      contractVertexPerm_of_ne iso e₁ hx, hval]
    exact iso.vertexPartition _

theorem contractEdgeEquiv_ends (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (hOne₂ : num_edges target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
      ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 = 1)
    (ê : (contractTarget e₁ hOne₁).edges) :
    UnorderedEnds (contractVertexEquiv iso e₁)
      (ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)
      (contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê :
        (contractTarget (iso.targetEdge e₁) hOne₂).V ×
        (contractTarget (iso.targetEdge e₁) hOne₂).V) := by
  have hf := fold_unfoldEdge (contracted := e₁) rfl (fst_ne_snd e₁) hOne₁ ê
  have hg := fold_unfoldEdge (contracted := iso.targetEdge e₁) rfl
    (fst_ne_snd (iso.targetEdge e₁)) hOne₂ (contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê)
  rw [unfoldEdge_contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê] at hg
  unfold UnorderedEnds
  rw [← hf, ← hg]
  dsimp only
  rw [contractVertexEquiv_fold, contractVertexEquiv_fold]
  rcases iso.ends (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) with h | h
  · rw [h]
    exact Or.inl rfl
  · rw [h]
    exact Or.inr rfl

/-- Contraction follows an actual geometric datum isomorphism, whether the
contracted occurrence preserves or reverses its stored orientation. -/
noncomputable def contractDatumIso (iso : GeometricDatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (hOne₂ : num_edges target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
      ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 = 1) :
    GeometricDatumIso (contractDatumAt first e₁ hOne₁)
      (contractDatumAt second (iso.targetEdge e₁) hOne₂) where
  targetVertex := contractVertexEquiv iso e₁
  targetEdge := contractEdgeEquiv iso e₁ hOne₁ hOne₂
  ends := contractEdgeEquiv_ends iso e₁ hOne₁ hOne₂
  vertexPerm := contractVertexPerm iso e₁
  edgePerm ê := iso.edgePerm (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê)
  vertexPartition := contractDatumIso_vertexPartition iso e₁
  edgePartition ê := by
    show second.edgePartition (unfoldEdge rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂
        (contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê))
      = (first.edgePartition (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê)).relabel _
    rw [unfoldEdge_contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê]
    exact iso.edgePartition _
  compatible edge vertex hv sheet := by
    rcases hv with h | h
    · subst vertex
      exact contractGeometricDatumIso_compatible_fst iso e₁ hOne₁ edge sheet
    · subst vertex
      exact contractGeometricDatumIso_compatible_snd iso e₁ hOne₁ edge sheet

/-- The contractibility receipt itself transports without an orientation choice. -/
theorem numEdges_targetEdge (iso : GeometricDatumIso first second) (e₁ : target₁.edges) :
    num_edges target₂ (iso.targetEdge e₁ : target₂.V × target₂.V).1
      (iso.targetEdge e₁ : target₂.V × target₂.V).2 =
    num_edges target₁ (e₁ : target₁.V × target₁.V).1
      (e₁ : target₁.V × target₁.V).2 := by
  rcases iso.ends e₁ with h | h
  · rw [h]
    exact iso.targetNumEdges_map _ _
  · rw [h]
    exact (iso.targetNumEdges_map _ _).trans (num_edges_symmetric _ _ _)

/-- The contraction constructor needs only the original contractibility receipt. -/
noncomputable def contractDatumIsoOfOne (iso : GeometricDatumIso first second)
    (e₁ : target₁.edges)
    (hOne : num_edges target₁ (e₁ : target₁.V × target₁.V).1
      (e₁ : target₁.V × target₁.V).2 = 1) :
    GeometricDatumIso (contractDatumAt first e₁ hOne)
      (contractDatumAt second (iso.targetEdge e₁) ((numEdges_targetEdge iso e₁).trans hOne)) :=
  contractDatumIso iso e₁ hOne _

end DraismaVargas.Count.GeometricContraction

