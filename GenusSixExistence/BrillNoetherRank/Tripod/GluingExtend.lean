module

public import GenusSixExistence.BrillNoetherRank.Tripod.GluingInjective

@[expose] public section

/-!
# Transporting a gluing along an isomorphism of members

The functoriality of the Cools--Draisma gluing (`glueDatum`) under isomorphisms of
gluing data, stage by stage. It is used for well-definedness of the gluing on classes
(`Research/genus-six-brill-noether-rank.md`, §5.5, The bijection):

* `refineIso`: `D ≅ D'` extends to `refineDatum D t ≅ refineDatum D' t'` for the image `t'` of
  `t` (the two halves of `t` go to the halves of `t'` at the corresponding ends);
* `extendIso`: to the new sheet, fixed;
* `leafIso`: to an arm, the tip permuted as its foot.

`glueIso` composes them, for the placement pushed forward along the isomorphism
(`pushPlacement`). With it, `isGluingOf_transport` moves a gluing of `ψ'` to a gluing of `ψ` along
`ψ ≅ ψ'`: the glued labels move with the old vertices, the marks, the arms and the new sheet, and
the clause `row` needs `GluingInjective.pieceLabel_eq`, because the first piece of an old edge
can go to its second piece.
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion
open GenusSixExistence.Tripod.Gadget

/-! ## Generic facts -/

section GenericMap

variable {S₁ S₂ : CFGraph} {k : ℕ} {E₁ : GluingDatum S₁ k} {E₂ : GluingDatum S₂ k}

theorem sourceEndpoint_map (iso : GeometricDatumIso E₁ E₂) (v : S₁.V) (i : Fin k) :
    iso.sourceVertexEquiv (E₁.sourceEndpoint v i) =
      E₂.sourceEndpoint (iso.targetVertex v) (iso.vertexPerm v i) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show iso.vertexPerm v ((E₁.vertexPartition v).repr i) =
    (E₂.vertexPartition (iso.targetVertex v)).repr (iso.vertexPerm v i)
  rw [iso.vertexPartition v]
  simp [SheetPartition.relabel]

theorem sourceEdge_map (iso : GeometricDatumIso E₁ E₂) (e : S₁.edges) (i : Fin k) :
    iso.sourceEdgeEquiv (E₁.sourceEdge e i) =
      E₂.sourceEdge (iso.targetEdge e) (iso.edgePerm e i) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show iso.edgePerm e ((E₁.edgePartition e).repr i) =
    (E₂.edgePartition (iso.targetEdge e)).repr (iso.edgePerm e i)
  rw [iso.edgePartition e]
  simp [SheetPartition.relabel]

theorem symm_trans_sourceVertexEquiv_symm {S₃ : CFGraph} {E₃ : GluingDatum S₃ k}
    (A : GeometricDatumIso E₁ E₂) (B : GeometricDatumIso E₁ E₃) (x : E₃.SourceVertex) :
    (A.symm.trans B).sourceVertexEquiv.symm x =
      A.sourceVertexEquiv (B.sourceVertexEquiv.symm x) := by
  rw [Equiv.symm_apply_eq]
  show x = B.sourceVertexEquiv (A.sourceVertexEquiv.symm
    (A.sourceVertexEquiv (B.sourceVertexEquiv.symm x)))
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem symm_sourceEdgeEquiv_apply (A : GeometricDatumIso E₁ E₂) (x : E₁.SourceEdge) :
    A.symm.sourceEdgeEquiv (A.sourceEdgeEquiv x) = x :=
  Equiv.symm_apply_apply A.sourceEdgeEquiv x

theorem pair_relabel {d : ℕ} (a b : Fin d) (σ : Equiv.Perm (Fin d)) :
    (SheetOps.pair a b).relabel σ = SheetOps.pair (σ a) (σ b) := by
  apply SheetPartition.ext_repr
  funext x
  show σ (if σ.symm x = b then a else σ.symm x) = if x = σ b then σ a else x
  by_cases h : x = σ b
  · rw [ite_eq_left h, ite_eq_left (by rw [h, Equiv.symm_apply_apply])]
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (by rw [← h', Equiv.apply_symm_apply])),
      Equiv.apply_symm_apply]

/-- **Extend a permutation by the new sheet.** -/
def extendPerm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Equiv.Perm (Fin (d + 1)) where
  toFun j := Fin.lastCases (Fin.last d) (fun i ↦ (σ i).castSucc) j
  invFun j := Fin.lastCases (Fin.last d) (fun i ↦ (σ.symm i).castSucc) j
  left_inv j := by induction j using Fin.lastCases <;> simp
  right_inv j := by induction j using Fin.lastCases <;> simp

@[simp] theorem extendPerm_last {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    extendPerm σ (Fin.last d) = Fin.last d := by simp [extendPerm]

@[simp] theorem extendPerm_castSucc {d : ℕ} (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    extendPerm σ i.castSucc = (σ i).castSucc := by simp [extendPerm]

@[simp] theorem extendPerm_symm_last {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (extendPerm σ).symm (Fin.last d) = Fin.last d := by
  rw [Equiv.symm_apply_eq, extendPerm_last]

@[simp] theorem extendPerm_symm_castSucc {d : ℕ} (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (extendPerm σ).symm i.castSucc = (σ.symm i).castSucc := by
  rw [Equiv.symm_apply_eq, extendPerm_castSucc, Equiv.apply_symm_apply]

theorem restrictPerm_extendPerm {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    restrictPerm (extendPerm σ) (extendPerm_last σ) = σ :=
  Equiv.ext fun i ↦ Fin.castSucc_injective _ (by
    rw [castSucc_restrictPerm, extendPerm_castSucc])

theorem extendNew_relabel_extendPerm {d : ℕ} (P : SheetPartition d) (σ : Equiv.Perm (Fin d)) :
    SheetOps.extendNew (P.relabel σ) = (SheetOps.extendNew P).relabel (extendPerm σ) := by
  rw [extendNew_relabel _ _ (extendPerm_last σ), restrictPerm_extendPerm]

end GenericMap

/-! ## Refining an isomorphism at an edge -/

section RefineIso

variable {T T' : CFGraph} {d : ℕ} {D : GluingDatum T d} {D' : GluingDatum T' d}
  (Θ : GeometricDatumIso D D') (t : T.edges)

/-- The old end of `T` at which an edge of the subdivision at `t` sits. -/
def endOf (t : T.edges) (ε : (subdivTarget T t).edges) : T.V :=
  Option.elim ((subdivOcc T t).symm ε) (t : T.V × T.V).2 fun e ↦ (e : T.V × T.V).1

theorem pieceT_of_ne {t e : T.edges} (h : e ≠ t) (w : T.V) :
    pieceT t w e = subdivOcc T t (some e) := by
  unfold pieceT
  rw [ite_eq_right (fun h' ↦ h h'.1)]

theorem pieceT_endOf (ε : (subdivTarget T t).edges) :
    pieceT t (endOf t ε) (parentT t ε) = ε := by
  obtain ⟨o, rfl⟩ := (subdivOcc T t).surjective ε
  cases o with
  | none =>
    rw [parentT_none]
    unfold pieceT endOf
    rw [Equiv.symm_apply_apply, ite_eq_left ⟨rfl, rfl⟩]
  | some e =>
    rw [parentT_some]
    unfold pieceT endOf
    rw [Equiv.symm_apply_apply]
    rw [ite_eq_right]
    rintro ⟨rfl, h⟩
    exact fst_ne_snd e h.symm

theorem endOf_mem (ε : (subdivTarget T t).edges) :
    parentT t ε ∈ GluingDatum.incidentEdges (endOf t ε) := by
  rw [mem_incidentEdges_iff]
  obtain ⟨o, rfl⟩ := (subdivOcc T t).surjective ε
  cases o with
  | none =>
    rw [parentT_none]
    unfold endOf
    rw [Equiv.symm_apply_apply]
    exact Or.inr rfl
  | some e =>
    rw [parentT_some]
    unfold endOf
    rw [Equiv.symm_apply_apply]
    exact Or.inl rfl

/-- The edge map of the refined isomorphism. -/
def refFwd (ε : (subdivTarget T t).edges) : (subdivTarget T' (Θ.targetEdge t)).edges :=
  pieceT (Θ.targetEdge t) (Θ.targetVertex (endOf t ε)) (Θ.targetEdge (parentT t ε))

theorem parentT_refFwd (ε : (subdivTarget T t).edges) :
    parentT (Θ.targetEdge t) (refFwd Θ t ε) = Θ.targetEdge (parentT t ε) :=
  parentT_pieceT _ _ _

/-- The orientation of `t` read through `Θ`. -/
theorem orient_iff {a b : T.V} (ha : (t : T.V × T.V).1 = a ∨ (t : T.V × T.V).2 = a)
    (hb : (t : T.V × T.V).1 = b ∨ (t : T.V × T.V).2 = b)
    (h : (Θ.targetEdge t : T'.V × T'.V).2 = Θ.targetVertex a ↔
      (Θ.targetEdge t : T'.V × T'.V).2 = Θ.targetVertex b) :
    ((t : T.V × T.V).2 = a ↔ (t : T.V × T.V).2 = b) := by
  have hne := fst_ne_snd t
  have hinj := Θ.targetVertex.injective
  rcases Θ.ends t with h' | h' <;> rw [h'] at h <;>
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp_all [hinj.eq_iff, Ne.symm hne]

theorem pieceT_self_eq_iff (a b : T.V) : pieceT t a t = pieceT t b t ↔
    ((t : T.V × T.V).2 = a ↔ (t : T.V × T.V).2 = b) := by
  unfold pieceT
  by_cases ha : (t : T.V × T.V).2 = a <;> by_cases hb : (t : T.V × T.V).2 = b <;>
    simp [ha, hb, (subdivOcc T t).injective.eq_iff]

/-- **The refined edge map at a piece.** -/
theorem refFwd_pieceT {w : T.V} {e : T.edges} (hw : e ∈ GluingDatum.incidentEdges w) :
    refFwd Θ t (pieceT t w e) = pieceT (Θ.targetEdge t) (Θ.targetVertex w) (Θ.targetEdge e) := by
  unfold refFwd
  rw [parentT_pieceT]
  by_cases het : e = t
  · subst het
    rw [mem_incidentEdges_iff] at hw
    congr 2
    unfold pieceT endOf
    by_cases h2 : (e : T.V × T.V).2 = w
    · rw [ite_eq_left ⟨rfl, h2⟩, Equiv.symm_apply_apply]
      exact h2
    · rw [ite_eq_right (fun h ↦ h2 h.2), Equiv.symm_apply_apply]
      exact hw.resolve_right h2
  · have hne : Θ.targetEdge e ≠ Θ.targetEdge t := Θ.targetEdge.injective.ne het
    rw [pieceT_of_ne hne, pieceT_of_ne hne]

theorem refFwd_injective : Function.Injective (refFwd Θ t) := by
  intro ε₁ ε₂ h
  have hp : parentT t ε₁ = parentT t ε₂ :=
    Θ.targetEdge.injective (by rw [← parentT_refFwd, ← parentT_refFwd, h])
  rw [← pieceT_endOf t ε₁, ← pieceT_endOf t ε₂] at h ⊢
  rw [refFwd_pieceT Θ t (endOf_mem t ε₁), refFwd_pieceT Θ t (endOf_mem t ε₂)] at h
  rw [hp] at h ⊢
  by_cases het : parentT t ε₂ = t
  · have h₁ := endOf_mem t ε₁
    have h₂ := endOf_mem t ε₂
    rw [hp, het, mem_incidentEdges_iff] at h₁
    rw [het, mem_incidentEdges_iff] at h₂
    rw [het] at h ⊢
    rw [pieceT_self_eq_iff] at h ⊢
    exact orient_iff Θ t h₁ h₂ h
  · rw [pieceT_of_ne het, pieceT_of_ne het]

theorem refFwd_bijective : Function.Bijective (refFwd Θ t) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨refFwd_injective Θ t, ?_⟩
  rw [← Fintype.card_congr (subdivOcc T t), ← Fintype.card_congr (subdivOcc T' _),
    Fintype.card_option, Fintype.card_option, Fintype.card_congr Θ.targetEdge]

/-- The target edges of the refined isomorphism. -/
def refEdgeEquiv : (subdivTarget T t).edges ≃ (subdivTarget T' (Θ.targetEdge t)).edges :=
  Equiv.ofBijective (refFwd Θ t) (refFwd_bijective Θ t)

/-- The target vertices of the refined isomorphism. -/
def refVertexEquiv : (subdivTarget T t).V ≃ (subdivTarget T' (Θ.targetEdge t)).V :=
  Equiv.sumCongr Θ.targetVertex (Equiv.refl Unit)

theorem refFwd_incident_iff (ε : (subdivTarget T t).edges) (v : (subdivTarget T t).V) :
    refFwd Θ t ε ∈ GluingDatum.incidentEdges (refVertexEquiv Θ t v) ↔
      ε ∈ GluingDatum.incidentEdges v := by
  rcases v with w | ⟨⟩
  · show refFwd Θ t ε ∈ GluingDatum.incidentEdges (subdivOld T' _ (Θ.targetVertex w)) ↔
      ε ∈ GluingDatum.incidentEdges (subdivOld T t w)
    rw [mem_incidentEdges_subdivOld, mem_incidentEdges_subdivOld, parentT_refFwd,
      iso_mem_incidentEdges_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, refFwd_injective Θ t ?_⟩
      rw [h2, refFwd_pieceT Θ t h1]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      conv_lhs => rw [h2]
      rw [refFwd_pieceT Θ t h1]
  · show refFwd Θ t ε ∈ GluingDatum.incidentEdges (subdivFresh T' _) ↔
      ε ∈ GluingDatum.incidentEdges (subdivFresh T t)
    rw [mem_incidentEdges_subdivFresh, mem_incidentEdges_subdivFresh, parentT_refFwd,
      Θ.targetEdge.injective.eq_iff]

/-- **The refined isomorphism** `refineDatum D t ≅ refineDatum D' t'`. -/
def refineIso : GeometricDatumIso (refineDatum D t) (refineDatum D' (Θ.targetEdge t)) where
  targetVertex := refVertexEquiv Θ t
  targetEdge := refEdgeEquiv Θ t
  ends ε := unorderedEnds_of_incident _ _ _ (fst_ne_snd ε) fun v ↦ by
    rw [← mem_incidentEdges_iff, ← mem_incidentEdges_iff]
    exact refFwd_incident_iff Θ t ε v
  vertexPerm := Sum.elim Θ.vertexPerm fun _ ↦ Θ.edgePerm t
  edgePerm ε := Θ.edgePerm (parentT t ε)
  vertexPartition v := by
    rcases v with w | ⟨⟩
    · exact Θ.vertexPartition w
    · exact Θ.edgePartition t
  edgePartition ε := by
    show (refineDatum D' (Θ.targetEdge t)).edgePartition (refFwd Θ t ε) = _
    rw [refineDatum_edgePartition, refineDatum_edgePartition, parentT_refFwd]
    exact Θ.edgePartition _
  compatible ε w hw i := by
    rcases w with v | ⟨⟩
    · have hv := ((mem_incidentEdges_subdivOld t v ε).mp ((mem_incidentEdges_iff _ _).mpr hw)).1
      exact Θ.compatible (parentT t ε) v ((mem_incidentEdges_iff _ _).mp hv) i
    · have ht := (mem_incidentEdges_subdivFresh t ε).mp ((mem_incidentEdges_iff _ _).mpr hw)
      show (D.edgePartition t).Rel ((Θ.edgePerm t).symm (Θ.edgePerm (parentT t ε) i)) i
      rw [ht, Equiv.symm_apply_apply]
      exact rfl

theorem refineIso_parentT (ε : (subdivTarget T t).edges) :
    parentT (Θ.targetEdge t) ((refineIso Θ t).targetEdge ε) = Θ.targetEdge (parentT t ε) :=
  parentT_refFwd Θ t ε

theorem refineIso_oldSV (x : D.SourceVertex) :
    (refineIso Θ t).sourceVertexEquiv (Refine.oldSV D t x) =
      Refine.oldSV D' (Θ.targetEdge t) (Θ.sourceVertexEquiv x) := rfl

theorem refineIso_parentSE (y : (refineDatum D t).SourceEdge) :
    Refine.parentSE D' (Θ.targetEdge t) ((refineIso Θ t).sourceEdgeEquiv y) =
      Θ.sourceEdgeEquiv (Refine.parentSE D t y) :=
  Subtype.ext (Prod.ext (refineIso_parentT Θ t y.1.1) rfl)

end RefineIso

/-! ## Extending an isomorphism by the new sheet, and by an arm -/

section ExtendLeafIso

variable {T T' : CFGraph} {d : ℕ} {D : GluingDatum T d} {D' : GluingDatum T' d}
  (Θ : GeometricDatumIso D D')

/-- **The isomorphism with the new sheet added**, the new sheet fixed. -/
def extendIso : GeometricDatumIso (extendDatum D) (extendDatum D') where
  targetVertex := Θ.targetVertex
  targetEdge := Θ.targetEdge
  ends := Θ.ends
  vertexPerm v := extendPerm (Θ.vertexPerm v)
  edgePerm e := extendPerm (Θ.edgePerm e)
  vertexPartition v := by
    show SheetOps.extendNew (D'.vertexPartition _) = _
    rw [Θ.vertexPartition, extendNew_relabel_extendPerm]
    rfl
  edgePartition e := by
    show SheetOps.extendNew (D'.edgePartition _) = _
    rw [Θ.edgePartition, extendNew_relabel_extendPerm]
    rfl
  compatible e v hv j := by
    show (SheetOps.extendNew (D.vertexPartition v)).Rel _ j
    induction j using Fin.lastCases with
    | last => rw [extendPerm_last, extendPerm_symm_last]; exact rfl
    | cast i =>
      rw [extendPerm_castSucc, extendPerm_symm_castSucc, extendNew_rel_castSucc_iff]
      exact ⟨i, rfl, Θ.compatible e v hv i⟩

/-- **The isomorphism with an arm attached** at `u` and at its image `u'`, the tip permuted as
`u`. -/
def leafIso (u : T.V) (u' : T'.V) (a b a' b' : Fin d) (hu : Θ.targetVertex u = u')
    (ha : Θ.vertexPerm u a = a') (hb : Θ.vertexPerm u b = b') :
    GeometricDatumIso (leafDatum D u a b) (leafDatum D' u' a' b') where
  targetVertex := Equiv.sumCongr Θ.targetVertex (Equiv.refl Unit)
  targetEdge := (leafOcc T u).symm.trans ((Equiv.optionCongr Θ.targetEdge).trans (leafOcc T' u'))
  ends ε := by
    obtain ⟨o, rfl⟩ := (leafOcc T u).surjective ε
    cases o with
    | none =>
      left
      show ((leafOcc T' u' (Option.map Θ.targetEdge ((leafOcc T u).symm (leafOcc T u none))) :
        (leafTarget T' u').edges) : (leafTarget T' u').V × (leafTarget T' u').V) = _
      rw [Equiv.symm_apply_apply, Option.map_none, leafOcc_none, leafOcc_none, ← hu]
      rfl
    | some e =>
      show UnorderedEnds _ _ ((leafOcc T' u' (Option.map Θ.targetEdge ((leafOcc T u).symm
        (leafOcc T u (some e)))) : (leafTarget T' u').edges) :
          (leafTarget T' u').V × (leafTarget T' u').V)
      rw [Equiv.symm_apply_apply, Option.map_some, leafOcc_some, leafOcc_some]
      rcases Θ.ends e with h | h
      · left; rw [h]; rfl
      · right; rw [h]; rfl
  vertexPerm := Sum.elim Θ.vertexPerm fun _ ↦ Θ.vertexPerm u
  edgePerm ε := Option.elim ((leafOcc T u).symm ε) (Θ.vertexPerm u) Θ.edgePerm
  vertexPartition v := by
    rcases v with w | ⟨⟩
    · exact Θ.vertexPartition w
    · show SheetOps.pair a' b' = (SheetOps.pair a b).relabel (Θ.vertexPerm u)
      rw [pair_relabel, ha, hb]
  edgePartition ε := by
    obtain ⟨o, rfl⟩ := (leafOcc T u).surjective ε
    cases o with
    | none =>
      show (leafDatum D' u' a' b').edgePartition (leafOcc T' u' (Option.map Θ.targetEdge
        ((leafOcc T u).symm (leafOcc T u none)))) = _
      rw [Equiv.symm_apply_apply, Option.map_none, leafDatum_edgePartition_none,
        leafDatum_edgePartition_none, SheetPartition.discrete_relabel]
    | some e =>
      show (leafDatum D' u' a' b').edgePartition (leafOcc T' u' (Option.map Θ.targetEdge
        ((leafOcc T u).symm (leafOcc T u (some e))))) = _
      rw [Equiv.symm_apply_apply, Option.map_some, leafDatum_edgePartition_some,
        leafDatum_edgePartition_some]
      simp only [Option.elim_some]
      exact Θ.edgePartition e
  compatible ε w hw i := by
    obtain ⟨o, rfl⟩ := (leafOcc T u).surjective ε
    cases o with
    | none =>
      rw [leafOcc_none] at hw
      simp only [Equiv.symm_apply_apply, Option.elim_none]
      rcases w with v | ⟨⟩
      · have hv : u = v := by
          rcases hw with h | h
          · exact leafOld_injective T u h
          · exact absurd h (by simp [leafTip])
        subst hv
        show (D.vertexPartition u).Rel ((Θ.vertexPerm u).symm (Θ.vertexPerm u i)) i
        rw [Equiv.symm_apply_apply]
        exact rfl
      · show (SheetOps.pair a b).Rel ((Θ.vertexPerm u).symm (Θ.vertexPerm u i)) i
        rw [Equiv.symm_apply_apply]
        exact rfl
    | some e =>
      rw [leafOcc_some] at hw
      simp only [Equiv.symm_apply_apply, Option.elim_some]
      rcases w with v | ⟨⟩
      · have hv : (e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v := by
          rcases hw with h | h
          · exact Or.inl (leafOld_injective T u h)
          · exact Or.inr (leafOld_injective T u h)
        exact Θ.compatible e v hv i
      · exfalso
        rcases hw with h | h <;> exact absurd h (by simp [leafOld])

theorem leafIso_targetEdge_some (u : T.V) (u' : T'.V) (a b a' b' : Fin d) (hu ha hb)
    (e : T.edges) :
    (leafIso Θ u u' a b a' b' hu ha hb).targetEdge (leafOcc T u (some e)) =
      leafOcc T' u' (some (Θ.targetEdge e)) := by
  show leafOcc T' u' (Option.map Θ.targetEdge ((leafOcc T u).symm (leafOcc T u (some e)))) = _
  rw [Equiv.symm_apply_apply, Option.map_some]

theorem leafIso_targetEdge_none (u : T.V) (u' : T'.V) (a b a' b' : Fin d) (hu ha hb) :
    (leafIso Θ u u' a b a' b' hu ha hb).targetEdge (leafOcc T u none) = leafOcc T' u' none := by
  show leafOcc T' u' (Option.map Θ.targetEdge ((leafOcc T u).symm (leafOcc T u none))) = _
  rw [Equiv.symm_apply_apply, Option.map_none]

theorem leafIso_edgePerm_some (u : T.V) (u' : T'.V) (a b a' b' : Fin d) (hu ha hb)
    (e : T.edges) :
    (leafIso Θ u u' a b a' b' hu ha hb).edgePerm (leafOcc T u (some e)) = Θ.edgePerm e := by
  show Option.elim ((leafOcc T u).symm (leafOcc T u (some e))) _ _ = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem leafIso_edgePerm_none (u : T.V) (u' : T'.V) (a b a' b' : Fin d) (hu ha hb) :
    (leafIso Θ u u' a b a' b' hu ha hb).edgePerm (leafOcc T u none) = Θ.vertexPerm u := by
  show Option.elim ((leafOcc T u).symm (leafOcc T u none)) _ _ = _
  rw [Equiv.symm_apply_apply]
  rfl

end ExtendLeafIso

/-! ## The glued isomorphism -/

section GlueIso

variable {T T' : CFGraph} {d : ℕ} {D : GluingDatum T d} {D' : GluingDatum T' d}
  (Θ : GeometricDatumIso D D') (π : Placement T d)

/-- `Θ`, refined at mark `0`. -/
def refIso₁ : GeometricDatumIso (refineDatum D π.edge₀) (refineDatum D' (Θ.targetEdge π.edge₀)) :=
  refineIso Θ π.edge₀

/-- `Θ`, refined at marks `0, 1`. -/
def refIso₂ := refineIso (refIso₁ Θ π) π.edge₁

/-- **The placement pushed forward along `Θ`.** -/
def pushPlacement : Placement T' d where
  edge₀ := Θ.targetEdge π.edge₀
  edge₁ := (refIso₁ Θ π).targetEdge π.edge₁
  edge₂ := (refIso₂ Θ π).targetEdge π.edge₂
  sheet k := Θ.edgePerm (π.parentEdge k) (π.sheet k)

/-- `Θ`, refined at the three marks. -/
def refIso₃ : GeometricDatumIso (refine₃ D π) (refine₃ D' (pushPlacement Θ π)) :=
  refineIso (refIso₂ Θ π) π.edge₂

theorem refIso₃_markVertex₃ (k : Fin 3) :
    (refIso₃ Θ π).targetVertex (π.markVertex₃ k) = (pushPlacement Θ π).markVertex₃ k := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem refIso₃_vertexPerm_markVertex₃ (k : Fin 3) :
    (refIso₃ Θ π).vertexPerm (π.markVertex₃ k) = Θ.edgePerm (π.parentEdge k) := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem pushPlacement_parentEdge (k : Fin 3) :
    (pushPlacement Θ π).parentEdge k = Θ.targetEdge (π.parentEdge k) := by
  match k with
  | 0 => rfl
  | 1 =>
    show parentT _ ((refIso₁ Θ π).targetEdge π.edge₁) = _
    exact refineIso_parentT Θ π.edge₀ π.edge₁
  | 2 =>
    show parentT _ (parentT _ ((refIso₂ Θ π).targetEdge π.edge₂)) = _
    rw [show parentT _ ((refIso₂ Θ π).targetEdge π.edge₂) =
        (refIso₁ Θ π).targetEdge (parentT π.edge₁ π.edge₂) from
      refineIso_parentT (refIso₁ Θ π) π.edge₁ π.edge₂]
    exact refineIso_parentT Θ π.edge₀ _

theorem extend_sheet (k : Fin 3) :
    (extendIso (refIso₃ Θ π)).vertexPerm (π.markVertex₃ k) (π.sheet k).castSucc =
      ((pushPlacement Θ π).sheet k).castSucc := by
  show extendPerm _ _ = _
  rw [extendPerm_castSucc, refIso₃_vertexPerm_markVertex₃]
  rfl

/-- Stage four of `glueIso`: the arm at mark `0`. -/
def glueIso₄ : GeometricDatumIso
    (leafDatum (extendDatum (refine₃ D π)) (π.markVertex₃ 0) (π.sheet 0).castSucc (Fin.last d))
    (leafDatum (extendDatum (refine₃ D' (pushPlacement Θ π))) ((pushPlacement Θ π).markVertex₃ 0)
      ((pushPlacement Θ π).sheet 0).castSucc (Fin.last d)) :=
  leafIso (extendIso (refIso₃ Θ π)) _ _ _ _ _ _ (refIso₃_markVertex₃ Θ π 0) (extend_sheet Θ π 0)
    (extendPerm_last _)

/-- Stage five: the arm at mark `1`. -/
def glueIso₅ := leafIso (glueIso₄ Θ π) (leafOld π.T₃ _ (π.markVertex₃ 1))
  (leafOld (pushPlacement Θ π).T₃ _ ((pushPlacement Θ π).markVertex₃ 1)) (π.sheet 1).castSucc
  (Fin.last d) ((pushPlacement Θ π).sheet 1).castSucc (Fin.last d)
  (congrArg Sum.inl (refIso₃_markVertex₃ Θ π 1)) (extend_sheet Θ π 1) (extendPerm_last _)

/-- **The glued isomorphism** `glue(D, π) ≅ glue(D', Θ π)`. -/
def glueIso : GeometricDatumIso (glueDatum D π) (glueDatum D' (pushPlacement Θ π)) :=
  leafIso (glueIso₅ Θ π) (leafOld π.T₄ _ (leafOld π.T₃ _ (π.markVertex₃ 2)))
    (leafOld (pushPlacement Θ π).T₄ _ (leafOld (pushPlacement Θ π).T₃ _
      ((pushPlacement Θ π).markVertex₃ 2))) (π.sheet 2).castSucc (Fin.last d)
    ((pushPlacement Θ π).sheet 2).castSucc (Fin.last d)
    (congrArg Sum.inl (congrArg Sum.inl (refIso₃_markVertex₃ Θ π 2))) (extend_sheet Θ π 2)
    (extendPerm_last _)

theorem glueIso_lift₃ (v : π.T₃.V) :
    (glueIso Θ π).targetVertex (π.lift₃ v) =
      (pushPlacement Θ π).lift₃ ((refIso₃ Θ π).targetVertex v) := rfl

theorem glueIso_vertexPerm_lift₃ (v : π.T₃.V) :
    (glueIso Θ π).vertexPerm (π.lift₃ v) = extendPerm ((refIso₃ Θ π).vertexPerm v) := rfl

theorem glueIso_liftE₃ (ε : π.T₃.edges) :
    (glueIso Θ π).targetEdge (π.liftE₃ ε) =
      (pushPlacement Θ π).liftE₃ ((refIso₃ Θ π).targetEdge ε) := by
  refine (leafIso_targetEdge_some (glueIso₅ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_
  refine congrArg (fun x ↦ leafOcc _ _ (some x))
    ((leafIso_targetEdge_some (glueIso₄ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_)
  exact congrArg (fun x ↦ leafOcc _ _ (some x))
    (leafIso_targetEdge_some (extendIso (refIso₃ Θ π)) _ _ _ _ _ _ _ _ _ _)

theorem glueIso_edgePerm_liftE₃ (ε : π.T₃.edges) :
    (glueIso Θ π).edgePerm (π.liftE₃ ε) = extendPerm ((refIso₃ Θ π).edgePerm ε) := by
  refine (leafIso_edgePerm_some (glueIso₅ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_
  refine (leafIso_edgePerm_some (glueIso₄ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_
  exact leafIso_edgePerm_some (extendIso (refIso₃ Θ π)) _ _ _ _ _ _ _ _ _ _

theorem glueIso_armEdge (k : Fin 3) :
    (glueIso Θ π).targetEdge (π.armEdge k) = (pushPlacement Θ π).armEdge k ∧
      (glueIso Θ π).edgePerm (π.armEdge k) = extendPerm (Θ.edgePerm (π.parentEdge k)) := by
  rw [← refIso₃_vertexPerm_markVertex₃]
  match k with
  | 0 =>
    constructor
    · refine (leafIso_targetEdge_some (glueIso₅ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_
      refine congrArg (fun x ↦ leafOcc _ _ (some x))
        ((leafIso_targetEdge_some (glueIso₄ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_)
      exact congrArg (fun x ↦ leafOcc _ _ (some x))
        (leafIso_targetEdge_none (extendIso (refIso₃ Θ π)) _ _ _ _ _ _ _ _ _)
    · refine (leafIso_edgePerm_some (glueIso₅ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_
      refine (leafIso_edgePerm_some (glueIso₄ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_
      exact leafIso_edgePerm_none (extendIso (refIso₃ Θ π)) _ _ _ _ _ _ _ _ _
  | 1 =>
    constructor
    · refine (leafIso_targetEdge_some (glueIso₅ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_
      exact congrArg (fun x ↦ leafOcc _ _ (some x))
        (leafIso_targetEdge_none (glueIso₄ Θ π) _ _ _ _ _ _ _ _ _)
    · refine (leafIso_edgePerm_some (glueIso₅ Θ π) _ _ _ _ _ _ _ _ _ _).trans ?_
      exact leafIso_edgePerm_none (glueIso₄ Θ π) _ _ _ _ _ _ _ _ _
  | 2 =>
    exact ⟨leafIso_targetEdge_none (glueIso₅ Θ π) _ _ _ _ _ _ _ _ _,
      leafIso_edgePerm_none (glueIso₅ Θ π) _ _ _ _ _ _ _ _ _⟩

/-- **The new sheet is fixed everywhere.** -/
theorem glueIso_vertexPerm_last (v : π.T₆.V) :
    (glueIso Θ π).vertexPerm v (Fin.last d) = Fin.last d := by
  rcases π.T₆_vertex_cases v with ⟨w, rfl⟩ | ⟨k, rfl⟩
  · rw [glueIso_vertexPerm_lift₃, extendPerm_last]
  · match k with
    | 0 => exact extendPerm_last _
    | 1 => exact extendPerm_last _
    | 2 => exact extendPerm_last _

theorem glueIso_oldVertex₃ (x : (refine₃ D π).SourceVertex) :
    (glueIso Θ π).sourceVertexEquiv (oldVertex₃ D π x) =
      oldVertex₃ D' (pushPlacement Θ π) ((refIso₃ Θ π).sourceVertexEquiv x) := by
  apply Subtype.ext
  rw [sourceVertexEquiv_val, oldVertex₃_val, oldVertex₃_val, glueIso_vertexPerm_lift₃,
    extendPerm_castSucc]
  rfl

theorem glueIso_liftSE (z : (refine₃ D π).SourceEdge) :
    (glueIso Θ π).sourceEdgeEquiv (liftSE D π z) =
      liftSE D' (pushPlacement Θ π) ((refIso₃ Θ π).sourceEdgeEquiv z) := by
  apply Subtype.ext
  rw [sourceEdgeEquiv_val]
  refine Prod.ext (glueIso_liftE₃ Θ π z.1.1) ?_
  show (glueIso Θ π).edgePerm (π.liftE₃ z.1.1) z.1.2.castSucc = _
  rw [glueIso_edgePerm_liftE₃, extendPerm_castSucc]
  rfl

theorem refIso₃_oldSV₃ (x : D.SourceVertex) :
    (refIso₃ Θ π).sourceVertexEquiv (oldSV₃ D π x) =
      oldSV₃ D' (pushPlacement Θ π) (Θ.sourceVertexEquiv x) := rfl

theorem refIso₃_parentSE₃ (z : (refine₃ D π).SourceEdge) :
    parentSE₃ D' (pushPlacement Θ π) ((refIso₃ Θ π).sourceEdgeEquiv z) =
      Θ.sourceEdgeEquiv (parentSE₃ D π z) := by
  have e1 : Refine.parentSE (refineDatum (refineDatum D' (pushPlacement Θ π).edge₀)
      (pushPlacement Θ π).edge₁) (pushPlacement Θ π).edge₂ ((refIso₃ Θ π).sourceEdgeEquiv z) =
      (refIso₂ Θ π).sourceEdgeEquiv (Refine.parentSE _ π.edge₂ z) :=
    refineIso_parentSE (refIso₂ Θ π) π.edge₂ z
  have e2 : ∀ w, Refine.parentSE (refineDatum D' (pushPlacement Θ π).edge₀)
      (pushPlacement Θ π).edge₁ ((refIso₂ Θ π).sourceEdgeEquiv w) =
      (refIso₁ Θ π).sourceEdgeEquiv (Refine.parentSE _ π.edge₁ w) := fun w ↦
    refineIso_parentSE (refIso₁ Θ π) π.edge₁ w
  have e3 : ∀ w, Refine.parentSE D' (pushPlacement Θ π).edge₀ ((refIso₁ Θ π).sourceEdgeEquiv w) =
      Θ.sourceEdgeEquiv (Refine.parentSE D π.edge₀ w) := fun w ↦
    refineIso_parentSE Θ π.edge₀ w
  unfold parentSE₃
  rw [e1, e2, e3]

theorem glueIso_oldSourceVertex (x : D.SourceVertex) :
    (glueIso Θ π).sourceVertexEquiv (π.oldSourceVertex D x) =
      (pushPlacement Θ π).oldSourceVertex D' (Θ.sourceVertexEquiv x) := by
  rw [oldSourceVertex_eq, oldSourceVertex_eq, glueIso_oldVertex₃, refIso₃_oldSV₃]

theorem glueIso_markSourceVertex (k : Fin 3) :
    (glueIso Θ π).sourceVertexEquiv (π.markSourceVertex D k) =
      (pushPlacement Θ π).markSourceVertex D' k := by
  show (glueIso Θ π).sourceVertexEquiv ((glueDatum D π).sourceEndpoint
    (π.lift₃ (π.markVertex₃ k)) (π.sheet k).castSucc) = _
  rw [sourceEndpoint_map, glueIso_lift₃, glueIso_vertexPerm_lift₃, extendPerm_castSucc,
    refIso₃_markVertex₃, refIso₃_vertexPerm_markVertex₃]
  rfl

theorem glueIso_armSourceEdge (k : Fin 3) :
    (glueIso Θ π).sourceEdgeEquiv (π.armSourceEdge D k) =
      (pushPlacement Θ π).armSourceEdge D' k := by
  show (glueIso Θ π).sourceEdgeEquiv ((glueDatum D π).sourceEdge (π.armEdge k)
    (π.sheet k).castSucc) = _
  rw [sourceEdge_map, (glueIso_armEdge Θ π k).1, (glueIso_armEdge Θ π k).2, extendPerm_castSucc]
  rfl

theorem pushPlacement_nonDangling (hD : D.Connected) (hπ : π.NonDangling D) :
    (pushPlacement Θ π).NonDangling D' := by
  intro k
  have h := (Θ.isDangling_map_iff hD (D.sourceEdge (π.parentEdge k) (π.sheet k))).not.mpr (hπ k)
  rw [sourceEdge_map, ← pushPlacement_parentEdge] at h
  exact h

end GlueIso

/-! ## Transporting a gluing along an isomorphism of members -/

section Transport

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {d : ℕ} {yG : Fin p → ℚ}
  {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}

/-- **A gluing of `ψ'` is a gluing of every `ψ ≅ ψ'`** (§5.5, the transport
half): push the placement forward along the isomorphism and compose with the glued isomorphism
`glueIso`. -/
theorem exists_gluing_transport {ψ ψ' : FibreMember core yG d} (m : GeometricMemberIso ψ' ψ)
    {π' : Placement ψ'.target d} (hπ' : π'.NonDangling ψ'.data)
    {φ : FibreMember (tripodCore core s) y (d + 1)}
    (iso' : GeometricDatumIso (glueDatum ψ'.data π') φ.data)
    (hL' : GluedLabels s ψ' π' φ.ident iso') :
    ∃ π : Placement ψ.target d, π.NonDangling ψ.data ∧
      ∃ iso : GeometricDatumIso (glueDatum ψ.data π) φ.data, GluedLabels s ψ π φ.ident iso := by
  classical
  have hD' := ψ'.fullDim.valid.1
  have hD := ψ.fullDim.valid.1
  set Γ := glueIso m.datum π' with hΓ
  refine ⟨pushPlacement m.datum π', pushPlacement_nonDangling m.datum π' hD' hπ',
    Γ.symm.trans iso', ?_⟩
  have hsymm : ∀ x, m.datum.sourceVertexEquiv (m.symm.datum.sourceVertexEquiv x) = x :=
    fun x ↦ Equiv.apply_symm_apply _ _
  refine ⟨fun b ↦ ?_, fun k ↦ ?_, ?_, fun e ↦ ?_, fun k ↦ ?_⟩
  · -- old
    set b' := m.symm.datum.branchVertexEquiv hD b with hb'
    have hv : ψ'.ident.vertex b' = ψ.ident.vertex b := m.symm.overCore_vertex b
    have h := hL'.old b'
    rw [hv] at h
    rw [h]
    show iso'.sourceVertexEquiv _ = iso'.sourceVertexEquiv (Γ.sourceVertexEquiv.symm _)
    congr 1
    rw [Equiv.eq_symm_apply, hΓ, glueIso_oldSourceVertex]
    exact congrArg _ (hsymm b.1)
  · -- mark
    rw [hL'.mark k]
    show iso'.sourceVertexEquiv _ = iso'.sourceVertexEquiv (Γ.sourceVertexEquiv.symm _)
    congr 1
    rw [Equiv.eq_symm_apply, hΓ, glueIso_markSourceVertex]
  · -- centre
    rw [symm_trans_sourceVertexEquiv_symm, sourceVertexEquiv_val, hL'.centre, hΓ,
      glueIso_vertexPerm_last]
  · -- row: through `pieceLabel_eq`, since the first piece can go to a second piece
    have hΘc := π'.refine₃_connected ψ'.data hD'
    set Θ₃ := refIso₃ m.datum π' with hΘ₃
    set yP := firstPiece₃ ψ.data (pushPlacement m.datum π') e.1 with hyP
    set z := Θ₃.sourceEdgeEquiv.symm yP with hz
    have hzimg : Θ₃.sourceEdgeEquiv z = yP := Equiv.apply_symm_apply _ _
    have hzpar : parentSE₃ ψ'.data π' z = m.symm.datum.sourceEdgeEquiv e.1 := by
      have h := refIso₃_parentSE₃ m.datum π' z
      rw [← hΘ₃, hzimg, hyP, parentSE₃_firstPiece₃] at h
      rw [h]
      exact (symm_sourceEdgeEquiv_apply m.datum _).symm
    have hzND : ¬ IsDangling (refine₃ ψ'.data π') z := by
      rw [isDangling_iff₃ ψ'.data π' hD', hzpar]
      exact (m.symm.datum.isDangling_map_iff hD e.1).not.mpr e.2
    let z' : NonDanglingEdge (refine₃ ψ'.data π') := ⟨z, hzND⟩
    refine ⟨iso'.nonDanglingEdgeEquiv
      (glueDatum_connected ψ'.data π' hD' ψ'.fullDim.targetConnected) (gluedND hπ' z'), ?_, ?_⟩
    · show iso'.sourceEdgeEquiv (liftSE ψ'.data π' z) =
        iso'.sourceEdgeEquiv (Γ.sourceEdgeEquiv.symm _)
      congr 1
      rw [Equiv.eq_symm_apply, hΓ, glueIso_liftSE, ← hΘ₃, hzimg, hyP, liftSE_firstPiece₃]
    · have h := pieceLabel_eq hπ' iso' hL' z'
      unfold pieceLabel at h
      rw [h]
      have hp : parentND₃ z' = m.symm.datum.nonDanglingEdgeEquiv hD e :=
        Subtype.ext hzpar
      rw [hp, ← GeometricDatumIso.stablePathEquiv_mk, m.symm.overCore_row]
  · -- leg
    obtain ⟨f, hf, hr⟩ := hL'.leg k
    refine ⟨f, ?_, hr⟩
    rw [hf]
    show iso'.sourceEdgeEquiv _ = iso'.sourceEdgeEquiv (Γ.sourceEdgeEquiv.symm _)
    congr 1
    rw [Equiv.eq_symm_apply, hΓ, glueIso_armSourceEdge]

end Transport

end GenusSixExistence.Tripod.Gluing

end
