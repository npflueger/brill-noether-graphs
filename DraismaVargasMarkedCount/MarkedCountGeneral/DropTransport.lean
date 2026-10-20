module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropSmooth
public import DraismaVargasCount.GeometricLimitTransport

@[expose] public section

/-!
# The drop lemma: the drop descends to classes (I2)

An isomorphism of gluing data `iso : P₁ ≅ P₂` carrying a contraction site `S₁` to `S₂` (the
contracted edge to the contracted edge) contracts to an isomorphism `S₁.D ≅ S₂.D`
(`Site.contractIso`, the public `GeometricLimitTransport.contractDatumIsoOfEdgeEq`). It commutes
with the edge map of the contraction (`contractIso_edgeMap`) and with the vertex map at every
source vertex away from `x` carrying a surviving occurrence (`contractIso_vmap`; read off the
occurrence, so that the permutation the public construction chooses at the merged vertex never has
to be computed).

For typed frames over `subdivide core s`, an isomorphism carries the canonical contracted edge to
the canonical contracted edge (`targetEdge_t'`), so it descends to an isomorphism of the drops
(`dropIso`, I2).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction
open GenusSixExistence.Tripod.Gadget (subdivide)
open Utilities.Certificate.ExplicitPotential (Core)

namespace DivalentContraction

/-! ## 1.  Contracting an isomorphism of data -/

section Iso

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ} {P₁ : GluingDatum target₁ degree}
  {P₂ : GluingDatum target₂ degree}

/-- The edge permutations of the contracted isomorphism. -/
theorem edgePerm_contractDatumIsoOfEdgeEq (iso : GeometricDatumIso P₁ P₂) (e₁ : target₁.edges)
    (e₂ : target₂.edges) (h : iso.targetEdge e₁ = e₂)
    (hOne₁ : num_edges target₁ (e₁ : target₁.V × target₁.V).1 (e₁ : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (e₂ : target₂.V × target₂.V).1 (e₂ : target₂.V × target₂.V).2 = 1)
    (ê : (contractTarget e₁ hOne₁).edges) :
    (GeometricLimitTransport.contractDatumIsoOfEdgeEq iso e₁ e₂ h hOne₁ hOne₂).edgePerm ê =
      iso.edgePerm (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) := by
  subst h
  rfl

/-- The target vertices of the contracted isomorphism. -/
theorem targetVertex_contractDatumIsoOfEdgeEq (iso : GeometricDatumIso P₁ P₂) (e₁ : target₁.edges)
    (e₂ : target₂.edges) (h : iso.targetEdge e₁ = e₂)
    (hOne₁ : num_edges target₁ (e₁ : target₁.V × target₁.V).1 (e₁ : target₁.V × target₁.V).2 = 1)
    (hOne₂ : num_edges target₂ (e₂ : target₂.V × target₂.V).1 (e₂ : target₂.V × target₂.V).2 = 1)
    (u : target₁.V) :
    (GeometricLimitTransport.contractDatumIsoOfEdgeEq iso e₁ e₂ h hOne₁ hOne₂).targetVertex
        (fold target₁ (fst_ne_snd e₁) u) = fold target₂ (fst_ne_snd e₂) (iso.targetVertex u) := by
  subst h
  exact GeometricContraction.contractVertexEquiv_fold iso e₁ u

variable (iso : GeometricDatumIso P₁ P₂) (S₁ : Site P₁) (S₂ : Site P₂)

/-- **The contracted isomorphism.** -/
noncomputable def Site.contractIso (hc : iso.targetEdge S₁.c = S₂.c) : GeometricDatumIso S₁.D S₂.D :=
  GeometricLimitTransport.contractDatumIsoOfEdgeEq iso S₁.c S₂.c hc S₁.hOne S₂.hOne

/-- Its edge permutations. -/
theorem contractIso_edgePerm (hc : iso.targetEdge S₁.c = S₂.c) (ê : S₁.T'.edges) :
    (Site.contractIso iso S₁ S₂ hc).edgePerm ê =
      iso.edgePerm (unfoldEdge (contracted := S₁.c) rfl (fst_ne_snd S₁.c) S₁.hOne ê) :=
  edgePerm_contractDatumIsoOfEdgeEq iso S₁.c S₂.c hc S₁.hOne S₂.hOne ê

/-- The contracted isomorphism on contracted columns. -/
theorem contractIso_col (hc : iso.targetEdge S₁.c = S₂.c) (f : {f : target₁.edges // f ≠ S₁.c}) :
    (Site.contractIso iso S₁ S₂ hc).targetEdge (S₁.col f) =
      S₂.col ⟨iso.targetEdge f.1, fun h ↦ f.2 (iso.targetEdge.injective (h.trans hc.symm))⟩ := by
  have hU := GeometricLimitTransport.unfoldEdge_contractDatumIsoOfEdgeEq iso S₁.c S₂.c hc S₁.hOne
    S₂.hOne (S₁.col f)
  have hF : unfoldEdge (contracted := S₁.c) rfl (fst_ne_snd S₁.c) S₁.hOne (S₁.col f) = f.1 := by
    have := unfoldEdge_foldEdge (contracted := S₁.c) rfl (fst_ne_snd S₁.c) S₁.hOne f
    exact this
  rw [hF] at hU
  have hne : unfoldEdge (contracted := S₂.c) rfl (fst_ne_snd S₂.c) S₂.hOne
      ((Site.contractIso iso S₁ S₂ hc).targetEdge (S₁.col f)) ≠ S₂.c :=
    unfoldEdge_ne_contracted rfl (fst_ne_snd S₂.c) S₂.hOne _
  have := foldEdge_unfoldEdge (contracted := S₂.c) rfl (fst_ne_snd S₂.c) S₂.hOne
    ((Site.contractIso iso S₁ S₂ hc).targetEdge (S₁.col f)) hne
  rw [← this]
  congr 1
  exact Subtype.ext hU

/-- **The contracted isomorphism commutes with the source edge map away from `c`.** -/
theorem contractIso_emap (hc : iso.targetEdge S₁.c = S₂.c) (e : {e : P₁.SourceEdge // e.1.1 ≠ S₁.c}) :
    (Site.contractIso iso S₁ S₂ hc).sourceEdgeEquiv (S₁.emap e) =
      S₂.emap ⟨iso.sourceEdgeEquiv e.1, fun h ↦ e.2 (iso.targetEdge.injective (h.trans hc.symm))⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · exact contractIso_col iso S₁ S₂ hc ⟨e.1.1.1, e.2⟩
  · change (Site.contractIso iso S₁ S₂ hc).edgePerm (S₁.col ⟨e.1.1.1, e.2⟩) e.1.1.2 =
      iso.edgePerm e.1.1.1 e.1.1.2
    rw [contractIso_edgePerm]
    congr 2
    exact unfoldEdge_foldEdge (contracted := S₁.c) rfl (fst_ne_snd S₁.c) S₁.hOne ⟨e.1.1.1, e.2⟩

/-- **The other edge corresponds.** -/
theorem targetEdge_other (hc : iso.targetEdge S₁.c = S₂.c) (hx : iso.targetVertex S₁.x = S₂.x) :
    iso.targetEdge S₁.other = S₂.other := by
  have hMem : iso.targetEdge S₁.other ∈ incidentEdges S₂.x := by
    rw [← hx, mem_incidentEdges_iff]
    have h := (mem_incidentEdges_iff _ _).mp S₁.other_mem
    exact (iso.target_incident_map_iff S₁.other S₁.x).mpr h
  rcases S₂.eq_c_or_other hMem with h | h
  · exact absurd (iso.targetEdge.injective (h.trans hc.symm)) S₁.other_ne
  · exact h

/-- **Partners correspond.** -/
theorem sourceEdgeEquiv_partner (hc : iso.targetEdge S₁.c = S₂.c)
    (hx : iso.targetVertex S₁.x = S₂.x) {e : P₁.SourceEdge} (he : e.1.1 = S₁.c) :
    iso.sourceEdgeEquiv (S₁.partner e) = S₂.partner (iso.sourceEdgeEquiv e) := by
  unfold Site.partner
  apply Subtype.ext
  apply Prod.ext
  · exact targetEdge_other iso S₁ S₂ hc hx
  · change iso.edgePerm S₁.other ((P₁.edgePartition S₁.other).repr e.1.2) =
      (P₂.edgePartition S₂.other).repr (iso.edgePerm e.1.1 e.1.2)
    -- both are sheets of one block of the other edge at `x₂`
    have hRep := (iso.edgeRepr_iff S₁.other ((P₁.edgePartition S₁.other).repr e.1.2)).mpr
      ((P₁.edgePartition S₁.other).repr_idem _)
    rw [targetEdge_other iso S₁ S₂ hc hx] at hRep
    rw [← hRep]
    -- the two sheets are related at `x₂`
    have hRelx : (P₂.vertexPartition S₂.x).Rel
        (iso.edgePerm S₁.other ((P₁.edgePartition S₁.other).repr e.1.2))
        (iso.edgePerm e.1.1 e.1.2) := by
      have h₁ := iso.compatible S₁.other S₁.x ((mem_incidentEdges_iff _ _).mp S₁.other_mem)
        ((P₁.edgePartition S₁.other).repr e.1.2)
      have h₂ := iso.compatible e.1.1 S₁.x (by rw [he]; exact (mem_incidentEdges_iff _ _).mp S₁.mem)
        e.1.2
      have hR : (P₁.vertexPartition S₁.x).Rel ((P₁.edgePartition S₁.other).repr e.1.2) e.1.2 :=
        (S₁.other_rel_iff _ _).mp ((P₁.edgePartition S₁.other).rel_repr_left e.1.2)
      have hVx := iso.vertexPartition S₁.x
      rw [hx] at hVx
      rw [hVx]
      have h3 := ((P₁.vertexPartition S₁.x).relabel_rel_iff (iso.vertexPerm S₁.x) _ _).mpr
        ((h₁.trans hR).trans h₂.symm)
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h3
    exact (S₂.other_rel_iff _ _).mpr hRelx

/-- **The contracted isomorphism commutes with the edge map.** -/
theorem contractIso_edgeMap (hc : iso.targetEdge S₁.c = S₂.c) (hx : iso.targetVertex S₁.x = S₂.x)
    (e : P₁.SourceEdge) :
    (Site.contractIso iso S₁ S₂ hc).sourceEdgeEquiv (S₁.edgeMap e) =
      S₂.edgeMap (iso.sourceEdgeEquiv e) := by
  by_cases he : e.1.1 = S₁.c
  · have he₂ : (iso.sourceEdgeEquiv e).1.1 = S₂.c := by
      change iso.targetEdge e.1.1 = S₂.c
      rw [he, hc]
    unfold Site.edgeMap
    rw [S₁.mu_of_eq he, S₂.mu_of_eq he₂, contractIso_emap iso S₁ S₂ hc]
    congr 1
    exact Subtype.ext (sourceEdgeEquiv_partner iso S₁ S₂ hc hx he)
  · have he₂ : (iso.sourceEdgeEquiv e).1.1 ≠ S₂.c := fun h ↦
      he (iso.targetEdge.injective (h.trans hc.symm))
    rw [S₁.edgeMap_of_ne he, S₂.edgeMap_of_ne he₂, contractIso_emap iso S₁ S₂ hc]

/-- The contracted isomorphism on source vertices lies over the image target vertex. -/
theorem contractIso_vertex_target (hc : iso.targetEdge S₁.c = S₂.c) (X : P₁.SourceVertex) :
    ((Site.contractIso iso S₁ S₂ hc).sourceVertexEquiv (S₁.vmap X)).1.1 =
      (S₂.vmap (iso.sourceVertexEquiv X)).1.1 :=
  targetVertex_contractDatumIsoOfEdgeEq iso S₁.c S₂.c hc S₁.hOne S₂.hOne X.1.1

/-- Two source vertices over one target vertex meeting one occurrence are equal. -/
theorem eq_of_incident_of_target_eq {target : CFGraph} {data : GluingDatum target degree}
    {g : data.SourceEdge} {Y Z : data.SourceVertex} (hY : Incident data g Y)
    (hZ : Incident data g Z) (hYZ : Y.1.1 = Z.1.1) : Y = Z := by
  have hne := data.sourceEnds_ne g
  have hT : (data.sourceEnds g).1.1.1 ≠ (data.sourceEnds g).2.1.1 := by
    change (g.1.1 : target.V × target.V).1 ≠ (g.1.1 : target.V × target.V).2
    exact fst_ne_snd g.1.1
  rcases hY with hY | hY <;> rcases hZ with hZ | hZ
  · exact hY.symm.trans hZ
  · exact absurd (by rw [hY, hZ]; exact hYZ) hT
  · exact absurd (by rw [hY, hZ]; exact hYZ.symm) hT
  · exact hY.symm.trans hZ

/-- **The contracted isomorphism commutes with the vertex map** at a source vertex away from `x`
carrying an occurrence. -/
theorem contractIso_vmap (hc : iso.targetEdge S₁.c = S₂.c) (hx : iso.targetVertex S₁.x = S₂.x)
    {X : P₁.SourceVertex} (hX : X.1.1 ≠ S₁.x) {e : P₁.SourceEdge}
    (he : Incident P₁ e X) :
    (Site.contractIso iso S₁ S₂ hc).sourceVertexEquiv (S₁.vmap X) =
      S₂.vmap (iso.sourceVertexEquiv X) := by
  have hX₂ : (iso.sourceVertexEquiv X).1.1 ≠ S₂.x := by
    change iso.targetVertex X.1.1 ≠ S₂.x
    rw [← hx]
    exact fun h ↦ hX (iso.targetVertex.injective h)
  have h₁ : Incident S₂.D ((Site.contractIso iso S₁ S₂ hc).sourceEdgeEquiv (S₁.edgeMap e))
      ((Site.contractIso iso S₁ S₂ hc).sourceVertexEquiv (S₁.vmap X)) :=
    ((Site.contractIso iso S₁ S₂ hc).incident_map_iff _ _).mpr (S₁.incident_edgeMap hX he)
  rw [contractIso_edgeMap iso S₁ S₂ hc hx] at h₁
  have h₂ : Incident S₂.D (S₂.edgeMap (iso.sourceEdgeEquiv e)) (S₂.vmap (iso.sourceVertexEquiv X)) :=
    S₂.incident_edgeMap hX₂ ((iso.incident_map_iff e X).mpr he)
  exact eq_of_incident_of_target_eq h₁ h₂ (contractIso_vertex_target iso S₁ S₂ hc X)

end Iso

end DivalentContraction

/-! ## 2.  The drop of an isomorphism of typed frames (I2) -/

namespace DropSmooth

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {s : Fin p}

/-- The merge of the two pieces of `s`: `cs i ↦ i`, `last p ↦ s`. -/
def merge (s : Fin p) : Fin (p + 1) → Fin p := Fin.lastCases (motive := fun _ ↦ Fin p) s id

/-- **The rows of the drop, read on the old labels.** -/
theorem rowEquiv_rowMap (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)
    (hc : IsMarkedCubic core mark) (r : MarkedStablePath κ.data (M κ)) :
    rowEquiv κ hc ((site κ hc).rowMap (markHyp κ hc) r) = merge s (κ.ident.row r) := by
  obtain ⟨ℓ, rfl⟩ := κ.ident.row.symm.surjective r
  rw [Equiv.apply_symm_apply]
  have hInv : ∀ i, rowEquiv κ hc (rowOf κ hc i) = i := fun i ↦
    (Equiv.ofBijective _ (rowOf_bijective κ hc)).symm_apply_apply i
  induction ℓ using Fin.lastCases with
  | last =>
    have h : (site κ hc).rowMap (markHyp κ hc) (κ.ident.row.symm (Fin.last p)) = rowOf κ hc s :=
      ((site κ hc).rowMap_eq_iff (markHyp κ hc) _ _).mpr (Or.inr
        ⟨(mem_pair_iff κ hc _).mpr (Or.inr rfl), (mem_pair_iff κ hc _).mpr (Or.inl rfl)⟩)
    rw [h, hInv]
    simp [merge]
  | cast i =>
    rw [show (site κ hc).rowMap (markHyp κ hc) (κ.ident.row.symm i.castSucc) = rowOf κ hc i
      from rfl, hInv]
    simp [merge]

/-- A source vertex of positive surviving valency carries an occurrence. -/
theorem exists_incident_of_valency {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    {X : data.SourceVertex} (h : 0 < nonDanglingValency data X) :
    ∃ e : data.SourceEdge, Incident data e X := by
  rw [← card_nonDanglingIncident] at h
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  exact ⟨e, ((mem_nonDanglingIncident _ _ _).mp he).2⟩

/-- A marked branch vertex carries an occurrence. -/
theorem exists_incident_branch {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
    {marks : Finset data.SourceVertex} (hMarks : ∀ X ∈ marks, nonDanglingValency data X = 2)
    (B : MarkedBranchVertex data marks) : ∃ e : data.SourceEdge, Incident data e B.1 := by
  refine exists_incident_of_valency ?_
  rcases B.2 with h | h
  · omega
  · rw [hMarks _ h]; omega

variable {κ₁ κ₂ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree}
  (hc : IsMarkedCubic core mark) (iso : TypedFrameIso κ₁ κ₂)

/-- An isomorphism carries the divalent vertex of the drop to that of the drop. -/
theorem iso_x : iso.datum.targetVertex (site κ₁ hc).x = (site κ₂ hc).x :=
  congrArg (fun X : κ₂.data.SourceVertex ↦ X.1.1) (iso.mark (Fin.last k))

/-- **An isomorphism carries the chosen occurrence to the chosen occurrence.** -/
theorem iso_fV : iso.datum.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 (fV κ₁) = fV κ₂ := by
  set g := iso.datum.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 (fV κ₁)
  have hInc : Incident κ₂.data g.1 (V κ₂) := by
    have h := (iso.datum.incident_map_iff _ _).mpr (fV_spec κ₁).1
    rw [iso.mark] at h
    exact h
  have hRow : markedRow (M κ₂) g = κ₂.ident.row.symm s.castSucc := by
    rw [Equiv.eq_symm_apply, iso.overCore_row, (fV_spec κ₁).2, Equiv.apply_symm_apply]
  have hCard := count_V_cs κ₂
  unfold markedIncidenceCount at hCard
  have hMem : ∀ f : NonDanglingEdge κ₂.data, Incident κ₂.data f.1 (V κ₂) →
      markedRow (M κ₂) f = κ₂.ident.row.symm s.castSucc →
      f ∈ (StablePathCount.incidentEdges κ₂.data (V κ₂)).filter fun e ↦
        markedRow (M κ₂) e = κ₂.ident.row.symm s.castSucc :=
    fun f hf hr ↦ Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr hf, hr⟩
  exact Finset.card_le_one.mp hCard.le _ (hMem g hInc hRow) _
    (hMem _ (fV_spec κ₂).1 (fV_spec κ₂).2)

/-- An isomorphism carries the contracted edge of the drop to that of the drop. -/
theorem iso_t' : iso.datum.targetEdge (site κ₁ hc).c = (site κ₂ hc).c :=
  congrArg (fun f : NonDanglingEdge κ₂.data ↦ f.1.1.1) (iso_fV iso)

/-- The contracted isomorphism of the drop. -/
noncomputable abbrev ψ : GeometricDatumIso (site κ₁ hc).D (site κ₂ hc).D :=
  Site.contractIso iso.datum (site κ₁ hc) (site κ₂ hc) (iso_t' hc iso)

/-- An isomorphism carries marked branch vertices to marked branch vertices. -/
theorem iso_branch (B : MarkedBranchVertex κ₁.data (M κ₁)) :
    3 ≤ nonDanglingValency κ₂.data (iso.datum.sourceVertexEquiv B.1) ∨
      iso.datum.sourceVertexEquiv B.1 ∈ M κ₂ := by
  rcases B.2 with h | h
  · left; rw [GeometricDatumIso.nonDanglingValency_map iso.datum κ₁.fullDim.valid.1]; exact h
  · right; exact (iso.mem_markSet_map B.1).mpr h

/-- The contracted isomorphism on the image of a marked branch vertex. -/
theorem ψ_vmap_branch (B : MarkedBranchVertex κ₁.data (M κ₁)) (hB : B.1 ≠ V κ₁) :
    (ψ hc iso).sourceVertexEquiv ((site κ₁ hc).vmap B.1) =
      (site κ₂ hc).vmap (iso.datum.sourceVertexEquiv B.1) := by
  obtain ⟨e, he⟩ := exists_incident_branch κ₁.fullDim.markValency B
  exact contractIso_vmap iso.datum (site κ₁ hc) (site κ₂ hc) (iso_t' hc iso) (iso_x hc iso)
    ((site κ₁ hc).not_over_x (markHyp κ₁ hc) B hB) he

/-- **I2: the drop of an isomorphism.** -/
noncomputable def dropIso : TypedFrameIso (dropFrame' hc κ₁) (dropFrame' hc κ₂) where
  datum := ψ hc iso
  mark j := by
    change (ψ hc iso).sourceVertexEquiv ((site κ₁ hc).vmap (κ₁.markSource j.castSucc)) =
      (site κ₂ hc).vmap (κ₂.markSource j.castSucc)
    rw [ψ_vmap_branch hc iso ⟨κ₁.markSource j.castSucc, Or.inr (mem_markSet _ _)⟩
      (fun h ↦ markSource_castSucc_ne κ₁ hc j (congrArg (fun X : κ₁.data.SourceVertex ↦ X.1.1) h)),
      iso.mark]
  overCore_vertex Bd hImage := by
    obtain ⟨B, rfl⟩ := ((site κ₁ hc).branchEquiv (markHyp κ₁ hc)).surjective Bd
    have hB₂ : iso.datum.sourceVertexEquiv B.1.1 ≠ V κ₂ := by
      intro h
      apply B.2
      exact iso.datum.sourceVertexEquiv.injective (h.trans (iso.mark (Fin.last k)).symm)
    have hEq : (⟨(ψ hc iso).sourceVertexEquiv ((site κ₁ hc).branchEquiv (markHyp κ₁ hc) B).1,
        hImage⟩ : MarkedBranchVertex (site κ₂ hc).D (MD κ₂ hc)) =
        (site κ₂ hc).branchEquiv (markHyp κ₂ hc) ⟨⟨_, iso_branch iso B.1⟩, hB₂⟩ := by
      apply Subtype.ext
      show (ψ hc iso).sourceVertexEquiv ((site κ₁ hc).vmap B.1.1) =
        (site κ₂ hc).vmap (iso.datum.sourceVertexEquiv B.1.1)
      exact ψ_vmap_branch hc iso B.1 B.2
    change vertexEquiv κ₂ hc _ = vertexEquiv κ₁ hc _
    refine (congrArg (vertexEquiv κ₂ hc) hEq).trans ?_
    apply Fin.castSucc_injective
    rw [vertexEquiv_branchEquiv, vertexEquiv_branchEquiv]
    exact iso.overCore_vertex B.1 (iso_branch iso B.1)
  overCore_row g := by
    obtain ⟨e, rfl⟩ := (site κ₁ hc).ndMap_surjective g
    have hE : (ψ hc iso).nonDanglingEdgeEquiv (dropFrame' hc κ₁).fullDim.valid.1
        ((site κ₁ hc).ndMap e) =
        (site κ₂ hc).ndMap (iso.datum.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 e) :=
      Subtype.ext (contractIso_edgeMap iso.datum (site κ₁ hc) (site κ₂ hc) (iso_t' hc iso)
        (iso_x hc iso) e.1)
    change rowEquiv κ₂ hc (markedRow (MD κ₂ hc) _) = rowEquiv κ₁ hc (markedRow (MD κ₁ hc) _)
    refine (congrArg (fun g ↦ rowEquiv κ₂ hc (markedRow (MD κ₂ hc) g)) hE).trans ?_
    change rowEquiv κ₂ hc ((site κ₂ hc).rowMap (markHyp κ₂ hc) (markedRow (M κ₂) _)) =
      rowEquiv κ₁ hc ((site κ₁ hc).rowMap (markHyp κ₁ hc) (markedRow (M κ₁) e))
    rw [rowEquiv_rowMap, rowEquiv_rowMap, iso.overCore_row]

end DropSmooth

end DraismaVargas.Count.MarkedCountGeneral
