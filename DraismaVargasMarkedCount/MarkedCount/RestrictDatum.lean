module

public import DraismaVargas.LocalCases.FullDimensionalSource
public import DraismaVargas.LocalCases.DanglingDescent
public import DraismaVargas.LocalCases.StableLocalProperties
public import Utilities.Foundations.InducedSubgraph
public import DraismaVargas.Infrastructure.SheetGluing
public import GenusSixExistence.BrillNoetherRank.Tripod.Gluing
public import DraismaVargasMarkedCount.MarkedCount.MarkedPath
public import DraismaVargasCount.GeometricTransport

@[expose] public section

/-!
# Restricting a gluing datum to a set of target vertices

The generic layer of restriction: given a gluing datum `D` over a target `T` and a nonempty set
`Keep` of target vertices, `restrictDatum D Keep hKeep` is the datum over the induced subgraph
`restrictTarget Keep hKeep` (`Utilities.inducedSubgraph`) with the same partitions.  Its source is
the full preimage of the kept vertices.

This file proves the facts that need no lollipop:

* the dictionaries of target edges (`edgeEquiv`), source vertices (`svEquiv`) and source edges
  (`seEquiv`), compatible with endpoints, indices and incidence;
* **Riemann--Hurwitz is inherited** (`riemannHurwitz_restrictDatum`): deleting target edges at a
  vertex lowers both sides of the inequality, the left one by at most the block size per edge;
  and the local ramification after restriction (`localRamification_restrictDatum`);
* **connectedness** (`connected_restrictDatum`), from a retraction of the target onto the kept
  vertices along which the deleted partitions refine;
* the **genus** of the restricted source and target (`card_sourceVertex_restrictDatum`,
  `card_sourceEdge_restrictDatum`, `card_edges_restrictTarget`).
-/

namespace DraismaVargas.Count.MarkedCount.Restrict

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Infrastructure.GluingDatum (sourceEndpoint_congr)
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)

/-! ## 1.  The restricted target -/

section Target

variable {T : CFGraph.{0}} (Keep : Finset T.V) (hKeep : Keep.Nonempty)

/-- A target edge occurrence both of whose ends are kept. -/
def KeptEdge (e : T.edges) : Prop :=
  (e : T.V × T.V).1 ∈ Keep ∧ (e : T.V × T.V).2 ∈ Keep

instance (e : T.edges) : Decidable (KeptEdge Keep e) := by
  unfold KeptEdge; infer_instance

/-- **The restricted target**: the subgraph induced on the kept vertices. -/
def restrictTarget : CFGraph.{0} := Utilities.inducedSubgraph T Keep hKeep

@[simp] theorem restrictTarget_V : (restrictTarget Keep hKeep).V = {v : T.V // v ∈ Keep} := rfl

theorem count_restrictTarget_edges (a b : {v : T.V // v ∈ Keep}) :
    Multiset.count ((a, b) : (restrictTarget Keep hKeep).V × (restrictTarget Keep hKeep).V)
        (restrictTarget Keep hKeep).edges =
      Multiset.count ((a.1, b.1) : T.V × T.V) T.edges := by
  classical
  change Multiset.count (a, b) ((Utilities.inducedEdges T Keep).pmap
    (Utilities.restrictInducedEdge T Keep) (Utilities.inducedEdges_all T Keep)) = _
  rw [Multiset.pmap_eq_map_attach]
  set g : {e // e ∈ Utilities.inducedEdges T Keep} →
      {v : T.V // v ∈ Keep} × {v : T.V // v ∈ Keep} := fun e ↦
    Utilities.restrictInducedEdge T Keep e.1 (Utilities.inducedEdges_all T Keep e.1 e.2)
  have hinj : Function.Injective g := by
    rintro ⟨⟨x₁, y₁⟩, h₁⟩ ⟨⟨x₂, y₂⟩, h₂⟩ hEq
    simp only [g, Utilities.restrictInducedEdge, Prod.mk.injEq, Subtype.mk.injEq] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    rfl
  have hFilter : Multiset.count ((a.1, b.1) : T.V × T.V) (Utilities.inducedEdges T Keep) =
      Multiset.count ((a.1, b.1) : T.V × T.V) T.edges := by
    unfold Utilities.inducedEdges
    exact Multiset.count_filter_of_pos ⟨a.2, b.2⟩
  by_cases hmem : ((a.1, b.1) : T.V × T.V) ∈ Utilities.inducedEdges T Keep
  · have hab : (a, b) = g ⟨(a.1, b.1), hmem⟩ := rfl
    rw [hab, Multiset.count_map_eq_count' _ _ hinj, Multiset.count_attach, hFilter]
  · have h0 : Multiset.count ((a.1, b.1) : T.V × T.V) (Utilities.inducedEdges T Keep) = 0 :=
      Multiset.count_eq_zero.mpr hmem
    rw [← hFilter, h0, Multiset.count_eq_zero]
    intro hIn
    obtain ⟨e, -, he⟩ := Multiset.mem_map.mp hIn
    apply hmem
    have h1 : e.1 = ((a.1, b.1) : T.V × T.V) := by
      have hx := congrArg (fun q : {v : T.V // v ∈ Keep} × {v : T.V // v ∈ Keep} ↦
        ((q.1.1, q.2.1) : T.V × T.V)) he
      simpa [g, Utilities.restrictInducedEdge] using hx
    exact h1 ▸ e.2

variable {Keep hKeep}

/-- A restricted target vertex, read in the original target. -/
def vIncl (v : (restrictTarget Keep hKeep).V) : T.V := Subtype.val (p := (· ∈ Keep)) v

theorem vIncl_mem (v : (restrictTarget Keep hKeep).V) : vIncl v ∈ Keep :=
  Subtype.property (p := (· ∈ Keep)) v

/-- A kept target vertex, read in the restricted target. -/
def vRestrict (v : T.V) (h : v ∈ Keep) : (restrictTarget Keep hKeep).V :=
  (⟨v, h⟩ : {v : T.V // v ∈ Keep})

@[simp] theorem vIncl_vRestrict (v : T.V) (h : v ∈ Keep) :
    vIncl (vRestrict (hKeep := hKeep) v h) = v := rfl

@[simp] theorem vRestrict_vIncl (v : (restrictTarget Keep hKeep).V) :
    vRestrict (vIncl v) (vIncl_mem v) = v := rfl

theorem vIncl_injective : Function.Injective (vIncl (Keep := Keep) (hKeep := hKeep)) :=
  fun _ _ h ↦ Subtype.ext (p := (· ∈ Keep)) h

@[simp] theorem vIncl_inj {v w : (restrictTarget Keep hKeep).V} : vIncl v = vIncl w ↔ v = w :=
  vIncl_injective.eq_iff

/-- A restricted target edge occurrence, read in the original target. -/
def edgeIncl (e : (restrictTarget Keep hKeep).edges) : T.edges :=
  ⟨(vIncl e.1.1, vIncl e.1.2), Fin.cast (count_restrictTarget_edges Keep hKeep e.1.1 e.1.2) e.2⟩

@[simp] theorem edgeIncl_fst (e : (restrictTarget Keep hKeep).edges) :
    ((edgeIncl e : T.edges) : T.V × T.V).1 =
      vIncl (e : (restrictTarget Keep hKeep).V × (restrictTarget Keep hKeep).V).1 := rfl

@[simp] theorem edgeIncl_snd (e : (restrictTarget Keep hKeep).edges) :
    ((edgeIncl e : T.edges) : T.V × T.V).2 =
      vIncl (e : (restrictTarget Keep hKeep).V × (restrictTarget Keep hKeep).V).2 := rfl

theorem keptEdge_edgeIncl (e : (restrictTarget Keep hKeep).edges) :
    KeptEdge Keep (edgeIncl e) :=
  ⟨vIncl_mem _, vIncl_mem _⟩

/-- A kept target edge occurrence, read in the restricted target. -/
def edgeRestrict (e : T.edges) (h : KeptEdge Keep e) : (restrictTarget Keep hKeep).edges :=
  ⟨(vRestrict (e : T.V × T.V).1 h.1, vRestrict (e : T.V × T.V).2 h.2),
    Fin.cast (count_restrictTarget_edges Keep hKeep
      (⟨(e : T.V × T.V).1, h.1⟩ : {v : T.V // v ∈ Keep}) ⟨(e : T.V × T.V).2, h.2⟩).symm e.2⟩

@[simp] theorem edgeIncl_edgeRestrict (e : T.edges) (h : KeptEdge Keep e) :
    edgeIncl (edgeRestrict (hKeep := hKeep) e h) = e := rfl

@[simp] theorem edgeRestrict_edgeIncl (e : (restrictTarget Keep hKeep).edges) :
    edgeRestrict (edgeIncl e) (keptEdge_edgeIncl e) = e := rfl

theorem edgeIncl_injective :
    Function.Injective (edgeIncl (Keep := Keep) (hKeep := hKeep)) := by
  intro e₁ e₂ h
  rw [← edgeRestrict_edgeIncl e₁, ← edgeRestrict_edgeIncl e₂]
  congr 1

@[simp] theorem fst_edgeRestrict (e : T.edges) (h : KeptEdge Keep e) :
    vIncl ((edgeRestrict (hKeep := hKeep) e h :
      (restrictTarget Keep hKeep).V × (restrictTarget Keep hKeep).V).1) = (e : T.V × T.V).1 :=
  rfl

@[simp] theorem snd_edgeRestrict (e : T.edges) (h : KeptEdge Keep e) :
    vIncl ((edgeRestrict (hKeep := hKeep) e h :
      (restrictTarget Keep hKeep).V × (restrictTarget Keep hKeep).V).2) = (e : T.V × T.V).2 :=
  rfl

/-- **The edge dictionary**: restricted target edges are the kept ones. -/
def edgeEquiv : (restrictTarget Keep hKeep).edges ≃ {e : T.edges // KeptEdge Keep e} where
  toFun e := ⟨edgeIncl e, keptEdge_edgeIncl e⟩
  invFun e := edgeRestrict e.1 e.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_edges_restrictTarget :
    Multiset.card (restrictTarget Keep hKeep).edges =
      (Finset.univ.filter fun e : T.edges ↦ KeptEdge Keep e).card := by
  classical
  rw [← Multiset.card_coe (restrictTarget Keep hKeep).edges, Fintype.card_congr edgeEquiv,
    Fintype.card_subtype]

end Target

/-! ## 2.  The restricted datum and its source -/

section Datum

variable {T : CFGraph.{0}} {d : ℕ} (D : GluingDatum T d) (Keep : Finset T.V)
  (hKeep : Keep.Nonempty)

/-- **The restricted datum**: the same partitions over the kept vertices and edges. -/
def restrictDatum : GluingDatum (restrictTarget Keep hKeep) d where
  degree_pos := D.degree_pos
  vertexPartition v := D.vertexPartition (vIncl v)
  edgePartition e := D.edgePartition (edgeIncl e)
  refines_left e := D.refines_left (edgeIncl e)
  refines_right e := D.refines_right (edgeIncl e)

@[simp] theorem restrictDatum_vertexPartition (v : (restrictTarget Keep hKeep).V) :
    (restrictDatum D Keep hKeep).vertexPartition v = D.vertexPartition (vIncl v) := rfl

@[simp] theorem restrictDatum_edgePartition (e : (restrictTarget Keep hKeep).edges) :
    (restrictDatum D Keep hKeep).edgePartition e = D.edgePartition (edgeIncl e) := rfl

variable {D Keep hKeep}

/-- A source vertex of the restriction, read in `D`. -/
def svIncl (X : (restrictDatum D Keep hKeep).SourceVertex) : D.SourceVertex :=
  ⟨(vIncl X.1.1, X.1.2), X.2⟩

/-- A source vertex of `D` over a kept vertex, read in the restriction. -/
def svRestrict (X : D.SourceVertex) (h : X.1.1 ∈ Keep) :
    (restrictDatum D Keep hKeep).SourceVertex :=
  ⟨(vRestrict X.1.1 h, X.1.2), X.2⟩

/-- A source edge of the restriction, read in `D`. -/
def seIncl (E : (restrictDatum D Keep hKeep).SourceEdge) : D.SourceEdge :=
  ⟨(edgeIncl E.1.1, E.1.2), E.2⟩

/-- A source edge of `D` over a kept edge, read in the restriction. -/
def seRestrict (E : D.SourceEdge) (h : KeptEdge Keep E.1.1) :
    (restrictDatum D Keep hKeep).SourceEdge :=
  ⟨(edgeRestrict E.1.1 h, E.1.2), E.2⟩

@[simp] theorem svIncl_svRestrict (X : D.SourceVertex) (h : X.1.1 ∈ Keep) :
    svIncl (svRestrict (hKeep := hKeep) X h) = X := rfl

@[simp] theorem svRestrict_svIncl (X : (restrictDatum D Keep hKeep).SourceVertex) :
    svRestrict (svIncl X) (vIncl_mem X.1.1) = X := rfl

@[simp] theorem seIncl_seRestrict (E : D.SourceEdge) (h : KeptEdge Keep E.1.1) :
    seIncl (seRestrict (hKeep := hKeep) E h) = E := rfl

@[simp] theorem seRestrict_seIncl (E : (restrictDatum D Keep hKeep).SourceEdge) :
    seRestrict (seIncl E) (keptEdge_edgeIncl E.1.1) = E := rfl

theorem svIncl_target_mem (X : (restrictDatum D Keep hKeep).SourceVertex) :
    (svIncl X).1.1 ∈ Keep := vIncl_mem X.1.1

theorem seIncl_kept (E : (restrictDatum D Keep hKeep).SourceEdge) :
    KeptEdge Keep (seIncl E).1.1 := keptEdge_edgeIncl E.1.1

theorem svIncl_injective : Function.Injective (svIncl (D := D) (Keep := Keep) (hKeep := hKeep)) := by
  intro X Y h
  rw [← svRestrict_svIncl X, ← svRestrict_svIncl Y]
  congr 1

theorem seIncl_injective : Function.Injective (seIncl (D := D) (Keep := Keep) (hKeep := hKeep)) := by
  intro X Y h
  rw [← seRestrict_seIncl X, ← seRestrict_seIncl Y]
  congr 1

@[simp] theorem svIncl_inj {X Y : (restrictDatum D Keep hKeep).SourceVertex} :
    svIncl X = svIncl Y ↔ X = Y := svIncl_injective.eq_iff

@[simp] theorem seIncl_inj {X Y : (restrictDatum D Keep hKeep).SourceEdge} :
    seIncl X = seIncl Y ↔ X = Y := seIncl_injective.eq_iff

variable (D Keep hKeep) in
/-- **The source-vertex dictionary.** -/
def svEquiv : (restrictDatum D Keep hKeep).SourceVertex ≃ {X : D.SourceVertex // X.1.1 ∈ Keep} where
  toFun X := ⟨svIncl X, svIncl_target_mem X⟩
  invFun X := svRestrict X.1 X.2
  left_inv _ := rfl
  right_inv _ := rfl

variable (D Keep hKeep) in
/-- **The source-edge dictionary.** -/
def seEquiv : (restrictDatum D Keep hKeep).SourceEdge ≃ {E : D.SourceEdge // KeptEdge Keep E.1.1} where
  toFun E := ⟨seIncl E, seIncl_kept E⟩
  invFun E := seRestrict E.1 E.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem sourceEnds_seIncl (E : (restrictDatum D Keep hKeep).SourceEdge) :
    D.sourceEnds (seIncl E) =
      (svIncl ((restrictDatum D Keep hKeep).sourceEnds E).1,
        svIncl ((restrictDatum D Keep hKeep).sourceEnds E).2) := rfl

theorem sourceEdgeIndex_seIncl (E : (restrictDatum D Keep hKeep).SourceEdge) :
    D.sourceEdgeIndex (seIncl E) = (restrictDatum D Keep hKeep).sourceEdgeIndex E := rfl

theorem blockCard_svIncl (X : (restrictDatum D Keep hKeep).SourceVertex) :
    (D.vertexPartition (svIncl X).1.1).blockCard (svIncl X).1.2 =
      ((restrictDatum D Keep hKeep).vertexPartition X.1.1).blockCard X.1.2 := rfl

theorem incident_seIncl_iff (E : (restrictDatum D Keep hKeep).SourceEdge)
    (X : (restrictDatum D Keep hKeep).SourceVertex) :
    Incident D (seIncl E) (svIncl X) ↔ Incident (restrictDatum D Keep hKeep) E X := by
  unfold Incident
  rw [sourceEnds_seIncl]
  simp only [svIncl_inj]

/-- The endpoints of a kept source edge are kept. -/
theorem target_mem_of_incident {E : D.SourceEdge} (hE : KeptEdge Keep E.1.1) {X : D.SourceVertex}
    (hX : Incident D E X) : X.1.1 ∈ Keep := by
  rcases hX with h | h
  · rw [← h]; exact hE.1
  · rw [← h]; exact hE.2

theorem incident_iff_seRestrict {E : D.SourceEdge} (hE : KeptEdge Keep E.1.1)
    (X : (restrictDatum D Keep hKeep).SourceVertex) :
    Incident D E (svIncl X) ↔ Incident (restrictDatum D Keep hKeep) (seRestrict E hE) X := by
  rw [← incident_seIncl_iff, seIncl_seRestrict]

/-! ### Incident target edges -/

theorem incidentEdges_restrict (v : (restrictTarget Keep hKeep).V) :
    (GluingDatum.incidentEdges v).map ⟨edgeIncl, edgeIncl_injective⟩ =
      (GluingDatum.incidentEdges (vIncl v)).filter (KeptEdge Keep) := by
  classical
  ext e
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_filter,
    GluingDatum.incidentEdges, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e', he', rfl⟩
    refine ⟨?_, keptEdge_edgeIncl e'⟩
    rcases he' with h | h
    · left; rw [edgeIncl_fst, h]
    · right; rw [edgeIncl_snd, h]
  · rintro ⟨he, hk⟩
    refine ⟨edgeRestrict e hk, ?_, rfl⟩
    rcases he with h | h
    · left; exact vIncl_injective (by rw [fst_edgeRestrict, h])
    · right; exact vIncl_injective (by rw [snd_edgeRestrict, h])

theorem sum_incidentEdges_restrict (v : (restrictTarget Keep hKeep).V) {M : Type*}
    [AddCommMonoid M] (f : T.edges → M) :
    ∑ e ∈ GluingDatum.incidentEdges v, f (edgeIncl e) =
      ∑ e ∈ (GluingDatum.incidentEdges (vIncl v)).filter (KeptEdge Keep), f e := by
  rw [← incidentEdges_restrict, Finset.sum_map]
  rfl

theorem card_incidentEdges_restrict (v : (restrictTarget Keep hKeep).V) :
    (GluingDatum.incidentEdges v).card =
      ((GluingDatum.incidentEdges (vIncl v)).filter (KeptEdge Keep)).card := by
  rw [← incidentEdges_restrict, Finset.card_map]

/-! ### Riemann--Hurwitz -/

theorem blockCountWithin_le_blockCard (fine coarse : SheetPartition d) (i : Fin d) :
    fine.blockCountWithin coarse i ≤ coarse.blockCard i :=
  Finset.card_image_le

/-- **The local ramification after restriction**: each deleted target edge at the vertex adds
`m - k_e`, the block size minus the number of edge blocks inside it. -/
theorem localRamification_restrictDatum (v : (restrictTarget Keep hKeep).V)
    (b : ((restrictDatum D Keep hKeep).vertexPartition v).Blocks) :
    (restrictDatum D Keep hKeep).localRamification v b =
      D.localRamification (vIncl v) b +
        ∑ e ∈ (GluingDatum.incidentEdges (vIncl v)).filter (fun e ↦ ¬ KeptEdge Keep e),
          (((D.vertexPartition (vIncl v)).blockCard b.1 : ℤ) -
            ((D.edgePartition e).blockCountWithin (D.vertexPartition (vIncl v)) b.1 : ℤ)) := by
  classical
  unfold GluingDatum.localRamification
  simp only [restrictDatum_edgePartition, restrictDatum_vertexPartition]
  rw [sum_incidentEdges_restrict v
      (fun e ↦ ((D.edgePartition e).blockCountWithin (D.vertexPartition (vIncl v)) b.1 : ℤ)),
    card_incidentEdges_restrict]
  have hSum := Finset.sum_filter_add_sum_filter_not (GluingDatum.incidentEdges (vIncl v))
    (KeptEdge Keep)
    (fun e ↦ ((D.edgePartition e).blockCountWithin (D.vertexPartition (vIncl v)) b.1 : ℤ))
  have hCard := Finset.card_filter_add_card_filter_not
    (s := GluingDatum.incidentEdges (vIncl v)) (KeptEdge Keep)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hSum, ← hCard]
  push_cast
  ring

/-- **Riemann--Hurwitz is inherited by the restriction.** -/
theorem riemannHurwitz_restrictDatum (hRH : D.RiemannHurwitz) :
    (restrictDatum D Keep hKeep).RiemannHurwitz := by
  classical
  intro v sheet
  have hOld := hRH (vIncl v) sheet
  have hEq := localRamification_restrictDatum (D := D) (hKeep := hKeep) v
    ((D.vertexPartition (vIncl v)).toBlock sheet)
  have hNonneg : 0 ≤ ∑ e ∈ (GluingDatum.incidentEdges (vIncl v)).filter
      (fun e ↦ ¬ KeptEdge Keep e),
      (((D.vertexPartition (vIncl v)).blockCard
          ((D.vertexPartition (vIncl v)).toBlock sheet).1 : ℤ) -
        ((D.edgePartition e).blockCountWithin (D.vertexPartition (vIncl v))
          ((D.vertexPartition (vIncl v)).toBlock sheet).1 : ℤ)) :=
    Finset.sum_nonneg fun e _ ↦ by
      have := blockCountWithin_le_blockCard (D.edgePartition e) (D.vertexPartition (vIncl v))
        ((D.vertexPartition (vIncl v)).toBlock sheet).1
      omega
  have hRepr := SheetPartition.rel_repr_left (D.vertexPartition (vIncl v)) sheet
  have hBC : ∀ fine : SheetPartition d, fine.blockCountWithin (D.vertexPartition (vIncl v))
      ((D.vertexPartition (vIncl v)).repr sheet) =
      fine.blockCountWithin (D.vertexPartition (vIncl v)) sheet := by
    intro fine
    unfold SheetPartition.blockCountWithin
    rw [SheetPartition.block_eq_of_rel _ hRepr]
  have hCardEq : (D.vertexPartition (vIncl v)).blockCard ((D.vertexPartition (vIncl v)).repr sheet) =
      (D.vertexPartition (vIncl v)).blockCard sheet := by
    unfold SheetPartition.blockCard
    rw [SheetPartition.block_eq_of_rel _ hRepr]
  unfold GluingDatum.localRamification at hEq
  simp only [SheetPartition.toBlock_val, hBC, hCardEq, restrictDatum_edgePartition,
    restrictDatum_vertexPartition] at hEq hNonneg
  simp only [restrictDatum_edgePartition, restrictDatum_vertexPartition]
  linarith

end Datum

/-! ## 3.  Connectedness, through a retraction -/

section Connected

open DraismaVargas.LocalCases.DanglingDescent

universe u v

/-- A map sending every edge to an edge or a point carries walks to walks. -/
theorem reach_map {G : CFGraph.{u}} {H : CFGraph.{v}} (f : G.V → H.V)
    (hf : ∀ a b, 0 < num_edges G a b → f a = f b ∨ 0 < num_edges H (f a) (f b))
    {a b : G.V} (h : Reach G a b) : Reach H (f a) (f b) := by
  induction h with
  | refl => exact reach_refl _ _
  | tail _ hbc ih =>
    rcases hf _ _ hbc with h | h
    · rw [← h]; exact ih
    · exact reach_trans ih (reach_single h)

/-- **Connectedness passes along a surjective map sending edges to edges or points.** -/
theorem graph_connected_of_map {G : CFGraph.{u}} {H : CFGraph.{v}} (hG : graph_connected G)
    (f : G.V → H.V) (hsurj : Function.Surjective f)
    (hf : ∀ a b, 0 < num_edges G a b → f a = f b ∨ 0 < num_edges H (f a) (f b)) :
    graph_connected H := by
  obtain ⟨a₀⟩ := G.instNonempty
  refine graph_connected_of_reach (f a₀) fun w ↦ ?_
  obtain ⟨b, rfl⟩ := hsurj w
  exact reach_map f hf (reach_of_graph_connected hG a₀ b)

variable {T : CFGraph.{0}} {d : ℕ} {D : GluingDatum T d} {Keep : Finset T.V}
  {hKeep : Keep.Nonempty}

/-- **The restricted target is connected**, given a retraction of the target onto the kept
vertices that collapses every deleted edge. -/
theorem graph_connected_restrictTarget (hT : graph_connected T)
    (ρ : T.V → (restrictTarget Keep hKeep).V)
    (hρ : ∀ v (h : v ∈ Keep), ρ v = vRestrict v h)
    (hEdge : ∀ e : T.edges, ¬ KeptEdge Keep e → ρ (e : T.V × T.V).1 = ρ (e : T.V × T.V).2) :
    graph_connected (restrictTarget Keep hKeep) := by
  classical
  refine graph_connected_of_map hT ρ (fun w ↦ ⟨vIncl w, by rw [hρ _ (vIncl_mem w)]; rfl⟩) ?_
  intro a b hab
  obtain ⟨pair, hPair, hEnds⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos T a b hab
  let e : T.edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hPair⟩⟩
  by_cases hk : KeptEdge Keep e
  · right
    have hk' : pair.1 ∈ Keep ∧ pair.2 ∈ Keep := hk
    have ha : a ∈ Keep := by rcases hEnds with h | h <;> rw [h] at hk' <;> simp_all
    have hb : b ∈ Keep := by rcases hEnds with h | h <;> rw [h] at hk' <;> simp_all
    rw [hρ a ha, hρ b hb]
    change 0 < num_edges (Utilities.inducedSubgraph T Keep hKeep) ⟨a, ha⟩ ⟨b, hb⟩
    rw [Utilities.num_edges_inducedSubgraph]
    exact hab
  · left
    have h := hEdge e hk
    change ρ pair.1 = ρ pair.2 at h
    rcases hEnds with hp | hp <;> rw [hp] at h
    · exact h
    · exact h.symm

/-- **The restricted source is connected**, given a retraction `ρ` of the target onto the kept
vertices that collapses every deleted edge, along which the partitions of the deleted vertices
refine: every source vertex over a deleted vertex then lies in one source vertex over its
image, and the source retracts onto the restricted source. -/
theorem connected_restrictDatum (hConn : D.Connected)
    (ρ : T.V → (restrictTarget Keep hKeep).V)
    (hρ : ∀ v (h : v ∈ Keep), ρ v = vRestrict v h)
    (hEdge : ∀ e : T.edges, ¬ KeptEdge Keep e → ρ (e : T.V × T.V).1 = ρ (e : T.V × T.V).2)
    (hRefine : ∀ v, v ∉ Keep → (D.vertexPartition v).Refines (D.vertexPartition (vIncl (ρ v)))) :
    (restrictDatum D Keep hKeep).Connected := by
  classical
  set D' := restrictDatum D Keep hKeep
  have hRefine' : ∀ v, (D.vertexPartition v).Refines (D.vertexPartition (vIncl (ρ v))) := by
    intro v
    by_cases hv : v ∈ Keep
    · rw [hρ v hv]; exact SheetPartition.Refines.refl _
    · exact hRefine v hv
  let π : D.SourceVertex → D'.SourceVertex := fun X ↦ D'.sourceEndpoint (ρ X.1.1) X.1.2
  have hπ : ∀ X : D'.SourceVertex, π (svIncl X) = X := by
    intro X
    change D'.sourceEndpoint (ρ (vIncl X.1.1)) X.1.2 = X
    rw [hρ _ (vIncl_mem X.1.1), vRestrict_vIncl]
    exact D'.sourceEndpoint_self X
  -- the image of an endpoint of a source edge, through the sheet of the edge
  have hEnd : ∀ (w : T.V) (σ : Fin d),
      π (D.sourceEndpoint w σ) = D'.sourceEndpoint (ρ w) σ := by
    intro w σ
    change D'.sourceEndpoint (ρ w) ((D.vertexPartition w).repr σ) = D'.sourceEndpoint (ρ w) σ
    exact sourceEndpoint_congr D' (ρ w)
      ((hRefine' w).rel ((D.vertexPartition w).rel_repr_left σ))
  refine graph_connected_of_map hConn π (fun X ↦ ⟨svIncl X, hπ X⟩) ?_
  intro A B hAB
  obtain ⟨E, hE⟩ := exists_sourceEnds_of_num_edges_pos D hAB
  have h1 : π (D.sourceEnds E).1 = D'.sourceEndpoint (ρ (E.1.1 : T.V × T.V).1) E.1.2 :=
    hEnd _ _
  have h2 : π (D.sourceEnds E).2 = D'.sourceEndpoint (ρ (E.1.1 : T.V × T.V).2) E.1.2 :=
    hEnd _ _
  by_cases hk : KeptEdge Keep E.1.1
  · right
    have hEnds : D'.sourceEnds (seRestrict E hk) =
        (π (D.sourceEnds E).1, π (D.sourceEnds E).2) := by
      rw [h1, h2, hρ _ hk.1, hρ _ hk.2]
      rfl
    rcases hE with hE | hE <;> rw [hE] at hEnds
    · exact num_edges_pos_of_sourceEnds D' (Or.inl hEnds)
    · exact num_edges_pos_of_sourceEnds D' (Or.inr hEnds)
  · left
    have hEq : π (D.sourceEnds E).1 = π (D.sourceEnds E).2 := by
      rw [h1, h2, hEdge _ hk]
    rcases hE with hE | hE <;> rw [hE] at hEq
    · exact hEq
    · exact hEq.symm

end Connected

/-! ## 4.  Counts -/

section Counts

variable {T : CFGraph.{0}} {d : ℕ} (D : GluingDatum T d) (Keep : Finset T.V)
  (hKeep : Keep.Nonempty)

theorem card_sourceVertex_restrictDatum :
    Fintype.card (restrictDatum D Keep hKeep).SourceVertex =
      (Finset.univ.filter fun X : D.SourceVertex ↦ X.1.1 ∈ Keep).card := by
  rw [Fintype.card_congr (svEquiv D Keep hKeep), Fintype.card_subtype]

theorem card_sourceEdge_restrictDatum :
    Fintype.card (restrictDatum D Keep hKeep).SourceEdge =
      (Finset.univ.filter fun E : D.SourceEdge ↦ KeptEdge Keep E.1.1).card := by
  classical
  rw [Fintype.card_congr (seEquiv D Keep hKeep), Fintype.card_subtype]

theorem genus_sourceGraph (D : GluingDatum T d) :
    genus D.sourceGraph = (Fintype.card D.SourceEdge : ℤ) - Fintype.card D.SourceVertex + 1 := by
  unfold genus GluingDatum.sourceGraph
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ]

/-- **The source vertices of the restriction**: those of `D` minus the blocks over deleted
vertices. -/
theorem card_sourceVertex_restrict_add :
    Fintype.card (restrictDatum D Keep hKeep).SourceVertex +
        ∑ v ∈ Keepᶜ, Fintype.card (D.vertexPartition v).Blocks =
      Fintype.card D.SourceVertex := by
  classical
  rw [GluingDatum.card_sourceVertex_eq_sum_card_blocks,
    GluingDatum.card_sourceVertex_eq_sum_card_blocks]
  have h1 : (∑ v : (restrictTarget Keep hKeep).V,
      Fintype.card ((restrictDatum D Keep hKeep).vertexPartition v).Blocks) =
      ∑ v ∈ Keep, Fintype.card (D.vertexPartition v).Blocks := by
    rw [← Finset.sum_attach Keep]
    rfl
  rw [h1, ← Finset.sum_add_sum_compl Keep]

/-- **The source edges of the restriction**: those of `D` minus the blocks over deleted
edges. -/
theorem card_sourceEdge_restrict_add :
    Fintype.card (restrictDatum D Keep hKeep).SourceEdge +
        ∑ e ∈ Finset.univ.filter (fun e : T.edges ↦ ¬ KeptEdge Keep e),
          Fintype.card (D.edgePartition e).Blocks =
      Fintype.card D.SourceEdge := by
  classical
  rw [GluingDatum.card_sourceEdge_eq_sum_card_blocks,
    GluingDatum.card_sourceEdge_eq_sum_card_blocks]
  have h1 : (∑ e : (restrictTarget Keep hKeep).edges,
      Fintype.card ((restrictDatum D Keep hKeep).edgePartition e).Blocks) =
      ∑ e ∈ Finset.univ.filter (fun e : T.edges ↦ KeptEdge Keep e),
        Fintype.card (D.edgePartition e).Blocks := by
    rw [Finset.sum_subtype (Finset.univ.filter (fun e : T.edges ↦ KeptEdge Keep e))
      (p := fun e ↦ KeptEdge Keep e) (by simp)]
    exact Fintype.sum_equiv edgeEquiv _ _ fun _ ↦ rfl
  rw [h1, Finset.sum_filter_add_sum_filter_not]

theorem card_restrictTarget_V :
    Fintype.card (restrictTarget Keep hKeep).V = Keep.card :=
  Utilities.inducedSubgraph_vertex_card T Keep hKeep

end Counts

/-! ## 4b.  The local ramification at a kept source vertex, in index form -/

section RamIndex

variable {T : CFGraph.{0}} {d : ℕ} {D : GluingDatum T d} {Keep : Finset T.V}
  {hKeep : Keep.Nonempty}

theorem sum_incidentSourceEdge_eq {S : CFGraph} {k : ℕ} (E : GluingDatum S k) (X : E.SourceVertex)
    (f : E.SourceEdge → ℤ) :
    ∑ F : IncidentSourceEdge E X, f F.1 =
      ∑ F ∈ Finset.univ.filter (fun F ↦ Incident E F X), f F := by
  classical
  refine Finset.sum_bij' (fun F _ ↦ F.1) (fun F hF ↦ ⟨F, (Finset.mem_filter.mp hF).2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro F _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.2⟩
  · intro F _; exact Finset.mem_univ _
  · intro F _; rfl
  · intro F _; rfl
  · intro F _; rfl

/-- **The local ramification after restriction, in index form**: every deleted edge `E` at
the vertex adds `m(E) - 1`. -/
theorem localRamification_restrict_index (X : (restrictDatum D Keep hKeep).SourceVertex) :
    (restrictDatum D Keep hKeep).localRamification X.1.1 ⟨X.1.2, X.2⟩ =
      D.localRamification (svIncl X).1.1 ⟨(svIncl X).1.2, (svIncl X).2⟩ +
        ∑ E ∈ Finset.univ.filter
            (fun E : D.SourceEdge ↦ Incident D E (svIncl X) ∧ ¬ KeptEdge Keep E.1.1),
          ((D.sourceEdgeIndex E : ℤ) - 1) := by
  classical
  rw [DraismaVargas.LocalCases.StableLocalProperties.localRamification_eq_index_form,
    DraismaVargas.LocalCases.StableLocalProperties.localRamification_eq_index_form,
    sum_incidentSourceEdge_eq _ _ (fun F ↦ ((restrictDatum D Keep hKeep).sourceEdgeIndex F : ℤ) - 1),
    sum_incidentSourceEdge_eq _ _ (fun F ↦ (D.sourceEdgeIndex F : ℤ) - 1)]
  have hKept : (∑ F ∈ Finset.univ.filter
      (fun F ↦ Incident (restrictDatum D Keep hKeep) F X),
        (((restrictDatum D Keep hKeep).sourceEdgeIndex F : ℤ) - 1)) =
      ∑ E ∈ Finset.univ.filter
        (fun E : D.SourceEdge ↦ Incident D E (svIncl X) ∧ KeptEdge Keep E.1.1),
        ((D.sourceEdgeIndex E : ℤ) - 1) := by
    refine Finset.sum_bij' (fun F _ ↦ seIncl F)
      (fun E hE ↦ seRestrict E (Finset.mem_filter.mp hE).2.2) ?_ ?_ ?_ ?_ ?_
    · intro F hF
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (incident_seIncl_iff F X).mpr (Finset.mem_filter.mp hF).2, seIncl_kept F⟩
    · intro E hE
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (incident_iff_seRestrict _ X).mp (Finset.mem_filter.mp hE).2.1⟩
    · intro F _; rfl
    · intro E _; rfl
    · intro F _; rfl
  rw [hKept]
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun E : D.SourceEdge ↦ Incident D E (svIncl X)))
    (fun E ↦ KeptEdge Keep E.1.1) (fun E ↦ (D.sourceEdgeIndex E : ℤ) - 1)
  rw [Finset.filter_filter, Finset.filter_filter] at hSplit
  have hb : ((restrictDatum D Keep hKeep).vertexPartition X.1.1).blockCard X.1.2 =
      (D.vertexPartition (svIncl X).1.1).blockCard (svIncl X).1.2 := rfl
  rw [hb]
  linarith

end RamIndex

/-! ## 5.  Dangling edges -/

section Dangling

open GenusSixExistence.Tripod.Gluing (wCount not_isDangling_of_witness wCount_nonDangling_ne_one
  nonDanglingValency_eq_wCount)

variable {T : CFGraph.{0}} {d : ℕ} {D : GluingDatum T d} {Keep : Finset T.V}
  {hKeep : Keep.Nonempty}

theorem wCount_or_of_disjoint {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    {W W' : E.SourceEdge → Prop} (h : ∀ e, W e → ¬ W' e) (v : E.SourceVertex) :
    wCount E (fun e ↦ W e ∨ W' e) v = wCount E W v + wCount E W' v := by
  classical
  unfold wCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_filter]
    intro e _ h1 h2
    exact h e h1.1 h2.1

theorem wCount_mono {S : CFGraph} {k : ℕ} (E : GluingDatum S k)
    {W W' : E.SourceEdge → Prop} (h : ∀ e, W e → W' e) (v : E.SourceVertex) :
    wCount E W v ≤ wCount E W' v :=
  GenusSixExistence.Tripod.Gluing.wCount_le_of_imp E v fun e _ hw ↦ h e hw

/-- Counting edges of the restriction at a vertex is counting kept edges of `D` there. -/
theorem wCount_restrict (Q : D.SourceEdge → Prop)
    (X : (restrictDatum D Keep hKeep).SourceVertex) :
    wCount (restrictDatum D Keep hKeep) (fun E ↦ Q (seIncl E)) X =
      wCount D (fun E ↦ Q E ∧ KeptEdge Keep E.1.1) (svIncl X) := by
  classical
  unfold wCount
  refine Finset.card_bij (fun E _ ↦ seIncl E) ?_ ?_ ?_
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE ⊢
    exact ⟨⟨hE.1, seIncl_kept E⟩, (incident_seIncl_iff E X).mpr hE.2⟩
  · intro _ _ _ _ h
    exact seIncl_injective h
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    refine ⟨seRestrict E hE.1.2, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, seIncl_seRestrict]
    exact ⟨hE.1.1, (incident_iff_seRestrict hE.1.2 X).mp hE.2⟩

/-- At a deleted vertex no kept edge is incident. -/
theorem wCount_kept_eq_zero (Q : D.SourceEdge → Prop) {X : D.SourceVertex} (hX : X.1.1 ∉ Keep) :
    wCount D (fun E ↦ Q E ∧ KeptEdge Keep E.1.1) X = 0 := by
  classical
  unfold wCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro E hE
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
  exact hX (target_mem_of_incident hE.1.2 hE.2)

variable (Keep) in
/-- **The lollipop hypotheses** of the dangling dictionary: the deleted surviving edges `Lol` are
the surviving edges over deleted target edges; a kept vertex meets at most one of them, and then
has surviving valency three; no deleted vertex meets exactly one. -/
structure DeletionPattern (D : GluingDatum T d) (Lol : D.SourceEdge → Prop) : Prop where
  lol_iff : ∀ E, Lol E ↔ ¬ IsDangling D E ∧ ¬ KeptEdge Keep E.1.1
  kept : ∀ X : D.SourceVertex, X.1.1 ∈ Keep →
    wCount D Lol X = 0 ∨ (wCount D Lol X = 1 ∧ nonDanglingValency D X = 3)
  deleted : ∀ X : D.SourceVertex, X.1.1 ∉ Keep → wCount D Lol X ≠ 1

variable {Lol : D.SourceEdge → Prop}

/-- The surviving valency of `D` splits into kept survivors and deleted ones. -/
theorem nonDanglingValency_split (hP : DeletionPattern Keep D Lol) (X : D.SourceVertex) :
    nonDanglingValency D X =
      wCount D (fun E ↦ ¬ IsDangling D E ∧ KeptEdge Keep E.1.1) X + wCount D Lol X := by
  rw [nonDanglingValency_eq_wCount, ← wCount_or_of_disjoint]
  · apply GenusSixExistence.Tripod.Gluing.wCount_congr
    intro E _
    rw [hP.lol_iff]
    tauto
  · intro E h1 h2
    exact ((hP.lol_iff E).mp h2).2 h1.2

/-- **Surviving in `D` implies surviving in the restriction.** -/
theorem not_isDangling_restrict_of (hD : D.Connected) (hP : DeletionPattern Keep D Lol)
    {E : (restrictDatum D Keep hKeep).SourceEdge} (h : ¬ IsDangling D (seIncl E)) :
    ¬ IsDangling (restrictDatum D Keep hKeep) E := by
  refine not_isDangling_of_witness _ (fun E ↦ ¬ IsDangling D (seIncl E)) ?_ h
  intro X
  rw [wCount_restrict (fun E ↦ ¬ IsDangling D E) X]
  have hSplit := nonDanglingValency_split hP (svIncl X)
  have hNe := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one D hD
    (svIncl X)
  rcases hP.kept (svIncl X) (svIncl_target_mem X) with h0 | ⟨h1, h3⟩ <;> omega

/-- **Surviving in the restriction implies surviving in `D`.** -/
theorem not_isDangling_of_restrict (hD : D.Connected)
    (hD' : (restrictDatum D Keep hKeep).Connected) (hP : DeletionPattern Keep D Lol)
    {E : (restrictDatum D Keep hKeep).SourceEdge}
    (h : ¬ IsDangling (restrictDatum D Keep hKeep) E) : ¬ IsDangling D (seIncl E) := by
  classical
  let W : D.SourceEdge → Prop := fun F ↦
    (KeptEdge Keep F.1.1 ∧ ∀ hk : KeptEdge Keep F.1.1,
      ¬ IsDangling (restrictDatum D Keep hKeep) (seRestrict F hk)) ∨ Lol F
  refine not_isDangling_of_witness D W ?_ (Or.inl ⟨seIncl_kept E, fun _ ↦ h⟩)
  intro X
  have hDisj : ∀ F, (KeptEdge Keep F.1.1 ∧ ∀ hk : KeptEdge Keep F.1.1,
      ¬ IsDangling (restrictDatum D Keep hKeep) (seRestrict F hk)) → ¬ Lol F :=
    fun F h1 h2 ↦ ((hP.lol_iff F).mp h2).2 h1.1
  have hW := wCount_or_of_disjoint D hDisj X
  change wCount D W X ≠ 1
  rw [hW]
  by_cases hX : X.1.1 ∈ Keep
  · set X' : (restrictDatum D Keep hKeep).SourceVertex := svRestrict X hX
    have hXX : svIncl X' = X := rfl
    have hKeptPart : wCount D (fun F ↦ KeptEdge Keep F.1.1 ∧ ∀ hk : KeptEdge Keep F.1.1,
        ¬ IsDangling (restrictDatum D Keep hKeep) (seRestrict F hk)) X =
        nonDanglingValency (restrictDatum D Keep hKeep) X' := by
      have hComm : wCount D (fun F ↦ KeptEdge Keep F.1.1 ∧ ∀ hk : KeptEdge Keep F.1.1,
          ¬ IsDangling (restrictDatum D Keep hKeep) (seRestrict F hk)) X =
          wCount D (fun F ↦ (∀ hk : KeptEdge Keep F.1.1,
            ¬ IsDangling (restrictDatum D Keep hKeep) (seRestrict F hk)) ∧
              KeptEdge Keep F.1.1) (svIncl X') :=
        GenusSixExistence.Tripod.Gluing.wCount_congr _ _ fun F _ ↦ and_comm
      rw [hComm, ← wCount_restrict (fun F ↦ ∀ hk : KeptEdge Keep F.1.1,
          ¬ IsDangling (restrictDatum D Keep hKeep) (seRestrict F hk)) X',
        nonDanglingValency_eq_wCount]
      apply GenusSixExistence.Tripod.Gluing.wCount_congr
      intro F _
      simp only [seRestrict_seIncl]
      exact ⟨fun h' ↦ h' (seIncl_kept F), fun h' _ ↦ h'⟩
    rw [hKeptPart]
    have hNe' := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hD' X'
    have hLower : wCount D (fun E ↦ ¬ IsDangling D E ∧ KeptEdge Keep E.1.1) X ≤
        nonDanglingValency (restrictDatum D Keep hKeep) X' := by
      rw [← hXX, ← wCount_restrict (fun E ↦ ¬ IsDangling D E) X', nonDanglingValency_eq_wCount]
      exact wCount_mono _ (fun F hF ↦ not_isDangling_restrict_of hD hP hF) X'
    have hSplit := nonDanglingValency_split hP X
    rcases hP.kept X hX with h0 | ⟨h1, h3⟩ <;> omega
  · rw [show wCount D (fun F ↦ KeptEdge Keep F.1.1 ∧ ∀ hk : KeptEdge Keep F.1.1,
        ¬ IsDangling (restrictDatum D Keep hKeep) (seRestrict F hk)) X = 0 by
      rw [← wCount_kept_eq_zero (fun F ↦ ∀ hk : KeptEdge Keep F.1.1,
        ¬ IsDangling (restrictDatum D Keep hKeep) (seRestrict F hk)) hX]
      apply GenusSixExistence.Tripod.Gluing.wCount_congr
      intro F _
      exact ⟨fun ⟨a, b⟩ ↦ ⟨b, a⟩, fun ⟨a, b⟩ ↦ ⟨b, a⟩⟩, zero_add]
    exact hP.deleted X hX

/-- **The dangling dictionary.** -/
theorem isDangling_restrict_iff (hD : D.Connected)
    (hD' : (restrictDatum D Keep hKeep).Connected) (hP : DeletionPattern Keep D Lol)
    (E : (restrictDatum D Keep hKeep).SourceEdge) :
    IsDangling (restrictDatum D Keep hKeep) E ↔ IsDangling D (seIncl E) := by
  constructor
  · intro h
    by_contra h'
    exact not_isDangling_restrict_of hD hP h' h
  · intro h
    by_contra h'
    exact not_isDangling_of_restrict hD hD' hP h' h

/-- **The surviving valency after restriction.** -/
theorem nonDanglingValency_restrict (hD : D.Connected)
    (hD' : (restrictDatum D Keep hKeep).Connected) (hP : DeletionPattern Keep D Lol)
    (X : (restrictDatum D Keep hKeep).SourceVertex) :
    nonDanglingValency (restrictDatum D Keep hKeep) X + wCount D Lol (svIncl X) =
      nonDanglingValency D (svIncl X) := by
  rw [nonDanglingValency_split hP, nonDanglingValency_eq_wCount,
    ← wCount_restrict (fun E ↦ ¬ IsDangling D E) X]
  congr 1
  apply GenusSixExistence.Tripod.Gluing.wCount_congr
  intro E _
  exact (not_congr (isDangling_restrict_iff hD hD' hP E))

end Dangling

/-! ## 6.  Rows -/

section Quot

/-- **A quotient restricted to a saturated subset** is the subset of the quotient. -/
def quotSubtypeEquiv {α : Type*} (r : α → α → Prop) (P : α → Prop)
    (hP : ∀ a b, r a b → (P a ↔ P b)) :
    Quot (fun a b : Subtype P ↦ r a.1 b.1) ≃
      {q : Quot r // Quot.lift P (fun a b h ↦ propext (hP a b h)) q} := by
  classical
  have key : ∀ x y, Relation.EqvGen r x y → (P x ↔ P y) ∧
      ∀ hx hy, Relation.EqvGen (fun a b : Subtype P ↦ r a.1 b.1) ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x y h
    induction h with
    | rel x y h => exact ⟨hP x y h, fun _ _ ↦ Relation.EqvGen.rel _ _ h⟩
    | refl x => exact ⟨Iff.rfl, fun _ _ ↦ Relation.EqvGen.refl _⟩
    | symm x y _ ih => exact ⟨ih.1.symm, fun hx hy ↦ Relation.EqvGen.symm _ _ (ih.2 hy hx)⟩
    | trans x y z _ _ ih₁ ih₂ =>
      exact ⟨ih₁.1.trans ih₂.1, fun hx hz ↦
        Relation.EqvGen.trans _ _ _ (ih₁.2 hx (ih₁.1.mp hx)) (ih₂.2 _ hz)⟩
  have hOut : ∀ q : Quot r, Quot.lift P (fun a b h ↦ propext (hP a b h)) q → P q.out := by
    intro q hq
    rw [← Quot.out_eq q] at hq
    exact hq
  exact {
    toFun := Quot.lift (fun a ↦ ⟨Quot.mk r a.1, a.2⟩) (fun a b h ↦ Subtype.ext (Quot.sound h))
    invFun := fun q ↦ Quot.mk _ ⟨q.1.out, hOut q.1 q.2⟩
    left_inv := by
      intro x
      induction x using Quot.ind with
      | mk a =>
        apply Quot.eqvGen_sound
        exact (key _ _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk r a.1)))).2 _ _
    right_inv := by
      intro q
      apply Subtype.ext
      exact Quot.out_eq q.1 }

end Quot

section Rows

variable {T : CFGraph.{0}} {d : ℕ} {D : GluingDatum T d} {Keep : Finset T.V}
  {hKeep : Keep.Nonempty} {Lol : D.SourceEdge → Prop}
  (hD : D.Connected) (hD' : (restrictDatum D Keep hKeep).Connected)
  (hP : DeletionPattern Keep D Lol)

include hD hD' hP in
/-- A survivor of the restriction, read in `D`. -/
def ndIncl (E : NonDanglingEdge (restrictDatum D Keep hKeep)) : NonDanglingEdge D :=
  ⟨seIncl E.1, not_isDangling_of_restrict hD hD' hP E.2⟩

include hD hP in
/-- A kept survivor of `D`, read in the restriction. -/
def ndRestrict (F : NonDanglingEdge D) (hk : KeptEdge Keep F.1.1.1) :
    NonDanglingEdge (restrictDatum D Keep hKeep) :=
  ⟨seRestrict F.1 hk, not_isDangling_restrict_of hD hP (by rw [seIncl_seRestrict]; exact F.2)⟩

/-- **The survivor dictionary.** -/
def ndEquiv : NonDanglingEdge (restrictDatum D Keep hKeep) ≃
    {F : NonDanglingEdge D // KeptEdge Keep F.1.1.1} where
  toFun E := ⟨ndIncl hD hD' hP E, seIncl_kept E.1⟩
  invFun F := ndRestrict hD hP F.1 F.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem ndIncl_val (E : NonDanglingEdge (restrictDatum D Keep hKeep)) :
    (ndIncl hD hD' hP E).1 = seIncl E.1 := rfl

theorem ndIncl_injective : Function.Injective (ndIncl hD hD' hP) := by
  intro E F h
  exact Subtype.ext (seIncl_injective (congrArg Subtype.val h))

include hP in
/-- **Kept-ness is constant along stable paths.** -/
theorem keptEdge_iff_of_consecutive {F G : NonDanglingEdge D} (h : Consecutive D F G) :
    KeptEdge Keep F.1.1.1 ↔ KeptEdge Keep G.1.1.1 := by
  classical
  obtain ⟨-, X, hF, hG, h2⟩ := h
  have key : ∀ {A B : NonDanglingEdge D}, Incident D A.1 X → Incident D B.1 X →
      KeptEdge Keep A.1.1.1 → KeptEdge Keep B.1.1.1 := by
    intro A B hA hB hk
    by_contra hnk
    have hX := target_mem_of_incident hk hA
    have hLol : Lol B.1 := (hP.lol_iff B.1).mpr ⟨B.2, hnk⟩
    have hPos : 1 ≤ GenusSixExistence.Tripod.Gluing.wCount D Lol X := by
      unfold GenusSixExistence.Tripod.Gluing.wCount
      exact Finset.card_pos.mpr ⟨B.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLol, hB⟩⟩
    rcases hP.kept X hX with h0 | ⟨-, h3⟩ <;> omega
  exact ⟨key hF hG, key hG hF⟩

/-- A stable path of `D` all of whose survivors are kept. -/
def KeptRow (hP : DeletionPattern Keep D Lol) : StablePath D → Prop :=
  Quot.lift (fun F : NonDanglingEdge D ↦ KeptEdge Keep F.1.1.1)
    (fun _ _ h ↦ propext (keptEdge_iff_of_consecutive hP h))

theorem keptRow_mk (F : NonDanglingEdge D) :
    KeptRow hP (NonDanglingEdge.stablePath F) ↔ KeptEdge Keep F.1.1.1 := Iff.rfl

include hD hD' in
/-- **Marked consecutiveness is consecutiveness in `D`**, when the marks are exactly the
divalent vertices of the restriction that were not divalent in `D`. -/
theorem markedConsecutive_iff (marks : Finset (restrictDatum D Keep hKeep).SourceVertex)
    (hMarks : ∀ X : (restrictDatum D Keep hKeep).SourceVertex,
      (nonDanglingValency (restrictDatum D Keep hKeep) X = 2 ∧ X ∉ marks) ↔
        nonDanglingValency D (svIncl X) = 2)
    (E F : NonDanglingEdge (restrictDatum D Keep hKeep)) :
    MarkedConsecutive (restrictDatum D Keep hKeep) marks E F ↔
      Consecutive D (ndIncl hD hD' hP E) (ndIncl hD hD' hP F) := by
  constructor
  · rintro ⟨hne, X, hE, hF, h2, hX⟩
    exact ⟨fun h ↦ hne (ndIncl_injective hD hD' hP h), svIncl X,
      (incident_seIncl_iff _ _).mpr hE, (incident_seIncl_iff _ _).mpr hF,
      (hMarks X).mp ⟨h2, hX⟩⟩
  · rintro ⟨hne, X, hE, hF, h2⟩
    have hX := target_mem_of_incident (seIncl_kept E.1) hE
    have h2' := (hMarks (svRestrict X hX)).mpr h2
    refine ⟨fun h ↦ hne (by rw [h]), svRestrict X hX, ?_, ?_, h2'.1, h2'.2⟩
    · exact (incident_seIncl_iff _ _).mp hE
    · exact (incident_seIncl_iff _ _).mp hF

/-- **The marked rows of the restriction are the kept stable paths of `D`.** -/
def markedRowEquiv (marks : Finset (restrictDatum D Keep hKeep).SourceVertex)
    (hMarks : ∀ X : (restrictDatum D Keep hKeep).SourceVertex,
      (nonDanglingValency (restrictDatum D Keep hKeep) X = 2 ∧ X ∉ marks) ↔
        nonDanglingValency D (svIncl X) = 2) :
    MarkedStablePath (restrictDatum D Keep hKeep) marks ≃ {r : StablePath D // KeptRow hP r} :=
  (Quot.congr (ndEquiv hD hD' hP) fun E F ↦ markedConsecutive_iff hD hD' hP marks hMarks E F).trans
    (quotSubtypeEquiv (Consecutive D) (fun F ↦ KeptEdge Keep F.1.1.1)
      (fun _ _ h ↦ keptEdge_iff_of_consecutive hP h))

theorem markedRowEquiv_markedRow (marks : Finset (restrictDatum D Keep hKeep).SourceVertex)
    (hMarks : ∀ X : (restrictDatum D Keep hKeep).SourceVertex,
      (nonDanglingValency (restrictDatum D Keep hKeep) X = 2 ∧ X ∉ marks) ↔
        nonDanglingValency D (svIncl X) = 2)
    (E : NonDanglingEdge (restrictDatum D Keep hKeep)) :
    (markedRowEquiv hD hD' hP marks hMarks (markedRow marks E)).1 =
      NonDanglingEdge.stablePath (ndIncl hD hD' hP E) := rfl

end Rows

/-! ## 7.  Entries of a marked length matrix -/

section MarkedMatrix

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {marks : Finset data.SourceVertex} {coordinate : Type*} [DecidableEq coordinate]

/-- The occurrences of one marked row over one target edge. -/
def markedRowFibre (L : MarkedLabelling data marks coordinate) (r : coordinate)
    (item : target.edges) : Finset data.SourceEdge := by
  classical
  exact Finset.univ.filter fun e ↦
    (∃ h : ¬ IsDangling data e, L.row (markedRow marks (⟨e, h⟩ : NonDanglingEdge data)) = r) ∧
      e.1.1 = item

theorem mem_markedRowFibre (L : MarkedLabelling data marks coordinate) (r : coordinate)
    (item : target.edges) (e : data.SourceEdge) :
    e ∈ markedRowFibre L r item ↔
      (∃ h : ¬ IsDangling data e, L.row (markedRow marks (⟨e, h⟩ : NonDanglingEdge data)) = r) ∧
        e.1.1 = item := by
  classical
  simp [markedRowFibre]

/-- **One entry of a marked length matrix** is the sum of reciprocal indices over the fibre. -/
theorem markedMatrix_eq_sum (L : MarkedLabelling data marks coordinate) (r : coordinate)
    (item : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix L.presentation r (L.targetEdge.symm item) =
      ∑ e ∈ markedRowFibre L r item, (1 : ℚ) / data.sourceEdgeIndex e := by
  classical
  have hNodup : (L.path r).Nodup := by
    unfold MarkedLabelling.path
    exact List.Nodup.filter _ (Finset.univ.nodup_toList)
  have hToFinset : (L.path r).toFinset = Finset.univ.filter (fun e : data.SourceEdge ↦
      ∃ h : ¬ IsDangling data e, L.row (markedRow marks (⟨e, h⟩ : NonDanglingEdge data)) = r) := by
    ext e
    simp [MarkedLabelling.path]
  calc
    GluingDatum.LengthMatrixPresentation.matrix L.presentation r (L.targetEdge.symm item)
        = ((L.path r).map fun e ↦
            GluingDatum.LengthMatrixPresentation.coefficient L.presentation e
              (L.targetEdge.symm item)).sum := rfl
    _ = ∑ e ∈ (L.path r).toFinset,
          GluingDatum.LengthMatrixPresentation.coefficient L.presentation e
            (L.targetEdge.symm item) := (List.sum_toFinset _ hNodup).symm
    _ = ∑ e ∈ markedRowFibre L r item, (1 : ℚ) / data.sourceEdgeIndex e := by
        rw [hToFinset]
        have hF : markedRowFibre L r item = (Finset.univ.filter (fun e : data.SourceEdge ↦
            ∃ h : ¬ IsDangling data e,
              L.row (markedRow marks (⟨e, h⟩ : NonDanglingEdge data)) = r)).filter
            (fun e ↦ e.1.1 = item) := by
          ext e
          rw [mem_markedRowFibre]
          simp
        rw [hF]
        conv_rhs => rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases hCase : e.1.1 = item
        · rw [ite_eq_left hCase]
          simp [GluingDatum.LengthMatrixPresentation.coefficient, MarkedLabelling.presentation,
            hCase]
        · rw [ite_eq_right hCase]
          apply GluingDatum.LengthMatrixPresentation.coefficient_eq_zero_of_target_ne
          simp only [MarkedLabelling.presentation, Equiv.apply_symm_apply]
          exact fun h ↦ hCase h.symm

end MarkedMatrix


/-! ## 8.  Restricting an isomorphism of data -/

section Iso

variable {T₁ T₂ : CFGraph.{0}} {d : ℕ} {D₁ : GluingDatum T₁ d} {D₂ : GluingDatum T₂ d}
  {K₁ : Finset T₁.V} {K₂ : Finset T₂.V} {h₁ : K₁.Nonempty} {h₂ : K₂.Nonempty}

theorem keptEdge_map (Φ : GeometricDatumIso D₁ D₂) (hK : ∀ v, Φ.targetVertex v ∈ K₂ ↔ v ∈ K₁)
    (e : T₁.edges) : KeptEdge K₂ (Φ.targetEdge e) ↔ KeptEdge K₁ e := by
  unfold KeptEdge
  rcases Φ.ends e with h | h <;> rw [h] <;> simp only [hK]
  exact and_comm

/-- **An isomorphism of data carrying kept vertices to kept vertices restricts.** -/
def restrictIso (Φ : GeometricDatumIso D₁ D₂)
    (hK : ∀ v, Φ.targetVertex v ∈ K₂ ↔ v ∈ K₁) :
    GeometricDatumIso (restrictDatum D₁ K₁ h₁) (restrictDatum D₂ K₂ h₂) where
  targetVertex :=
    { toFun := fun v ↦ vRestrict (Φ.targetVertex (vIncl v)) ((hK _).mpr (vIncl_mem v))
      invFun := fun w ↦ vRestrict (Φ.targetVertex.symm (vIncl w))
        ((hK _).mp (by rw [Equiv.apply_symm_apply]; exact vIncl_mem w))
      left_inv := fun v ↦ vIncl_injective (by simp)
      right_inv := fun w ↦ vIncl_injective (by simp) }
  targetEdge :=
    { toFun := fun e ↦ edgeRestrict (Φ.targetEdge (edgeIncl e))
        ((keptEdge_map Φ hK _).mpr (keptEdge_edgeIncl e))
      invFun := fun e ↦ edgeRestrict (Φ.targetEdge.symm (edgeIncl e))
        ((keptEdge_map Φ hK _).mp (by rw [Equiv.apply_symm_apply]; exact keptEdge_edgeIncl e))
      left_inv := fun e ↦ edgeIncl_injective (Φ.targetEdge.symm_apply_apply (edgeIncl e))
      right_inv := fun e ↦ edgeIncl_injective (Φ.targetEdge.apply_symm_apply (edgeIncl e)) }
  ends e := by
    rcases Φ.ends (edgeIncl e) with h | h
    · left
      apply Prod.ext <;> apply vIncl_injective
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    · right
      apply Prod.ext <;> apply vIncl_injective
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
  vertexPerm v := Φ.vertexPerm (vIncl v)
  edgePerm e := Φ.edgePerm (edgeIncl e)
  vertexPartition v := Φ.vertexPartition (vIncl v)
  edgePartition e := Φ.edgePartition (edgeIncl e)
  compatible e v hv := Φ.compatible (edgeIncl e) (vIncl v) (by
    rcases hv with h | h
    · left; rw [edgeIncl_fst, h]
    · right; rw [edgeIncl_snd, h])

theorem svIncl_restrictIso (Φ : GeometricDatumIso D₁ D₂)
    (hK : ∀ v, Φ.targetVertex v ∈ K₂ ↔ v ∈ K₁) (X : (restrictDatum D₁ K₁ h₁).SourceVertex) :
    svIncl ((restrictIso (h₁ := h₁) (h₂ := h₂) Φ hK).sourceVertexEquiv X) =
      Φ.sourceVertexEquiv (svIncl X) := rfl

theorem seIncl_restrictIso (Φ : GeometricDatumIso D₁ D₂)
    (hK : ∀ v, Φ.targetVertex v ∈ K₂ ↔ v ∈ K₁) (E : (restrictDatum D₁ K₁ h₁).SourceEdge) :
    seIncl ((restrictIso (h₁ := h₁) (h₂ := h₂) Φ hK).sourceEdgeEquiv E) =
      Φ.sourceEdgeEquiv (seIncl E) := rfl

end Iso

end

end DraismaVargas.Count.MarkedCount.Restrict
