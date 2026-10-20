module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailCount
public import DraismaVargasMarkedCount.MarkedCountGeneral.Sheets

@[expose] public section

/-!
# Restriction over the tails: the components of the restriction

Over the kept target vertices, the restricted datum `D₀ = rData` has one component carrying the
core of the marked core, and further components which are index-one copies of `T'` (**lone
sheets**). This module proves the half of that statement the restriction needs:

* the deletion pattern, as in the ramification-one count (`deletionPattern`): the only deleted
  survivor at a kept vertex is the first path edge at a mark;
* **(a)** (`reach_of_survivors`): any two vertices over `T'` carrying survivors are joined in `D₀`.
  The proof follows a walk of the connected source; an excursion into the tails or into a pendant
  tree comes back through the vertex it left by (the pendant-side confinement of
  `DanglingSideStructure`), so the walk can be read in `D₀`. No connectedness of the marked core
  is used: it follows from the frame.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

/-! ## 1.  Generic facts about source graphs -/

section Generic

variable {target : CFGraph} {d : ℕ} (D : GluingDatum target d)

/-- Two ends of one source edge are joined. -/
theorem reach_of_incident {E : D.SourceEdge} {X Y : D.SourceVertex} (hX : Incident D E X)
    (hY : Incident D E Y) : Reach D.sourceGraph X Y := by
  by_cases hXY : X = Y
  · rw [hXY]; exact reach_refl _ _
  · refine reach_single (num_edges_pos_of_sourceEnds D (edge := E) ?_)
    rcases hX with hX | hX <;> rcases hY with hY | hY
    · exact absurd (hX.symm.trans hY) hXY
    · exact Or.inl (Prod.ext hX hY)
    · exact Or.inr (Prod.ext hY hX)
    · exact absurd (hX.symm.trans hY) hXY

/-- The ends of a source edge joining `a` and `b`. -/
theorem incident_of_sourceEnds {E : D.SourceEdge} {a b : D.SourceVertex}
    (h : D.sourceEnds E = (a, b) ∨ D.sourceEnds E = (b, a)) :
    Incident D E a ∧ Incident D E b := by
  rcases h with h | h
  · exact ⟨Or.inl (congrArg Prod.fst h), Or.inr (congrArg Prod.snd h)⟩
  · exact ⟨Or.inr (congrArg Prod.snd h), Or.inl (congrArg Prod.fst h)⟩

/-- **A dangling edge at a non-dangling vertex has its pendant side away from it.** -/
theorem exists_pendant_away {E : D.SourceEdge} (hE : IsDangling D E) {a b : D.SourceVertex}
    (h : D.sourceEnds E = (a, b) ∨ D.sourceEnds E = (b, a)) (ha : nonDanglingValency D a ≠ 0) :
    Nonempty (DanglingSide D.sourceGraph b a) := by
  rcases NonDanglingValency.danglingSide_of_isDangling D h hE with ⟨⟨cut⟩⟩ | ⟨⟨cut⟩⟩
  · exact absurd (DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side D cut cut.left_mem) ha
  · exact ⟨cut⟩

/-- A step out of a pendant side lands on its outer end. -/
theorem eq_outer_of_step {inner outer : D.SourceVertex}
    (cut : DanglingSide D.sourceGraph inner outer) {a b : D.SourceVertex} (ha : a ∈ cut.side)
    (hab : 0 < num_edges D.sourceGraph a b) (hb : b ∉ cut.side) : b = outer := by
  have h := cut.cross_num_edges a b ha hb
  by_contra hne
  rw [ite_eq_right (fun hPair ↦ hne hPair.2)] at h
  omega

end Generic

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree)

/-! ## 2.  The deletion pattern -/

/-- The deleted survivors: survivors over deleted target edges. -/
def Lol (E : M.data.SourceEdge) : Prop :=
  ¬ IsDangling M.data E ∧ ¬ KeptEdge (Keep T M) E.1.1

theorem uSource_incident_pathE (j : Fin k) :
    Incident M.data (TailAt.pathE (cat T j) M (T.cubic hc) 0).1 (uSource T M j) := by
  have h := TailAt.pathE_incident_tail (cat T j) M (T.cubic hc) 0
  rwa [(cat T j).tail_path_zero] at h

/-- **A deleted survivor at a kept vertex is the first path edge at a mark.** -/
theorem eq_pathE_of_lol {X : M.data.SourceVertex} (hX : X.1.1 ∈ Keep T M) {E : M.data.SourceEdge}
    (hE : Lol T M E) (hInc : Incident M.data E X) :
    ∃ j, E = (TailAt.pathE (cat T j) M (T.cubic hc) 0).1 ∧ X = uSource T M j := by
  have hMem := SpineStep.target_mem_of_incident hInc
  obtain ⟨j, hj, hjx⟩ := eq_tEdge_zero_of_kept T hc M hX hMem hE.2
  have hEq := TailAt.eq_pathE_of_over (cat T j) M (T.cubic hc) 0 hE.1 hj
  subst hEq
  refine ⟨j, rfl, ?_⟩
  exact LollipopBridgeFibre.eq_of_incident_of_target_eq hjx.symm hInc
    (uSource_incident_pathE T hc M j) |>.symm.symm

theorem uSource_injective (hc : IsMarkedCubic core mark) : Function.Injective (uSource T M) := by
  intro i j h
  have := TailAt.vSource_injective M h
  exact hc.injective (Sum.inl_injective (T.vertexEquiv.injective this))

include hc in
open GenusSixExistence.Tripod.Gluing (wCount) in
theorem wCount_lol_kept {X : M.data.SourceVertex} (hX : X.1.1 ∈ Keep T M) :
    wCount M.data (Lol T M) X = 0 ∨
      (wCount M.data (Lol T M) X = 1 ∧ nonDanglingValency M.data X = 3) := by
  classical
  by_cases h : ∃ E, Lol T M E ∧ Incident M.data E X
  · obtain ⟨E, hE, hI⟩ := h
    obtain ⟨j, rfl, rfl⟩ := eq_pathE_of_lol T hc M hX hE hI
    right
    refine ⟨?_, nonDanglingValency_uSource T M j⟩
    unfold wCount
    rw [Finset.card_eq_one]
    refine ⟨(TailAt.pathE (cat T j) M (T.cubic hc) 0).1, ?_⟩
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hF, hFI⟩
      obtain ⟨i, rfl, hi⟩ := eq_pathE_of_lol T hc M hX hF hFI
      rw [uSource_injective T M hc hi]
    · rintro rfl; exact ⟨hE, hI⟩
  · left
    push Not at h
    unfold wCount
    rw [Finset.card_eq_zero]
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_and]
    exact h F

open GenusSixExistence.Tripod.Gluing (wCount nonDanglingValency_eq_wCount) in
/-- At a deleted vertex every incident edge is deleted, so the deleted survivors there are all
the survivors. -/
theorem wCount_lol_deleted {X : M.data.SourceVertex} (hX : X.1.1 ∉ Keep T M) :
    wCount M.data (Lol T M) X = nonDanglingValency M.data X := by
  rw [nonDanglingValency_eq_wCount]
  apply GenusSixExistence.Tripod.Gluing.wCount_congr
  intro E hE
  have hk : ¬ KeptEdge (Keep T M) E.1.1 := fun h ↦ hX (target_mem_of_incident h hE)
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hk⟩⟩

include hc in
/-- **The deletion pattern** of the ramification-one `Restrict.DeletionPattern`. -/
theorem deletionPattern : DeletionPattern (Keep T M) M.data (Lol T M) where
  lol_iff _ := Iff.rfl
  kept X hX := wCount_lol_kept T hc M hX
  deleted X hX := by
    rw [wCount_lol_deleted T M hX]
    exact NonDanglingValency.nonDanglingValency_ne_one M.data M.fullDim.connected X

/-! ## 3.  (a) The survivors over `T'` are joined in `D₀` -/

/-- A vertex over `T'` with a survivor, joined in `D₀` to the restriction of `X₀`. -/
def RegR (X₀ : M.data.SourceVertex) (hX₀ : X₀.1.1 ∈ Keep T M) (Z : M.data.SourceVertex) : Prop :=
  ∃ h : Z.1.1 ∈ Keep T M, 0 < nonDanglingValency M.data Z ∧
    Reach (rData T hc M).sourceGraph (svRestrict X₀ hX₀) (svRestrict Z h)

/-- A vertex over the tail at `j` with a survivor, the mark `u_j` being reached. -/
def RegTC (X₀ : M.data.SourceVertex) (hX₀ : X₀.1.1 ∈ Keep T M) (Z : M.data.SourceVertex) : Prop :=
  ∃ j, (∃ t, tailVertex T M ⟨j, t⟩ = Z.1.1) ∧ 0 < nonDanglingValency M.data Z ∧
    RegR T hc M X₀ hX₀ (uSource T M j)

/-- A vertex of a pendant side hanging from the region. -/
def RegPend (X₀ : M.data.SourceVertex) (hX₀ : X₀.1.1 ∈ Keep T M) (Z : M.data.SourceVertex) : Prop :=
  ∃ (inner outer : M.data.SourceVertex) (cut : DanglingSide M.data.sourceGraph inner outer),
    Z ∈ cut.side ∧ (RegR T hc M X₀ hX₀ outer ∨ RegTC T hc M X₀ hX₀ outer)

theorem reach_rData_of_kept {E : M.data.SourceEdge} (hk : KeptEdge (Keep T M) E.1.1)
    {a b : M.data.SourceVertex} (ha : Incident M.data E a) (hb : Incident M.data E b)
    (ha' : a.1.1 ∈ Keep T M) (hb' : b.1.1 ∈ Keep T M) :
    Reach (rData T hc M).sourceGraph (svRestrict a ha') (svRestrict b hb') :=
  reach_of_incident _ (E := seRestrict E hk)
    ((incident_iff_seRestrict hk (svRestrict a ha')).mp ha)
    ((incident_iff_seRestrict hk (svRestrict b hb')).mp hb)

/-- The tail ends of a tail survivor: the mark or a tail vertex. -/
theorem end_of_tail_survivor {j : Fin k} {s : CatSlot (c j)} {E : M.data.SourceEdge}
    (hE : ¬ IsDangling M.data E) (hT : E.1.1 = tEdge T hc M j s) {Z : M.data.SourceVertex}
    (hZ : Incident M.data E Z) :
    Z = uSource T M j ∨ ∃ t, tailVertex T M ⟨j, t⟩ = Z.1.1 := by
  have hMem : tEdge T hc M j s ∈ GluingDatum.incidentEdges Z.1.1 := hT ▸ SpineStep.target_mem_of_incident hZ
  rcases inTail_of_mem_tEdge T hc M j s hMem with h | h
  · left
    have hKeep : Z.1.1 ∈ Keep T M := h ▸ xMark_mem_Keep T hc M j
    obtain ⟨i, hEi, hZi⟩ := eq_pathE_of_lol T hc M hKeep ⟨hE, hT ▸ not_keptEdge_tEdge T hc M j s⟩ hZ
    have hti : E.1.1 = tEdge T hc M i (Sum.inl 0) := by rw [hEi]; rfl
    have hq := tailEdge_injective T hc M (a₁ := ⟨i, Sum.inl 0⟩) (a₂ := ⟨j, s⟩) (hti.symm.trans hT)
    have hij : i = j := congrArg Sigma.fst hq
    rw [hZi, hij]
  · exact Or.inr h

/-- **The step of the walk.** -/
theorem reg_step (X₀ : M.data.SourceVertex) (hX₀ : X₀.1.1 ∈ Keep T M) {a b : M.data.SourceVertex}
    (hab : 0 < num_edges M.data.sourceGraph a b)
    (ha : RegR T hc M X₀ hX₀ a ∨ RegTC T hc M X₀ hX₀ a ∨ RegPend T hc M X₀ hX₀ a) :
    RegR T hc M X₀ hX₀ b ∨ RegTC T hc M X₀ hX₀ b ∨ RegPend T hc M X₀ hX₀ b := by
  obtain ⟨E, hEnds⟩ := exists_sourceEnds_of_num_edges_pos M.data hab
  obtain ⟨hEa, hEb⟩ := incident_of_sourceEnds M.data hEnds
  rcases ha with hR | hTC | hP
  · obtain ⟨haK, haNd, haReach⟩ := hR
    by_cases hES : IsDangling M.data E
    · obtain ⟨cut⟩ := exists_pendant_away M.data hES hEnds haNd.ne'
      exact Or.inr (Or.inr ⟨b, a, cut, cut.left_mem, Or.inl ⟨haK, haNd, haReach⟩⟩)
    · have hbNd := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hES hEb
      by_cases hk : KeptEdge (Keep T M) E.1.1
      · have hbK := target_mem_of_incident hk hEb
        exact Or.inl ⟨hbK, hbNd,
          reach_trans haReach (reach_rData_of_kept T hc M hk hEa hEb haK hbK)⟩
      · obtain ⟨j, hE, haj⟩ := eq_pathE_of_lol T hc M haK ⟨hES, hk⟩ hEa
        have hT : E.1.1 = tEdge T hc M j (Sum.inl 0) := by rw [hE]; rfl
        have hRu : RegR T hc M X₀ hX₀ (uSource T M j) := haj ▸ ⟨haK, haNd, haReach⟩
        rcases end_of_tail_survivor T hc M hES hT hEb with hbU | ⟨t, ht⟩
        · exact Or.inl (hbU ▸ hRu)
        · exact Or.inr (Or.inl ⟨j, ⟨t, ht⟩, hbNd, hRu⟩)
  · obtain ⟨j, ⟨t, ht⟩, haNd, hu⟩ := hTC
    by_cases hES : IsDangling M.data E
    · obtain ⟨cut⟩ := exists_pendant_away M.data hES hEnds haNd.ne'
      exact Or.inr (Or.inr ⟨b, a, cut, cut.left_mem, Or.inr ⟨j, ⟨t, ht⟩, haNd, hu⟩⟩)
    · have hbNd := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hES hEb
      have hnk : ¬ KeptEdge (Keep T M) E.1.1 := fun h ↦
        tailVertex_notMem_Keep T M ⟨j, t⟩ (ht ▸ target_mem_of_incident h hEa)
      obtain ⟨j', s', hj'⟩ := (not_keptEdge_iff T hc M _).mp hnk
      have hjj : j' = j := by
        have hMem : tEdge T hc M j' s' ∈ GluingDatum.incidentEdges a.1.1 :=
          hj' ▸ SpineStep.target_mem_of_incident hEa
        rcases inTail_of_mem_tEdge T hc M j' s' hMem with h | ⟨t', ht'⟩
        · have hK : tailVertex T M ⟨j, t⟩ ∈ Keep T M := by
            rw [ht, h]; exact xMark_mem_Keep T hc M j'
          exact absurd hK (tailVertex_notMem_Keep T M ⟨j, t⟩)
        · exact congrArg Sigma.fst (tailVertex_injective T hc M (ht'.trans ht.symm))
      subst hjj
      rcases end_of_tail_survivor T hc M hES hj' hEb with hbU | ⟨t', ht'⟩
      · exact Or.inl (hbU ▸ hu)
      · exact Or.inr (Or.inl ⟨j', ⟨t', ht'⟩, hbNd, hu⟩)
  · obtain ⟨inner, outer, cut, ha, hO⟩ := hP
    by_cases hb : b ∈ cut.side
    · exact Or.inr (Or.inr ⟨inner, outer, cut, hb, hO⟩)
    · have := eq_outer_of_step M.data cut ha hab hb
      subst this
      rcases hO with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- **(a): any two vertices over `T'` with survivors are joined in `D₀`.** -/
theorem reach_of_survivors {X Y : M.data.SourceVertex} (hX : X.1.1 ∈ Keep T M)
    (hY : Y.1.1 ∈ Keep T M) (hXnd : 0 < nonDanglingValency M.data X)
    (hYnd : 0 < nonDanglingValency M.data Y) :
    Reach (rData T hc M).sourceGraph (svRestrict X hX) (svRestrict Y hY) := by
  have hWalk := reach_of_graph_connected M.fullDim.connected X Y
  have hQ := reach_propagate
    (motive := fun Z ↦ RegR T hc M X hX Z ∨ RegTC T hc M X hX Z ∨ RegPend T hc M X hX Z)
    (Or.inl ⟨hX, hXnd, reach_refl _ _⟩) (fun a b hab ha ↦ reg_step T hc M X hX hab ha) hWalk
  rcases hQ with ⟨h', -, hR⟩ | ⟨j, ⟨t, ht⟩, -, -⟩ | ⟨inner, outer, cut, hYs, -⟩
  · exact hR
  · exact absurd (ht ▸ hY) (tailVertex_notMem_Keep T M ⟨j, t⟩)
  · have := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side M.data cut hYs
    omega

/-! ## 4.  Sheet traces, and (b): a component without survivors is a lone sheet -/

/-- The vertex of sheet `σ` over a kept vertex. -/
abbrev trace (σ : Fin degree) (v : (rTarget T hc M).V) : (rData T hc M).SourceVertex :=
  (rData T hc M).sourceEndpoint v σ

/-- **A sheet's trace is connected**: `T'` is connected. -/
theorem reach_trace (σ : Fin degree) (v w : (rTarget T hc M).V) :
    Reach (rData T hc M).sourceGraph (trace T hc M σ v) (trace T hc M σ w) := by
  have hT := reach_of_graph_connected (rTarget_connected T hc M) v w
  refine reach_propagate (motive := fun w ↦ Reach (rData T hc M).sourceGraph (trace T hc M σ v)
    (trace T hc M σ w)) (reach_refl _ _) (fun a b hab ha ↦ ?_) hT
  obtain ⟨pair, hPair, hEnds⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos _ a b hab
  let e : (rTarget T hc M).edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hPair⟩⟩
  have hea : e ∈ GluingDatum.incidentEdges a := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change pair.1 = a ∨ pair.2 = a
    rcases hEnds with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have heb : e ∈ GluingDatum.incidentEdges b := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change pair.1 = b ∨ pair.2 = b
    rcases hEnds with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl rfl
  refine reach_trans ha (reach_of_incident _ (E := (rData T hc M).sourceEdge e σ) ?_ ?_)
  · exact incident_sourceEdge_sourceEndpoint _ a e hea σ
  · exact incident_sourceEdge_sourceEndpoint _ b e heb σ

theorem trace_self (Z : (rData T hc M).SourceVertex) : trace T hc M Z.1.2 Z.1.1 = Z :=
  (rData T hc M).sourceEndpoint_self Z

/-- A source vertex with no survivor is a single sheet (in `D₀`, whose blocks are `D`'s). -/
theorem blockCard_rData_of_zero {Z : (rData T hc M).SourceVertex}
    (h0 : nonDanglingValency M.data (svIncl Z) = 0) :
    ((rData T hc M).vertexPartition Z.1.1).blockCard Z.1.2 = 1 :=
  (PendantFibre.degree_one_of_nonDanglingValency_zero M.fullDim (svIncl Z) h0).1

/-- **(b): a component of `D₀` without survivors is a lone sheet.** -/
theorem isLone_of_component (Z : (rData T hc M).SourceVertex)
    (hZ : ∀ W, Reach (rData T hc M).sourceGraph Z W → nonDanglingValency M.data (svIncl W) = 0) :
    Sheets.IsLone (rData T hc M) Z.1.2 := by
  intro v j hj
  have hR : Reach (rData T hc M).sourceGraph Z (trace T hc M Z.1.2 v) := by
    have h := reach_trace T hc M Z.1.2 Z.1.1 v
    rwa [trace_self] at h
  have h1 := blockCard_rData_of_zero T hc M (hZ _ hR)
  -- the trace vertex's block is the block of `Z.1.2`
  have hRel : ((rData T hc M).vertexPartition v).Rel (trace T hc M Z.1.2 v).1.2 Z.1.2 :=
    Lollipops.rel_sourceEndpoint (rData T hc M) v Z.1.2
  have hb := Lollipops.eq_of_blockCard_eq_one h1 hRel rfl
  have hb' := Lollipops.eq_of_blockCard_eq_one h1 (hRel.trans hj) rfl
  exact hb'.trans hb.symm

/-! ## 5.  (c): no survivor over `T'` lies in a lone sheet -/

/-- **A lone sheet's trace is closed**: everything joined to it in `D₀` lies in it. -/
theorem sheet_eq_of_reach_lone {τ : Fin degree} (hτ : Sheets.IsLone (rData T hc M) τ)
    {X Y : (rData T hc M).SourceVertex} (hX : X.1.2 = τ)
    (h : Reach (rData T hc M).sourceGraph X Y) : Y.1.2 = τ := by
  refine reach_propagate (motive := fun Y : (rData T hc M).SourceVertex ↦ Y.1.2 = τ) hX
    (fun a b hab ha ↦ ?_) h
  obtain ⟨E, hEnds⟩ := exists_sourceEnds_of_num_edges_pos _ hab
  obtain ⟨hEa, hEb⟩ := incident_of_sourceEnds _ hEnds
  have h1 := ((incident_iff_target_mem_and_rel _ E a).mp hEa).2
  rw [ha] at h1
  have hE : E.1.2 = τ := hτ _ _ h1
  have h2 := ((incident_iff_target_mem_and_rel _ E b).mp hEb).2
  rw [hE] at h2
  exact (hτ _ _ ((SheetPartition.rel_iff _ _ _).mpr h2.symm))

theorem trace_sheet_of_lone {τ : Fin degree} (hτ : Sheets.IsLone (rData T hc M) τ)
    (v : (rTarget T hc M).V) : (trace T hc M τ v).1.2 = τ :=
  hτ.repr_vertex v

include hc in
/-- If one survivor over `T'` had a lone sheet, every sheet would be lone. -/
theorem all_lone_of_lone_survivor {X : M.data.SourceVertex} (hX : X.1.1 ∈ Keep T M)
    (hXnd : 0 < nonDanglingValency M.data X)
    (hL : Sheets.IsLone (rData T hc M) X.1.2) (τ : Fin degree) :
    Sheets.IsLone (rData T hc M) τ := by
  set X' := svRestrict (hKeep := Keep_nonempty T hc M) X hX
  set Z := trace T hc M τ X'.1.1
  by_cases hW : ∃ W, Reach (rData T hc M).sourceGraph Z W ∧
      0 < nonDanglingValency M.data (svIncl W)
  · obtain ⟨W, hZW, hWnd⟩ := hW
    have hXW := reach_of_survivors T hc M hX (svIncl_target_mem W) hXnd hWnd
    change Reach _ (svRestrict X hX) W at hXW
    have hXZ := reach_trans hXW (reach_symm hZW)
    have hZ := sheet_eq_of_reach_lone T hc M hL rfl hXZ
    -- `τ` is in the block of the lone sheet over `X'.1.1`
    have hRel : ((rData T hc M).vertexPartition X'.1.1).Rel X'.1.2 τ := by
      have h := Lollipops.rel_sourceEndpoint (rData T hc M) X'.1.1 τ
      change ((rData T hc M).vertexPartition X'.1.1).Rel Z.1.2 τ at h
      rw [hZ] at h
      exact h
    have := hL _ _ hRel
    rw [this]; exact hL
  · push Not at hW
    have hZL := isLone_of_component T hc M Z fun W hW' ↦ Nat.le_zero.mp (hW W hW')
    have hRel : ((rData T hc M).vertexPartition Z.1.1).Rel Z.1.2 τ :=
      Lollipops.rel_sourceEndpoint _ _ τ
    have := hZL _ _ hRel
    rw [this]; exact hZL

/-- A telescoping sum over `Fin c`. -/
theorem sum_fin_succ_sub {c : ℕ} (f : Fin (c + 1) → ℤ) :
    ∑ i : Fin c, (f i.succ - f i.castSucc) = f (Fin.last c) - f 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i ↦ f i.castSucc)
    simp only [Fin.succ_castSucc] at h ⊢
    rw [h, Fin.succ_last]
    simp only [Fin.castSucc_zero]
    ring

/-- **Twice the block excess** is `c + 2 - s_1`: the number of ascents of a slope sequence. -/
theorem two_mul_blockExcess (j : Fin k) :
    2 * blockExcess T hc M j = c j + 2 - sPath T hc M j 0 := by
  have hStep : ∀ i : Fin (c j), 2 * ((mSpine T M j i : ℤ) - sPath T hc M j i.castSucc) =
      ((sPath T hc M j i.succ : ℤ) - sPath T hc M j i.castSucc) + 1 := by
    intro i
    have h := SpineStep.spineStep_index M.fullDim (TailAt.spineHyp (cat T j) M (T.cubic hc) i)
    rw [TailAt.third_spineHyp, TailAt.bridgeAt_index] at h
    unfold mSpine sPath
    omega
  unfold blockExcess
  rw [Finset.mul_sum, Finset.sum_congr rfl fun i _ ↦ hStep i, Finset.sum_add_distrib,
    sum_fin_succ_sub (fun i ↦ (sPath T hc M j i : ℤ)), sPath_last]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem one_le_sPath (j : Fin k) (i : Fin (c j + 1)) : 1 ≤ sPath T hc M j i :=
  StableLocalProperties.sourceEdgeIndex_pos _ _

theorem two_mul_blockExcess_le (j : Fin k) : 2 * blockExcess T hc M j ≤ c j + 1 := by
  rw [two_mul_blockExcess]
  have := one_le_sPath T hc M j 0
  omega

/-- `p ≥ k` for a marked cubic core: the marks alone carry `2k` slot ends. -/
theorem k_le_p (hc : IsMarkedCubic core mark) : k ≤ p := by
  classical
  have hSum : ∑ v, core.incidenceDegree v = 2 * p := by
    unfold Core.incidenceDegree
    rw [Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hLe : ∑ j, core.incidenceDegree (mark j) ≤ ∑ v, core.incidenceDegree v := by
    rw [← Finset.sum_image (fun i _ j _ h ↦ hc.injective h)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simp only [hc.mark_degree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hLe
  omega

theorem card_blocks_of_allSingleton {d : ℕ} (P : SheetPartition d) (hd : 0 < d)
    (h1 : ∀ i, P.blockCard i = 1) : Fintype.card P.Blocks = d :=
  MarkedCount.Lollipops.card_blocks_of_discrete P hd fun b ↦ h1 b.1

/-- **Not every sheet of `D₀` is lone**: else the Euler count of the restriction (`genus_rData`)
would make `p + 3 ≤ k`. -/
theorem false_of_all_lone (hAll : ∀ τ, Sheets.IsLone (rData T hc M) τ) : False := by
  classical
  have hd := M.data.degree_pos
  -- every partition of `D₀` is discrete
  have hV : Fintype.card (rData T hc M).SourceVertex =
      degree * Fintype.card (rTarget T hc M).V := by
    rw [GluingDatum.card_sourceVertex_eq_sum_card_blocks]
    rw [Finset.sum_congr rfl fun v _ ↦ card_blocks_of_allSingleton _ hd fun i ↦
      (hAll i).blockCard_vertex v]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hE : Fintype.card (rData T hc M).SourceEdge =
      degree * Fintype.card (rTarget T hc M).edges := by
    rw [GluingDatum.card_sourceEdge_eq_sum_card_blocks]
    rw [Finset.sum_congr rfl fun e _ ↦ card_blocks_of_allSingleton _ hd fun i ↦
      (hAll i).blockCard_edge e]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hGenus0 : genus (rData T hc M).sourceGraph = 1 - degree := by
    have hT := rTarget_genus T hc M
    unfold genus at hT
    rw [genus_sourceGraph, hV, hE, Multiset.card_coe]
    push_cast
    linear_combination (degree : ℤ) * hT
  have hG := genus_rData T hc M
  have hSat := M.fullDim.saturated
  rw [card_edges_target T M] at hSat
  have hB : ∀ j, 2 * blockExcess T hc M j ≤ c j + 1 := two_mul_blockExcess_le T hc M
  have hBsum : 2 * ∑ j, blockExcess T hc M j ≤ ∑ j, ((c j : ℤ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ ↦ hB j
  have hkp := k_le_p hc
  have hSum3 : (∑ j, (3 * (c j : ℤ) + 2)) = 3 * ∑ j, (c j : ℤ) + 2 * k := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hSum1 : (∑ j, ((c j : ℤ) + 1 + blockExcess T hc M j)) =
      ∑ j, (c j : ℤ) + k + ∑ j, blockExcess T hc M j := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp
  have hSum2 : (∑ j, ((c j : ℤ) + 1)) = ∑ j, (c j : ℤ) + k := by
    rw [Finset.sum_add_distrib]; simp
  push_cast at hSat
  rw [hSum3] at hSat
  rw [hSum1] at hG
  rw [hSum2] at hBsum
  have hkp' : (k : ℤ) ≤ p := by exact_mod_cast hkp
  linarith

include hc in
/-- **(c): a survivor over `T'` never lies in a lone sheet** (else every sheet would be lone). -/
theorem not_isLone_of_survivor {X : M.data.SourceVertex} (hX : X.1.1 ∈ Keep T M)
    (hXnd : 0 < nonDanglingValency M.data X) :
    ¬ Sheets.IsLone (rData T hc M) X.1.2 := fun hL ↦
  false_of_all_lone T hc M (all_lone_of_lone_survivor T hc M hX hXnd hL)

/-- **(c'), the other half**: a vertex of `D₀` in a lone sheet carries no survivor of the frame. -/
theorem nonDanglingValency_eq_zero_of_isLone {Z : (rData T hc M).SourceVertex}
    (hZ : Sheets.IsLone (rData T hc M) Z.1.2) : nonDanglingValency M.data (svIncl Z) = 0 := by
  by_contra h
  exact not_isLone_of_survivor T hc M (svIncl_target_mem Z) (Nat.pos_of_ne_zero h) hZ

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
