module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailLone

@[expose] public section

/-!
# Restriction over the tails: the shed sheets, one per ascent

At an **ascent** of the slope sequence of a tail (`IsAscent`: `m(B_{i+1}) = s_{i+1} + 1`), the block
of the spine vertex `B_{i+1}` holds exactly one sheet outside the block of the lower path edge,
the **shed sheet** (`shedSheet`); its edge over the lower path edge is dangling (`shedEdge`), and
its pendant side contains the whole sheet over `T'`:

* (i) `isLone_shedSheet`: the shed sheet is lone in `D₀`;
* (ii) `shedSheet_injective`: distinct ascents shed distinct sheets;
* (iii) `exists_ascent_of_isLone`: every lone sheet of `D₀` is shed at some ascent.

The propagation along the target is `mem_side_of_reachP_target`: a target walk from the inner end
of a pendant side that never visits the image of the outer end stays, sheet by sheet, in the side.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.DanglingSideStructure (ReachP reachP_refl reachP_tail reachP_mono
  mem_side_of_reachP)
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

/-! ## 1.  Propagation along target walks -/

section Generic

variable {target : CFGraph} {d : ℕ} (D : GluingDatum target d)

/-- Two vertices joined by a target edge. -/
theorem num_edges_pos_of_mem_incidentEdges {e : target.edges} {a b : target.V}
    (ha : e ∈ GluingDatum.incidentEdges a) (hb : e ∈ GluingDatum.incidentEdges b) (hab : a ≠ b) :
    0 < num_edges target a b := by
  have hMem : (e : target.V × target.V) ∈ target.edges := Multiset.coe_mem
  have ha' := Count.fst_eq_or_snd_eq_of_mem_incidentEdges ha
  have hb' := Count.fst_eq_or_snd_eq_of_mem_incidentEdges hb
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · exact absurd (ha'.symm.trans hb') hab
  · have : (e : target.V × target.V) = (a, b) := Prod.ext ha' hb'
    rw [this] at hMem
    exact NonDanglingValency.num_edges_pos_of_mem_edges hMem
  · have : (e : target.V × target.V) = (b, a) := Prod.ext hb' ha'
    rw [this] at hMem
    rw [num_edges_symmetric]
    exact NonDanglingValency.num_edges_pos_of_mem_edges hMem
  · exact absurd (ha'.symm.trans hb') hab

/-- **Propagation along a target walk avoiding the image of the outer end.** -/
theorem mem_side_of_reachP_target {inner outer : D.SourceVertex}
    (cut : DanglingSide D.sourceGraph inner outer) (σ : Fin d) {y₀ y : target.V}
    (h₀ : D.sourceEndpoint y₀ σ ∈ cut.side) (hy : ReachP target (· ≠ outer.1.1) y₀ y) :
    D.sourceEndpoint y σ ∈ cut.side := by
  induction hy with
  | refl => exact h₀
  | @tail a b _ hab ih =>
    obtain ⟨hab, hb⟩ := hab
    obtain ⟨pair, hPair, hEnds⟩ := GraphContraction.exists_mem_edges_of_num_edges_pos _ a b hab
    let e : target.edges := ⟨pair, ⟨0, Multiset.count_pos.mpr hPair⟩⟩
    have hne : a ≠ b := by
      intro h; subst h
      rcases hEnds with h | h <;> rw [h] at hPair <;> exact target.loopless a hPair
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
    have hIa := incident_sourceEdge_sourceEndpoint D a e hea σ
    have hIb := incident_sourceEdge_sourceEndpoint D b e heb σ
    have hNe : D.sourceEndpoint a σ ≠ D.sourceEndpoint b σ := by
      intro h; exact hne (congrArg (fun X : D.SourceVertex ↦ X.1.1) h)
    have hAdj : 0 < num_edges D.sourceGraph (D.sourceEndpoint a σ) (D.sourceEndpoint b σ) := by
      refine num_edges_pos_of_sourceEnds D (edge := D.sourceEdge e σ) ?_
      rcases hIa with ha' | ha' <;> rcases hIb with hb' | hb'
      · exact absurd (ha'.symm.trans hb') hNe
      · exact Or.inl (Prod.ext ha' hb')
      · exact Or.inr (Prod.ext hb' ha')
      · exact absurd (ha'.symm.trans hb') hNe
    by_contra hNot
    have := eq_outer_of_step D cut ih hAdj hNot
    exact hb (congrArg (fun X : D.SourceVertex ↦ X.1.1) this)

end Generic

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree)

include hc

/-! ## 2.  Target walks along the tails -/

theorem num_edges_path (j : Fin k) (i : Fin (c j + 1)) :
    0 < num_edges M.target (lowerX T M j i) (upperX T M j i) :=
  num_edges_pos_of_mem_incidentEdges (path_mem_lowerX T hc M j i) (path_mem_upperX T hc M j i)
    (lowerX_ne_upperX T hc M j i)

/-- **Down a spine**: from `lowerX j i₀` to the image of the mark, through `lowerX j i` for
`i ≤ i₀`. -/
theorem reachP_down (j : Fin k) (P : M.target.V → Prop) :
    ∀ (i₀ : Fin (c j + 1)), (∀ i : Fin (c j + 1), i.val < i₀.val → P (lowerX T M j i)) →
      ReachP M.target P (lowerX T M j i₀) (xMark T M j) := by
  intro i₀
  induction i₀ using Fin.induction with
  | zero => intro _; rw [lowerX_zero]; exact reachP_refl _ _
  | succ i₁ ih =>
    intro hP
    have hStep : 0 < num_edges M.target (lowerX T M j i₁.succ) (lowerX T M j i₁.castSucc) := by
      rw [num_edges_symmetric, lowerX_succ, ← upperX_castSucc]
      exact num_edges_path T hc M j i₁.castSucc
    refine Relation.ReflTransGen.head ⟨hStep, hP _ (by simp)⟩ (ih fun i hi ↦ hP i ?_)
    simp at hi ⊢; omega

/-- **Up a spine**: from the image of the mark to `upperX j i₀`, through `upperX j i` for
`i ≤ i₀`. -/
theorem reachP_up (j : Fin k) (P : M.target.V → Prop) :
    ∀ (i₀ : Fin (c j + 1)), (∀ i : Fin (c j + 1), i.val ≤ i₀.val → P (upperX T M j i)) →
      ReachP M.target P (xMark T M j) (upperX T M j i₀) := by
  intro i₀
  induction i₀ using Fin.induction with
  | zero =>
    intro hP
    refine Relation.ReflTransGen.single ⟨?_, hP 0 le_rfl⟩
    rw [← lowerX_zero]; exact num_edges_path T hc M j 0
  | succ i₁ ih =>
    intro hP
    refine reachP_tail (ih fun i hi ↦ hP i ?_) ?_ (hP _ le_rfl)
    · simp at hi ⊢; omega
    · rw [upperX_castSucc, ← lowerX_succ]; exact num_edges_path T hc M j i₁.succ

/-- **Inside `T'`**: kept vertices are joined by walks of kept vertices. -/
theorem reachP_keep (v w : (rTarget T hc M).V) :
    ReachP M.target (· ∈ Keep T M) (vIncl v) (vIncl w) := by
  have h := reach_of_graph_connected (rTarget_connected T hc M) v w
  exact DanglingSideStructure.reachP_of_reach_induced (Keep_nonempty T hc M) h

theorem reachP_keep_xMark (j : Fin k) (v : (rTarget T hc M).V) :
    ReachP M.target (· ∈ Keep T M) (xMark T M j) (vIncl v) :=
  reachP_keep T hc M (vRestrict (xMark T M j) (xMark_mem_Keep T hc M j)) v

theorem reachP_keep_xMark' (j j' : Fin k) :
    ReachP M.target (· ∈ Keep T M) (xMark T M j) (xMark T M j') :=
  reachP_keep T hc M (vRestrict (xMark T M j) (xMark_mem_Keep T hc M j))
    (vRestrict (xMark T M j') (xMark_mem_Keep T hc M j'))

/-! ## 3.  The spine blocks and the ascents -/

/-- The block of the spine vertex `B_{i+1}`. -/
def sBlock (j : Fin k) (i : Fin (c j)) : Finset (Fin degree) :=
  (M.data.vertexPartition (xSpine T M j i)).block (TailAt.spineV (cat T j) M i).1.2

/-- The block of the lower path edge `h_{i+1}` at `B_{i+1}`. -/
def pBlock (j : Fin k) (i : Fin (c j)) : Finset (Fin degree) :=
  (M.data.edgePartition (tEdge T hc M j (Sum.inl i.castSucc))).block
    (TailAt.pathE (cat T j) M (T.cubic hc) i.castSucc).1.1.2

omit hc in
theorem card_sBlock (j : Fin k) (i : Fin (c j)) : (sBlock T M j i).card = mSpine T M j i := rfl

theorem card_pBlock (j : Fin k) (i : Fin (c j)) :
    (pBlock T hc M j i).card = sPath T hc M j i.castSucc := rfl

omit hc in
theorem mem_sBlock {j : Fin k} {i : Fin (c j)} {σ : Fin degree} :
    σ ∈ sBlock T M j i ↔ M.data.sourceEndpoint (xSpine T M j i) σ = TailAt.spineV (cat T j) M i := by
  rw [sBlock, SheetPartition.mem_block_iff, M.data.sourceEndpoint_eq_iff]
  exact ⟨fun h ↦ ⟨rfl, ((M.data.vertexPartition _).rel_iff _ _).mpr h.symm⟩,
    fun h ↦ ((M.data.vertexPartition _).rel_iff _ _).mpr h.2.symm⟩

theorem pBlock_subset_sBlock (j : Fin k) (i : Fin (c j)) : pBlock T hc M j i ⊆ sBlock T M j i := by
  intro σ hσ
  have hI := TailAt.pathE_incident_spine_lower (cat T j) M (T.cubic hc) i
  obtain ⟨hMem, hRel⟩ := (incident_iff_target_mem_and_rel M.data _ _).mp hI
  have hRef := StableLocalProperties.refines_of_mem_incidentEdges M.data hMem
  rw [pBlock, SheetPartition.mem_block_iff] at hσ
  rw [sBlock, SheetPartition.mem_block_iff]
  exact hRel.trans (hRef.rel hσ)

/-- The slope relations at `B_{i+1}`: `m = max(s_{i+1}, s_{i+2})`, steps of one. -/
theorem spine_relation (j : Fin k) (i : Fin (c j)) :
    2 + sPath T hc M j i.succ + sPath T hc M j i.castSucc = 2 * mSpine T M j i + 1 ∧
      sPath T hc M j i.succ ≤ mSpine T M j i ∧ sPath T hc M j i.castSucc ≤ mSpine T M j i := by
  have h := SpineStep.spineStep_index M.fullDim (TailAt.spineHyp (cat T j) M (T.cubic hc) i)
  rw [TailAt.third_spineHyp, TailAt.bridgeAt_index] at h
  refine ⟨h, ?_, ?_⟩
  · exact StableLocalProperties.sourceEdgeIndex_le_blockCard M.data _
      ⟨_, TailAt.pathE_incident_spine_upper (cat T j) M (T.cubic hc) i⟩
  · exact StableLocalProperties.sourceEdgeIndex_le_blockCard M.data _
      ⟨_, TailAt.pathE_incident_spine_lower (cat T j) M (T.cubic hc) i⟩

theorem two_le_mSpine (j : Fin k) (i : Fin (c j)) : 2 ≤ mSpine T M j i := by
  have := spine_relation T hc M j i
  have := one_le_sPath T hc M j i.succ
  have := one_le_sPath T hc M j i.castSucc
  omega

theorem card_sdiff_block (j : Fin k) (i : Fin (c j)) :
    (sBlock T M j i \ pBlock T hc M j i).card = mSpine T M j i - sPath T hc M j i.castSucc := by
  rw [Finset.card_sdiff_of_subset (pBlock_subset_sBlock T hc M j i), card_sBlock, card_pBlock]

/-- **An ascent** at the spine vertex `B_{i+1}`. -/
def IsAscent (j : Fin k) (i : Fin (c j)) : Prop := mSpine T M j i = sPath T hc M j i.castSucc + 1

instance (j : Fin k) (i : Fin (c j)) : Decidable (IsAscent T hc M j i) := by
  unfold IsAscent; infer_instance

theorem mSpine_sub_eq (j : Fin k) (i : Fin (c j)) :
    ((mSpine T M j i : ℤ) - sPath T hc M j i.castSucc) = if IsAscent T hc M j i then 1 else 0 := by
  have := spine_relation T hc M j i
  unfold IsAscent
  split_ifs with h <;> omega

theorem exists_shed (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    ∃ σ, sBlock T M j i \ pBlock T hc M j i = {σ} := by
  have hc' := card_sdiff_block T hc M j i
  rw [h] at hc'
  exact Finset.card_eq_one.mp (by omega)

/-- **The shed sheet** of an ascent. -/
def shedSheet (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) : Fin degree :=
  (exists_shed T hc M j i h).choose

theorem shed_spec (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    sBlock T M j i \ pBlock T hc M j i = {shedSheet T hc M j i h} :=
  (exists_shed T hc M j i h).choose_spec

theorem shed_mem_sBlock (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    shedSheet T hc M j i h ∈ sBlock T M j i := by
  have := (Finset.ext_iff.mp (shed_spec T hc M j i h) (shedSheet T hc M j i h)).mpr
    (Finset.mem_singleton_self _)
  exact (Finset.mem_sdiff.mp this).1

theorem shed_notMem_pBlock (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    shedSheet T hc M j i h ∉ pBlock T hc M j i := by
  have := (Finset.ext_iff.mp (shed_spec T hc M j i h) (shedSheet T hc M j i h)).mpr
    (Finset.mem_singleton_self _)
  exact (Finset.mem_sdiff.mp this).2

theorem eq_shed_of_mem {j : Fin k} {i : Fin (c j)} {σ : Fin degree} (hS : σ ∈ sBlock T M j i)
    (hP : σ ∉ pBlock T hc M j i) :
    ∃ h : IsAscent T hc M j i, σ = shedSheet T hc M j i h := by
  have hMem : σ ∈ sBlock T M j i \ pBlock T hc M j i := Finset.mem_sdiff.mpr ⟨hS, hP⟩
  have hPos : 0 < (sBlock T M j i \ pBlock T hc M j i).card := Finset.card_pos.mpr ⟨σ, hMem⟩
  rw [card_sdiff_block] at hPos
  have hAsc : IsAscent T hc M j i := by
    have := spine_relation T hc M j i
    unfold IsAscent; omega
  refine ⟨hAsc, ?_⟩
  rw [shed_spec T hc M j i hAsc] at hMem
  exact Finset.mem_singleton.mp hMem

/-! ## 4.  The shed edge and its pendant side -/

/-- The lower path edge at `B_{i+1}`. -/
abbrev tLow (j : Fin k) (i : Fin (c j)) : M.target.edges := tEdge T hc M j (Sum.inl i.castSucc)

theorem tLow_mem_xSpine (j : Fin k) (i : Fin (c j)) :
    tLow T hc M j i ∈ GluingDatum.incidentEdges (xSpine T M j i) := by
  rw [incidentEdges_xSpine T hc M]; simp

/-- **The shed edge**: the edge of the shed sheet over the lower path edge. -/
def shedEdge (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) : M.data.SourceEdge :=
  M.data.sourceEdge (tLow T hc M j i) (shedSheet T hc M j i h)

theorem shedEdge_incident_spine (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    Incident M.data (shedEdge T hc M j i h) (TailAt.spineV (cat T j) M i) := by
  have := incident_sourceEdge_sourceEndpoint M.data _ _ (tLow_mem_xSpine T hc M j i)
    (shedSheet T hc M j i h)
  rwa [(mem_sBlock T M).mp (shed_mem_sBlock T hc M j i h)] at this

theorem shedEdge_dangling (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    IsDangling M.data (shedEdge T hc M j i h) := by
  by_contra hS
  have := TailAt.eq_pathE_of_over (cat T j) M (T.cubic hc) i.castSucc hS rfl
  apply shed_notMem_pBlock T hc M j i h
  rw [pBlock, ← this, SheetPartition.mem_block_iff]
  exact (M.data.edgePartition _).rel_repr_left _

theorem lowerX_ne_xSpine (j : Fin k) (i : Fin (c j)) : lowerX T M j i.castSucc ≠ xSpine T M j i := by
  rw [← upperX_castSucc]; exact lowerX_ne_upperX T hc M j _

theorem tLow_mem_lowerX (j : Fin k) (i : Fin (c j)) :
    tLow T hc M j i ∈ GluingDatum.incidentEdges (lowerX T M j i.castSucc) :=
  path_mem_lowerX T hc M j _

/-- The lower end of the shed edge. -/
abbrev shedLow (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) : M.data.SourceVertex :=
  M.data.sourceEndpoint (lowerX T M j i.castSucc) (shedSheet T hc M j i h)

theorem shedEdge_ends (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    M.data.sourceEnds (shedEdge T hc M j i h) = (TailAt.spineV (cat T j) M i, shedLow T hc M j i h) ∨
      M.data.sourceEnds (shedEdge T hc M j i h) = (shedLow T hc M j i h, TailAt.spineV (cat T j) M i) := by
  have hI1 := shedEdge_incident_spine T hc M j i h
  have hI2 := incident_sourceEdge_sourceEndpoint M.data _ _ (tLow_mem_lowerX T hc M j i)
    (shedSheet T hc M j i h)
  have hNe : TailAt.spineV (cat T j) M i ≠ shedLow T hc M j i h := by
    intro he
    have := congrArg (fun X : M.data.SourceVertex ↦ X.1.1) he
    exact lowerX_ne_xSpine T hc M j i this.symm
  rcases hI1 with h1 | h1 <;> rcases hI2 with h2 | h2
  · exact absurd (h1.symm.trans h2) hNe
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h2 h1)
  · exact absurd (h1.symm.trans h2) hNe

/-- **The pendant side of the shed edge**, hanging from `B_{i+1}`. -/
theorem exists_shed_side (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    Nonempty (DanglingSide M.data.sourceGraph (shedLow T hc M j i h)
      (TailAt.spineV (cat T j) M i)) :=
  exists_pendant_away M.data (shedEdge_dangling T hc M j i h) (shedEdge_ends T hc M j i h)
    (by rw [TailAt.nonDanglingValency_vSource]; omega)

omit hc in
theorem spineV_fst (j : Fin k) (i : Fin (c j)) :
    (TailAt.spineV (cat T j) M i).1.1 = xSpine T M j i := rfl

/-! ## 5.  (i) The shed sheet is lone -/

theorem lowerX_ne_xSpine_of_le (j : Fin k) (i' : Fin (c j + 1)) (i : Fin (c j))
    (h : i'.val ≤ i.val) : lowerX T M j i' ≠ xSpine T M j i := by
  induction i' using Fin.cases with
  | zero => rw [lowerX_zero]; exact xMark_ne_xSpine T hc M j j i
  | succ i'' =>
    rw [lowerX_succ]
    intro he
    have := xSpine_inj T hc M he
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Sum.inl.injEq, true_and] at this
    subst this
    simp at h

theorem reachP_shed_kept (j : Fin k) (i : Fin (c j)) (v : (rTarget T hc M).V) :
    ReachP M.target (· ≠ xSpine T M j i) (lowerX T M j i.castSucc) (vIncl v) :=
  Relation.ReflTransGen.trans
    (reachP_down T hc M j _ i.castSucc fun i' hi' ↦
      lowerX_ne_xSpine_of_le T hc M j i' i (by simp at hi'; omega))
    (reachP_mono (P := (· ∈ Keep T M)) (Q := (· ≠ xSpine T M j i))
      (fun z hz hzx ↦ xSpine_notMem_Keep T M j i (hzx ▸ hz)) (reachP_keep_xMark T hc M j v))

omit hc in
/-- The block of a sheet at a vertex of a pendant side is a singleton. -/
theorem blockCard_of_mem_side {inner outer : M.data.SourceVertex}
    (cut : DanglingSide M.data.sourceGraph inner outer) {v : M.target.V} {σ : Fin degree}
    (h : M.data.sourceEndpoint v σ ∈ cut.side) : (M.data.vertexPartition v).blockCard σ = 1 := by
  have h0 := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side M.data cut h
  have h1 := (PendantFibre.degree_one_of_nonDanglingValency_zero M.fullDim _ h0).1
  change (M.data.vertexPartition v).blockCard ((M.data.vertexPartition v).repr σ) = 1 at h1
  rwa [SheetPartition.blockCard_congr _ ((M.data.vertexPartition v).rel_repr_left σ)] at h1

/-- **(i): the shed sheet of an ascent is lone in `D₀`.** -/
theorem isLone_shedSheet (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) :
    Sheets.IsLone (rData T hc M) (shedSheet T hc M j i h) := by
  obtain ⟨cut⟩ := exists_shed_side T hc M j i h
  intro v τ hτ
  have hMem := mem_side_of_reachP_target M.data cut (shedSheet T hc M j i h) cut.left_mem
    (reachP_shed_kept T hc M j i v)
  have h1 := blockCard_of_mem_side T M cut hMem
  exact eq_of_blockCard_eq_one' h1 hτ

/-! ## 6.  (ii) Distinct ascents shed distinct sheets -/

theorem upperX_ne_xSpine (j j' : Fin k) (i' : Fin (c j' + 1)) (i : Fin (c j))
    (h : j' ≠ j ∨ i'.val < i.val) : upperX T M j' i' ≠ xSpine T M j i := by
  induction i' using Fin.lastCases with
  | last =>
    rw [upperX_last]; exact (xSpine_ne_xBulb T hc M j i j' _).symm
  | cast i'' =>
    rw [upperX_castSucc]
    intro he
    have := xSpine_inj T hc M he
    simp only [Sigma.mk.inj_iff] at this
    obtain ⟨rfl, h2⟩ := this
    simp only [heq_eq_eq, Sum.inl.injEq] at h2
    subst h2
    rcases h with h | h
    · exact h rfl
    · simp at h

theorem reachP_shed_spine (j : Fin k) (i : Fin (c j)) (j' : Fin k) (i' : Fin (c j'))
    (h : j' ≠ j ∨ i'.val < i.val) :
    ReachP M.target (· ≠ xSpine T M j i) (lowerX T M j i.castSucc) (xSpine T M j' i') := by
  have hDown := reachP_down T hc M j (· ≠ xSpine T M j i) i.castSucc fun i'' hi'' ↦
    lowerX_ne_xSpine_of_le T hc M j i'' i (by simp at hi''; omega)
  have hAcross := reachP_mono (P := (· ∈ Keep T M)) (Q := (· ≠ xSpine T M j i))
    (fun z hz hzx ↦ xSpine_notMem_Keep T M j i (hzx ▸ hz)) (reachP_keep_xMark' T hc M j j')
  have hUp := reachP_up T hc M j' (· ≠ xSpine T M j i) i'.castSucc fun i'' hi'' ↦
    upperX_ne_xSpine T hc M j j' i'' i (by
      rcases h with h | h
      · exact Or.inl h
      · right; simp at hi''; omega)
  rw [upperX_castSucc] at hUp
  exact (hDown.trans hAcross).trans hUp

theorem not_shed_eq (j : Fin k) (i : Fin (c j)) (h : IsAscent T hc M j i) (j' : Fin k)
    (i' : Fin (c j')) (h' : IsAscent T hc M j' i') (hji : j' ≠ j ∨ i'.val < i.val)
    (heq : shedSheet T hc M j i h = shedSheet T hc M j' i' h') : False := by
  obtain ⟨cut⟩ := exists_shed_side T hc M j i h
  have hMem := mem_side_of_reachP_target M.data cut (shedSheet T hc M j i h) cut.left_mem
    (reachP_shed_spine T hc M j i j' i' hji)
  rw [heq, (mem_sBlock T M).mp (shed_mem_sBlock T hc M j' i' h')] at hMem
  have := DanglingSideStructure.nonDanglingValency_eq_zero_of_mem_side M.data cut hMem
  rw [TailAt.nonDanglingValency_vSource] at this
  omega

/-- **(ii): distinct ascents shed distinct sheets.** -/
theorem shedSheet_injective {j j' : Fin k} {i : Fin (c j)} {i' : Fin (c j')}
    (h : IsAscent T hc M j i) (h' : IsAscent T hc M j' i')
    (heq : shedSheet T hc M j i h = shedSheet T hc M j' i' h') :
    (⟨j, i⟩ : Σ j, Fin (c j)) = ⟨j', i'⟩ := by
  by_cases hj : j' = j
  · subst hj
    rcases lt_trichotomy i'.val i.val with hlt | heq' | hgt
    · exact (not_shed_eq T hc M j' i h j' i' h' (Or.inr hlt) heq).elim
    · rw [Fin.ext heq']
    · exact (not_shed_eq T hc M j' i' h' j' i h (Or.inr hgt) heq.symm).elim
  · exact (not_shed_eq T hc M j i h j' i' h' (Or.inl hj) heq).elim

/-! ## 7.  (iii) Every lone sheet is shed -/

/-- `τ` is alone in its block over `y`. -/
def Sing (τ : Fin degree) (yv : M.target.V) : Prop := (M.data.vertexPartition yv).blockCard τ = 1

omit hc in
theorem sing_of_refines {y₁ y₂ : M.target.V}
    (h : (M.data.vertexPartition y₁).Refines (M.data.vertexPartition y₂)) {τ : Fin degree}
    (h' : Sing T M τ y₂) : Sing T M τ y₁ := by
  unfold Sing at *
  have hsub : (M.data.vertexPartition y₁).block τ ⊆ (M.data.vertexPartition y₂).block τ :=
    fun σ hσ ↦ (SheetPartition.mem_block_iff _ _ _).mpr
      (h.rel ((SheetPartition.mem_block_iff _ _ _).mp hσ))
  have h1 := Finset.card_le_card hsub
  have h2 := (M.data.vertexPartition y₁).blockCard_pos τ
  unfold SheetPartition.blockCard at *
  omega

omit hc in
theorem sing_edge {e : M.target.edges} {yv : M.target.V} (he : e ∈ GluingDatum.incidentEdges yv)
    {τ : Fin degree} (h : Sing T M τ yv) : (M.data.edgePartition e).blockCard τ = 1 := by
  have hRef := StableLocalProperties.refines_of_mem_incidentEdges M.data he
  unfold Sing at h
  have hsub : (M.data.edgePartition e).block τ ⊆ (M.data.vertexPartition yv).block τ :=
    fun σ hσ ↦ (SheetPartition.mem_block_iff _ _ _).mpr
      (hRef.rel ((SheetPartition.mem_block_iff _ _ _).mp hσ))
  have h1 := Finset.card_le_card hsub
  have h2 := (M.data.edgePartition e).blockCard_pos τ
  unfold SheetPartition.blockCard at *
  omega

omit hc in
theorem sing_of_zero {yv : M.target.V} {τ : Fin degree}
    (h0 : nonDanglingValency M.data (M.data.sourceEndpoint yv τ) = 0) : Sing T M τ yv := by
  have h1 := (PendantFibre.degree_one_of_nonDanglingValency_zero M.fullDim _ h0).1
  change (M.data.vertexPartition yv).blockCard ((M.data.vertexPartition yv).repr τ) = 1 at h1
  rwa [SheetPartition.blockCard_congr _ ((M.data.vertexPartition yv).rel_repr_left τ)] at h1

/-- **The spine step**: a lone sheet that is never shed stays alone up the spine. -/
theorem sing_xSpine {τ : Fin degree} (hτ : Sheets.IsLone (rData T hc M) τ)
    (hno : ∀ j i h, shedSheet T hc M j i h ≠ τ) (j : Fin k) (i : Fin (c j))
    (hLow : Sing T M τ (lowerX T M j i.castSucc)) : Sing T M τ (xSpine T M j i) := by
  by_cases hY : nonDanglingValency M.data (M.data.sourceEndpoint (xSpine T M j i) τ) = 0
  · exact sing_of_zero T M hY
  · have hYB := eq_spineV_of_over T hc M (X := M.data.sourceEndpoint (xSpine T M j i) τ) rfl hY
    have hτS : τ ∈ sBlock T M j i := (mem_sBlock T M).mpr hYB
    by_cases hτP : τ ∈ pBlock T hc M j i
    · exfalso
      set L := TailAt.vSource M (T.H.tail ((cat T j).slot (Sum.inl i.castSucc))) with hL
      have hI := TailAt.pathE_incident_tail (cat T j) M (T.cubic hc) i.castSucc
      obtain ⟨hMemL, hRelL⟩ := (incident_iff_target_mem_and_rel M.data _ _).mp hI
      have hRef := StableLocalProperties.refines_of_mem_incidentEdges M.data hMemL
      have hLτ : (M.data.vertexPartition L.1.1).Rel L.1.2 τ := by
        rw [pBlock, SheetPartition.mem_block_iff] at hτP
        exact hRelL.trans (hRef.rel hτP)
      have hLow' : (M.data.vertexPartition L.1.1).blockCard τ = 1 := hLow
      have hL1 : (M.data.vertexPartition L.1.1).blockCard L.1.2 = 1 := by
        rw [SheetPartition.blockCard_congr _ hLτ]; exact hLow'
      rcases Fin.eq_zero_or_eq_succ i.castSucc with h0 | ⟨i', hi'⟩
      · -- the lower core vertex is the mark
        have hLu : L = uSource T M j := by
          rw [hL, h0, (cat T j).tail_path_zero]; rfl
        have hτL : τ = L.1.2 := eq_of_blockCard_eq_one' hL1 hLτ
        apply not_isLone_of_survivor T hc M (xMark_mem_Keep T hc M j)
          (X := uSource T M j) (by rw [nonDanglingValency_uSource]; omega)
        rw [← hLu, ← hτL]; exact hτ
      · -- the lower core vertex is a spine vertex, with a block of two sheets at least
        have hLs : L = TailAt.spineV (cat T j) M i' := by
          rw [hL, hi', (cat T j).tail_path_succ]
        have := two_le_mSpine T hc M j i'
        unfold mSpine at this
        rw [← hLs] at this
        omega
    · obtain ⟨h, hEq⟩ := eq_shed_of_mem T hc M hτS hτP
      exact (hno j i h hEq.symm).elim

/-- **The bulbs**: the partition at a bulb refines the one at the foot of its bridge. -/
theorem sing_xBulb {τ : Fin degree} (j : Fin k) (i : Fin (c j + 1))
    (h : Sing T M τ (TailAt.vSource M (T.H.tail ((cat T j).slot (bulbBridge i)))).1.1) :
    Sing T M τ (xBulb T M j i) := by
  have hRef := LoopAt.refines_uP_xV M ((cat T j).isLoop i)
  unfold LoopAt.xV at hRef
  rw [TailAt.farEnd_eq (cat T j) M (T.cubic hc)] at hRef
  exact sing_of_refines T M hRef h

omit hc in
/-- **The leaves**: the partition at a leaf refines the one at its bulb. -/
theorem sing_xLeaf {τ : Fin degree} (j : Fin k) (i : Fin (c j + 1)) (h : Sing T M τ (xBulb T M j i)) :
    Sing T M τ (xLeaf T M j i) :=
  sing_of_refines T M (LoopAt.refines_vC_uP M ((cat T j).isLoop i)) h

/-- **A lone sheet that is never shed is alone everywhere.** -/
theorem sing_all {τ : Fin degree} (hτ : Sheets.IsLone (rData T hc M) τ)
    (hno : ∀ j i h, shedSheet T hc M j i h ≠ τ) (yv : M.target.V) : Sing T M τ yv := by
  have hKeep : ∀ v (hv : v ∈ Keep T M), Sing T M τ v := fun v hv ↦
    hτ.blockCard_vertex (vRestrict (hKeep := Keep_nonempty T hc M) v hv)
  have hLow : ∀ j (i : Fin (c j + 1)), Sing T M τ (lowerX T M j i) := by
    intro j i
    induction i using Fin.induction with
    | zero => rw [lowerX_zero]; exact hKeep _ (xMark_mem_Keep T hc M j)
    | succ i' ih => rw [lowerX_succ]; exact sing_xSpine T hc M hτ hno j i' ih
  have hSpine : ∀ j (i : Fin (c j)), Sing T M τ (xSpine T M j i) := fun j i ↦ by
    rw [← lowerX_succ]; exact hLow j i.succ
  have hBulb : ∀ j (i : Fin (c j + 1)), Sing T M τ (xBulb T M j i) := by
    intro j i
    refine sing_xBulb T hc M j i ?_
    induction i using Fin.lastCases with
    | last => rw [bulbBridge_last]; exact hLow j _
    | cast i' => rw [bulbBridge_castSucc, (cat T j).tail_bridge]; exact hSpine j i'
  by_cases hy : yv ∈ Keep T M
  · exact hKeep yv hy
  · obtain ⟨⟨j, t⟩, rfl⟩ := exists_tailVertex_of_notMem T M hy
    rcases t with i | i | i
    · exact hSpine j i
    · exact hBulb j i
    · exact sing_xLeaf T M j i (hBulb j i)

omit hc in
/-- A full-dimensional datum has at least two sheets. -/
theorem two_le_degree {N P : ℕ} {H : Core N P} {yH : Fin P → ℚ} (M : FibreMember H yH degree) :
    2 ≤ degree := by
  by_contra hd
  have hd1 : degree = 1 := by have := M.data.degree_pos; omega
  subst hd1
  have hBlocks : ∀ P : SheetPartition 1, Fintype.card P.Blocks = 1 := fun P ↦
    card_blocks_of_allSingleton P one_pos fun i ↦ by
      have := P.blockCard_pos i
      have hle : P.blockCard i ≤ 1 := by
        unfold SheetPartition.blockCard
        exact (Finset.card_le_univ _).trans (by simp)
      omega
  have hV : Fintype.card M.data.SourceVertex = Fintype.card M.target.V := by
    rw [GluingDatum.card_sourceVertex_eq_sum_card_blocks]
    simp [hBlocks]
  have hE : Fintype.card M.data.SourceEdge = Fintype.card M.target.edges := by
    rw [GluingDatum.card_sourceEdge_eq_sum_card_blocks]
    simp [hBlocks]
  have hSat := M.fullDim.saturated
  have hTg := M.fullDim.targetGenus
  rw [genus_sourceGraph, hV, hE] at hSat
  unfold genus at hTg
  rw [Multiset.card_coe] at hSat
  omega

/-- **(iii): every lone sheet of `D₀` is shed at some ascent.** -/
theorem exists_ascent_of_isLone {τ : Fin degree} (hτ : Sheets.IsLone (rData T hc M) τ) :
    ∃ j i h, shedSheet T hc M j i h = τ := by
  by_contra hno
  push Not at hno
  have hS := sing_all T hc M hτ hno
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin degree, σ ≠ τ := by
    have := two_le_degree M
    by_contra hall
    push Not at hall
    have h1 : (Finset.univ : Finset (Fin degree)) ⊆ {τ} := fun σ _ ↦ by simp [hall σ]
    have := Finset.card_le_card h1
    simp at this
    omega
  obtain ⟨y₀⟩ := M.target.instNonempty
  have hR := reach_of_graph_connected M.fullDim.connected (M.data.sourceEndpoint y₀ τ)
    (M.data.sourceEndpoint y₀ σ)
  have hBlock : ∀ yv : M.target.V, (M.data.vertexPartition yv).block τ = {τ} := fun yv ↦
    (M.data.vertexPartition yv).block_eq_singleton_of_blockCard_eq_one τ (hS yv)
  have hEqτ : ∀ {yv : M.target.V} {σ' : Fin degree}, (M.data.vertexPartition yv).Rel τ σ' →
      σ' = τ := fun {yv σ'} h ↦ by
    have := (SheetPartition.mem_block_iff _ _ _).mpr h
    rw [hBlock yv, Finset.mem_singleton] at this
    exact this
  have hBase : (M.data.sourceEndpoint y₀ τ).1.2 = τ :=
    hEqτ ((M.data.vertexPartition y₀).rel_repr_right τ)
  have hAll := reach_propagate (motive := fun Z : M.data.SourceVertex ↦ Z.1.2 = τ) hBase
    (fun a b hab ha ↦ by
      obtain ⟨E, hEnds⟩ := exists_sourceEnds_of_num_edges_pos _ hab
      obtain ⟨hEa, hEb⟩ := incident_of_sourceEnds _ hEnds
      have h1 := ((incident_iff_target_mem_and_rel _ E a).mp hEa).2
      rw [ha] at h1
      have hE : E.1.2 = τ := hEqτ h1
      have h2 := ((incident_iff_target_mem_and_rel _ E b).mp hEb).2
      rw [hE] at h2
      exact hEqτ ((SheetPartition.rel_iff _ _ _).mpr h2.symm)) hR
  apply hσ
  have hrτ : (M.data.vertexPartition y₀).repr τ = τ :=
    hEqτ ((M.data.vertexPartition y₀).rel_repr_right τ)
  have h3 : (M.data.vertexPartition y₀).Rel τ σ := by
    rw [SheetPartition.rel_iff]
    have : (M.data.vertexPartition y₀).repr σ = τ := hAll
    rw [this, hrτ]
  exact hEqτ h3

/-! ## 8.  The count -/

/-- The ascents of all the tails. -/
def Asc : Type := {q : Σ j, Fin (c j) // IsAscent T hc M q.1 q.2}

noncomputable instance : Fintype (Asc T hc M) := by unfold Asc; infer_instance

/-- The lone sheets of `D₀`. -/
noncomputable def loneSet : Finset (Fin degree) := by
  classical
  exact Finset.univ.filter fun τ ↦ Sheets.IsLone (rData T hc M) τ

theorem mem_loneSet {τ : Fin degree} : τ ∈ loneSet T hc M ↔ Sheets.IsLone (rData T hc M) τ := by
  classical
  unfold loneSet
  simp

/-- **The lone sheets are counted by the ascents.** -/
theorem card_loneSet : (loneSet T hc M).card = Fintype.card (Asc T hc M) := by
  classical
  symm
  rw [← Finset.card_univ]
  refine Finset.card_bij (fun q _ ↦ shedSheet T hc M q.1.1 q.1.2 q.2) ?_ ?_ ?_
  · intro q _
    exact (mem_loneSet T hc M).mpr (isLone_shedSheet T hc M _ _ _)
  · intro q _ q' _ h
    exact Subtype.ext (shedSheet_injective T hc M q.2 q'.2 h)
  · intro τ hτ
    obtain ⟨j, i, h, rfl⟩ := exists_ascent_of_isLone T hc M ((mem_loneSet T hc M).mp hτ)
    exact ⟨⟨⟨j, i⟩, h⟩, Finset.mem_univ _, rfl⟩

theorem card_Asc : (Fintype.card (Asc T hc M) : ℤ) = ∑ j, blockExcess T hc M j := by
  classical
  unfold Asc
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun q : Σ j, Fin (c j) ↦ IsAscent T hc M q.1 q.2) =
      Finset.univ.sigma fun j ↦ Finset.univ.filter fun i ↦ IsAscent T hc M j i := by
    ext q; simp
  rw [this, Finset.card_sigma]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  unfold blockExcess
  simp only [mSpine_sub_eq T hc M j]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_one]

/-- **`#lone sheets = Σⱼ (ascents of tail j)`.** -/
theorem card_loneSet_eq : ((loneSet T hc M).card : ℤ) = ∑ j, blockExcess T hc M j := by
  rw [card_loneSet, card_Asc]

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
