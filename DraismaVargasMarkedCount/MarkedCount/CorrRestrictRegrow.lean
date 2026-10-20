module

public import DraismaVargasMarkedCount.MarkedCount.Restriction
public import DraismaVargasMarkedCount.MarkedCount.Regrowth

@[expose] public section

/-!
# The lollipop correspondence, part 1: restriction after regrowth

For a marked frame `κ`, the
restriction of its regrowth `regrowFrame hc κ` is isomorphic to `κ` over the marked core.

**The branch names line up.** In the regrowth, the lollipop package used by restriction finds
exactly the branches regrowth attached: `w_j = wSV j` (`loopV_regrow`), `u_j = oldSV (markSource
j)` (`markV_regrow`), `φ(w_j) = midV j` (`uP_regrow`) and `φ(C_j) = tipV j` (`vC_regrow`). So the
kept target vertices are the old ones (`mem_Keep_regrow`).

**The isomorphism** (`restrictRegrowIso`) is the old-vertex inclusion `v ↦ oldV v` read backwards,
with identity sheet permutations: restriction keeps the partitions of the regrowth, and regrowth
kept the partitions of `κ` on the old part.
-/

namespace DraismaVargas.Count.MarkedCount.CorrRestrictRegrow

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count (GeometricDatumIso UnorderedEnds)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.MarkedCount.Regrow
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}
  (hc : IsMarkedCubic core mark) (κ : MarkedFrame core mark degree)

/-- The member of the regrowth at the zero request, on which the restriction modules work. -/
abbrev mem : FibreMember (attachLollipops core mark) 0 degree := (regrowFrame hc κ).member 0

/-! ## 1.  The branches of the regrowth -/

theorem leafE_mem_midV {T : CFGraph.{0}} (x : Fin k → T.V) (j : Fin k) :
    leafE x j ∈ GluingDatum.incidentEdges (midV x j) := by
  simp [GluingDatum.incidentEdges]

theorem leafE_mem_tipV {T : CFGraph.{0}} (x : Fin k → T.V) (j : Fin k) :
    leafE x j ∈ GluingDatum.incidentEdges (tipV x j) := by
  simp [GluingDatum.incidentEdges]

theorem loopV_regrow (j : Fin k) :
    Lollipops.loopV (mem hc κ) j = wSV (branching κ) j := by
  have h1 := Lollipops.ident_loopV (mem hc κ) j
  have h2 := ident_vertex_apply κ hc (.inr j)
  have h3 : (⟨Lollipops.loopV (mem hc κ) j, Lollipops.three_le_loopV (mem hc κ) j⟩ :
      BranchVertex (mem hc κ).data) =
      branchVertexEquiv (branching κ) (connected κ) (markValency_ne_zero κ)
        (κ.ident.markSource_injective hc) (.inr j) := by
    apply (ident κ hc).vertex.injective
    rw [h2]
    exact h1
  exact congrArg Subtype.val h3

theorem markV_regrow (j : Fin k) :
    Lollipops.markV (mem hc κ) j = oldSV (branching κ) (κ.markSource j) := by
  have h1 := Lollipops.ident_markV (mem hc κ) j
  have h2 := ident_vertex_apply κ hc
    (.inl ⟨κ.markSource j, Or.inr (mem_markSet κ.markSource j)⟩)
  have h3 : (⟨Lollipops.markV (mem hc κ) j, Lollipops.three_le_markV (mem hc κ) j⟩ :
      BranchVertex (mem hc κ).data) =
      branchVertexEquiv (branching κ) (connected κ) (markValency_ne_zero κ)
        (κ.ident.markSource_injective hc)
        (.inl ⟨κ.markSource j, Or.inr (mem_markSet κ.markSource j)⟩) := by
    apply (ident κ hc).vertex.injective
    rw [h2]
    refine h1.trans ?_
    change oldVertex k (mark j) = Fin.castAdd k (κ.ident.vertex _)
    rw [κ.ident.vertex_mark j]
    rfl
  exact congrArg Subtype.val h3

theorem uP_regrow (j : Fin k) :
    Lollipops.uP (mem hc κ) j = midV (branching κ).x j := by
  change (Lollipops.loopV (mem hc κ) j).1.1 = _
  rw [loopV_regrow]
  rfl

theorem xV_regrow (j : Fin k) :
    Lollipops.xV (mem hc κ) j = oldV (branching κ).x ((branching κ).x j) := by
  unfold Lollipops.xV
  rw [markV_regrow]
  rfl

theorem vC_regrow (j : Fin k) :
    Lollipops.vC (mem hc κ) j = tipV (branching κ).x j := by
  symm
  refine Lollipops.eq_vC_of_leaf (mem hc κ) (e := leafE (branching κ).x j) ?_ ?_ ?_
  · exact card_incidentEdges_tipV (branching κ).x j
  · rw [uP_regrow]
    exact leafE_mem_midV _ j
  · exact leafE_mem_tipV _ j

theorem mem_Keep_regrow (v : (mem hc κ).target.V) :
    v ∈ Lollipops.Keep (mem hc κ) ↔ ∃ w, v = oldV (branching κ).x w := by
  rw [Lollipops.mem_Keep, Lollipops.mem_Del]
  simp only [uP_regrow, vC_regrow]
  constructor
  · intro h
    rcases vertex_cases (branching κ).x v with ⟨w, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨w, rfl⟩
    · exact absurd (Or.inl ⟨j, rfl⟩) h
    · exact absurd (Or.inr ⟨j, rfl⟩) h
  · rintro ⟨w, rfl⟩ (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact midV_ne_oldV _ j w hj
    · exact tipV_ne_oldV _ j w hj

theorem oldV_mem_Keep (w : κ.target.V) :
    oldV (branching κ).x w ∈ Lollipops.Keep (mem hc κ) :=
  (mem_Keep_regrow hc κ _).mpr ⟨w, rfl⟩

/-! ## 2.  The target dictionary -/

/-- The restricted target vertex of an old vertex. -/
def keepV (w : κ.target.V) : (Lollipops.rTarget (mem hc κ)).V :=
  vRestrict (oldV (branching κ).x w) (oldV_mem_Keep hc κ w)

theorem keepV_bijective : Function.Bijective (keepV hc κ) := by
  constructor
  · intro w w' h
    exact oldV_injective _ (congrArg vIncl h)
  · intro v
    obtain ⟨w, hw⟩ := (mem_Keep_regrow hc κ (vIncl v)).mp (vIncl_mem v)
    exact ⟨w, vIncl_injective hw.symm⟩

/-- **The target vertex dictionary**, restriction of the regrowth to `κ`. -/
def tv : (Lollipops.rTarget (mem hc κ)).V ≃ κ.target.V :=
  (Equiv.ofBijective _ (keepV_bijective hc κ)).symm

theorem oldV_tv (v : (Lollipops.rTarget (mem hc κ)).V) :
    oldV (branching κ).x (tv hc κ v) = vIncl v := by
  have h : keepV hc κ (tv hc κ v) = v :=
    (Equiv.ofBijective _ (keepV_bijective hc κ)).apply_symm_apply v
  exact (congrArg vIncl h)

theorem keptEdge_oldE (e : κ.target.edges) :
    KeptEdge (Lollipops.Keep (mem hc κ)) (oldE (branching κ).x e) := by
  unfold KeptEdge
  rw [oldE_ends]
  exact ⟨oldV_mem_Keep hc κ _, oldV_mem_Keep hc κ _⟩

/-- An old edge, as a kept edge. -/
def keepE (e : κ.target.edges) :
    {e : (mem hc κ).target.edges // KeptEdge (Lollipops.Keep (mem hc κ)) e} :=
  ⟨oldE (branching κ).x e, keptEdge_oldE hc κ e⟩

theorem keepE_bijective : Function.Bijective (keepE hc κ) := by
  constructor
  · intro e e' h
    exact oldE_injective _ (congrArg Subtype.val h)
  · rintro ⟨e, he⟩
    rcases edge_cases (branching κ).x e with ⟨f, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨f, rfl⟩
    · exfalso
      have h := he.2
      rw [bridgeE_ends] at h
      exact absurd (uP_regrow hc κ j ▸ h) (Lollipops.uP_notMem_Keep (mem hc κ) j)
    · exfalso
      have h := he.1
      rw [leafE_ends] at h
      exact absurd (uP_regrow hc κ j ▸ h) (Lollipops.uP_notMem_Keep (mem hc κ) j)

/-- **The target edge dictionary.** -/
def te : (Lollipops.rTarget (mem hc κ)).edges ≃ κ.target.edges :=
  (edgeEquiv (Keep := Lollipops.Keep (mem hc κ))
    (hKeep := Lollipops.Keep_nonempty (mem hc κ))).trans
    (Equiv.ofBijective _ (keepE_bijective hc κ)).symm

theorem oldE_te (e : (Lollipops.rTarget (mem hc κ)).edges) :
    oldE (branching κ).x (te hc κ e) = edgeIncl e := by
  have h : keepE hc κ (te hc κ e) = ⟨edgeIncl e, keptEdge_edgeIncl e⟩ :=
    (Equiv.ofBijective _ (keepE_bijective hc κ)).apply_symm_apply _
  exact congrArg Subtype.val h

/-! ## 3.  The isomorphism of data -/

/-- **The isomorphism of data**: the old-vertex inclusion read backwards, with identity sheet
permutations. -/
def datumIso : GeometricDatumIso (Lollipops.rData (mem hc κ)) κ.data where
  targetVertex := tv hc κ
  targetEdge := te hc κ
  ends e := by
    left
    have h := oldE_ends (branching κ).x (te hc κ e)
    rw [oldE_te] at h
    apply Prod.ext <;> apply oldV_injective (branching κ).x
    · rw [oldV_tv]
      exact (congrArg Prod.fst h).symm
    · rw [oldV_tv]
      exact (congrArg Prod.snd h).symm
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition v := by
    rw [Transport.DatumIso.relabel_refl]
    change κ.data.vertexPartition (tv hc κ v) = (mem hc κ).data.vertexPartition (vIncl v)
    rw [← oldV_tv]
    rfl
  edgePartition e := by
    rw [Transport.DatumIso.relabel_refl]
    change κ.data.edgePartition (te hc κ e) = (mem hc κ).data.edgePartition (edgeIncl e)
    rw [← oldE_te]
    exact (ep_oldE (branching κ) _).symm
  compatible _ _ _ _ := by
    simp only [Equiv.refl_apply, Equiv.refl_symm]
    rfl

theorem oldSV_sourceVertexEquiv (X : (Lollipops.rData (mem hc κ)).SourceVertex) :
    oldSV (branching κ) ((datumIso hc κ).sourceVertexEquiv X) = svIncl X :=
  Subtype.ext (Prod.ext (oldV_tv hc κ X.1.1) rfl)

theorem oldSE_sourceEdgeEquiv (E : (Lollipops.rData (mem hc κ)).SourceEdge) :
    oldSE (branching κ) ((datumIso hc κ).sourceEdgeEquiv E) = seIncl E :=
  Subtype.ext (Prod.ext (oldE_te hc κ E.1.1) rfl)

/-! ## 4.  The marked isomorphism -/

theorem ident_row_oldND (F : NonDanglingEdge κ.data) :
    (ident κ hc).row (oldND (branching κ) (connected κ) (markValency_ne_zero κ) F).stablePath =
      coreSlot k (κ.ident.row (markedRow (markSet κ.markSource) F)) := by
  rw [ident_row_stablePath, rowTag_oldND]
  rfl

/-- **Restriction after regrowth is the identity**, up to isomorphism over the marked core. -/
def restrictRegrowIso : MarkedFrameIso (restrictFrame hc (regrowFrame hc κ)) κ where
  datum := datumIso hc κ
  mark j := by
    apply oldSV_injective (branching κ)
    exact (oldSV_sourceVertexEquiv hc κ (Lollipops.markSource (mem hc κ) j)).trans
      (markV_regrow hc κ j)
  overCore_vertex vertex hImage := by
    apply Fin.castAdd_injective n k
    refine Eq.trans ?_ (Lollipops.oldVertex_vertexEquiv (mem hc κ) hc vertex).symm
    have h := ident_vertex_apply κ hc (.inl ⟨_, hImage⟩)
    have hB : branchVertexEquiv (branching κ) (connected κ) (markValency_ne_zero κ)
        (κ.ident.markSource_injective hc) (.inl ⟨_, hImage⟩) =
        ⟨svIncl vertex.1, (Lollipops.branch_iff (mem hc κ) hc vertex.1).mp vertex.2⟩ :=
      Subtype.ext (oldSV_sourceVertexEquiv hc κ vertex.1)
    rw [hB] at h
    exact h.symm
  overCore_row edge := by
    apply Lollipops.coreSlot_injective
    refine Eq.trans ?_ (Lollipops.coreSlot_rowEquiv (mem hc κ) hc edge).symm
    have hE : Lollipops.ndIncl' (mem hc κ) hc edge =
        oldND (branching κ) (connected κ) (markValency_ne_zero κ)
          ((datumIso hc κ).nonDanglingEdgeEquiv
            (restrictFrame hc (regrowFrame hc κ)).fullDim.valid.1 edge) :=
      Subtype.ext (oldSE_sourceEdgeEquiv hc κ edge.1).symm
    rw [hE]
    exact (ident_row_oldND hc κ _).symm

end

end DraismaVargas.Count.MarkedCount.CorrRestrictRegrow
