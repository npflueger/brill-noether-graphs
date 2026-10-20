module

public import DraismaVargasMarkedCount.MarkedCount.RestrictFrame
public import DraismaVargasCount.GeometricSegmentWalls
public import DraismaVargasCount.GeometricValidityTransport

@[expose] public section

/-!
# Restriction is functorial on isomorphisms of frames

An isomorphism of frames over
the identity of the lollipop core carries the lollipop vertices and the marks to themselves
(it is over the identity on branch vertices), hence the branches to the branches
(`targetVertex_uP`, `targetVertex_vC`) and the kept target vertices to the kept ones.  So it
restricts (`Restrict.restrictIso`), and the restriction is over the identity of the marked core
(`vertexEquiv_restrictIso`, `rowEquiv_restrictIso`).
-/

namespace DraismaVargas.Count.MarkedCount.Lollipops

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open DraismaVargas.Count (GeometricDatumIso)
open Utilities.Certificate.ExplicitPotential (Core)
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}

/-- The leaf adjacent to `φ(w_j)` is `φ(C_j)`. -/
theorem eq_vC_of_leaf {y : Fin (p + (k + k)) → ℚ}
    (M : FibreMember (attachLollipops core mark) y degree) {j : Fin k} {w : M.target.V}
    (hw : Count.IsLeafVertex M.target w) {e : M.target.edges}
    (he₁ : e ∈ GluingDatum.incidentEdges (uP M j)) (he₂ : e ∈ GluingDatum.incidentEdges w) :
    w = vC M j := by
  have hEnds := Count.fst_eq_or_snd_eq_of_mem_incidentEdges he₂
  have hw1 : (GluingDatum.incidentEdges w).card = 1 := hw
  have hxV := valency_xV M j
  have huP := uP_divalent M j
  rw [incidentEdges_uP] at he₁
  simp only [Finset.mem_insert, Finset.mem_singleton] at he₁
  rcases he₁ with rfl | rfl
  · exfalso
    rcases tb_ends M j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hEnds with h | h
    all_goals first
      | (rw [h1] at h; subst h; omega)
      | (rw [h2] at h; subst h; omega)
  · rcases tl_ends M j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hEnds with h | h
    · rw [h1] at h; subst h; omega
    · rw [h2] at h; exact h.symm
    · rw [h1] at h; exact h.symm
    · rw [h2] at h; subst h; omega

variable {f f' : Frame (attachLollipops core mark) degree} (iso : FrameIso f f')

/-- The isomorphism of data, read between the members. -/
def isoD : GeometricDatumIso (f.member 0).data (f'.member 0).data := iso.datum

theorem sourceVertexEquiv_loopV (j : Fin k) :
    (isoD iso).sourceVertexEquiv (loopV (f.member 0) j) = loopV (f'.member 0) j := by
  have h := iso.overCore_vertex ⟨loopV (f.member 0) j, three_le_loopV (f.member 0) j⟩
  have h' : iso.datum.branchVertexEquiv f.fullDim.valid.1
      ⟨loopV (f.member 0) j, three_le_loopV (f.member 0) j⟩ =
      ⟨loopV (f'.member 0) j, three_le_loopV (f'.member 0) j⟩ := by
    apply f'.ident.vertex.injective
    exact h.trans ((ident_loopV (f.member 0) j).trans (ident_loopV (f'.member 0) j).symm)
  exact congrArg Subtype.val h'

theorem sourceVertexEquiv_markV (j : Fin k) :
    (isoD iso).sourceVertexEquiv (markV (f.member 0) j) = markV (f'.member 0) j := by
  have h := iso.overCore_vertex ⟨markV (f.member 0) j, three_le_markV (f.member 0) j⟩
  have h' : iso.datum.branchVertexEquiv f.fullDim.valid.1
      ⟨markV (f.member 0) j, three_le_markV (f.member 0) j⟩ =
      ⟨markV (f'.member 0) j, three_le_markV (f'.member 0) j⟩ := by
    apply f'.ident.vertex.injective
    exact h.trans ((ident_markV (f.member 0) j).trans (ident_markV (f'.member 0) j).symm)
  exact congrArg Subtype.val h'

theorem targetVertex_uP (j : Fin k) :
    (isoD iso).targetVertex (uP (f.member 0) j) = uP (f'.member 0) j :=
  congrArg (fun X : (f'.member 0).data.SourceVertex ↦ X.1.1) (sourceVertexEquiv_loopV iso j)

theorem targetVertex_vC (j : Fin k) :
    (isoD iso).targetVertex (vC (f.member 0) j) = vC (f'.member 0) j := by
  refine eq_vC_of_leaf (f'.member 0) (e := (isoD iso).targetEdge (tl (f.member 0) j)) ?_ ?_ ?_
  · exact ((isoD iso).incidentEdges_card_map (vC (f.member 0) j)).trans
      (vC_isLeaf (f.member 0) j)
  · rw [← targetVertex_uP iso j]
    exact ((isoD iso).mem_incidentEdges_map _ _).mpr (tl_mem_uP (f.member 0) j)
  · exact ((isoD iso).mem_incidentEdges_map _ _).mpr (tl_mem_vC (f.member 0) j)

theorem targetVertex_mem_Keep (v : (f.member 0).target.V) :
    (isoD iso).targetVertex v ∈ Keep (f'.member 0) ↔ v ∈ Keep (f.member 0) := by
  rw [mem_Keep, mem_Keep, not_iff_not, mem_Del, mem_Del]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · left
      exact ⟨j, (isoD iso).targetVertex.injective ((targetVertex_uP iso j).trans hj)⟩
    · right
      exact ⟨j, (isoD iso).targetVertex.injective ((targetVertex_vC iso j).trans hj)⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Or.inl ⟨j, (targetVertex_uP iso j).symm⟩
    · exact Or.inr ⟨j, (targetVertex_vC iso j).symm⟩

/-- **The restricted isomorphism.** -/
def restrictFrameIso : GeometricDatumIso (rData (f.member 0)) (rData (f'.member 0)) :=
  restrictIso (Φ := isoD iso) (targetVertex_mem_Keep iso)

theorem restrictFrameIso_markSource (j : Fin k) :
    (restrictFrameIso iso).sourceVertexEquiv (markSource (f.member 0) j) =
      markSource (f'.member 0) j :=
  svIncl_injective (sourceVertexEquiv_markV iso j)

theorem vertexEquiv_restrictFrameIso (hc : IsMarkedCubic core mark)
    (X : MarkedBranchVertex (rData (f.member 0)) (marks (f.member 0)))
    (X' : MarkedBranchVertex (rData (f'.member 0)) (marks (f'.member 0)))
    (hX : X'.1 = (restrictFrameIso iso).sourceVertexEquiv X.1) :
    vertexEquiv (f'.member 0) hc X' = vertexEquiv (f.member 0) hc X := by
  apply Fin.castAdd_injective n k
  refine (oldVertex_vertexEquiv (f'.member 0) hc X').trans
    (Eq.trans ?_ (oldVertex_vertexEquiv (f.member 0) hc X).symm)
  have h := iso.overCore_vertex ⟨svIncl X.1, (branch_iff (f.member 0) hc X.1).mp X.2⟩
  refine Eq.trans ?_ h
  congr 1
  apply Subtype.ext
  change svIncl X'.1 = (isoD iso).sourceVertexEquiv (svIncl X.1)
  rw [hX]
  rfl

theorem rowEquiv_restrictFrameIso (hc : IsMarkedCubic core mark)
    (E : NonDanglingEdge (rData (f.member 0)))
    (E' : NonDanglingEdge (rData (f'.member 0)))
    (hE : E'.1 = (restrictFrameIso iso).sourceEdgeEquiv E.1) :
    rowEquiv (f'.member 0) hc (markedRow (marks (f'.member 0)) E') =
      rowEquiv (f.member 0) hc (markedRow (marks (f.member 0)) E) := by
  apply coreSlot_injective
  rw [coreSlot_rowEquiv, coreSlot_rowEquiv]
  have h := iso.overCore_row (NonDanglingEdge.stablePath (ndIncl' (f.member 0) hc E))
  refine Eq.trans ?_ h
  congr 1
  refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
  change seIncl E'.1 = (isoD iso).sourceEdgeEquiv (seIncl E.1)
  rw [hE]
  rfl

end

end DraismaVargas.Count.MarkedCount.Lollipops
