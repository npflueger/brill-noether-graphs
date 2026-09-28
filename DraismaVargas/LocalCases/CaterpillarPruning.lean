import DraismaVargas.LocalCases.CaterpillarDatum
import DraismaVargas.LocalCases.CycleRows
import DraismaVargas.LocalCases.DanglingSideStructure

/-!
# Pruning the caterpillar source

This file proves the occurrence-level pruning facts needed to identify the
stable source of `CaterpillarDatum.caterpillarDatum`.  The first layer is the
literal loop census: over every leaf edge of the target, sheets `0` and the
partner sheet give two distinct quotient-source occurrences with the same
two endpoints.  Hence neither occurrence can be the unique crossing
occurrence of a dangling cut.

The later layers use these loop flags as the positive-genus anchors on both
sides of every caterpillar bridge and identify the singleton sheet tails as
the dangling occurrences.
-/

namespace DraismaVargas.LocalCases.CaterpillarPruning

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingSideStructure

/-- The target occurrences `u_i v_i`.  In the depth-first occurrence
numbering these are the indices divisible by three, together with the final
exceptional index `6m+2`. -/
def IsLeafEdge (m : ℕ) (i : Fin (6 * m + 3)) : Prop :=
  i.val % 3 = 0 ∨ i.val = 6 * m + 2

instance (m : ℕ) (i : Fin (6 * m + 3)) : Decidable (IsLeafEdge m i) := by
  unfold IsLeafEdge
  infer_instance

theorem not_pair_of_leaf {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) : ¬ IsPairEdge m i.val := by
  unfold IsLeafEdge at hLeaf
  unfold IsPairEdge
  omega

/-- The two ends of a leaf edge belong to the same lollipop pair. -/
theorem pairIndex_parent_eq_of_leaf {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    pairIndex (parentIndex (i.val + 1)) = pairIndex (i.val + 1) := by
  have hi := i.isLt
  unfold IsLeafEdge at hLeaf
  unfold pairIndex lolli parentIndex
  split_ifs <;> omega

/-- The partner sheet of the lollipop containing the child of `i`. -/
def partnerSheet (m : ℕ) (i : Fin (6 * m + 3)) : Fin (m + 2) :=
  ⟨pairIndex (i.val + 1), pairIndex_lt m (i.val + 1) (by omega)⟩

@[simp] theorem partnerSheet_val (m : ℕ) (i : Fin (6 * m + 3)) :
    (partnerSheet m i).val = pairIndex (i.val + 1) := rfl

theorem partnerSheet_pos (m : ℕ) (i : Fin (6 * m + 3)) :
    1 ≤ (partnerSheet m i).val := pairIndex_pos _

/-- At a target vertex, its partner sheet and the spine sheet name the same
quotient-source vertex. -/
theorem sourceEndpoint_partner_eq_zero (m : ℕ) (v : (catTree m).V) :
    (caterpillarDatum m).sourceEndpoint v
        ⟨pairIndex v.val, pairIndex_lt m v.val (by omega)⟩ =
      (caterpillarDatum m).sourceEndpoint v 0 := by
  refine (caterpillarDatum m).sourceEndpoint_congr v ?_
  show (pairPart m (pairIndex v.val)).Rel
    ⟨pairIndex v.val, pairIndex_lt m v.val (by omega)⟩ 0
  exact pairPart_rel_zero m _ _ rfl

/-- A sheet other than `0` and the local partner is a singleton block. -/
theorem blockCard_pairPart_other (m j : ℕ) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsj : s.val ≠ j) :
    (pairPart m j).blockCard s = 1 := by
  have hBlock : (pairPart m j).block s = {s} := by
    ext t
    rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff,
      pairPart_repr, pairPart_repr, if_neg hsj]
    by_cases ht : t.val = j
    · rw [if_pos ht, Finset.mem_singleton]
      constructor
      · intro h
        have : s.val = 0 := by simpa using congrArg Fin.val h
        exact (hs0 this).elim
      · intro h
        have : s.val = j := by simpa [h] using ht
        exact (hsj this).elim
    · rw [if_neg ht, Finset.mem_singleton]
      exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  rw [SheetPartition.blockCard, hBlock, Finset.card_singleton]

/-- The spine-sheet occurrence over a target leaf edge. -/
noncomputable def loopFirst (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).SourceEdge :=
  (caterpillarDatum m).sourceEdge (occ m i) 0

/-- The partner-sheet occurrence over the same target leaf edge. -/
noncomputable def loopSecond (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).SourceEdge :=
  (caterpillarDatum m).sourceEdge (occ m i) (partnerSheet m i)

/-- Over a leaf edge the two loop flags are distinct actual source
occurrences: its occurrence partition is discrete and the partner is nonzero. -/
theorem loopFirst_ne_loopSecond {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) : loopFirst m i ≠ loopSecond m i := by
  intro hEq
  have hSheet := congrArg
    (fun edge : (caterpillarDatum m).SourceEdge ↦ edge.1.2) hEq
  unfold loopFirst loopSecond at hSheet
  rw [(caterpillarDatum m).sourceEdge_sheet,
    (caterpillarDatum m).sourceEdge_sheet,
    caterpillarDatum_edgePartition,
    catEdgePart_of_not_pair m i (not_pair_of_leaf hLeaf)] at hSheet
  change (0 : Fin (m + 2)) = partnerSheet m i at hSheet
  have hVal := congrArg Fin.val hSheet
  simp only [Fin.val_zero, partnerSheet_val] at hVal
  have hPos := partnerSheet_pos m i
  have hZero : (partnerSheet m i).val = 0 := by
    exact hVal.symm
  omega

/-- The two loop flags have the same ordered endpoints.  The edge partition
is discrete, but the vertex partition glues the partner sheet to sheet `0` at
both ends of the leaf edge. -/
theorem sourceEnds_loopSecond_eq_loopFirst {m : ℕ}
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) :
    (caterpillarDatum m).sourceEnds (loopSecond m i) =
      (caterpillarDatum m).sourceEnds (loopFirst m i) := by
  unfold loopSecond loopFirst
  rw [sourceEnds_sourceEdge, sourceEnds_sourceEdge]
  apply Prod.ext
  · have hPair := pairIndex_parent_eq_of_leaf hLeaf
    have h := sourceEndpoint_partner_eq_zero m (catParent m i)
    simpa [loopFirst, loopSecond, partnerSheet, hPair] using h
  · exact sourceEndpoint_partner_eq_zero m i.succ

/-- Two distinct occurrences joining the same endpoints cannot be dangling:
a dangling cut requires its distinguished occurrence to be the unique
crossing occurrence. -/
theorem not_isDangling_of_parallel
    {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
    {first second : data.SourceEdge} (hNe : first ≠ second)
    (hEnds : data.sourceEnds second = data.sourceEnds first) :
    ¬ IsDangling data first := by
  intro hDangling
  have hTwo : 2 ≤ num_edges data.sourceGraph
      (data.sourceEnds first).1 (data.sourceEnds first).2 :=
    CycleRows.two_le_num_edges_of_ne data hNe (Or.inl rfl)
      (Or.inl hEnds)
  rcases hDangling with hCut | hCut <;> obtain ⟨cut⟩ := hCut
  · have hOne := cut.num_edges_endpoints
    omega
  · have hOne := cut.num_edges_endpoints
    have hSym := num_edges_symmetric data.sourceGraph
      (data.sourceEnds first).1 (data.sourceEnds first).2
    omega

/-- **Both actual flags of every caterpillar loop survive pruning.** -/
theorem loopFirst_survives {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    ¬ IsDangling (caterpillarDatum m) (loopFirst m i) := by
  exact not_isDangling_of_parallel (caterpillarDatum m)
    (loopFirst_ne_loopSecond hLeaf) (sourceEnds_loopSecond_eq_loopFirst hLeaf)

theorem loopSecond_survives {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    ¬ IsDangling (caterpillarDatum m) (loopSecond m i) := by
  exact not_isDangling_of_parallel (caterpillarDatum m)
    (loopFirst_ne_loopSecond hLeaf).symm
    (sourceEnds_loopSecond_eq_loopFirst hLeaf).symm

/-! ## The complete surviving star at a fold -/

/-- The fold vertex `C_i` at the leaf end of `u_i v_i`, named on the spine
sheet.  Its partner sheet gives the same quotient-source vertex. -/
def leafTarget (m : ℕ) (i : Fin (6 * m + 3)) : (catTree m).V :=
  ((occ m i : (catTree m).edges) : (catTree m).V × (catTree m).V).2

@[simp] theorem leafTarget_val (m : ℕ) (i : Fin (6 * m + 3)) :
    (leafTarget m i).val = i.val + 1 := rfl

def foldVertex (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).SourceVertex :=
  (caterpillarDatum m).sourceEndpoint (leafTarget m i) 0

@[simp] theorem foldVertex_target (m : ℕ) (i : Fin (6 * m + 3)) :
    (foldVertex m i).1.1 = leafTarget m i := rfl

@[simp] theorem foldVertex_sheet (m : ℕ) (i : Fin (6 * m + 3)) :
    (foldVertex m i).1.2 = 0 := by
  change (catVertexPart m (leafTarget m i)).repr 0 = 0
  rw [catVertexPart, pairPart_repr]
  split <;> rfl

theorem loopFirst_incident_fold (m : ℕ) (i : Fin (6 * m + 3)) :
    Incident (caterpillarDatum m) (loopFirst m i) (foldVertex m i) := by
  unfold Incident loopFirst foldVertex
  rw [sourceEnds_sourceEdge]
  exact Or.inr rfl

theorem loopSecond_incident_fold {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    Incident (caterpillarDatum m) (loopSecond m i) (foldVertex m i) := by
  unfold Incident
  rw [show (caterpillarDatum m).sourceEnds (loopSecond m i) =
      (caterpillarDatum m).sourceEnds (loopFirst m i) from
    sourceEnds_loopSecond_eq_loopFirst hLeaf]
  exact loopFirst_incident_fold m i

/-- Exactly two actual source occurrences meet a caterpillar fold. -/
theorem card_incidentSourceEdge_fold {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    Fintype.card (IncidentSourceEdge (caterpillarDatum m) (foldVertex m i)) = 2 := by
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  simp only [foldVertex_target, foldVertex_sheet]
  rcases hLeaf with hMod | hLast
  · have hInc := incidentIndices_leaf m (leafTarget m i) (by
      simp only [leafTarget_val]
      omega)
    rw [sum_incidentEdges_one m (leafTarget m i) hInc]
    have hPred : (⟨(leafTarget m i).val - 1, by omega⟩ : Fin (6 * m + 3)) = i := by
      apply Fin.ext
      simp only [leafTarget_val]
      omega
    rw [hPred]
    rw [caterpillarDatum_edgePartition,
      catEdgePart_of_not_pair m i (not_pair_of_leaf (Or.inl hMod)),
      caterpillarDatum_vertexPartition, catVertexPart,
      blockCountWithin_discrete, blockCard_pairPart_zero]
    · exact pairIndex_pos _
    · exact pairIndex_lt m (leafTarget m i).val (by omega)
  · have hTarget : (leafTarget m i).val = 6 * m + 3 := by
      rw [leafTarget_val, hLast]
    have hInc := incidentIndices_lastLeaf m (leafTarget m i) hTarget
    rw [sum_incidentEdges_one m (leafTarget m i) hInc]
    have hIndex : (⟨6 * m + 2, by omega⟩ : Fin (6 * m + 3)) = i := by
      apply Fin.ext
      exact hLast.symm
    rw [hIndex]
    rw [caterpillarDatum_edgePartition,
      catEdgePart_of_not_pair m i (not_pair_of_leaf (Or.inr hLast)),
      caterpillarDatum_vertexPartition, catVertexPart,
      blockCountWithin_discrete, blockCard_pairPart_zero]
    · exact pairIndex_pos _
    · exact pairIndex_lt m _ (by omega)

/-- The two flags are the complete surviving fold star; in particular the
surviving valency at every fold is exactly two. -/
theorem nonDanglingValency_fold {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    nonDanglingValency (caterpillarDatum m) (foldVertex m i) = 2 := by
  classical
  have hFirst := loopFirst_survives hLeaf
  have hSecond := loopSecond_survives hLeaf
  have hFirstInc := loopFirst_incident_fold m i
  have hSecondInc := loopSecond_incident_fold hLeaf
  have hLower : 2 ≤ nonDanglingValency (caterpillarDatum m) (foldVertex m i) := by
    rw [← card_nonDanglingIncident]
    refine le_trans ?_ (Finset.card_le_card (s :=
      {loopFirst m i, loopSecond m i}) (t :=
        nonDanglingIncident (caterpillarDatum m) (foldVertex m i)) ?_)
    · rw [Finset.card_pair (loopFirst_ne_loopSecond hLeaf)]
    · intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with rfl | hEdge
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨hFirst, hFirstInc⟩
      · rw [Finset.mem_singleton] at hEdge
        subst edge
        exact (mem_nonDanglingIncident _ _ _).mpr ⟨hSecond, hSecondInc⟩
  have hUpper := NonDanglingValency.nonDanglingValency_le_card_incidentSourceEdge
    (caterpillarDatum m) (foldVertex m i)
  rw [card_incidentSourceEdge_fold hLeaf] at hUpper
  omega

/-- The two actual loop flags are consecutive in their stable row.  Both
flags count, although they meet the same pair of quotient-source vertices. -/
theorem loopFlags_consecutive {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) :
    Consecutive (caterpillarDatum m)
      ⟨loopFirst m i, loopFirst_survives hLeaf⟩
      ⟨loopSecond m i, loopSecond_survives hLeaf⟩ := by
  refine ⟨?_, foldVertex m i, loopFirst_incident_fold m i,
    loopSecond_incident_fold hLeaf, nonDanglingValency_fold hLeaf⟩
  intro hEq
  exact loopFirst_ne_loopSecond hLeaf (congrArg Subtype.val hEq)

/-- The attachment end `u_i` of a leaf edge, named on the central sheet. -/
def loopBaseVertex (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).SourceVertex :=
  (caterpillarDatum m).sourceEndpoint
    ((occ m i : (catTree m).edges) : (catTree m).V × (catTree m).V).1 0

theorem loopFirst_incident_base (m : ℕ) (i : Fin (6 * m + 3)) :
    Incident (caterpillarDatum m) (loopFirst m i) (loopBaseVertex m i) := by
  unfold Incident loopFirst loopBaseVertex
  rw [sourceEnds_sourceEdge]
  exact Or.inl rfl

/-- A proved loop flag makes its attachment vertex active. -/
theorem nonDanglingValency_loopBase_ne_zero {m : ℕ}
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i) :
    nonDanglingValency (caterpillarDatum m) (loopBaseVertex m i) ≠ 0 := by
  intro hZero
  have hMem : loopFirst m i ∈
      nonDanglingIncident (caterpillarDatum m) (loopBaseVertex m i) :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨loopFirst_survives hLeaf, loopFirst_incident_base m i⟩
  have hPos := Finset.card_pos.mpr ⟨loopFirst m i, hMem⟩
  rw [card_nonDanglingIncident, hZero] at hPos
  omega

/-! ## A bridge survives when both sides reach a loop anchor -/

/-- One positive source adjacency, landing away from `forbidden`, is a
confined one-step reach. -/
theorem reachP_single {G : CFGraph} {start finish forbidden : G.V}
    (hEdge : 0 < num_edges G start finish) (hNe : finish ≠ forbidden) :
    ReachP G (fun vertex ↦ vertex ≠ forbidden) start finish :=
  Relation.ReflTransGen.tail (Relation.ReflTransGen.refl) ⟨hEdge, hNe⟩

/-- If each endpoint can reach an active loop vertex without stepping onto
the other endpoint, neither orientation can be the genus-zero side of a
dangling cut.  This is the bridge-safe replacement for a cycle-through-edge
argument. -/
theorem not_isDangling_of_active_reaches
    {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
    (edge : data.SourceEdge)
    {first second firstAnchor secondAnchor : data.SourceVertex}
    (hEnds : data.sourceEnds edge = (first, second))
    (hFirstActive : nonDanglingValency data firstAnchor ≠ 0)
    (hSecondActive : nonDanglingValency data secondAnchor ≠ 0)
    (hFirstReach : ReachP data.sourceGraph (fun vertex ↦ vertex ≠ second)
      first firstAnchor)
    (hSecondReach : ReachP data.sourceGraph (fun vertex ↦ vertex ≠ first)
      second secondAnchor) :
    ¬ IsDangling data edge := by
  intro hDangling
  rcases hDangling with hCut | hCut
  · obtain ⟨cut⟩ := hCut
    rw [hEnds] at cut
    have hMem := mem_side_of_reachP cut cut.left_mem hFirstReach
    exact hFirstActive
      (nonDanglingValency_eq_zero_of_mem_side data cut hMem)
  · obtain ⟨cut⟩ := hCut
    rw [hEnds] at cut
    have hMem := mem_side_of_reachP cut cut.left_mem hSecondReach
    exact hSecondActive
      (nonDanglingValency_eq_zero_of_mem_side data cut hMem)

/-! ## The complete leaf-fibre pruning census -/

/-- A singleton sheet occurrence over a leaf edge. -/
noncomputable def leafOccurrence (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) : (caterpillarDatum m).SourceEdge :=
  (caterpillarDatum m).sourceEdge (occ m i) s

/-- Its endpoint above the target leaf. -/
def leafSourceVertex (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) : (caterpillarDatum m).SourceVertex :=
  (caterpillarDatum m).sourceEndpoint (leafTarget m i) s

@[simp] theorem leafSourceVertex_target (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) :
    (leafSourceVertex m i s).1.1 = leafTarget m i := rfl

@[simp] theorem leafSourceVertex_sheet_of_other (m : ℕ)
    (i : Fin (6 * m + 3)) (s : Fin (m + 2))
    (hs : s.val ≠ pairIndex (leafTarget m i).val) :
    (leafSourceVertex m i s).1.2 = s := by
  change (pairPart m (pairIndex (leafTarget m i).val)).repr s = s
  exact pairPart_repr_of_ne m _ s hs

theorem leafOccurrence_incident_leaf (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) :
    Incident (caterpillarDatum m) (leafOccurrence m i s)
      (leafSourceVertex m i s) := by
  unfold Incident leafOccurrence leafSourceVertex
  rw [sourceEnds_sourceEdge]
  exact Or.inr rfl

/-- Away from the two-sheet loop block, the source vertex above the target
leaf has graph degree one. -/
theorem card_incidentSourceEdge_leaf_other {m : ℕ}
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i)
    (s : Fin (m + 2)) (hs0 : s.val ≠ 0)
    (hsPartner : s.val ≠ (partnerSheet m i).val) :
    Fintype.card
      (IncidentSourceEdge (caterpillarDatum m) (leafSourceVertex m i s)) = 1 := by
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  simp only [leafSourceVertex_target,
    leafSourceVertex_sheet_of_other m i s (by simpa [leafTarget_val] using hsPartner)]
  rcases hLeaf with hMod | hLast
  · have hInc := incidentIndices_leaf m (leafTarget m i) (by
      simp only [leafTarget_val]
      omega)
    rw [sum_incidentEdges_one m (leafTarget m i) hInc]
    have hPred : (⟨(leafTarget m i).val - 1, by omega⟩ : Fin (6 * m + 3)) = i := by
      apply Fin.ext
      simp only [leafTarget_val]
      omega
    rw [hPred, caterpillarDatum_edgePartition,
      catEdgePart_of_not_pair m i (not_pair_of_leaf (Or.inl hMod)),
      caterpillarDatum_vertexPartition, catVertexPart,
      blockCountWithin_discrete,
      blockCard_pairPart_other m _ s hs0]
    simpa [leafTarget_val] using hsPartner
  · have hTarget : (leafTarget m i).val = 6 * m + 3 := by
      rw [leafTarget_val, hLast]
    have hInc := incidentIndices_lastLeaf m (leafTarget m i) hTarget
    rw [sum_incidentEdges_one m (leafTarget m i) hInc]
    have hIndex : (⟨6 * m + 2, by omega⟩ : Fin (6 * m + 3)) = i := by
      apply Fin.ext
      exact hLast.symm
    rw [hIndex, caterpillarDatum_edgePartition,
      catEdgePart_of_not_pair m i (not_pair_of_leaf (Or.inr hLast)),
      caterpillarDatum_vertexPartition, catVertexPart,
      blockCountWithin_discrete,
      blockCard_pairPart_other m _ s hs0]
    simpa [leafTarget_val] using hsPartner

theorem vertex_degree_leaf_other {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPartner : s.val ≠ (partnerSheet m i).val) :
    vertex_degree (caterpillarDatum m).sourceGraph (leafSourceVertex m i s) = 1 := by
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge,
    card_incidentSourceEdge_leaf_other hLeaf s hs0 hsPartner]
  norm_num

/-- Every other sheet over a target leaf is a genuine dangling occurrence,
with the singleton leaf as its explicit genus-zero side. -/
theorem leafOccurrence_dangles_of_other {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPartner : s.val ≠ (partnerSheet m i).val) :
    IsDangling (caterpillarDatum m) (leafOccurrence m i s) := by
  apply isDangling_of_sourceEnds_snd_degree_eq_one
    (caterpillarDatum m) (caterpillarDatum_connected m)
  unfold leafOccurrence
  rw [sourceEnds_sourceEdge]
  exact vertex_degree_leaf_other hLeaf s hs0 hsPartner

/-- **Exact leaf-fibre occurrence census.**  The two loop flags, named by
sheet `0` and the local partner, survive; every other singleton sheet
occurrence dangles. -/
theorem leafOccurrence_isDangling_iff {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : IsLeafEdge m i) (s : Fin (m + 2)) :
    IsDangling (caterpillarDatum m) (leafOccurrence m i s) ↔
      s.val ≠ 0 ∧ s.val ≠ (partnerSheet m i).val := by
  constructor
  · intro hDangling
    constructor
    · intro hs0
      have hs : s = 0 := Fin.ext hs0
      subst s
      exact loopFirst_survives hLeaf hDangling
    · intro hsPartner
      have hs : s = partnerSheet m i := Fin.ext hsPartner
      subst s
      exact loopSecond_survives hLeaf hDangling
  · rintro ⟨hs0, hsPartner⟩
    exact leafOccurrence_dangles_of_other hLeaf s hs0 hsPartner

/-! ## The stem census -/

/-- The target occurrences `p_i u_i`, excluding the exceptional final leaf
index which has the same residue. -/
def IsStemEdge (m : ℕ) (i : Fin (6 * m + 3)) : Prop :=
  i.val % 3 = 2 ∧ i.val ≠ 6 * m + 2

instance (m : ℕ) (i : Fin (6 * m + 3)) : Decidable (IsStemEdge m i) := by
  unfold IsStemEdge
  infer_instance

theorem pair_of_stem {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) : IsPairEdge m i.val :=
  Or.inr hStem

/-- The leaf occurrence immediately after a stem in the depth-first target
numbering. -/
def stemLeafIndex (m : ℕ) (i : Fin (6 * m + 3))
    (hStem : IsStemEdge m i) : Fin (6 * m + 3) :=
  ⟨i.val + 1, by
    have hi := i.isLt
    rcases hStem with ⟨hMod, hLast⟩
    omega⟩

@[simp] theorem stemLeafIndex_val {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) : (stemLeafIndex m i hStem).val = i.val + 1 := rfl

theorem stemLeafIndex_isLeaf {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) : IsLeafEdge m (stemLeafIndex m i hStem) := by
  left
  simp only [stemLeafIndex_val]
  have hMod := hStem.1
  omega

theorem partnerSheet_stemLeaf {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) :
    partnerSheet m (stemLeafIndex m i hStem) = partnerSheet m i := by
  have hLolli : lolli (i.val + 1 + 1) = lolli (i.val + 1) := by
    unfold lolli
    have hMod := hStem.1
    omega
  apply Fin.ext
  simp only [partnerSheet_val, stemLeafIndex_val]
  unfold pairIndex
  rw [hLolli]

/-- An actual source occurrence over a target stem. -/
noncomputable def stemOccurrence (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) : (caterpillarDatum m).SourceEdge :=
  (caterpillarDatum m).sourceEdge (occ m i) s

/-- Its endpoint above `u_i`. -/
def stemTarget (m : ℕ) (i : Fin (6 * m + 3)) : (catTree m).V :=
  ((occ m i : (catTree m).edges) : (catTree m).V × (catTree m).V).2

@[simp] theorem stemTarget_val (m : ℕ) (i : Fin (6 * m + 3)) :
    (stemTarget m i).val = i.val + 1 := rfl

def stemTipVertex (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) : (caterpillarDatum m).SourceVertex :=
  (caterpillarDatum m).sourceEndpoint (stemTarget m i) s

@[simp] theorem stemTipVertex_target (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) :
    (stemTipVertex m i s).1.1 = stemTarget m i := rfl

@[simp] theorem stemTipVertex_sheet_of_other (m : ℕ)
    (i : Fin (6 * m + 3)) (s : Fin (m + 2))
    (hs : s.val ≠ (partnerSheet m i).val) :
    (stemTipVertex m i s).1.2 = s := by
  change (pairPart m (pairIndex (i.val + 1))).repr s = s
  exact pairPart_repr_of_ne m _ s hs

theorem stemOccurrence_incident_tip (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) :
    Incident (caterpillarDatum m) (stemOccurrence m i s)
      (stemTipVertex m i s) := by
  unfold Incident stemOccurrence stemTipVertex
  rw [sourceEnds_sourceEdge]
  exact Or.inr rfl

theorem stemLeaf_incident_tip {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) (s : Fin (m + 2)) :
    Incident (caterpillarDatum m)
      (leafOccurrence m (stemLeafIndex m i hStem) s)
      (stemTipVertex m i s) := by
  unfold Incident leafOccurrence stemTipVertex
  rw [sourceEnds_sourceEdge]
  left
  change (caterpillarDatum m).sourceEndpoint
      (catParent m (stemLeafIndex m i hStem)) s =
    (caterpillarDatum m).sourceEndpoint (stemTarget m i) s
  congr 1
  apply Fin.ext
  change parentIndex (i.val + 1 + 1) = i.val + 1
  unfold parentIndex
  have hMod := hStem.1
  split_ifs <;> omega

theorem stemOccurrence_ne_stemLeaf {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) (s : Fin (m + 2)) :
    stemOccurrence m i s ≠ leafOccurrence m (stemLeafIndex m i hStem) s := by
  intro hEq
  have hTarget := congrArg
    (fun edge : (caterpillarDatum m).SourceEdge ↦ edge.1.1) hEq
  unfold stemOccurrence leafOccurrence at hTarget
  simp only [GluingDatum.sourceEdge_target] at hTarget
  have hIndex := occ_injective m hTarget
  have hVal := congrArg Fin.val hIndex
  simp only [stemLeafIndex_val] at hVal
  omega

/-- Away from the stem's paired block, the source vertex above `u_i` has
exactly the stem and its leaf occurrence. -/
theorem card_incidentSourceEdge_stemTip_other {m : ℕ}
    {i : Fin (6 * m + 3)} (hStem : IsStemEdge m i)
    (s : Fin (m + 2)) (hs0 : s.val ≠ 0)
    (hsPartner : s.val ≠ (partnerSheet m i).val) :
    Fintype.card
      (IncidentSourceEdge (caterpillarDatum m) (stemTipVertex m i s)) = 2 := by
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  simp only [stemTipVertex_target,
    stemTipVertex_sheet_of_other m i s hsPartner]
  have hTipMod : (i.val + 1) % 3 = 0 := by
    have hMod := hStem.1
    omega
  have hTipLo : 3 ≤ i.val + 1 := by
    have := hStem.1
    omega
  have hTipHi : i.val + 1 ≤ 6 * m := by
    have hi := i.isLt
    rcases hStem with ⟨hMod, hLast⟩
    omega
  have hInc := incidentIndices_stem m
    (stemTarget m i)
    hTipMod hTipLo hTipHi
  rw [sum_incidentEdges_two m _ (by
      simp only [ne_eq, Fin.mk.injEq]
      exact Nat.ne_of_lt (Nat.sub_lt
        (lt_of_lt_of_le (by norm_num) hTipLo) (by norm_num))) hInc]
  have hTargetEdgeLt : (stemTarget m i).val < 6 * m + 3 := by
    simpa only [stemTarget_val, stemLeafIndex_val] using
      (stemLeafIndex m i hStem).isLt
  have hPredLt : (stemTarget m i).val - 1 < 6 * m + 3 :=
    lt_of_le_of_lt (Nat.sub_le _ _) hTargetEdgeLt
  have hFirst : (⟨(stemTarget m i).val - 1, hPredLt⟩ : Fin (6 * m + 3)) = i := by
    apply Fin.ext
    simp only [stemTarget_val]
    clear hsPartner hs0 s
    omega
  have hSecond : (⟨(stemTarget m i).val, hTargetEdgeLt⟩ : Fin (6 * m + 3)) =
      stemLeafIndex m i hStem := by
    apply Fin.ext
    simp only [stemTarget_val, stemLeafIndex_val]
  rw [hFirst, hSecond]
  simp only [caterpillarDatum_edgePartition]
  rw [
    catEdgePart_of_pair m i (pair_of_stem hStem),
    catEdgePart_of_not_pair m (stemLeafIndex m i hStem)
      (not_pair_of_leaf (stemLeafIndex_isLeaf hStem)),
    caterpillarDatum_vertexPartition, catVertexPart]
  have hPairEq : pairIndex (i.val + 1) =
      pairIndex (stemTarget m i).val := rfl
  have hsTarget : s.val ≠ pairIndex (stemTarget m i).val := by
    rw [← hPairEq]
    exact hsPartner
  rw [hPairEq, SheetPartition.blockCountWithin_self,
    blockCountWithin_discrete,
    blockCard_pairPart_other m _ s hs0 hsTarget]

theorem vertex_degree_stemTip_other {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPartner : s.val ≠ (partnerSheet m i).val) :
    vertex_degree (caterpillarDatum m).sourceGraph (stemTipVertex m i s) = 2 := by
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge,
    card_incidentSourceEdge_stemTip_other hStem s hs0 hsPartner]
  norm_num

/-- Every singleton-sheet stem occurrence outside the paired block is the
next edge of the dangling lollipop tail. -/
theorem stemOccurrence_dangles_of_other {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPartner : s.val ≠ (partnerSheet m i).val) :
    IsDangling (caterpillarDatum m) (stemOccurrence m i s) := by
  have hPartnerLeaf : s.val ≠
      (partnerSheet m (stemLeafIndex m i hStem)).val := by
    rw [partnerSheet_stemLeaf hStem]
    exact hsPartner
  have hLeafDangling := leafOccurrence_dangles_of_other
    (stemLeafIndex_isLeaf hStem) s hs0 hPartnerLeaf
  exact isDangling_of_incident_of_vertex_degree_eq_two
    (caterpillarDatum m) (stemOccurrence_ne_stemLeaf hStem s).symm
    (stemLeaf_incident_tip hStem s) (stemOccurrence_incident_tip m i s)
    (vertex_degree_stemTip_other hStem s hs0 hsPartner) hLeafDangling

/-! ### The paired stem occurrence survives -/

/-- A target vertex on the central sheet. -/
def coreVertex (m : ℕ) (v : (catTree m).V) :
    (caterpillarDatum m).SourceVertex :=
  (caterpillarDatum m).sourceEndpoint v 0

/-- Positivity of an undirected adjacency can be read in either order.  Kept
abstract so downstream concrete vertex representations do not enter the
symmetry rewrite. -/
theorem num_edges_pos_rev {G : CFGraph} {a b : G.V}
    (h : 0 < num_edges G a b) : 0 < num_edges G b a := by
  rw [num_edges_symmetric]
  exact h

/-- Every target occurrence has its literal central-sheet lift. -/
theorem coreStep_pos (m : ℕ) (k : Fin (6 * m + 3)) :
    0 < num_edges (caterpillarDatum m).sourceGraph
      (coreVertex m (catParent m k)) (coreVertex m k.succ) := by
  have hOne := TreeFamily.num_edges_rootedTree_eq_one
    (6 * m + 3) (catParent m) (catParent_le m) k
  have hTarget : 0 < num_edges (catTree m) (catParent m k) k.succ := by
    change 0 < num_edges
      (TreeFamily.rootedTree (6 * m + 3) (catParent m) (catParent_le m))
        (catParent m k) k.succ
    rw [hOne]
    norm_num
  exact num_edges_sourceEndpoint_pos (caterpillarDatum m) 0
    (catParent m k) k.succ hTarget

/-- The same lifted target step, traversed toward the root. -/
theorem coreStep_rev_pos (m : ℕ) (k : Fin (6 * m + 3)) :
    0 < num_edges (caterpillarDatum m).sourceGraph
      (coreVertex m k.succ) (coreVertex m (catParent m k)) := by
  exact num_edges_pos_rev (coreStep_pos m k)

/-- The central-sheet endpoint of a stem at its junction `p_i`. -/
def stemJunctionVertex (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).SourceVertex :=
  coreVertex m (catParent m i)

theorem sourceEnds_stemMain (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).sourceEnds (stemOccurrence m i 0) =
      (stemJunctionVertex m i, stemTipVertex m i 0) := by
  unfold stemOccurrence
  rw [sourceEnds_sourceEdge]
  rfl

/-- The loop at the tip of a stem makes that tip active. -/
theorem nonDanglingValency_stemTipMain_ne_zero {m : ℕ}
    {i : Fin (6 * m + 3)} (hStem : IsStemEdge m i) :
    nonDanglingValency (caterpillarDatum m) (stemTipVertex m i 0) ≠ 0 := by
  intro hZero
  let leaf := stemLeafIndex m i hStem
  have hMem : loopFirst m leaf ∈
      nonDanglingIncident (caterpillarDatum m) (stemTipVertex m i 0) :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨loopFirst_survives (stemLeafIndex_isLeaf hStem),
        stemLeaf_incident_tip hStem 0⟩
  have hPos := Finset.card_pos.mpr ⟨loopFirst m leaf, hMem⟩
  rw [card_nonDanglingIncident, hZero] at hPos
  omega

/-- The previous lollipop's leaf edge.  It is the loop anchor reached from a
stem junction without crossing that stem. -/
def previousLeafIndex (m : ℕ) (i : Fin (6 * m + 3))
    (_hStem : IsStemEdge m i) : Fin (6 * m + 3) :=
  ⟨i.val - 2, by
    have hi := i.isLt
    omega⟩

@[simp] theorem previousLeafIndex_val {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) : (previousLeafIndex m i hStem).val = i.val - 2 := rfl

theorem previousLeafIndex_isLeaf {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) : IsLeafEdge m (previousLeafIndex m i hStem) := by
  left
  simp only [previousLeafIndex_val]
  have hMod := hStem.1
  omega

/-- The central-sheet path from a stem junction to the preceding lollipop
has one step at `p₂`, and two steps thereafter.  It never visits the stem
tip. -/
theorem stemJunction_reaches_previousLoop {m : ℕ}
    {i : Fin (6 * m + 3)} (hStem : IsStemEdge m i) :
    ReachP (caterpillarDatum m).sourceGraph
      (fun vertex ↦ vertex ≠ stemTipVertex m i 0)
      (stemJunctionVertex m i)
      (loopBaseVertex m (previousLeafIndex m i hStem)) := by
  have hiLow : 2 ≤ i.val := by
    have hMod := hStem.1
    omega
  by_cases hFirst : i.val = 2
  · let spine : Fin (6 * m + 3) := ⟨1, by omega⟩
    have hStep := coreStep_rev_pos m spine
    have hJunction : stemJunctionVertex m i = coreVertex m spine.succ := by
      unfold stemJunctionVertex
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      unfold catParent
      simp only
      change parentIndex (i.val + 1) = 2
      have hMod : (i.val + 1) % 3 ≠ 2 := by omega
      simp only [parentIndex, if_neg hMod]
      omega
    have hAnchor : loopBaseVertex m (previousLeafIndex m i hStem) =
        coreVertex m (catParent m spine) := by
      unfold loopBaseVertex coreVertex previousLeafIndex spine
      congr 1
      apply Fin.ext
      change parentIndex (i.val - 2 + 1) = parentIndex (1 + 1)
      simp only [hFirst]
      norm_num [parentIndex]
    have hAway : coreVertex m (catParent m spine) ≠ stemTipVertex m i 0 := by
      intro hEq
      have hTarget := congrArg
        (fun vertex : (caterpillarDatum m).SourceVertex ↦ vertex.1.1.val) hEq
      change (catParent m spine).val = (stemTarget m i).val at hTarget
      simp only [catParent_val, spine, stemTarget_val] at hTarget
      norm_num [parentIndex] at hTarget
    rw [hJunction, hAnchor]
    exact reachP_single hStep hAway
  · have hiMore : 5 ≤ i.val := by
      have hMod := hStem.1
      omega
    let spine : Fin (6 * m + 3) := ⟨i.val - 1, by
      have hi := i.isLt
      omega⟩
    let previousStem : Fin (6 * m + 3) := ⟨i.val - 3, by
      have hi := i.isLt
      omega⟩
    have hSpine := coreStep_pos m spine
    have hPreviousStem := coreStep_pos m previousStem
    have hJunction : stemJunctionVertex m i = coreVertex m spine.succ := by
      unfold stemJunctionVertex
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ, spine]
      change parentIndex (i.val + 1) = i.val - 1 + 1
      have hiMod : i.val % 3 = 2 := hStem.1
      have hMod : (i.val + 1) % 3 ≠ 2 := by omega
      simp only [parentIndex, if_neg hMod]
      omega
    have hMiddle : coreVertex m (catParent m spine) =
        coreVertex m (catParent m previousStem) := by
      congr 1
      apply Fin.ext
      simp only [catParent_val, spine, previousStem]
      have hiMod : i.val % 3 = 2 := hStem.1
      have hSpineMod : (i.val - 1 + 1) % 3 = 2 := by omega
      have hPreviousMod : (i.val - 3 + 1) % 3 ≠ 2 := by omega
      simp only [parentIndex, if_pos hSpineMod, if_neg hPreviousMod]
      omega
    have hAnchor : loopBaseVertex m (previousLeafIndex m i hStem) =
        coreVertex m previousStem.succ := by
      unfold loopBaseVertex previousLeafIndex coreVertex
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ, previousStem]
      change parentIndex (i.val - 2 + 1) = i.val - 3 + 1
      have hiMod : i.val % 3 = 2 := hStem.1
      have hMod : (i.val - 2 + 1) % 3 ≠ 2 := by omega
      simp only [parentIndex, if_neg hMod]
      omega
    have hMiddleNe : coreVertex m (catParent m spine) ≠
        stemTipVertex m i 0 := by
      intro hEq
      have hTarget := congrArg
        (fun vertex : (caterpillarDatum m).SourceVertex ↦ vertex.1.1.val) hEq
      change (catParent m spine).val = (stemTarget m i).val at hTarget
      simp only [catParent_val, spine, stemTarget_val] at hTarget
      have hiMod : i.val % 3 = 2 := hStem.1
      have hMod : (i.val - 1 + 1) % 3 = 2 := by omega
      simp only [parentIndex, if_pos hMod] at hTarget
      omega
    have hAnchorNe : coreVertex m previousStem.succ ≠
        stemTipVertex m i 0 := by
      intro hEq
      have hTarget := congrArg
        (fun vertex : (caterpillarDatum m).SourceVertex ↦ vertex.1.1.val) hEq
      change previousStem.succ.val = (stemTarget m i).val at hTarget
      simp only [Fin.val_succ, previousStem, stemTarget_val] at hTarget
      omega
    have hSpineRev := coreStep_rev_pos m spine
    rw [hJunction]
    have hFirstStep : ReachP (caterpillarDatum m).sourceGraph
        (fun vertex ↦ vertex ≠ stemTipVertex m i 0)
        (coreVertex m spine.succ) (coreVertex m (catParent m spine)) :=
      reachP_single hSpineRev hMiddleNe
    rw [hAnchor]
    refine reachP_tail hFirstStep ?_ hAnchorNe
    rw [hMiddle]
    exact hPreviousStem

/-- **The paired bridge of every lollipop survives.**  The tip side contains
its own parallel loop, and the junction side reaches the preceding parallel
loop along the central sheet; hence neither side has genus zero. -/
theorem stemMain_survives {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) :
    ¬ IsDangling (caterpillarDatum m) (stemOccurrence m i 0) := by
  let anchor := loopBaseVertex m (previousLeafIndex m i hStem)
  apply not_isDangling_of_active_reaches (caterpillarDatum m)
    (stemOccurrence m i 0) (sourceEnds_stemMain m i)
    (firstAnchor := anchor) (secondAnchor := stemTipVertex m i 0)
  · exact nonDanglingValency_loopBase_ne_zero
      (previousLeafIndex_isLeaf hStem)
  · exact nonDanglingValency_stemTipMain_ne_zero hStem
  · exact stemJunction_reaches_previousLoop hStem
  · exact Relation.ReflTransGen.refl

/-- **Exact stem-fibre occurrence census.**  The paired block, named by
sheet `0` or its partner, is the unique surviving stem occurrence; every
other singleton sheet occurrence dangles. -/
theorem stemOccurrence_isDangling_iff {m : ℕ} {i : Fin (6 * m + 3)}
    (hStem : IsStemEdge m i) (s : Fin (m + 2)) :
    IsDangling (caterpillarDatum m) (stemOccurrence m i s) ↔
      s.val ≠ 0 ∧ s.val ≠ (partnerSheet m i).val := by
  constructor
  · intro hDangling
    constructor
    · intro hs0
      have hs : s = 0 := Fin.ext hs0
      subst s
      exact stemMain_survives hStem hDangling
    · intro hsPartner
      have hs : s = partnerSheet m i := Fin.ext hsPartner
      subst s
      have hSame : stemOccurrence m i (partnerSheet m i) =
          stemOccurrence m i 0 := by
        unfold stemOccurrence
        apply Subtype.ext
        apply Prod.ext
        · rfl
        change ((caterpillarDatum m).edgePartition (occ m i)).Rel
          (partnerSheet m i) 0
        rw [caterpillarDatum_edgePartition,
          catEdgePart_of_pair m i (pair_of_stem hStem)]
        exact pairPart_rel_zero m _ _ rfl
      exact stemMain_survives hStem (hSame ▸ hDangling)
  · rintro ⟨hs0, hsPartner⟩
    exact stemOccurrence_dangles_of_other hStem s hs0 hsPartner

end DraismaVargas.LocalCases.CaterpillarPruning
