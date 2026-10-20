module

public import DiagonalSecant.CMDictionary
public import DiagonalSecant.TypedRows

@[expose] public section

/-!
# The walk dictionary between a typed frame and its regrowth

Used for the hairpin receipt (`CMHairpin.lean`). Two facts, both about ordered rows.

1. **A marked row has two ends, and the walk from the far end is the reverse** (§1, on any
   marked datum). The public `RowWalk.orderedRow` of the regrown frame and the typed
   `TypedRows.orderedRow` of `κ` start at *independently chosen* path ends, so the two walks of
   one row agree or are reverses of each other. `markedTraverse_pathEnd` is the typed half of
   that: the marked traversal from any marked path end of `path` is the ordered row or its
   reverse (`markedPathEnd_cases`, `markedTraverse_finish`), and `walkVertex_reverse` reads the
   vertices of the reversed walk.
2. **The public traversal of the regrowth, started at an old edge, is the marked traversal of
   `κ`** (§2, on any caterpillar branching): the far ends correspond (`otherEnd_psiSE`), the
   stopping conditions agree because an old non-mark vertex keeps its surviving valency and a
   mark becomes trivalent (`nonDanglingValency_psiSV_eq_two_iff`), and the step edge is the old
   step edge because no surviving tail edge meets a non-mark (`stepEdge_psiSE`); hence
   `traverse_psiSE` and `walkVertex_psiSE`.
-/

namespace DiagonalSecant.CM

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.OrientedTraversal (walkVertex walkVertex_succ)
open DraismaVargas.Count DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.CatRegrow
open DiagonalSecant.TypedRows

/-! ## 1.  The two ends of a marked row -/

section Ends

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {marks : Finset data.SourceVertex} (hEnds : HasMarkedPathEnds data marks)
  (path : MarkedStablePath data marks)

/-- The far end of an occurrence, entered at one of its two distinct ends, is the other. -/
theorem otherEnd_eq_of_incident_of_ne {e : data.SourceEdge} {a b : data.SourceVertex}
    (ha : Incident data e a) (hb : Incident data e b) (hab : b ≠ a) : otherEnd data e a = b := by
  rcases eq_or_eq_otherEnd data ha hb with h | h
  · exact absurd h hab
  · exact h.symm

/-- Entering the `j`-th occurrence at the walk vertex `j + 1` leads back to the walk vertex `j`. -/
theorem otherEnd_rowVertex_succ {j : ℕ} (hj : j < (orderedRow hEnds path).length) :
    otherEnd data (orderedRow hEnds path)[j] (rowVertex hEnds path (j + 1)) =
      rowVertex hEnds path j :=
  otherEnd_eq_of_incident_of_ne (rowVertex_succ_incident hEnds path hj)
    (rowVertex_incident hEnds path hj) (rowVertex_ne_succ hEnds path hj).symm

/-- An entry of a duplicate-free list is not among the later entries. -/
theorem getElem_notMem_drop_succ {α : Type*} {l : List α} (hl : l.Nodup) {m : ℕ}
    (hm : m < l.length) : l[m] ∉ l.drop (m + 1) := by
  intro h
  obtain ⟨i, hi, hI⟩ := List.mem_iff_getElem.mp h
  rw [List.getElem_drop] at hI
  have := (hl.getElem_inj_iff).mp hI
  omega

/-- Two distinct indices of the ordered row carry distinct occurrences. -/
theorem orderedRow_getElem_ne {i j : ℕ} (hi : i < (orderedRow hEnds path).length)
    (hj : j < (orderedRow hEnds path).length) (hij : i ≠ j) :
    (orderedRow hEnds path)[i] ≠ (orderedRow hEnds path)[j] := fun h ↦
  hij (((orderedRow_nodup hEnds path).getElem_inj_iff).mp h)

/-- At an interior walk vertex, the step away from the occurrence after it is the occurrence
before it. -/
theorem stepEdge_rowVertex {m : ℕ} (hm : 0 < m) (hmL : m < (orderedRow hEnds path).length)
    (hv : nonDanglingValency data (rowVertex hEnds path m) = 2) :
    stepEdge data hv (orderedRow hEnds path)[m] =
      (orderedRow hEnds path)[m - 1]'(by omega) := by
  have hsucc : m - 1 + 1 = m := by omega
  have hOtherInc : Incident data ((orderedRow hEnds path)[m - 1]'(by omega))
      (rowVertex hEnds path m) := by
    have h := rowVertex_succ_incident hEnds path (j := m - 1) (by omega)
    rwa [hsucc] at h
  rcases eq_or_eq_stepEdge data hv (orderedRow_survives hEnds path _ (List.getElem_mem hmL))
      (rowVertex_incident hEnds path hmL)
      (orderedRow_survives hEnds path _ (List.getElem_mem (by omega))) hOtherInc with h | h
  · exact absurd h (orderedRow_getElem_ne hEnds path (by omega) hmL (by omega))
  · exact h.symm

/-- The marked traversal from the `m`-th walk vertex back along the first `m` occurrences, with
the later occurrences already visited, is the reverse of the first `m` occurrences. -/
theorem markedTraverse_back (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ (orderedRow hEnds path).length) :
    markedTraverse data marks ((orderedRow hEnds path).drop m).toFinset
        ((orderedRow hEnds path)[m - 1]'(by omega)) (rowVertex hEnds path m) =
      ((orderedRow hEnds path).take m).reverse := by
  classical
  induction m, hm1 using Nat.le_induction with
  | base =>
    have h0 : 0 < (orderedRow hEnds path).length := by omega
    have hNot : (orderedRow hEnds path)[0] ∉ ((orderedRow hEnds path).drop 1).toFinset := by
      rw [List.mem_toFinset]
      exact getElem_notMem_drop_succ (orderedRow_nodup hEnds path) h0
    have hStart := startEdge_isMarkedPathEnd hEnds path
    rw [← orderedRow_getElem_zero hEnds path, ← rowVertex_zero hEnds path] at hStart
    rw [markedTraverse_of_stop data marks hNot (by
      rw [otherEnd_rowVertex_succ hEnds path h0]
      intro hCont
      rcases hStart.2 with h | h
      · exact h hCont.1
      · exact hCont.2 h)]
    rw [List.take_succ_eq_append_getElem h0, List.take_zero, List.nil_append,
      List.reverse_singleton]
  | succ m hm1 ih =>
    have hmL' : m < (orderedRow hEnds path).length := by omega
    have hNot : (orderedRow hEnds path)[m] ∉
        ((orderedRow hEnds path).drop (m + 1)).toFinset := by
      rw [List.mem_toFinset]
      exact getElem_notMem_drop_succ (orderedRow_nodup hEnds path) hmL'
    have hoe := otherEnd_rowVertex_succ hEnds path hmL'
    have hInt := rowVertex_interior hEnds path (j := m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega] at hInt
    have hCont : nonDanglingValency data
        (otherEnd data (orderedRow hEnds path)[m] (rowVertex hEnds path (m + 1))) = 2 ∧
        otherEnd data (orderedRow hEnds path)[m] (rowVertex hEnds path (m + 1)) ∉ marks := by
      rw [hoe]; exact hInt
    simp only [Nat.add_sub_cancel]
    rw [markedTraverse_of_step data marks hNot hCont]
    have hstep : stepEdge data hCont.1 (orderedRow hEnds path)[m] =
        (orderedRow hEnds path)[m - 1]'(by omega) := by
      have hv : nonDanglingValency data (rowVertex hEnds path m) = 2 := hInt.1
      have key : ∀ (X : data.SourceVertex) (hX : X = rowVertex hEnds path m)
          (hX2 : nonDanglingValency data X = 2),
          stepEdge data hX2 (orderedRow hEnds path)[m] =
            stepEdge data hv (orderedRow hEnds path)[m] := by
        intro X hX hX2
        subst hX
        rfl
      rw [key _ hoe hCont.1]
      exact stepEdge_rowVertex hEnds path (by omega) hmL' hv
    rw [hstep, hoe, ← List.toFinset_cons, ← List.drop_eq_getElem_cons hmL', ih (by omega),
      List.take_succ_eq_append_getElem hmL', List.reverse_append, List.reverse_singleton,
      List.singleton_append]

/-- **The marked traversal from the finish is the reverse of the ordered row.** -/
theorem markedTraverse_finish :
    markedTraverse data marks ∅ (finishEdge hEnds path)
        (rowVertex hEnds path (orderedRow hEnds path).length) =
      (orderedRow hEnds path).reverse := by
  have hPos := orderedRow_length_pos hEnds path
  have h := markedTraverse_back hEnds path (orderedRow hEnds path).length hPos le_rfl
  rw [List.drop_length, List.toFinset_nil, List.take_length] at h
  rw [finishEdge_eq_getElem hEnds path]
  exact h

/-- **A marked row has exactly two marked path ends**: the start and the finish of its walk. -/
theorem markedPathEnd_cases {F : NonDanglingEdge data} {Y : data.SourceVertex}
    (hF : markedRow marks F = path) (hEnd : IsMarkedPathEnd data marks F.1 Y) :
    (F.1 = (orderedRow hEnds path)[0]'(orderedRow_length_pos hEnds path) ∧
        Y = rowVertex hEnds path 0) ∨
      (F.1 = finishEdge hEnds path ∧
        Y = rowVertex hEnds path (orderedRow hEnds path).length) := by
  have hMem : F.1 ∈ orderedRow hEnds path := (mem_orderedRow_iff hEnds path _).mpr ⟨F.2, hF⟩
  obtain ⟨m, hm, hM⟩ := List.mem_iff_getElem.mp hMem
  have hInc : Incident data (orderedRow hEnds path)[m] Y := hM ▸ hEnd.1
  have hNotInterior : ∀ j, j + 1 < (orderedRow hEnds path).length →
      Y ≠ rowVertex hEnds path (j + 1) := by
    intro j hj hY
    obtain ⟨hv, hmark⟩ := rowVertex_interior hEnds path hj
    rw [← hY] at hv hmark
    rcases hEnd.2 with h | h
    · exact h hv
    · exact hmark h
  rcases eq_or_eq_otherEnd data (rowVertex_incident hEnds path hm) hInc with hY | hY
  · rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact Or.inl ⟨hM.symm, hY⟩
    · exfalso
      have := hNotInterior (m - 1) (by omega)
      rw [show m - 1 + 1 = m by omega] at this
      exact this hY
  · rw [← rowVertex_succ hEnds path hm] at hY
    by_cases hLast : m + 1 = (orderedRow hEnds path).length
    · right
      refine ⟨?_, hLast ▸ hY⟩
      rw [finishEdge_eq_getElem hEnds path, ← hM]
      congr 1
      omega
    · exact absurd hY (hNotInterior m (by omega))

/-- **The marked traversal from any marked path end of a row is its ordered row or the
reverse.** -/
theorem markedTraverse_pathEnd {F : NonDanglingEdge data} {Y : data.SourceVertex}
    (hF : markedRow marks F = path) (hEnd : IsMarkedPathEnd data marks F.1 Y) :
    markedTraverse data marks ∅ F.1 Y = orderedRow hEnds path ∨
      markedTraverse data marks ∅ F.1 Y = (orderedRow hEnds path).reverse := by
  rcases markedPathEnd_cases hEnds path hF hEnd with ⟨hF0, hY0⟩ | ⟨hFL, hYL⟩
  · left
    rw [hF0, hY0, orderedRow_getElem_zero, rowVertex_zero]
    rfl
  · right
    rw [hFL, hYL]
    exact markedTraverse_finish hEnds path

/-- The walk vertices of the reversed row, from the finish. -/
theorem walkVertex_reverse (m : ℕ) (hm : m ≤ (orderedRow hEnds path).length) :
    walkVertex data (orderedRow hEnds path).reverse
        (rowVertex hEnds path (orderedRow hEnds path).length) m =
      rowVertex hEnds path ((orderedRow hEnds path).length - m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm' : m < (orderedRow hEnds path).reverse.length := by rw [List.length_reverse]; omega
    rw [walkVertex_succ _ _ hm', ih (by omega), List.getElem_reverse]
    have hj : (orderedRow hEnds path).length - 1 - m < (orderedRow hEnds path).length := by omega
    have heq : (orderedRow hEnds path).length - m = (orderedRow hEnds path).length - 1 - m + 1 := by
      omega
    rw [heq, otherEnd_rowVertex_succ hEnds path hj]
    congr 1
    omega

end Ends

/-! ## 2.  The traversal of the regrowth along an old row -/

section Regrow

variable {T : CFGraph.{0}} {d' d k : ℕ} {N : Type} {c : Fin k → ℕ} {ψ : GluingDatum T d'}
  (β : CatBranching ψ N d c)

/-- The far end of an old occurrence, in the regrowth, is the old far end. -/
theorem otherEnd_psiSE (F : ψ.SourceEdge) (Y : ψ.SourceVertex) :
    otherEnd β.regrowDatum (β.psiSE F) (β.psiSV Y) = β.psiSV (otherEnd ψ F Y) := by
  unfold otherEnd
  rw [β.sourceEnds_psiSE]
  simp only [CatBranching.psiSV_inj]
  split_ifs <;> rfl

variable (hψ : ψ.Connected) (hT : graph_connected T) (hT0 : genus T = 0)
  (hMark : ∀ j, nonDanglingValency ψ (β.mark j) ≠ 0)

include hψ hT hT0 hMark

/-- The step away from an old occurrence through an old non-mark vertex is old. -/
theorem stepEdge_psiSE {Z : ψ.SourceVertex} (hZ : nonDanglingValency ψ Z = 2) (hZm : Z ∉ β.marks)
    {X : β.regrowDatum.SourceVertex} (hX : X = β.psiSV Z)
    (hX' : nonDanglingValency β.regrowDatum X = 2) {F : ψ.SourceEdge}
    (hF : ¬ IsDangling ψ F) (hFZ : Incident ψ F Z) :
    stepEdge β.regrowDatum hX' (β.psiSE F) = β.psiSE (stepEdge ψ hZ F) := by
  subst hX
  have hSurv := stepEdge_not_dangling β.regrowDatum hX' (β.psiSE F)
  have hInc := stepEdge_incident β.regrowDatum hX' (β.psiSE F)
  have hNe := stepEdge_ne β.regrowDatum hX' (β.psiSE F)
  rcases β.nonDanglingEdge_cases hψ hT hT0 hMark ⟨_, hSurv⟩ with ⟨F', hF'⟩ | ⟨t, q, hq, ht⟩
  · have hE : stepEdge β.regrowDatum hX' (β.psiSE F) = β.psiSE F'.1 := congrArg Subtype.val hF'
    rw [hE] at hInc hNe ⊢
    have hInc' : Incident ψ F'.1 Z := (β.incident_psiSE_psiSV _ _).mp hInc
    rcases eq_or_eq_stepEdge ψ hZ hF hFZ F'.2 hInc' with h | h
    · exact absurd (congrArg β.psiSE h) hNe
    · rw [h]
  · have hE : stepEdge β.regrowDatum hX' (β.psiSE F) = β.tailSE t q := congrArg Subtype.val ht
    rw [hE] at hInc
    exact absurd hInc (β.not_incident_tail_psiSV hq hZm)

/-- **The public traversal of the regrowth along an old surviving occurrence is the marked
traversal of `ψ`**, occurrence by occurrence. -/
theorem traverse_psiSE (visited : Finset ψ.SourceEdge) (F : ψ.SourceEdge) (Y : ψ.SourceVertex)
    (hF : ¬ IsDangling ψ F) :
    traverse β.regrowDatum (visited.map ⟨β.psiSE, β.psiSE_injective⟩) (β.psiSE F) (β.psiSV Y) =
      (markedTraverse ψ β.marks visited F Y).map β.psiSE := by
  classical
  refine markedTraverse_rec ψ β.marks
    (motive := fun visited F Y ↦ ¬ IsDangling ψ F →
      traverse β.regrowDatum (visited.map ⟨β.psiSE, β.psiSE_injective⟩) (β.psiSE F) (β.psiSV Y) =
        (markedTraverse ψ β.marks visited F Y).map β.psiSE)
    ?_ ?_ ?_ visited F Y hF
  · intro visited F Y hV _
    have hV' : β.psiSE F ∈ visited.map ⟨β.psiSE, β.psiSE_injective⟩ := Finset.mem_map_of_mem _ hV
    rw [traverse_of_mem _ _ hV', markedTraverse_of_mem _ _ _ hV]
    rfl
  · intro visited F Y hV hStop _
    have hV' : β.psiSE F ∉ visited.map ⟨β.psiSE, β.psiSE_injective⟩ := fun h ↦
      hV ((Finset.mem_map' ⟨β.psiSE, β.psiSE_injective⟩).mp h)
    rw [markedTraverse_of_stop _ _ hV hStop, traverse_of_valency_ne _ hV' (by
      rw [otherEnd_psiSE β F Y]
      intro h
      exact hStop ((β.nonDanglingValency_psiSV_eq_two_iff hψ hT hT0 hMark _).mp h))]
    rfl
  · intro visited F Y hV hCont ih hF
    have hV' : β.psiSE F ∉ visited.map ⟨β.psiSE, β.psiSE_injective⟩ := fun h ↦
      hV ((Finset.mem_map' ⟨β.psiSE, β.psiSE_injective⟩).mp h)
    have hX' : nonDanglingValency β.regrowDatum
        (otherEnd β.regrowDatum (β.psiSE F) (β.psiSV Y)) = 2 := by
      rw [otherEnd_psiSE β F Y]
      exact (β.nonDanglingValency_psiSV_eq_two_iff hψ hT hT0 hMark _).mpr hCont
    have hstep : stepEdge β.regrowDatum hX' (β.psiSE F) = β.psiSE (stepEdge ψ hCont.1 F) :=
      stepEdge_psiSE β hψ hT hT0 hMark hCont.1 hCont.2 (otherEnd_psiSE β F Y) hX' hF
        (incident_otherEnd ψ F Y)
    have hins : insert (β.psiSE F) (visited.map ⟨β.psiSE, β.psiSE_injective⟩) =
        (insert F visited).map ⟨β.psiSE, β.psiSE_injective⟩ := (Finset.map_insert _ _ _).symm
    rw [markedTraverse_of_step _ _ hV hCont, traverse_of_valency_eq _ hV' hX', hstep,
      otherEnd_psiSE β F Y, hins, ih (stepEdge_not_dangling ψ hCont.1 F), List.map_cons]

omit hψ hT hT0 hMark in
/-- The walk vertices along the image of a list of old occurrences are the images of the walk
vertices. -/
theorem walkVertex_psiSE (l : List ψ.SourceEdge) (Y : ψ.SourceVertex) (j : ℕ) (hj : j ≤ l.length) :
    walkVertex β.regrowDatum (l.map β.psiSE) (β.psiSV Y) j = β.psiSV (walkVertex ψ l Y j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j < l.length := by omega
    have hj'' : j < (l.map β.psiSE).length := by rw [List.length_map]; exact hj'
    rw [walkVertex_succ _ _ hj'', walkVertex_succ _ _ hj', ih (by omega), List.getElem_map,
      otherEnd_psiSE β _ _]

end Regrow

end DiagonalSecant.CM
