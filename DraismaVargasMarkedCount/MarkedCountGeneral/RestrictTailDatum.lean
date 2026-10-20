module

public import DraismaVargasMarkedCount.MarkedCountGeneral.RestrictTailShed

@[expose] public section

/-!
# Restriction over the tails: the restricted datum `ψ`

The target restriction `D₀ = rData` with its lone sheets split off (`Sheets.restrictSheets`, along
`Sheets.splitBy (loneSet)`), at any degree `m` with `m + #lone = degree`:

* `dat T hc M m hm : GluingDatum (rTarget T hc M) m`, connected (`dat_connected`, from (a), (b),
  (c) of `RestrictTailLone`), Riemann--Hurwitz (`dat_valid`);
* the composite inclusions `cSV`, `cSE` into the frame's datum, with incidence, indices and blocks;
* **the dangling dictionary** (`isDangling_dat_iff`): a source edge of `ψ` dangles iff it dangles in
  the frame (the ramification-one `Restrict.isDangling_restrict_iff`, for the composite: a lone
  sheet carries no survivor), and the surviving valencies (`nonDanglingValency_dat`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral.TailRestrict

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCount.Restrict
open DraismaVargas.Count.MarkedCountGeneral.Sheets (IsNew IsLone restrictSheets inclSV inclSE
  splitBy isNew_splitBy)
open GenusSixExistence.Tripod.Gluing (wCount not_isDangling_of_witness nonDanglingValency_eq_wCount)
open Utilities.Certificate.ExplicitPotential (Core)
open CatSlot
open scoped DraismaVargas.Infrastructure.GluingContraction

noncomputable section

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}
  (T : Tailed core mark c) (hc : IsMarkedCubic core mark) {y : Fin T.P → ℚ}
  (M : FibreMember T.H y degree)

/-! ## 1.  The datum -/

/-- The number of shed sheets. -/
abbrev nShed : ℕ := (loneSet T hc M).card

theorem nShed_lt : nShed T hc M < degree := by
  by_contra h
  have hAll : loneSet T hc M = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (by simpa using not_lt.mp h))
  exact false_of_all_lone T hc M fun τ ↦
    (mem_loneSet T hc M).mp (hAll ▸ Finset.mem_univ τ)

variable (m : ℕ) (hm : m + nShed T hc M = degree)

/-- The decomposition of the sheets: old ones, then the lone ones. -/
def split : Fin degree ≃ Fin m ⊕ Fin (nShed T hc M) := splitBy (loneSet T hc M) m _ hm rfl

theorem isNew_split_iff (i : Fin degree) :
    IsNew (split T hc M m hm) i ↔ IsLone (rData T hc M) i := by
  rw [split, isNew_splitBy, mem_loneSet]

theorem isLone_split (q : Fin (nShed T hc M)) :
    IsLone (rData T hc M) ((split T hc M m hm).symm (.inr q)) :=
  (isNew_split_iff T hc M m hm _).mp (Sheets.isNew_inr _ q)

include hm in
theorem m_pos : 0 < m := by have := nShed_lt T hc M; omega

/-- **The restricted datum `ψ`**: the target restriction with its lone sheets deleted. -/
abbrev dat : GluingDatum (rTarget T hc M) m :=
  restrictSheets (rData T hc M) (split T hc M m hm) (isLone_split T hc M m hm) (m_pos T hc M m hm)

/-! ## 2.  The composite inclusions -/

/-- A source vertex of `ψ`, read in the frame. -/
abbrev cSV (X : (dat T hc M m hm).SourceVertex) : M.data.SourceVertex := svIncl (inclSV X)

/-- A source edge of `ψ`, read in the frame. -/
abbrev cSE (E : (dat T hc M m hm).SourceEdge) : M.data.SourceEdge := seIncl (inclSE E)

theorem cSV_injective : Function.Injective (cSV T hc M m hm) :=
  fun _ _ h ↦ Sheets.inclSV_injective (svIncl_injective h)

theorem cSE_injective : Function.Injective (cSE T hc M m hm) :=
  fun _ _ h ↦ Sheets.inclSE_injective (seIncl_injective h)

theorem cSV_mem_Keep (X : (dat T hc M m hm).SourceVertex) : (cSV T hc M m hm X).1.1 ∈ Keep T M :=
  svIncl_target_mem _

theorem cSE_kept (E : (dat T hc M m hm).SourceEdge) : KeptEdge (Keep T M) (cSE T hc M m hm E).1.1 :=
  seIncl_kept _

theorem incident_cSE_iff (E : (dat T hc M m hm).SourceEdge) (X : (dat T hc M m hm).SourceVertex) :
    Incident M.data (cSE T hc M m hm E) (cSV T hc M m hm X) ↔ Incident (dat T hc M m hm) E X :=
  (incident_seIncl_iff _ _).trans (Sheets.incident_inclSE_inclSV E X)

theorem sourceEdgeIndex_cSE (E : (dat T hc M m hm).SourceEdge) :
    M.data.sourceEdgeIndex (cSE T hc M m hm E) = (dat T hc M m hm).sourceEdgeIndex E :=
  (sourceEdgeIndex_seIncl _).trans (Sheets.sourceEdgeIndex_inclSE E)

theorem cSV_not_isLone (X : (dat T hc M m hm).SourceVertex) :
    ¬ IsLone (rData T hc M) (inclSV X).1.2 := fun h ↦
  (Sheets.inclSV_isOld X) ((isNew_split_iff T hc M m hm _).mpr h)

/-- **A vertex over `T'` in a sheet that is not lone is a vertex of `ψ`.** -/
theorem exists_cSV {X : M.data.SourceVertex} (hX : X.1.1 ∈ Keep T M)
    (hNL : ¬ IsLone (rData T hc M) X.1.2) :
    ∃ X' : (dat T hc M m hm).SourceVertex, cSV T hc M m hm X' = X := by
  obtain ⟨X', hX'⟩ := Sheets.exists_inclSV_of_old (hLone := isLone_split T hc M m hm)
    (hm := m_pos T hc M m hm) (X := svRestrict X hX)
    (fun h ↦ hNL ((isNew_split_iff T hc M m hm _).mp h))
  exact ⟨X', by change svIncl (inclSV X') = X; rw [hX']; rfl⟩

/-- **A survivor of the frame over a kept edge is an edge of `ψ`.** -/
theorem exists_cSE_of_survivor {F : M.data.SourceEdge} (hF : ¬ IsDangling M.data F)
    (hk : KeptEdge (Keep T M) F.1.1) :
    ∃ E : (dat T hc M m hm).SourceEdge, cSE T hc M m hm E = F := by
  set F₀ := seRestrict (hKeep := Keep_nonempty T hc M) F hk
  obtain ⟨X, hX⟩ := exists_other_sourceEnd M.data (edge := F) (vertex := M.data.sourceEnds F |>.1)
    (Or.inl rfl)
  have hXK : (M.data.sourceEnds F).1.1.1 ∈ Keep T M := target_mem_of_incident hk (Or.inl rfl)
  have hXI : Incident M.data F (M.data.sourceEnds F).1 := Or.inl rfl
  have hNd := LollipopBridgeFibre.nonDanglingValency_pos_of_survivor hF hXI
  have hNL := not_isLone_of_survivor T hc M hXK hNd
  obtain ⟨X', hX'⟩ := exists_cSV T hc M m hm hXK hNL
  have hI₀ : Incident (rData T hc M) F₀ (inclSV X') := by
    rw [← incident_iff_seRestrict hk]
    change Incident M.data F (cSV T hc M m hm X')
    rw [hX']; exact hXI
  have hOld := Sheets.not_isNew_of_incident (hLone := isLone_split T hc M m hm) hI₀
    (Sheets.inclSV_isOld X')
  obtain ⟨E, hE⟩ := Sheets.exists_inclSE_of_old (hLone := isLone_split T hc M m hm)
    (hm := m_pos T hc M m hm) hOld
  exact ⟨E, by change seIncl (inclSE E) = F; rw [hE]; rfl⟩

/-! ## 3.  Validity -/

/-- Every vertex of `D₀` in a sheet that is not lone is joined to a survivor. -/
theorem exists_survivor_reach {Z : (rData T hc M).SourceVertex} (hZ : ¬ IsLone (rData T hc M) Z.1.2) :
    ∃ W, Reach (rData T hc M).sourceGraph Z W ∧ 0 < nonDanglingValency M.data (svIncl W) := by
  by_contra hNo
  push Not at hNo
  exact hZ (isLone_of_component T hc M Z fun W hW ↦ Nat.le_zero.mp (hNo W hW))

theorem reach_inclSV (X Y : (dat T hc M m hm).SourceVertex) :
    Reach (rData T hc M).sourceGraph (inclSV X) (inclSV Y) := by
  obtain ⟨W, hXW, hW⟩ := exists_survivor_reach T hc M (cSV_not_isLone T hc M m hm X)
  obtain ⟨W', hYW', hW'⟩ := exists_survivor_reach T hc M (cSV_not_isLone T hc M m hm Y)
  have hWW' := reach_of_survivors T hc M (svIncl_target_mem W) (svIncl_target_mem W') hW hW'
  change Reach _ W W' at hWW'
  exact reach_trans hXW (reach_trans hWW' (reach_symm hYW'))

/-- **`ψ` is connected.** -/
theorem dat_connected : (dat T hc M m hm).Connected := by
  obtain ⟨X₀⟩ := (dat T hc M m hm).sourceGraph.instNonempty
  exact graph_connected_of_reach X₀ fun Y ↦
    Sheets.reach_of_reach_inclSV (reach_inclSV T hc M m hm X₀ Y)

theorem dat_valid : (dat T hc M m hm).Valid :=
  ⟨dat_connected T hc M m hm,
    Sheets.riemannHurwitz_restrictSheets (riemannHurwitz_restrictDatum M.fullDim.valid.2)⟩

/-! ## 4.  The dangling dictionary -/

/-- Counting edges of `ψ` at a vertex is counting kept edges of the frame there. -/
theorem wCount_dat (Q : M.data.SourceEdge → Prop) (X : (dat T hc M m hm).SourceVertex) :
    wCount (dat T hc M m hm) (fun E ↦ Q (cSE T hc M m hm E)) X =
      wCount M.data (fun E ↦ Q E ∧ KeptEdge (Keep T M) E.1.1) (cSV T hc M m hm X) := by
  classical
  unfold wCount
  refine Finset.card_bij (fun E _ ↦ cSE T hc M m hm E) ?_ ?_ ?_
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE ⊢
    exact ⟨⟨hE.1, cSE_kept T hc M m hm E⟩, (incident_cSE_iff T hc M m hm E X).mpr hE.2⟩
  · intro _ _ _ _ h
    exact cSE_injective T hc M m hm h
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    obtain ⟨⟨hQ, hk⟩, hI⟩ := hF
    set F₀ := seRestrict (hKeep := Keep_nonempty T hc M) F hk
    have hI₀ : Incident (rData T hc M) F₀ (inclSV X) :=
      (incident_iff_seRestrict hk (inclSV X)).mp hI
    have hOld := Sheets.not_isNew_of_incident (hLone := isLone_split T hc M m hm) hI₀
      (Sheets.inclSV_isOld X)
    obtain ⟨E, hE⟩ := Sheets.exists_inclSE_of_old (hLone := isLone_split T hc M m hm)
      (hm := m_pos T hc M m hm) hOld
    have hEF : cSE T hc M m hm E = F := by change seIncl (inclSE E) = F; rw [hE]; rfl
    refine ⟨E, ?_, hEF⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hEF]
    exact ⟨hQ, (incident_cSE_iff T hc M m hm E X).mp (hEF ▸ hI)⟩

/-- **Surviving in the frame implies surviving in `ψ`.** -/
theorem not_isDangling_dat_of {E : (dat T hc M m hm).SourceEdge}
    (h : ¬ IsDangling M.data (cSE T hc M m hm E)) : ¬ IsDangling (dat T hc M m hm) E := by
  refine not_isDangling_of_witness _ (fun E ↦ ¬ IsDangling M.data (cSE T hc M m hm E)) ?_ h
  intro X
  rw [wCount_dat T hc M m hm (fun E ↦ ¬ IsDangling M.data E) X]
  have hP := deletionPattern T hc M
  have hSplit := nonDanglingValency_split hP (cSV T hc M m hm X)
  have hNe := NonDanglingValency.nonDanglingValency_ne_one M.data M.fullDim.connected
    (cSV T hc M m hm X)
  rcases hP.kept (cSV T hc M m hm X) (cSV_mem_Keep T hc M m hm X) with h0 | ⟨h1, h3⟩ <;> omega

/-- **Surviving in `ψ` implies surviving in the frame.** -/
theorem not_isDangling_of_dat {E : (dat T hc M m hm).SourceEdge}
    (h : ¬ IsDangling (dat T hc M m hm) E) : ¬ IsDangling M.data (cSE T hc M m hm E) := by
  classical
  have hP := deletionPattern T hc M
  let W : M.data.SourceEdge → Prop := fun F ↦
    (KeptEdge (Keep T M) F.1.1 ∧ ∃ E' : (dat T hc M m hm).SourceEdge,
      cSE T hc M m hm E' = F ∧ ¬ IsDangling (dat T hc M m hm) E') ∨ Lol T M F
  refine not_isDangling_of_witness M.data W ?_ (Or.inl ⟨cSE_kept T hc M m hm E, E, rfl, h⟩)
  intro X
  have hDisj : ∀ F, (KeptEdge (Keep T M) F.1.1 ∧ ∃ E' : (dat T hc M m hm).SourceEdge,
      cSE T hc M m hm E' = F ∧ ¬ IsDangling (dat T hc M m hm) E') → ¬ Lol T M F :=
    fun F h1 h2 ↦ h2.2 h1.1
  have hW := MarkedCount.Restrict.wCount_or_of_disjoint M.data hDisj X
  change wCount M.data W X ≠ 1
  rw [hW]
  -- the kept part, read in `ψ`
  have hKeptPart : ∀ X' : (dat T hc M m hm).SourceVertex, cSV T hc M m hm X' = X →
      wCount M.data (fun F ↦ KeptEdge (Keep T M) F.1.1 ∧ ∃ E' : (dat T hc M m hm).SourceEdge,
        cSE T hc M m hm E' = F ∧ ¬ IsDangling (dat T hc M m hm) E') X =
        nonDanglingValency (dat T hc M m hm) X' := by
    intro X' hX'
    rw [← hX']
    have hComm : wCount M.data (fun F ↦ KeptEdge (Keep T M) F.1.1 ∧ ∃ E' : (dat T hc M m hm).SourceEdge,
        cSE T hc M m hm E' = F ∧ ¬ IsDangling (dat T hc M m hm) E') (cSV T hc M m hm X') =
        wCount M.data (fun F ↦ (∃ E' : (dat T hc M m hm).SourceEdge,
          cSE T hc M m hm E' = F ∧ ¬ IsDangling (dat T hc M m hm) E') ∧
            KeptEdge (Keep T M) F.1.1) (cSV T hc M m hm X') :=
      GenusSixExistence.Tripod.Gluing.wCount_congr _ _ fun F _ ↦ and_comm
    rw [hComm, ← wCount_dat T hc M m hm (fun F ↦ ∃ E' : (dat T hc M m hm).SourceEdge,
      cSE T hc M m hm E' = F ∧ ¬ IsDangling (dat T hc M m hm) E') X',
      nonDanglingValency_eq_wCount]
    apply GenusSixExistence.Tripod.Gluing.wCount_congr
    intro F _
    constructor
    · rintro ⟨E', hE', hS⟩; rw [← cSE_injective T hc M m hm hE']; exact hS
    · intro hS; exact ⟨F, rfl, hS⟩
  by_cases hXK : X.1.1 ∈ Keep T M
  · by_cases hNL : IsLone (rData T hc M) X.1.2
    · -- a lone sheet: nothing survives there, and no edge of `ψ` meets it
      have h0 : nonDanglingValency M.data X = 0 :=
        nonDanglingValency_eq_zero_of_isLone T hc M (Z := svRestrict X hXK) hNL
      have hKept0 : wCount M.data (fun F ↦ KeptEdge (Keep T M) F.1.1 ∧
          ∃ E' : (dat T hc M m hm).SourceEdge,
            cSE T hc M m hm E' = F ∧ ¬ IsDangling (dat T hc M m hm) E') X = 0 := by
        unfold wCount
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_of_forall_notMem
        intro F hF
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
        obtain ⟨⟨-, E', rfl, -⟩, hI⟩ := hF
        have hI₀ : Incident (rData T hc M) (inclSE E') (svRestrict X hXK) :=
          (incident_seIncl_iff (inclSE E') (svRestrict X hXK)).mp hI
        have := Sheets.not_isNew_of_incident' (hLone := isLone_split T hc M m hm) hI₀
          (Sheets.not_isNew_inl _ _)
        exact this ((isNew_split_iff T hc M m hm _).mpr hNL)
      have hLol0 : wCount M.data (Lol T M) X = 0 := by
        have hle := GenusSixExistence.Tripod.Gluing.wCount_le_of_imp M.data
          (W := Lol T M) (W' := fun e ↦ ¬ IsDangling M.data e) X fun e _ he ↦ he.1
        rw [← nonDanglingValency_eq_wCount, h0] at hle
        omega
      rw [hKept0, hLol0]
      omega
    · obtain ⟨X', hX'⟩ := exists_cSV T hc M m hm hXK hNL
      rw [hKeptPart X' hX']
      have hNe' := NonDanglingValency.nonDanglingValency_ne_one _ (dat_connected T hc M m hm) X'
      have hLower : wCount M.data (fun E ↦ ¬ IsDangling M.data E ∧ KeptEdge (Keep T M) E.1.1) X ≤
          nonDanglingValency (dat T hc M m hm) X' := by
        rw [← hX', ← wCount_dat T hc M m hm (fun E ↦ ¬ IsDangling M.data E) X',
          nonDanglingValency_eq_wCount]
        exact MarkedCount.Restrict.wCount_mono _ (fun F hF ↦ not_isDangling_dat_of T hc M m hm hF) X'
      have hSplit := nonDanglingValency_split hP X
      rcases hP.kept X hXK with h0 | ⟨h1, h3⟩ <;> omega
  · rw [show wCount M.data (fun F ↦ KeptEdge (Keep T M) F.1.1 ∧ ∃ E' : (dat T hc M m hm).SourceEdge,
        cSE T hc M m hm E' = F ∧ ¬ IsDangling (dat T hc M m hm) E') X = 0 by
      unfold wCount
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro F hF
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
      exact hXK (target_mem_of_incident hF.1.1 hF.2), zero_add]
    exact hP.deleted X hXK

/-- **The dangling dictionary.** -/
theorem isDangling_dat_iff (E : (dat T hc M m hm).SourceEdge) :
    IsDangling (dat T hc M m hm) E ↔ IsDangling M.data (cSE T hc M m hm E) := by
  constructor
  · intro h; by_contra h'; exact not_isDangling_dat_of T hc M m hm h' h
  · intro h; by_contra h'; exact not_isDangling_of_dat T hc M m hm h' h

/-- **The surviving valency of `ψ`**: the frame's, minus the deleted survivors. -/
theorem nonDanglingValency_dat (X : (dat T hc M m hm).SourceVertex) :
    nonDanglingValency (dat T hc M m hm) X + wCount M.data (Lol T M) (cSV T hc M m hm X) =
      nonDanglingValency M.data (cSV T hc M m hm X) := by
  rw [nonDanglingValency_split (deletionPattern T hc M), nonDanglingValency_eq_wCount,
    ← wCount_dat T hc M m hm (fun E ↦ ¬ IsDangling M.data E) X]
  congr 1
  apply GenusSixExistence.Tripod.Gluing.wCount_congr
  intro E _
  exact not_congr (isDangling_dat_iff T hc M m hm E)

/-! ### Survivors -/

/-- A survivor of `ψ`, read in the frame. -/
def ndInc (E : NonDanglingEdge (dat T hc M m hm)) : NonDanglingEdge M.data :=
  ⟨cSE T hc M m hm E.1, not_isDangling_of_dat T hc M m hm E.2⟩

theorem ndInc_val (E : NonDanglingEdge (dat T hc M m hm)) :
    (ndInc T hc M m hm E).1 = cSE T hc M m hm E.1 := rfl

theorem ndInc_injective : Function.Injective (ndInc T hc M m hm) := fun _ _ h ↦
  Subtype.ext (cSE_injective T hc M m hm (congrArg Subtype.val h))

theorem ndInc_kept (E : NonDanglingEdge (dat T hc M m hm)) :
    KeptEdge (Keep T M) (ndInc T hc M m hm E).1.1.1 := cSE_kept T hc M m hm E.1

/-- **The survivor dictionary**: survivors of `ψ` are the kept survivors of the frame. -/
noncomputable def ndEquiv :
    NonDanglingEdge (dat T hc M m hm) ≃ {F : NonDanglingEdge M.data // KeptEdge (Keep T M) F.1.1.1} :=
  Equiv.ofBijective (fun E ↦ ⟨ndInc T hc M m hm E, ndInc_kept T hc M m hm E⟩) (by
    constructor
    · intro E F h
      exact ndInc_injective T hc M m hm (congrArg Subtype.val h)
    · intro F
      obtain ⟨E, hE⟩ := exists_cSE_of_survivor T hc M m hm F.1.2 F.2
      refine ⟨⟨E, not_isDangling_dat_of T hc M m hm (hE ▸ F.1.2)⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hE))

@[simp] theorem ndEquiv_apply (E : NonDanglingEdge (dat T hc M m hm)) :
    (ndEquiv T hc M m hm E).1 = ndInc T hc M m hm E := rfl

end

end DraismaVargas.Count.MarkedCountGeneral.TailRestrict
