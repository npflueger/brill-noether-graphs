module

public import DraismaVargasMarkedCount.MarkedCount.RegrowDangling
public import DraismaVargasMarkedCount.MarkedCount.MarkedFrame

@[expose] public section

/-!
# Regrowth, part 4: the stable graph of the regrown datum

With the dangling dictionary of
`RegrowDangling`, the stable graph of `regrowDatum β` is the marked stable graph of `D` (marks
`marks β`, the image of `β.mark`) with a lollipop at every mark:

* `stablePathEquiv : StablePath R ≃ MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k)`: the marked
  rows of `D`, the bridge rows `{e_b j}` and the loop rows `{e₁ j, e₂ j}`;
* `branchVertexEquiv : MarkedBranchVertex D (marks β) ⊕ Fin k ≃ BranchVertex R`: the marked
  vertices of `D` (a mark becomes trivalent) and the vertices `w j`;
* the incidence counts (`incidenceCount_*`), the occurrences of every row over every target
  edge (`occurrences_*`), `trivalent` and `pathEnds`.

Hypotheses: `D` connected, every mark with a surviving edge (`hMark`), and for the vertex and
incidence statements the marks distinct (`hInj`).
-/

namespace DraismaVargas.Count.MarkedCount.Regrow

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open GenusSixExistence.Tripod.Gluing (SheetOps.pair)

variable {T : CFGraph.{0}} {d k : ℕ} {D : GluingDatum T d} (β : Branching D k)

/-- The marks, as a finset of source vertices of `D` (`markSet`, reducibly). -/
abbrev marks : Finset D.SourceVertex := markSet β.mark

theorem mem_marks_iff (Y : D.SourceVertex) : Y ∈ marks β ↔ ∃ j, β.mark j = Y := by
  simp [marks, markSet]

theorem markCount_eq_zero_iff (Y : D.SourceVertex) : markCount β Y = 0 ↔ Y ∉ marks β := by
  unfold markCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff, mem_marks_iff]
  simp

theorem markCount_eq_ite (hInj : Function.Injective β.mark) (Y : D.SourceVertex) :
    markCount β Y = if Y ∈ marks β then 1 else 0 := by
  split_ifs with hY
  · obtain ⟨j, rfl⟩ := (mem_marks_iff β _).mp hY
    unfold markCount
    rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    simp [hInj.eq_iff]
  · exact (markCount_eq_zero_iff β Y).mpr hY

/-! ## 1.  Incident vertices of the surviving edges -/

theorem incident_oldSE_iff (F : D.SourceEdge) (X : (regrowDatum β).SourceVertex) :
    Incident (regrowDatum β) (oldSE β F) X ↔ ∃ Y, X = oldSV β Y ∧ Incident D F Y := by
  rcases sourceVertex_cases β X with ⟨Y, rfl⟩ | ⟨j, i, rfl⟩ | ⟨j, i, rfl⟩
  · simp
  · simp
  · simp

theorem incident_ebSE_iff (j : Fin k) (X : (regrowDatum β).SourceVertex) :
    Incident (regrowDatum β) (ebSE β j) X ↔ X = oldSV β (β.mark j) ∨ X = wSV β j := by
  unfold ebSE wSV
  rcases sourceVertex_cases β X with ⟨Y, rfl⟩ | ⟨j', i, rfl⟩ | ⟨j', i, rfl⟩
  · rw [incident_bridgeSE_oldSV, sourceEndpoint_x_of_rel β j rfl]
    simp [eq_comm]
  · rw [incident_bridgeSE_midSV, midSV_eq_iff]
    simp only [false_or, midSV_ne_oldSV]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h.symm⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h.symm⟩
  · simp

theorem incident_leafSE_iff (j : Fin k) {i : Fin d} (hi : (β.P j).Rel i (β.a j))
    (X : (regrowDatum β).SourceVertex) :
    Incident (regrowDatum β) (leafSE β j i) X ↔ X = wSV β j ∨ X = cSV β j := by
  unfold wSV cSV
  rcases sourceVertex_cases β X with ⟨Y, rfl⟩ | ⟨j', i', rfl⟩ | ⟨j', i', rfl⟩
  · simp
  · rw [incident_leafSE_midSV, midSV_eq_iff]
    simp only [midSV_ne_tipSV, or_false]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h.symm.trans hi⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, hi.trans h.symm⟩
  · rw [incident_leafSE_tipSV, tipSV_eq_iff]
    simp only [tipSV_ne_midSV, false_or]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h.symm.trans hi⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, hi.trans h.symm⟩

theorem incident_e₁SE_iff (j : Fin k) (X : (regrowDatum β).SourceVertex) :
    Incident (regrowDatum β) (e₁SE β j) X ↔ X = wSV β j ∨ X = cSV β j :=
  incident_leafSE_iff β j rfl X

theorem incident_e₂SE_iff (j : Fin k) (X : (regrowDatum β).SourceVertex) :
    Incident (regrowDatum β) (e₂SE β j) X ↔ X = wSV β j ∨ X = cSV β j :=
  incident_leafSE_iff β j ((β.P_rel_other j).symm) X

@[simp] theorem wSV_ne_oldSV (j : Fin k) (Y : D.SourceVertex) : wSV β j ≠ oldSV β Y :=
  midSV_ne_oldSV β Y j _
@[simp] theorem cSV_ne_oldSV (j : Fin k) (Y : D.SourceVertex) : cSV β j ≠ oldSV β Y :=
  tipSV_ne_oldSV β Y j _
@[simp] theorem oldSV_ne_wSV (j : Fin k) (Y : D.SourceVertex) : oldSV β Y ≠ wSV β j :=
  oldSV_ne_midSV β Y j _
@[simp] theorem oldSV_ne_cSV (j : Fin k) (Y : D.SourceVertex) : oldSV β Y ≠ cSV β j :=
  oldSV_ne_tipSV β Y j _
@[simp] theorem incident_oldSE_wSV (F : D.SourceEdge) (j : Fin k) :
    ¬ Incident (regrowDatum β) (oldSE β F) (wSV β j) := incident_oldSE_midSV β F j _
@[simp] theorem incident_oldSE_cSV (F : D.SourceEdge) (j : Fin k) :
    ¬ Incident (regrowDatum β) (oldSE β F) (cSV β j) := incident_oldSE_tipSV β F j _
@[simp] theorem wSV_ne_cSV (j j' : Fin k) : wSV β j ≠ cSV β j' := midSV_ne_tipSV β _ _ _ _
@[simp] theorem cSV_ne_wSV (j j' : Fin k) : cSV β j ≠ wSV β j' := tipSV_ne_midSV β _ _ _ _
@[simp] theorem wSV_inj {j j' : Fin k} : wSV β j = wSV β j' ↔ j = j' := by
  unfold wSV
  rw [midSV_eq_iff]
  constructor
  · exact fun h ↦ h.1
  · rintro rfl; exact ⟨rfl, rfl⟩
@[simp] theorem cSV_inj {j j' : Fin k} : cSV β j = cSV β j' ↔ j = j' := by
  unfold cSV
  rw [tipSV_eq_iff]
  constructor
  · exact fun h ↦ h.1
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem e₁SE_ne_e₂SE (j j' : Fin k) : e₁SE β j ≠ e₂SE β j' := by
  unfold e₁SE e₂SE
  rw [Ne, leafSE_eq_iff]
  rintro ⟨rfl, h⟩
  exact β.a_ne j h

@[simp] theorem ebSE_inj {j j' : Fin k} : ebSE β j = ebSE β j' ↔ j = j' := by
  unfold ebSE
  rw [bridgeSE_eq_iff]
  constructor
  · exact fun h ↦ h.1
  · rintro rfl; exact ⟨rfl, rfl⟩

@[simp] theorem e₁SE_inj {j j' : Fin k} : e₁SE β j = e₁SE β j' ↔ j = j' := by
  unfold e₁SE
  rw [leafSE_eq_iff]
  constructor
  · rintro ⟨rfl, -⟩; rfl
  · rintro rfl; exact ⟨rfl, rfl⟩

@[simp] theorem e₂SE_inj {j j' : Fin k} : e₂SE β j = e₂SE β j' ↔ j = j' := by
  unfold e₂SE
  rw [leafSE_eq_iff]
  constructor
  · rintro ⟨rfl, -⟩; rfl
  · rintro rfl; exact ⟨rfl, rfl⟩

@[simp] theorem oldSE_ne_ebSE (F : D.SourceEdge) (j : Fin k) : oldSE β F ≠ ebSE β j :=
  oldSE_ne_bridgeSE β _ _ _
@[simp] theorem oldSE_ne_e₁SE (F : D.SourceEdge) (j : Fin k) : oldSE β F ≠ e₁SE β j :=
  oldSE_ne_leafSE β _ _ _
@[simp] theorem oldSE_ne_e₂SE (F : D.SourceEdge) (j : Fin k) : oldSE β F ≠ e₂SE β j :=
  oldSE_ne_leafSE β _ _ _
@[simp] theorem ebSE_ne_e₁SE (j j' : Fin k) : ebSE β j ≠ e₁SE β j' := bridgeSE_ne_leafSE β _ _ _ _
@[simp] theorem ebSE_ne_e₂SE (j j' : Fin k) : ebSE β j ≠ e₂SE β j' := bridgeSE_ne_leafSE β _ _ _ _

/-! ## 2.  Surviving edges and valencies -/

variable (hD : D.Connected) (hMark : ∀ j, nonDanglingValency D (β.mark j) ≠ 0)

/-- An old surviving edge, in the regrowth. -/
def oldND (F : NonDanglingEdge D) : NonDanglingEdge (regrowDatum β) :=
  ⟨oldSE β F.1, fun h ↦ F.2 ((isDangling_oldSE_iff β hD hMark F.1).mp h)⟩

/-- The bridge `e_b j`, as a surviving edge. -/
def ebND (j : Fin k) : NonDanglingEdge (regrowDatum β) :=
  ⟨ebSE β j, not_isDangling_ebSE β hD hMark j⟩

/-- The loop edge `e₁ j`, as a surviving edge. -/
def e₁ND (j : Fin k) : NonDanglingEdge (regrowDatum β) :=
  ⟨e₁SE β j, not_isDangling_e₁SE β hD hMark j⟩

/-- The loop edge `e₂ j`, as a surviving edge. -/
def e₂ND (j : Fin k) : NonDanglingEdge (regrowDatum β) :=
  ⟨e₂SE β j, not_isDangling_e₂SE β hD hMark j⟩

theorem nonDanglingEdge_cases (E : NonDanglingEdge (regrowDatum β)) :
    (∃ F, E = oldND β hD hMark F) ∨ (∃ j, E = ebND β hD hMark j) ∨
      (∃ j, E = e₁ND β hD hMark j) ∨ (∃ j, E = e₂ND β hD hMark j) := by
  rcases (not_isDangling_iff β hD hMark E.1).mp E.2 with ⟨F, h, hF⟩ | ⟨j, h⟩ | ⟨j, h⟩ | ⟨j, h⟩
  · exact Or.inl ⟨⟨F, hF⟩, Subtype.ext h⟩
  · exact Or.inr (Or.inl ⟨j, Subtype.ext h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨j, Subtype.ext h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, Subtype.ext h⟩))

include hD hMark

theorem two_le_nonDanglingValency_mark (j : Fin k) : 2 ≤ nonDanglingValency D (β.mark j) := by
  have h1 := hMark j
  have h2 := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one D hD (β.mark j)
  omega

theorem three_le_nonDanglingValency_oldSV_mark (j : Fin k) :
    3 ≤ nonDanglingValency (regrowDatum β) (oldSV β (β.mark j)) := by
  rw [nonDanglingValency_oldSV β hD hMark]
  have h1 := two_le_nonDanglingValency_mark β hD hMark j
  have h2 : markCount β (β.mark j) ≠ 0 := by
    rw [Ne, markCount_eq_zero_iff, not_not, mem_marks_iff]
    exact ⟨j, rfl⟩
  omega

theorem nonDanglingValency_oldSV_of_not_mem {Y : D.SourceVertex} (hY : Y ∉ marks β) :
    nonDanglingValency (regrowDatum β) (oldSV β Y) = nonDanglingValency D Y := by
  rw [nonDanglingValency_oldSV β hD hMark, (markCount_eq_zero_iff β Y).mpr hY, add_zero]

/-- The surviving valency at an old vertex is two iff it is two in `D` and the vertex is not a
mark. -/
theorem nonDanglingValency_oldSV_eq_two_iff (Y : D.SourceVertex) :
    nonDanglingValency (regrowDatum β) (oldSV β Y) = 2 ↔
      nonDanglingValency D Y = 2 ∧ Y ∉ marks β := by
  constructor
  · intro h
    by_cases hY : Y ∈ marks β
    · obtain ⟨j, rfl⟩ := (mem_marks_iff β _).mp hY
      have := three_le_nonDanglingValency_oldSV_mark β hD hMark j
      omega
    · rw [nonDanglingValency_oldSV_of_not_mem β hD hMark hY] at h
      exact ⟨h, hY⟩
  · rintro ⟨h, hY⟩
    rw [nonDanglingValency_oldSV_of_not_mem β hD hMark hY, h]

/-! ## 3.  The stable paths -/

open Classical in
/-- The row of a surviving edge of the regrowth: a marked row of `D`, a bridge row or a loop
row. -/
def rowTag (E : NonDanglingEdge (regrowDatum β)) :
    MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k) :=
  if h : ∃ F : NonDanglingEdge D, E.1 = oldSE β F.1 then .inl (markedRow (marks β) h.choose)
  else if h' : ∃ j, E.1 = ebSE β j then .inr (.inl h'.choose)
  else if h'' : ∃ j, E.1 = e₁SE β j ∨ E.1 = e₂SE β j then .inr (.inr h''.choose)
  else False.elim (by
    rcases nonDanglingEdge_cases β hD hMark E with ⟨F, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact h ⟨F, rfl⟩
    · exact h' ⟨j, rfl⟩
    · exact h'' ⟨j, Or.inl rfl⟩
    · exact h'' ⟨j, Or.inr rfl⟩)

theorem rowTag_oldND (F : NonDanglingEdge D) :
    rowTag β hD hMark (oldND β hD hMark F) = .inl (markedRow (marks β) F) := by
  have h : ∃ F' : NonDanglingEdge D, (oldND β hD hMark F).1 = oldSE β F'.1 := ⟨F, rfl⟩
  unfold rowTag
  rw [dite_eq_left h]
  congr 2
  exact Subtype.ext (oldSE_injective β h.choose_spec).symm

theorem rowTag_ebND (j : Fin k) :
    rowTag β hD hMark (ebND β hD hMark j) = .inr (.inl j) := by
  have h0 : ¬ ∃ F' : NonDanglingEdge D, (ebND β hD hMark j).1 = oldSE β F'.1 :=
    fun ⟨F', h⟩ ↦ oldSE_ne_ebSE β F'.1 j h.symm
  have h : ∃ j', (ebND β hD hMark j).1 = ebSE β j' := ⟨j, rfl⟩
  unfold rowTag
  rw [dite_eq_right h0, dite_eq_left h]
  congr 2
  exact ((ebSE_inj β).mp h.choose_spec).symm

theorem rowTag_loop {j : Fin k} (E : NonDanglingEdge (regrowDatum β))
    (hE : E.1 = e₁SE β j ∨ E.1 = e₂SE β j) : rowTag β hD hMark E = .inr (.inr j) := by
  have h0 : ¬ ∃ F' : NonDanglingEdge D, E.1 = oldSE β F'.1 := by
    rintro ⟨F', h⟩
    rcases hE with hE | hE <;> rw [hE] at h
    · exact oldSE_ne_e₁SE β F'.1 j h.symm
    · exact oldSE_ne_e₂SE β F'.1 j h.symm
  have h1 : ¬ ∃ j', E.1 = ebSE β j' := by
    rintro ⟨j', h⟩
    rcases hE with hE | hE <;> rw [hE] at h
    · exact ebSE_ne_e₁SE β j' j h.symm
    · exact ebSE_ne_e₂SE β j' j h.symm
  have h : ∃ j', E.1 = e₁SE β j' ∨ E.1 = e₂SE β j' := ⟨j, hE⟩
  unfold rowTag
  rw [dite_eq_right h0, dite_eq_right h1, dite_eq_left h]
  congr 2
  obtain ⟨c, hc⟩ : ∃ c, h.choose = c := ⟨_, rfl⟩
  have h' := h.choose_spec
  rw [hc] at h' ⊢
  rcases h' with h' | h' <;> rcases hE with hE | hE <;> rw [hE] at h'
  · exact ((e₁SE_inj β).mp h').symm
  · exact absurd h' (e₁SE_ne_e₂SE β _ _).symm
  · exact absurd h' (e₁SE_ne_e₂SE β _ _)
  · exact ((e₂SE_inj β).mp h').symm

theorem rowTag_e₁ND (j : Fin k) : rowTag β hD hMark (e₁ND β hD hMark j) = .inr (.inr j) :=
  rowTag_loop β hD hMark _ (Or.inl rfl)

theorem rowTag_e₂ND (j : Fin k) : rowTag β hD hMark (e₂ND β hD hMark j) = .inr (.inr j) :=
  rowTag_loop β hD hMark _ (Or.inr rfl)

/-- A surviving edge at the vertex `C j` is a loop edge of mark `j`. -/
theorem rowTag_of_incident_cSV (E : NonDanglingEdge (regrowDatum β)) (j : Fin k)
    (hE : Incident (regrowDatum β) E.1 (cSV β j)) : rowTag β hD hMark E = .inr (.inr j) := by
  rcases nonDanglingEdge_cases β hD hMark E with ⟨F, rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · obtain ⟨Y, hY, -⟩ := (incident_oldSE_iff β _ _).mp hE
    exact absurd hY (cSV_ne_oldSV β _ _)
  · rcases (incident_ebSE_iff β _ _).mp hE with h | h
    · exact absurd h (cSV_ne_oldSV β _ _)
    · exact absurd h (cSV_ne_wSV β _ _)
  · rcases (incident_e₁SE_iff β _ _).mp hE with h | h
    · exact absurd h (cSV_ne_wSV β _ _)
    · rw [(cSV_inj β).mp h]; exact rowTag_e₁ND β hD hMark j'
  · rcases (incident_e₂SE_iff β _ _).mp hE with h | h
    · exact absurd h (cSV_ne_wSV β _ _)
    · rw [(cSV_inj β).mp h]; exact rowTag_e₂ND β hD hMark j'

/-- A new surviving edge at a vertex of surviving valency two meets it at `C j`. -/
theorem eq_cSV_of_new (E : NonDanglingEdge (regrowDatum β)) (hE : ¬ ∃ F, E = oldND β hD hMark F)
    {X : (regrowDatum β).SourceVertex} (hX : Incident (regrowDatum β) E.1 X)
    (hTwo : nonDanglingValency (regrowDatum β) X = 2) : ∃ j, X = cSV β j := by
  have hW : ∀ j, nonDanglingValency (regrowDatum β) (wSV β j) ≠ 2 := fun j ↦ by
    rw [nonDanglingValency_wSV β hD hMark]; omega
  have hM : ∀ j, nonDanglingValency (regrowDatum β) (oldSV β (β.mark j)) ≠ 2 := fun j ↦ by
    have := three_le_nonDanglingValency_oldSV_mark β hD hMark j; omega
  rcases nonDanglingEdge_cases β hD hMark E with ⟨F, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact absurd ⟨F, rfl⟩ hE
  · rcases (incident_ebSE_iff β _ _).mp hX with rfl | rfl
    · exact absurd hTwo (hM j)
    · exact absurd hTwo (hW j)
  · rcases (incident_e₁SE_iff β _ _).mp hX with rfl | rfl
    · exact absurd hTwo (hW j)
    · exact ⟨j, rfl⟩
  · rcases (incident_e₂SE_iff β _ _).mp hX with rfl | rfl
    · exact absurd hTwo (hW j)
    · exact ⟨j, rfl⟩

/-- **Consecutive surviving edges have the same row.** -/
theorem rowTag_eq_of_consecutive {E E' : NonDanglingEdge (regrowDatum β)}
    (h : Consecutive (regrowDatum β) E E') : rowTag β hD hMark E = rowTag β hD hMark E' := by
  obtain ⟨hne, X, hE, hE', hX⟩ := h
  by_cases hOld : ∃ F, E = oldND β hD hMark F
  · by_cases hOld' : ∃ F', E' = oldND β hD hMark F'
    · obtain ⟨F, rfl⟩ := hOld
      obtain ⟨F', rfl⟩ := hOld'
      obtain ⟨Y, rfl, hFY⟩ := (incident_oldSE_iff β _ _).mp hE
      obtain ⟨Y', hY', hF'Y⟩ := (incident_oldSE_iff β _ _).mp hE'
      rw [oldSV_inj] at hY'
      subst hY'
      rw [rowTag_oldND, rowTag_oldND]
      obtain ⟨hTwo, hNot⟩ := (nonDanglingValency_oldSV_eq_two_iff β hD hMark Y).mp hX
      refine congrArg Sum.inl (markedRow_eq_of_markedConsecutive ⟨fun hFF ↦ hne ?_, Y, hFY,
        hF'Y, hTwo, hNot⟩)
      rw [hFF]
    · obtain ⟨j, rfl⟩ := eq_cSV_of_new β hD hMark E' hOld' hE' hX
      obtain ⟨F, rfl⟩ := hOld
      obtain ⟨Y, hY, -⟩ := (incident_oldSE_iff β _ _).mp hE
      exact absurd hY (cSV_ne_oldSV β _ _)
  · obtain ⟨j, rfl⟩ := eq_cSV_of_new β hD hMark E hOld hE hX
    rw [rowTag_of_incident_cSV β hD hMark E j hE, rowTag_of_incident_cSV β hD hMark E' j hE']

/-- The row of a stable path of the regrowth. -/
def pathTag : StablePath (regrowDatum β) → MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k) :=
  Quot.lift (rowTag β hD hMark) fun _ _ h ↦ rowTag_eq_of_consecutive β hD hMark h

/-- Marked consecutiveness in `D` is consecutiveness in the regrowth. -/
theorem consecutive_oldND {F F' : NonDanglingEdge D} (h : MarkedConsecutive D (marks β) F F') :
    Consecutive (regrowDatum β) (oldND β hD hMark F) (oldND β hD hMark F') := by
  obtain ⟨hne, Y, hF, hF', hTwo, hNot⟩ := h
  refine ⟨fun h ↦ hne (Subtype.ext (oldSE_injective β (congrArg Subtype.val h))), oldSV β Y,
    (incident_oldSE_oldSV β _ _).mpr hF, (incident_oldSE_oldSV β _ _).mpr hF', ?_⟩
  exact (nonDanglingValency_oldSV_eq_two_iff β hD hMark Y).mpr ⟨hTwo, hNot⟩

/-- The stable path of the regrowth with a given row. -/
def tagPath : MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k) → StablePath (regrowDatum β)
  | .inl P => Quot.lift (fun F ↦ (oldND β hD hMark F).stablePath)
      (fun _ _ h ↦ stablePath_eq_of_consecutive (consecutive_oldND β hD hMark h)) P
  | .inr (.inl j) => (ebND β hD hMark j).stablePath
  | .inr (.inr j) => (e₁ND β hD hMark j).stablePath

theorem tagPath_inl_markedRow (F : NonDanglingEdge D) :
    tagPath β hD hMark (.inl (markedRow (marks β) F)) = (oldND β hD hMark F).stablePath := rfl

theorem stablePath_e₂ND (j : Fin k) :
    (e₂ND β hD hMark j).stablePath = (e₁ND β hD hMark j).stablePath := by
  refine (stablePath_eq_of_consecutive ⟨fun h ↦ e₁SE_ne_e₂SE β j j
    (congrArg Subtype.val h).symm, cSV β j, ?_, ?_, nonDanglingValency_cSV β hD hMark j⟩)
  · exact (incident_e₂SE_iff β j _).mpr (Or.inr rfl)
  · exact (incident_e₁SE_iff β j _).mpr (Or.inr rfl)

/-- **The stable paths of the regrowth**: the marked rows of `D`, one bridge row and one loop row
per mark. -/
def stablePathEquiv :
    StablePath (regrowDatum β) ≃ MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k) where
  toFun := pathTag β hD hMark
  invFun := tagPath β hD hMark
  left_inv path := by
    induction path using Quot.ind with
    | mk E =>
      change tagPath β hD hMark (rowTag β hD hMark E) = E.stablePath
      rcases nonDanglingEdge_cases β hD hMark E with ⟨F, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [rowTag_oldND]; rfl
      · rw [rowTag_ebND]; rfl
      · rw [rowTag_e₁ND]; rfl
      · rw [rowTag_e₂ND, stablePath_e₂ND]; rfl
  right_inv tag := by
    rcases tag with P | j | j
    · induction P using Quot.ind with
      | mk F => exact rowTag_oldND β hD hMark F
    · exact rowTag_ebND β hD hMark j
    · exact rowTag_e₁ND β hD hMark j

theorem stablePathEquiv_symm_apply (tag : MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k)) :
    (stablePathEquiv β hD hMark).symm tag = tagPath β hD hMark tag := rfl

theorem stablePathEquiv_stablePath (E : NonDanglingEdge (regrowDatum β)) :
    stablePathEquiv β hD hMark E.stablePath = rowTag β hD hMark E := rfl

/-- The row of a surviving edge, from its stable path. -/
theorem stablePath_eq_tagPath_iff (E : NonDanglingEdge (regrowDatum β))
    (tag : MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k)) :
    E.stablePath = tagPath β hD hMark tag ↔ rowTag β hD hMark E = tag := by
  rw [← stablePathEquiv_symm_apply, Equiv.eq_symm_apply]
  rfl

/-! ## 4.  Sums over the surviving edges -/

theorem oldND_injective : Function.Injective (oldND β hD hMark) := fun _ _ h ↦
  Subtype.ext (oldSE_injective β (congrArg Subtype.val h))

/-- The forward map of the decomposition of the surviving edges. -/
def ndOfSum : NonDanglingEdge D ⊕ (Fin k ⊕ (Fin k ⊕ Fin k)) → NonDanglingEdge (regrowDatum β)
  | .inl F => oldND β hD hMark F
  | .inr (.inl j) => ebND β hD hMark j
  | .inr (.inr (.inl j)) => e₁ND β hD hMark j
  | .inr (.inr (.inr j)) => e₂ND β hD hMark j

theorem ndOfSum_bijective : Function.Bijective (ndOfSum β hD hMark) := by
  constructor
  · rintro (F | j | j | j) (F' | j' | j' | j') h <;>
      have h' := congrArg Subtype.val h <;>
      simp only [ndOfSum, oldND, ebND, e₁ND, e₂ND, oldSE_inj, ebSE_inj, e₁SE_inj, e₂SE_inj,
        oldSE_ne_ebSE, oldSE_ne_e₁SE, oldSE_ne_e₂SE, ebSE_ne_e₁SE, ebSE_ne_e₂SE] at h'
    all_goals first
      | (subst h'; rfl)
      | exact absurd h' (oldSE_ne_ebSE β _ _).symm
      | exact absurd h' (oldSE_ne_e₁SE β _ _).symm
      | exact absurd h' (oldSE_ne_e₂SE β _ _).symm
      | exact absurd h' (ebSE_ne_e₁SE β _ _).symm
      | exact absurd h' (ebSE_ne_e₂SE β _ _).symm
      | exact absurd h' (e₁SE_ne_e₂SE β _ _)
      | exact absurd h' (e₁SE_ne_e₂SE β _ _).symm
      | (rw [Subtype.ext h'])
  · intro E
    rcases nonDanglingEdge_cases β hD hMark E with ⟨F, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨.inl F, rfl⟩
    · exact ⟨.inr (.inl j), rfl⟩
    · exact ⟨.inr (.inr (.inl j)), rfl⟩
    · exact ⟨.inr (.inr (.inr j)), rfl⟩

/-- **Sums over the surviving edges of the regrowth.** -/
theorem sum_nonDanglingEdge {M : Type*} [AddCommMonoid M]
    (f : NonDanglingEdge (regrowDatum β) → M) :
    ∑ E, f E = ∑ F, f (oldND β hD hMark F) + ∑ j, f (ebND β hD hMark j) +
      ∑ j, f (e₁ND β hD hMark j) + ∑ j, f (e₂ND β hD hMark j) := by
  rw [← Fintype.sum_bijective _ (ndOfSum_bijective β hD hMark)
    (fun z ↦ f (ndOfSum β hD hMark z)) f (fun _ ↦ rfl), Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc, ← add_assoc]
  rfl

/-! ## 5.  Incidence counts -/

omit hD hMark in
open Classical in
theorem incidenceCount_eq_sum (X : (regrowDatum β).SourceVertex)
    (path : StablePath (regrowDatum β)) :
    StablePathCount.incidenceCount (regrowDatum β) X path =
      ∑ E : NonDanglingEdge (regrowDatum β),
        if Incident (regrowDatum β) E.1 X ∧ E.stablePath = path then 1 else 0 := by
  unfold StablePathCount.incidenceCount StablePathCount.incidentEdges
  rw [Finset.filter_filter, Finset.card_filter]

omit hD hMark in
open Classical in
theorem markedIncidenceCount_eq_sum (Y : D.SourceVertex) (P : MarkedStablePath D (marks β)) :
    markedIncidenceCount D (marks β) Y P =
      ∑ F : NonDanglingEdge D, if Incident D F.1 Y ∧ markedRow (marks β) F = P then 1 else 0 := by
  classical
  unfold markedIncidenceCount StablePathCount.incidentEdges
  rw [Finset.filter_filter, Finset.card_filter]

/-- An incidence count of the regrowth, by rows: summed over the four kinds of surviving edge. -/
theorem incidenceCount_tagPath (X : (regrowDatum β).SourceVertex)
    (tag : MarkedStablePath D (marks β) ⊕ (Fin k ⊕ Fin k)) :
    StablePathCount.incidenceCount (regrowDatum β) X (tagPath β hD hMark tag) =
      (∑ F : NonDanglingEdge D,
          if Incident (regrowDatum β) (oldSE β F.1) X ∧ Sum.inl (markedRow (marks β) F) = tag
            then 1 else 0) +
        (∑ j, if Incident (regrowDatum β) (ebSE β j) X ∧ Sum.inr (Sum.inl j) = tag
            then 1 else 0) +
        (∑ j, if Incident (regrowDatum β) (e₁SE β j) X ∧ Sum.inr (Sum.inr j) = tag
            then 1 else 0) +
        (∑ j, if Incident (regrowDatum β) (e₂SE β j) X ∧ Sum.inr (Sum.inr j) = tag
            then 1 else 0) := by
  classical
  rw [incidenceCount_eq_sum, sum_nonDanglingEdge β hD hMark]
  simp only [stablePath_eq_tagPath_iff, rowTag_oldND, rowTag_ebND, rowTag_e₁ND, rowTag_e₂ND]
  rfl

theorem incidenceCount_oldSV_inl (Y : D.SourceVertex) (P : MarkedStablePath D (marks β)) :
    StablePathCount.incidenceCount (regrowDatum β) (oldSV β Y) (tagPath β hD hMark (.inl P)) =
      markedIncidenceCount D (marks β) Y P := by
  classical
  rw [incidenceCount_tagPath, markedIncidenceCount_eq_sum]
  simp [incident_ebSE_iff, incident_e₁SE_iff, incident_e₂SE_iff]

theorem incidenceCount_oldSV_bridge (Y : D.SourceVertex) (j : Fin k) :
    StablePathCount.incidenceCount (regrowDatum β) (oldSV β Y)
        (tagPath β hD hMark (.inr (.inl j))) = if β.mark j = Y then 1 else 0 := by
  classical
  rw [incidenceCount_tagPath]
  simp [incident_ebSE_iff, incident_e₁SE_iff, incident_e₂SE_iff, eq_comm]
  by_cases h : Y = β.mark j
  · rw [ite_eq_left h, eq_comm, Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩; rfl
    · rintro rfl; exact ⟨h, rfl⟩
  · rw [ite_eq_right h, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨hx, rfl⟩
    exact h hx

theorem incidenceCount_oldSV_loop (Y : D.SourceVertex) (j : Fin k) :
    StablePathCount.incidenceCount (regrowDatum β) (oldSV β Y)
        (tagPath β hD hMark (.inr (.inr j))) = 0 := by
  classical
  rw [incidenceCount_tagPath]
  simp [incident_ebSE_iff, incident_e₁SE_iff, incident_e₂SE_iff]

theorem incidenceCount_wSV_inl (j : Fin k) (P : MarkedStablePath D (marks β)) :
    StablePathCount.incidenceCount (regrowDatum β) (wSV β j) (tagPath β hD hMark (.inl P)) =
      0 := by
  classical
  rw [incidenceCount_tagPath]
  simp [incident_ebSE_iff, incident_e₁SE_iff, incident_e₂SE_iff]

theorem incidenceCount_wSV_bridge (j j' : Fin k) :
    StablePathCount.incidenceCount (regrowDatum β) (wSV β j)
        (tagPath β hD hMark (.inr (.inl j'))) = if j' = j then 1 else 0 := by
  classical
  rw [incidenceCount_tagPath]
  simp [incident_ebSE_iff, incident_e₁SE_iff, incident_e₂SE_iff, eq_comm]
  by_cases h : j = j'
  · subst h
    rw [ite_eq_left rfl, eq_comm, Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, -⟩; rfl
    · rintro rfl; exact ⟨rfl, rfl⟩
  · rw [ite_eq_right h, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨rfl, rfl⟩
    exact h rfl

theorem incidenceCount_wSV_loop (j j' : Fin k) :
    StablePathCount.incidenceCount (regrowDatum β) (wSV β j)
        (tagPath β hD hMark (.inr (.inr j'))) = if j' = j then 2 else 0 := by
  classical
  rw [incidenceCount_tagPath]
  simp only [incident_ebSE_iff, incident_e₁SE_iff, incident_e₂SE_iff, incident_oldSE_wSV,
    wSV_ne_oldSV, wSV_inj, wSV_ne_cSV, or_false, false_or, ite_false,
    Finset.sum_const_zero, reduceCtorEq, and_false, zero_add, Sum.inr.injEq]
  have hsum : (∑ x : Fin k, if j = x ∧ x = j' then (1 : ℕ) else 0) = if j' = j then 1 else 0 := by
    rw [Finset.sum_eq_single j]
    · by_cases h : j' = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro x _ hx; simp [Ne.symm hx]
    · simp
  rw [hsum]
  split_ifs <;> rfl

/-! ## 6.  The branch vertices -/

variable (hInj : Function.Injective β.mark)

include hInj

theorem three_le_nonDanglingValency_oldSV_iff (Y : D.SourceVertex) :
    3 ≤ nonDanglingValency (regrowDatum β) (oldSV β Y) ↔
      3 ≤ nonDanglingValency D Y ∨ Y ∈ marks β := by
  rw [nonDanglingValency_oldSV β hD hMark, markCount_eq_ite β hInj]
  split_ifs with hY
  · obtain ⟨j, rfl⟩ := (mem_marks_iff β _).mp hY
    have := two_le_nonDanglingValency_mark β hD hMark j
    simp only [hY, or_true, iff_true]
    omega
  · simp [hY]

/-- The map onto the branch vertices of the regrowth. -/
def bvOfSum : MarkedBranchVertex D (marks β) ⊕ Fin k → BranchVertex (regrowDatum β)
  | .inl Y => ⟨oldSV β Y.1, (three_le_nonDanglingValency_oldSV_iff β hD hMark hInj Y.1).mpr Y.2⟩
  | .inr j => ⟨wSV β j, by rw [nonDanglingValency_wSV β hD hMark]⟩

theorem bvOfSum_bijective : Function.Bijective (bvOfSum β hD hMark hInj) := by
  constructor
  · rintro (Y | j) (Y' | j') h <;> have h' := congrArg Subtype.val h <;>
      simp only [bvOfSum, oldSV_inj, wSV_inj] at h'
    · exact congrArg Sum.inl (Subtype.ext h')
    · exact absurd h'.symm (wSV_ne_oldSV β _ _)
    · exact absurd h' (wSV_ne_oldSV β _ _)
    · rw [h']
  · rintro ⟨X, hX⟩
    rcases sourceVertex_cases β X with ⟨Y, rfl⟩ | ⟨j, i, rfl⟩ | ⟨j, i, rfl⟩
    · exact ⟨.inl ⟨Y, (three_le_nonDanglingValency_oldSV_iff β hD hMark hInj Y).mp hX⟩, rfl⟩
    · rw [nonDanglingValency_midSV β hD hMark] at hX
      split_ifs at hX with hi
      · refine ⟨.inr j, Subtype.ext ?_⟩
        exact (midSV_eq_iff β _ _ _ _).mpr ⟨rfl, hi.symm⟩
      · omega
    · rw [nonDanglingValency_tipSV β hD hMark] at hX
      split_ifs at hX <;> omega

/-- **The branch vertices of the regrowth**: the marked vertices of `D` and one `w j` per
mark. -/
def branchVertexEquiv : MarkedBranchVertex D (marks β) ⊕ Fin k ≃ BranchVertex (regrowDatum β) :=
  Equiv.ofBijective _ (bvOfSum_bijective β hD hMark hInj)

theorem branchVertexEquiv_inl (Y : MarkedBranchVertex D (marks β)) :
    (branchVertexEquiv β hD hMark hInj (.inl Y)).1 = oldSV β Y.1 := rfl

theorem branchVertexEquiv_inr (j : Fin k) :
    (branchVertexEquiv β hD hMark hInj (.inr j)).1 = wSV β j := rfl

omit hInj

/-! ## 7.  Trivalence and path ends -/

theorem nonDanglingValency_le_three (hTri : ∀ Y, nonDanglingValency D Y ≤ 3)
    (hTwo : ∀ j, nonDanglingValency D (β.mark j) = 2) (hInj : Function.Injective β.mark)
    (X : (regrowDatum β).SourceVertex) : nonDanglingValency (regrowDatum β) X ≤ 3 := by
  rcases sourceVertex_cases β X with ⟨Y, rfl⟩ | ⟨j, i, rfl⟩ | ⟨j, i, rfl⟩
  · rw [nonDanglingValency_oldSV β hD hMark, markCount_eq_ite β hInj]
    split_ifs with hY
    · obtain ⟨j, rfl⟩ := (mem_marks_iff β _).mp hY
      rw [hTwo j]
    · simpa using hTri Y
  · rw [nonDanglingValency_midSV β hD hMark]; split_ifs <;> omega
  · rw [nonDanglingValency_tipSV β hD hMark]; split_ifs <;> omega

theorem hasPathEnds_regrowDatum (hEnds : HasMarkedPathEnds D (marks β)) :
    HasPathEnds (regrowDatum β) := by
  intro E
  have hW : ∀ j, nonDanglingValency (regrowDatum β) (wSV β j) ≠ 2 := fun j ↦ by
    rw [nonDanglingValency_wSV β hD hMark]; omega
  rcases nonDanglingEdge_cases β hD hMark E with ⟨F, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · obtain ⟨F', Y, hRow, hInc, hEnd⟩ := hEnds F
    refine ⟨oldND β hD hMark F', oldSV β Y, ?_, (incident_oldSE_oldSV β _ _).mpr hInc, ?_⟩
    · rw [← tagPath_inl_markedRow, ← tagPath_inl_markedRow, hRow]
    · intro hTwo
      obtain ⟨hTwo', hNot⟩ := (nonDanglingValency_oldSV_eq_two_iff β hD hMark Y).mp hTwo
      rcases hEnd with h | h
      · exact h hTwo'
      · exact hNot h
  · exact ⟨ebND β hD hMark j, wSV β j, rfl, (incident_ebSE_iff β j _).mpr (Or.inr rfl), hW j⟩
  · exact ⟨e₁ND β hD hMark j, wSV β j, rfl, (incident_e₁SE_iff β j _).mpr (Or.inl rfl), hW j⟩
  · exact ⟨e₂ND β hD hMark j, wSV β j, rfl, (incident_e₂SE_iff β j _).mpr (Or.inl rfl), hW j⟩

end

end DraismaVargas.Count.MarkedCount.Regrow
