module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropRows
public import DraismaVargasMarkedCount.MarkedCountGeneral.DropWalk

@[expose] public section

/-!
# The drop lemma: the two sides of the dropped mark

A contraction site `S` with the dropped mark `V` (`MarkHyp`), and a walk `W` of the contracted row
`ρ` through `V` (`MarkedWalk.seq`) from an end. The occurrence `g` of the contraction through `V`
is the `i`-th of the walk, and the walk enters it at one of its two ends. Let `f★` be the occurrence
at `V` (over `c` or over the other edge) whose far end lies over that end (`Orient`). Then
**the row of `f★` consists of the occurrences of the fibre of `ρ` before `g`, and `f★` itself**
(`row_eq_iff_side`), and the two rows through `V` are different (`fc_row_ne_fo_row`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.MarkedWalk

namespace DivalentContraction

namespace Site

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree} (S : Site data)
  {M : Finset data.SourceVertex} {V : data.SourceVertex} {M' : Finset S.D.SourceVertex}
  (hM : S.MarkHyp M V M')

/-! ## 1.  The two occurrences at `V` -/

/-- The far end of an occurrence at `V`. -/
noncomputable abbrev far (V : data.SourceVertex) (f : NonDanglingEdge data) : data.SourceVertex :=
  otherEnd data f.1 V

/-- An occurrence at `V`: the one over `c` or the other one. -/
def AtV (f : NonDanglingEdge data) : Prop := f = S.fc hM ∨ f = S.fo hM

/-- An occurrence at `V` meets `V`. -/
theorem incident_of_atV {f : NonDanglingEdge data} (hf : S.AtV hM f) : Incident data f.1 V := by
  rcases hf with rfl | rfl
  · exact S.incident_fc hM
  · exact S.incident_fo hM

/-- The far end of an occurrence at `V` is not over `x`. -/
theorem far_not_over_x {f : NonDanglingEdge data} (hf : S.AtV hM f) : (far V f).1.1 ≠ S.x := by
  intro h
  have hInc := incident_otherEnd data f.1 V
  have hne := MarkedWalk.otherEnd_ne (S.incident_of_atV hM hf)
  -- both ends of an occurrence lie over different target vertices
  have hT : ∀ (e : data.SourceEdge) (Y Z : data.SourceVertex), Incident data e Y → Incident data e Z →
      Y ≠ Z → Y.1.1 ≠ Z.1.1 := by
    intro e Y Z hY hZ hYZ hEq
    have hne' := data.sourceEnds_ne e
    have hT' : (data.sourceEnds e).1.1.1 ≠ (data.sourceEnds e).2.1.1 := by
      change (e.1.1 : target.V × target.V).1 ≠ (e.1.1 : target.V × target.V).2
      exact GluingContraction.fst_ne_snd e.1.1
    rcases hY with hY | hY <;> rcases hZ with hZ | hZ
    · exact hYZ (hY.symm.trans hZ)
    · exact hT' (by rw [hY, hZ]; exact hEq)
    · exact hT' (by rw [hY, hZ]; exact hEq.symm)
    · exact hYZ (hY.symm.trans hZ)
  exact hT f.1 _ _ hInc (S.incident_of_atV hM hf) hne (h.trans hM.onX.symm)

/-- The occurrence at `V` other than a given one is not incident to the far end of the first. -/
theorem not_incident_far {f f' : NonDanglingEdge data} (hf : S.AtV hM f) (hf' : S.AtV hM f')
    (hne : f ≠ f') : ¬ Incident data f'.1 (far V f) := by
  intro hInc
  -- `f` and `f'` lie over the two edges at `x`; `far f` is over the far end of `f`'s edge
  have hFarX := S.far_not_over_x hM hf
  have hMem := ((incident_iff_target_mem_and_rel data _ _).mp hInc).1
  have hMemf := ((incident_iff_target_mem_and_rel data _ _).mp (incident_otherEnd data f.1 V)).1
  -- the target edges of `f`, `f'` are `c` and `other`, in some order
  rcases hf with rfl | rfl <;> rcases hf' with rfl | rfl
  · exact hne rfl
  · -- `f = fc`, so `far f` is over `w`; `f' = fo` is over `other`, which does not reach `w`
    have hw : (far V (S.fc hM)).1.1 = S.w := by
      rcases S.eq_x_or_eq_w hMemf with h | h
      · exact absurd h hFarX
      · exact h
    rw [hw] at hMem
    exact S.other_not_mem_w hMem
  · -- `f = fo`, so `far f` is over the far end of `other`; `f' = fc` is over `c`
    rcases S.eq_x_or_eq_w hMem with h | h
    · exact hFarX h
    · rw [h] at hMemf
      exact S.other_not_mem_w hMemf
  · exact hne rfl

/-- The fibre of an occurrence at `V`: `fc` and `fo`. -/
theorem atV_of_edgeMap_eq {f : NonDanglingEdge data}
    (h : S.edgeMap f.1 = S.edgeMap (S.fc hM).1) : S.AtV hM f := by
  rcases S.edgeMap_eq_imp h with h' | ⟨X, hX, hfX, hcX⟩
  · exact Or.inl (Subtype.ext h')
  · have hXV : X = V := by
      have hInc := S.incident_fc hM
      rcases (S.incident_c_iff _ X).mp hcX with h₁ | h₁
      · rw [h₁]; exact (S.eq_sourceEndpoint_x V hM.onX).symm
      · exact absurd (h₁ ▸ rfl : X.1.1 = S.w) (fun h ↦ S.w_ne_x (h.symm.trans hX))
    subst hXV
    rcases (S.incident_x_iff X hM.onX f.1).mp hfX with h₁ | h₁
    · exact Or.inl (Subtype.ext h₁)
    · exact Or.inr (Subtype.ext h₁)

/-- The two occurrences at `V` have the same image. -/
theorem edgeMap_fo : S.edgeMap (S.fo hM).1 = S.edgeMap (S.fc hM).1 :=
  S.edgeMap_eq_of_incident_x hM.onX (S.incident_fo hM) (S.incident_fc hM)

/-- The two occurrences at `V` differ (they lie over different target edges). -/
theorem fc_ne_fo : S.fc hM ≠ S.fo hM := fun h ↦
  S.other_ne (congrArg (fun e : NonDanglingEdge data ↦ e.1.1.1) h).symm

/-- The far end of the occurrence over `c` at `V` is its `c`-neighbour. -/
theorem far_fc : far V (S.fc hM) = S.cNbr V := by
  have hInc : Incident data (S.fc hM).1 (S.cNbr V) := (S.incident_c_iff _ _).mpr (Or.inr rfl)
  rcases eq_or_eq_otherEnd data (S.incident_fc hM) hInc with h | h
  · exfalso
    have := congrArg (fun X : data.SourceVertex ↦ X.1.1) h
    exact S.w_ne_x (this.trans hM.onX)
  · exact h.symm

/-- **The ends of the occurrence through `V`** in the contraction are the images of the far ends of
the two occurrences at `V`. -/
theorem incident_g {Y' : S.D.SourceVertex} (h : Incident S.D (S.edgeMap (S.fc hM).1) Y') :
    Y' = S.vmap (far V (S.fc hM)) ∨ Y' = S.vmap (far V (S.fo hM)) := by
  have hg : S.edgeMap (S.fc hM).1 = S.emap ⟨(S.fo hM).1, S.other_ne⟩ := by
    unfold edgeMap
    rw [S.mu_of_eq rfl]
    congr 1
    exact Subtype.ext (S.partner_sourceEdge_c V.1.2)
  rw [hg] at h
  have hEnds := GluingContraction.sourceEnds_sourceEdgeMap data (contracted := S.c) rfl
    (GluingContraction.fst_ne_snd S.c) S.hOne ⟨(S.fo hM).1, S.other_ne⟩
  have hV : S.vmap V = S.vmap (far V (S.fc hM)) := by
    rw [far_fc]; exact S.vmap_cNbr V hM.onX
  have key : ∀ Z : data.SourceVertex, Incident data (S.fo hM).1 Z →
      S.vmap Z = S.vmap (far V (S.fc hM)) ∨ S.vmap Z = S.vmap (far V (S.fo hM)) := by
    intro Z hZ
    rcases eq_or_eq_otherEnd data (S.incident_fo hM) hZ with h | h
    · rw [h]; exact Or.inl hV
    · rw [h]; exact Or.inr rfl
  rcases h with h | h
  · rw [congrArg Prod.fst hEnds] at h
    rcases key _ (incident_left data _) with h' | h'
    · exact Or.inl (h.symm.trans h')
    · exact Or.inr (h.symm.trans h')
  · rw [congrArg Prod.snd hEnds] at h
    rcases key _ (incident_right data _) with h' | h'
    · exact Or.inl (h.symm.trans h')
    · exact Or.inr (h.symm.trans h')

/-! ## 2.  The side function -/

/-- **A walk of the row through `V` from an end**, with the index `i` of the occurrence `g`
through `V` and the occurrence `fs` at `V` whose far end the walk enters `g` at. -/
structure SideSetup where
  /-- The first occurrence. -/
  ê₀ : S.D.SourceEdge
  /-- The vertex it is entered at, an end of the row. -/
  Â₀ : S.D.SourceVertex
  h₀ : Incident S.D ê₀ Â₀
  hNd : ¬ IsDangling S.D ê₀
  hEnd : ¬ Continues S.D M' Â₀
  hRow : markedRow M' (⟨ê₀, hNd⟩ : NonDanglingEdge S.D) = S.rowMap hM (markedRow M (S.fc hM))
  /-- The index of `g`. -/
  i : ℕ
  hi : i ≤ stop h₀ hNd hEnd
  hg : S.edgeMap (S.fc hM).1 = E (M := M') ê₀ Â₀ i
  /-- The occurrence at `V` on the side of the start. -/
  fs : NonDanglingEdge data
  hfs : S.AtV hM fs
  hOrient : A (M := M') ê₀ Â₀ i = S.vmap (far V fs)

variable {S hM} (W : S.SideSetup hM)

/-- **The side of the walk before `g`**: an occurrence whose image comes earlier than `i` in the
walk, or `fs` itself. -/
def SideSetup.Side (f : NonDanglingEdge data) : Prop :=
  (∃ j < W.i, S.edgeMap f.1 = E (M := M') W.ê₀ W.Â₀ j) ∨ f = W.fs

/-- The occurrence at `V` on the side of the start maps to `g`. -/
theorem SideSetup.hgs : S.edgeMap W.fs.1 = E (M := M') W.ê₀ W.Â₀ W.i := by
  rcases W.hfs with h | h <;> rw [h]
  · exact W.hg
  · rw [S.edgeMap_fo hM]; exact W.hg

/-- **The key step**: across a vertex where the row continues, the side does not change. -/
theorem SideSetup.side_step {f f' : NonDanglingEdge data} {j : ℕ}
    (hj : j < stop W.h₀ W.hNd W.hEnd)
    (hf : S.edgeMap f.1 = E (M := M') W.ê₀ W.Â₀ j)
    (hf' : S.edgeMap f'.1 = E (M := M') W.ê₀ W.Â₀ (j + 1))
    {Y : data.SourceVertex} (hYx : Y.1.1 ≠ S.x) (hY : S.vmap Y = exit (M := M') W.ê₀ W.Â₀ j)
    (hfY : Incident data f.1 Y) (hf'Y : Incident data f'.1 Y) : W.Side f ↔ W.Side f' := by
  rcases Nat.lt_or_ge (j + 1) W.i with hlt | hge
  · exact ⟨fun _ ↦ Or.inl ⟨j + 1, hlt, hf'⟩, fun _ ↦ Or.inl ⟨j, by omega, hf⟩⟩
  rcases Nat.eq_or_lt_of_le hge with heq | hgt
  · -- `j + 1 = i`: `f'` is at `V`, and it is the one at the entry, i.e. `fs`
    have hf'fc : S.edgeMap f'.1 = S.edgeMap (S.fc hM).1 := by rw [hf', ← heq, W.hg]
    have hf'V := S.atV_of_edgeMap_eq hM hf'fc
    have hYfar : Y = far V W.fs := by
      refine (S.vmap_inj hYx (S.far_not_over_x hM W.hfs)).mp ?_
      rw [hY, ← W.hOrient, heq, A_succ (continues_of_lt_stop W.h₀ W.hNd W.hEnd hj)]
    have hf's : f' = W.fs := by
      by_contra hne
      exact S.not_incident_far hM W.hfs hf'V (Ne.symm hne) (hYfar ▸ hf'Y)
    exact ⟨fun _ ↦ Or.inr hf's, fun _ ↦ Or.inl ⟨j, by omega, hf⟩⟩
  · -- `j + 1 > i`: neither is on the side
    have hnot : ∀ g : NonDanglingEdge data, ∀ l, W.i < l + 1 → l ≤ stop W.h₀ W.hNd W.hEnd →
        S.edgeMap g.1 = E (M := M') W.ê₀ W.Â₀ l →
        ¬ ∃ j' < W.i, S.edgeMap g.1 = E (M := M') W.ê₀ W.Â₀ j' := by
      rintro g l hl hlStop hgl ⟨j', hj', hgj'⟩
      have := E_injOn W.h₀ W.hNd W.hEnd (j := j') (i := l) hlStop (by have := W.hi; omega)
        (hgl.symm.trans hgj')
      omega
    constructor
    · rintro (h | h)
      · exact absurd h (hnot f j (by omega) hj.le hf)
      · rw [h] at hf hfY
        have hji : j = W.i := E_injOn W.h₀ W.hNd W.hEnd hj.le W.hi (hf.symm.trans W.hgs)
        have hYfar : Y = far V W.fs := by
          rcases eq_or_eq_otherEnd data (S.incident_of_atV hM W.hfs) hfY with h | h
          · exact absurd (h ▸ hM.onX) hYx
          · exact h
        exfalso
        apply MarkedWalk.otherEnd_ne (incident_A W.h₀ j)
        change exit (M := M') W.ê₀ W.Â₀ j = A (M := M') W.ê₀ W.Â₀ j
        rw [← hY, hji, W.hOrient, hYfar]
    · rintro (h | h)
      · exact absurd h (hnot f' (j + 1) (by omega) (by omega) hf')
      · rw [h] at hf'
        have := E_injOn W.h₀ W.hNd W.hEnd (by omega) W.hi (hf'.symm.trans W.hgs)
        omega

/-- The image of an occurrence in the fibre of the row through `V` is in the walk. -/
theorem SideSetup.exists_index_edgeMap {f : NonDanglingEdge data}
    (hf : S.rowMap hM (markedRow M f) = S.rowMap hM (markedRow M (S.fc hM))) :
    ∃ j ≤ stop W.h₀ W.hNd W.hEnd, S.edgeMap f.1 = E (M := M') W.ê₀ W.Â₀ j :=
  exists_index W.h₀ W.hNd W.hEnd (S.ndMap f) (hf.trans W.hRow.symm)

/-- `fs` is not incident to a source vertex over `x` other than `V`. -/
theorem SideSetup.fs_not_incident {Y : data.SourceVertex} (hYx : Y.1.1 = S.x) (hYV : Y ≠ V) :
    ¬ Incident data W.fs.1 Y := by
  intro hInc
  rcases eq_or_eq_otherEnd data (S.incident_of_atV hM W.hfs) hInc with h | h
  · exact hYV h
  · exact S.far_not_over_x hM W.hfs
      ((congrArg (fun X : data.SourceVertex ↦ X.1.1) h).symm.trans hYx)

/-- **The side is constant along marked consecutiveness** in the fibre of the row through `V`. -/
theorem SideSetup.side_invariant {f₁ f₂ : NonDanglingEdge data} (h : MarkedConsecutive data M f₁ f₂)
    (hf₁ : S.rowMap hM (markedRow M f₁) = S.rowMap hM (markedRow M (S.fc hM))) :
    W.Side f₁ ↔ W.Side f₂ := by
  obtain ⟨hne, Y, h₁, h₂, hY2, hYM⟩ := h
  by_cases hYx : Y.1.1 = S.x
  · have hYV : Y ≠ V := fun h ↦ hYM (h ▸ hM.mem)
    have hE : S.edgeMap f₁.1 = S.edgeMap f₂.1 := S.edgeMap_eq_of_incident_x hYx h₁ h₂
    have hn₁ : f₁ ≠ W.fs := fun h ↦ W.fs_not_incident hYx hYV (h ▸ h₁)
    have hn₂ : f₂ ≠ W.fs := fun h ↦ W.fs_not_incident hYx hYV (h ▸ h₂)
    unfold SideSetup.Side
    rw [hE]
    simp only [hn₁, hn₂, or_false]
  · obtain ⟨j₁, hj₁, hE₁⟩ := W.exists_index_edgeMap hf₁
    have hNe : S.edgeMap f₂.1 ≠ E (M := M') W.ê₀ W.Â₀ j₁ := by
      rw [← hE₁]
      exact fun h ↦ hne (Subtype.ext (S.edgeMap_injOn hYx h₁ h₂ h.symm))
    have hInc₁ : Incident S.D (E (M := M') W.ê₀ W.Â₀ j₁) (S.vmap Y) :=
      hE₁ ▸ S.incident_edgeMap hYx h₁
    have hInc₂ : Incident S.D (S.edgeMap f₂.1) (S.vmap Y) := S.incident_edgeMap hYx h₂
    have hCont : Continues S.D M' (S.vmap Y) :=
      ⟨by rw [S.nonDanglingValency_vmap hYx]; exact hY2, by rw [hM.marks Y hYx]; exact hYM⟩
    rcases adjacent_of_meet W.h₀ W.hNd W.hEnd hj₁ ((S.isDangling_edgeMap_iff f₂.1).not.mpr f₂.2)
        hNe hInc₁ hInc₂ hCont with ⟨hlt, hYexit, hE₂⟩ | ⟨i', rfl, hYexit, hE₂⟩
    · exact W.side_step hlt hE₁ hE₂ hYx hYexit h₁ h₂
    · exact (W.side_step (by omega) hE₂ hE₁ hYx hYexit h₂ h₁).symm

/-- The side is constant on the equivalence classes in the fibre. -/
theorem SideSetup.side_eqvGen {f₁ f₂ : NonDanglingEdge data}
    (h : Relation.EqvGen (MarkedConsecutive data M) f₁ f₂)
    (hf₁ : S.rowMap hM (markedRow M f₁) = S.rowMap hM (markedRow M (S.fc hM))) :
    W.Side f₁ ↔ W.Side f₂ := by
  induction h with
  | rel a b hab => exact W.side_invariant hab hf₁
  | refl a => exact Iff.rfl
  | symm a b hab ih =>
    have hRowEq : markedRow M a = markedRow M b := Quot.eqvGen_sound hab
    exact (ih (by rw [hRowEq]; exact hf₁)).symm
  | trans a b c hab _ ih₁ ih₂ =>
    have hRowEq : markedRow M a = markedRow M b := Quot.eqvGen_sound hab
    exact (ih₁ hf₁).trans (ih₂ (by rw [← hRowEq]; exact hf₁))

/-- The other occurrence at `V` is not on the side. -/
theorem SideSetup.not_side_other {f : NonDanglingEdge data} (hf : S.AtV hM f) (hne : f ≠ W.fs) :
    ¬ W.Side f := by
  have hgf : S.edgeMap f.1 = E (M := M') W.ê₀ W.Â₀ W.i := by
    rcases hf with h | h <;> rw [h]
    · exact W.hg
    · rw [S.edgeMap_fo hM]; exact W.hg
  rintro (⟨j, hj, hfj⟩ | h)
  · have := E_injOn W.h₀ W.hNd W.hEnd (by have := W.hi; omega) W.hi (hfj.symm.trans hgf)
    omega
  · exact hne h

/-- The other occurrence at `V`. -/
noncomputable def SideSetup.fo' : NonDanglingEdge data :=
  if W.fs = S.fc hM then S.fo hM else S.fc hM

/-- The other occurrence at `V` is at `V`. -/
theorem SideSetup.fo'_atV : S.AtV hM W.fo' := by
  unfold SideSetup.fo'
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The other occurrence at `V` is not `fs`. -/
theorem SideSetup.fo'_ne : W.fo' ≠ W.fs := by
  unfold SideSetup.fo'
  split_ifs with h
  · rw [h]; exact (S.fc_ne_fo hM).symm
  · exact Ne.symm h

/-- The row of `fs` contracts to the split row. -/
theorem SideSetup.row_fs : S.rowMap hM (markedRow M W.fs) = S.rowMap hM (markedRow M (S.fc hM)) := by
  rcases W.hfs with h | h <;> rw [h]
  exact (S.rowMap_eq_iff hM _ _).mpr (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩)

/-- The row of the other occurrence contracts to the split row. -/
theorem SideSetup.row_fo' : S.rowMap hM (markedRow M W.fo') = S.rowMap hM (markedRow M (S.fc hM)) := by
  rcases W.fo'_atV with h | h <;> rw [h]
  exact (S.rowMap_eq_iff hM _ _).mpr (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩)

/-- **The two rows through `V` are different.** -/
theorem SideSetup.row_fs_ne : markedRow M W.fs ≠ markedRow M W.fo' := by
  intro hEq
  have h := (W.side_eqvGen (Quot.eqvGen_exact hEq) W.row_fs).mp (Or.inr rfl)
  exact W.not_side_other W.fo'_atV W.fo'_ne h

/-- **The two rows through `V` are distinct**, given a side setup. -/
theorem fc_row_ne_fo_row (W : S.SideSetup hM) : markedRow M (S.fc hM) ≠ markedRow M (S.fo hM) := by
  have h := W.row_fs_ne
  unfold SideSetup.fo' at h
  split_ifs at h with hfs
  · rw [hfs] at h; exact h
  · rcases W.hfs with h' | h'
    · exact absurd h' hfs
    · rw [h'] at h; exact Ne.symm h

/-- **The row of `fs` is the side of the walk before `g`.** -/
theorem SideSetup.row_eq_iff_side {f : NonDanglingEdge data}
    (hf : S.rowMap hM (markedRow M f) = S.rowMap hM (markedRow M (S.fc hM))) :
    markedRow M f = markedRow M W.fs ↔ W.Side f := by
  constructor
  · intro hEq
    exact (W.side_eqvGen (Quot.eqvGen_exact hEq.symm) W.row_fs).mp (Or.inr rfl)
  · intro hSide
    by_contra hne
    -- then `f` lies on the other row through `V`
    have hOther : markedRow M f = markedRow M W.fo' := by
      have hfs' := W.hfs
      have hfo' := W.fo'_atV
      have hne' := W.fo'_ne
      rcases (S.rowMap_eq_iff hM _ _).mp hf with h | ⟨h₁, -⟩
      · rcases hfs' with h' | h' <;> rcases hfo' with h'' | h''
        · exact absurd (h''.trans h'.symm) hne'
        · rw [h'] at hne; exact absurd h hne
        · rw [h'']; exact h
        · exact absurd (h''.trans h'.symm) hne'
      · rcases hfs' with h' | h' <;> rcases hfo' with h'' | h'' <;> rcases h₁ with h₁ | h₁
        all_goals first
          | exact absurd (h''.trans h'.symm) hne'
          | (rw [h'] at hne; exact absurd h₁ hne)
          | (rw [h'']; exact h₁)
    have := (W.side_eqvGen (Quot.eqvGen_exact hOther.symm) W.row_fo').mpr hSide
    exact W.not_side_other W.fo'_atV W.fo'_ne this

end Site

end DivalentContraction

end DraismaVargas.Count.MarkedCountGeneral
