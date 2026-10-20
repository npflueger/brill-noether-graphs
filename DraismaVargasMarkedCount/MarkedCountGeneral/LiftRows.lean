module

public import DraismaVargasMarkedCount.MarkedCountGeneral.LiftFrame

@[expose] public section

/-!
# The drop lemma: the identification of the lift with the subdivided core (I5)

At a position `P` (module `LiftFrame`), the marked rows and branch vertices of the subdivided datum
are labelled by the slots and vertices of `subdivide core s`:

* rows (`rowEquiv`): the two rows through `V'` are `cs s` (the one of the occurrence over `c'`,
  on the side of `tail s`) and `last p`; every other row is the old row it contracts to
  (`rowMap`, then the contraction isomorphism `ρ`);
* branch vertices (`vertexEquiv`): `V'` is `last n`, every other one the old branch vertex it
  contracts to;
* incidences (`incidence`): away from `V'` and the two rows, those of `κ`; at `V'`, one each on the
  two rows; on the two rows, the occurrences at a branch vertex other than `V'` are read on the walk
  (`count_fc`: the row `cs s` meets a branch vertex other than `V'` only at the start of the walk).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction
open DraismaVargas.Count.MarkedCountGeneral.MarkedWalk
open GenusSixExistence.Tripod.Gadget (subdivide subdivide_tail_castSucc subdivide_head_castSucc)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Incidence counts under an isomorphism -/

section Transport

variable {target₁ target₂ : CFGraph} {degree : ℕ} {first : GluingDatum target₁ degree}
  {second : GluingDatum target₂ degree} {marks₁ : Finset first.SourceVertex}
  {marks₂ : Finset second.SourceVertex} (iso : GeometricDatumIso first second)
  (hConn : first.Connected) (hMarks : ∀ vertex, iso.sourceVertexEquiv vertex ∈ marks₂ ↔ vertex ∈ marks₁)

include hConn hMarks in
/-- **Incidence counts are invariant under an isomorphism.** -/
theorem markedIncidenceCount_map (vertex : first.SourceVertex) (path : MarkedStablePath first marks₁) :
    markedIncidenceCount second marks₂ (iso.sourceVertexEquiv vertex)
        (markedStablePathEquiv iso hConn hMarks path) =
      markedIncidenceCount first marks₁ vertex path := by
  classical
  unfold markedIncidenceCount
  symm
  refine Finset.card_bij (fun e _ ↦ iso.nonDanglingEdgeEquiv hConn e) ?_ ?_ ?_
  · intro e he
    obtain ⟨hInc, hRow⟩ := Finset.mem_filter.mp he
    rw [StablePathCount.mem_incidentEdges] at hInc
    refine Finset.mem_filter.mpr ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr ?_, ?_⟩
    · exact (iso.incident_map_iff _ _).mpr hInc
    · rw [← hRow]; rfl
  · intro e _ f _ h
    exact (iso.nonDanglingEdgeEquiv hConn).injective h
  · intro f hf
    obtain ⟨hInc, hRow⟩ := Finset.mem_filter.mp hf
    rw [StablePathCount.mem_incidentEdges] at hInc
    refine ⟨(iso.nonDanglingEdgeEquiv hConn).symm f, Finset.mem_filter.mpr ⟨?_, ?_⟩, by simp⟩
    · rw [StablePathCount.mem_incidentEdges]
      rw [← iso.incident_map_iff]
      convert hInc using 1
      exact congrArg Subtype.val ((iso.nonDanglingEdgeEquiv hConn).apply_symm_apply f)
    · apply (markedStablePathEquiv iso hConn hMarks).injective
      rw [← hRow, markedStablePathEquiv_markedRow, Equiv.apply_symm_apply]

end Transport

namespace LiftSmooth

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {s : Fin p} {κ : TypedFrame core mark types degree} (P : Pos s κ)

/-! ## 2.  Rows -/

/-- The rows of the contraction, read in `κ`. -/
noncomputable abbrev ρ : MarkedStablePath (S P).D (MD P) ≃ MarkedStablePath κ.data (M κ) :=
  markedStablePathEquiv (ι P) (S_valid P).1 (hMarksι P)

/-- The row through `V'` over `c'`. -/
noncomputable abbrev rfc : MarkedStablePath (D P) (MM P) := markedRow (MM P) ((S P).fc (markHyp P))

/-- The other row through `V'`. -/
noncomputable abbrev rfo : MarkedStablePath (D P) (MM P) := markedRow (MM P) ((S P).fo (markHyp P))

/-- The row of the contraction. -/
noncomputable abbrev rmap : MarkedStablePath (D P) (MM P) → MarkedStablePath (S P).D (MD P) :=
  (S P).rowMap (markHyp P)

/-- The row `cs s` contracts to the row `s` of `κ`. -/
theorem ρ_rfc : ρ P (rmap P (rfc P)) = κ.ident.row.symm s := by
  change ρ P (markedRow (MD P) ((S P).ndMap ((S P).fc (markHyp P)))) = _
  have hND : ¬ IsDangling (S P).D ((S P).edgeMap ((S P).fc (markHyp P)).1) :=
    ((S P).isDangling_edgeMap_iff _).not.mpr ((S P).fc (markHyp P)).2
  have hnd : ¬ IsDangling (S P).D ((ι P).sourceEdgeEquiv.symm (g P)) :=
    fun h ↦ hND (by rw [edgeMap_fc']; exact h)
  have h : (S P).ndMap ((S P).fc (markHyp P)) = ⟨(ι P).sourceEdgeEquiv.symm (g P), hnd⟩ :=
    Subtype.ext (edgeMap_fc' P)
  rw [h]
  refine (markedStablePathEquiv_markedRow _ _ _ _).trans ?_
  have h' : (ι P).nonDanglingEdgeEquiv (S_valid P).1 ⟨(ι P).sourceEdgeEquiv.symm (g P), hnd⟩ =
      ⟨Ej s κ P.i, not_isDangling_E (start_nd s κ) P.i⟩ :=
    Subtype.ext (Equiv.apply_symm_apply _ _)
  rw [h']
  exact (markedRow_E (start_incident s κ) (start_nd s κ) P.i).trans (start_row s κ)

/-- The rows contracting to the row `s` are the two rows through `V'`. -/
theorem rmap_eq_iff (r : MarkedStablePath (D P) (MM P)) :
    rmap P r = rmap P (rfc P) ↔ r = rfc P ∨ r = rfo P := by
  rw [(S P).rowMap_eq_iff]
  unfold Site.RowRel
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact h
  · intro h
    exact Or.inr ⟨h, Or.inl rfl⟩

/-- The row `last p` contracts to the row `s` of `κ`. -/
theorem rmap_rfo : rmap P (rfo P) = rmap P (rfc P) := (rmap_eq_iff P _).mpr (Or.inr rfl)

/-- Off the two rows through `V'`, the old label is not `s`. -/
theorem label_ne {r : MarkedStablePath (D P) (MM P)} (h₁ : r ≠ rfc P) (h₂ : r ≠ rfo P) :
    κ.ident.row (ρ P (rmap P r)) ≠ s := by
  intro h
  have h' : rmap P r = rmap P (rfc P) := by
    apply (ρ P).injective
    rw [ρ_rfc]
    exact (Equiv.eq_symm_apply κ.ident.row).mpr h
  rcases (rmap_eq_iff P r).mp h' with h | h
  · exact h₁ h
  · exact h₂ h

open Classical in
/-- **The labels of the rows.** -/
noncomputable def rowLab (r : MarkedStablePath (D P) (MM P)) : Fin (p + 1) :=
  if r = rfc P then s.castSucc else if r = rfo P then Fin.last p
  else (κ.ident.row (ρ P (rmap P r))).castSucc

/-- The row over `c'` is labelled `cs s`. -/
theorem rowLab_fc : rowLab P (rfc P) = s.castSucc := by simp [rowLab]

/-- The other row through `V'` is labelled `last p`. -/
theorem rowLab_fo : rowLab P (rfo P) = Fin.last p := by
  simp [rowLab, (row_fc_ne_fo P).symm]

/-- The other rows keep their old labels. -/
theorem rowLab_of_ne {r : MarkedStablePath (D P) (MM P)} (h₁ : r ≠ rfc P) (h₂ : r ≠ rfo P) :
    rowLab P r = (κ.ident.row (ρ P (rmap P r))).castSucc := by
  simp [rowLab, h₁, h₂]

/-- The row labels are a bijection. -/
theorem rowLab_bijective : Function.Bijective (rowLab P) := by
  have hcs : ∀ j : Fin p, j.castSucc ≠ Fin.last p := fun j ↦ (Fin.castSucc_lt_last j).ne
  constructor
  · intro r r' h
    by_cases h₁ : r = rfc P
    · by_cases h₁' : r' = rfc P
      · rw [h₁, h₁']
      · by_cases h₂' : r' = rfo P
        · rw [h₁, h₂', rowLab_fc, rowLab_fo] at h; exact absurd h (hcs s)
        · rw [h₁, rowLab_fc, rowLab_of_ne P h₁' h₂'] at h
          exact absurd (Fin.castSucc_injective _ h).symm (label_ne P h₁' h₂')
    · by_cases h₂ : r = rfo P
      · by_cases h₁' : r' = rfc P
        · rw [h₂, h₁', rowLab_fc, rowLab_fo] at h; exact absurd h.symm (hcs s)
        · by_cases h₂' : r' = rfo P
          · rw [h₂, h₂']
          · rw [h₂, rowLab_fo, rowLab_of_ne P h₁' h₂'] at h; exact absurd h.symm (hcs _)
      · rw [rowLab_of_ne P h₁ h₂] at h
        by_cases h₁' : r' = rfc P
        · rw [h₁', rowLab_fc] at h
          exact absurd (Fin.castSucc_injective _ h) (label_ne P h₁ h₂)
        · by_cases h₂' : r' = rfo P
          · rw [h₂', rowLab_fo] at h; exact absurd h (hcs _)
          · rw [rowLab_of_ne P h₁' h₂'] at h
            have h3 := κ.ident.row.injective (Fin.castSucc_injective _ h)
            have h4 := (S P).rowMap_eq_iff (markHyp P) r r'
            rcases h4.mp ((ρ P).injective h3) with h5 | ⟨h5, -⟩
            · exact h5
            · rcases h5 with h5 | h5
              · exact absurd h5 h₁
              · exact absurd h5 h₂
  · intro ℓ
    induction ℓ using Fin.lastCases with
    | last => exact ⟨rfo P, rowLab_fo P⟩
    | cast j =>
      by_cases hj : j = s
      · subst hj; exact ⟨rfc P, rowLab_fc P⟩
      · obtain ⟨r, hr⟩ := (S P).rowMap_surjective (markHyp P) ((ρ P).symm (κ.ident.row.symm j))
        have h₁ : r ≠ rfc P := by
          intro h
          apply hj
          change rmap P r = _ at hr
          rw [h] at hr
          have := congrArg (fun x ↦ κ.ident.row (ρ P x)) hr
          simp only [Equiv.apply_symm_apply] at this
          rw [← this, ρ_rfc, Equiv.apply_symm_apply]
        have h₂ : r ≠ rfo P := by
          intro h
          apply hj
          change rmap P r = _ at hr
          rw [h, rmap_rfo] at hr
          have := congrArg (fun x ↦ κ.ident.row (ρ P x)) hr
          simp only [Equiv.apply_symm_apply] at this
          rw [← this, ρ_rfc, Equiv.apply_symm_apply]
        refine ⟨r, ?_⟩
        rw [rowLab_of_ne P h₁ h₂]
        change (κ.ident.row (ρ P ((S P).rowMap (markHyp P) r))).castSucc = _
        rw [hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **The rows of the lift**, labelled by the slots of `subdivide core s`. -/
noncomputable def rowEquiv : MarkedStablePath (D P) (MM P) ≃ Fin (p + 1) :=
  Equiv.ofBijective _ (rowLab_bijective P)

/-- The row labelling, unfolded. -/
theorem rowEquiv_apply (r : MarkedStablePath (D P) (MM P)) : rowEquiv P r = rowLab P r := rfl

/-- The row labelled `cs s` is the row over `c'`. -/
theorem rowEquiv_symm_cs : (rowEquiv P).symm s.castSucc = rfc P := by
  rw [Equiv.symm_apply_eq]; exact (rowLab_fc P).symm

/-- The row labelled `last p` is the other row through `V'`. -/
theorem rowEquiv_symm_last : (rowEquiv P).symm (Fin.last p) = rfo P := by
  rw [Equiv.symm_apply_eq]; exact (rowLab_fo P).symm

/-! ## 3.  Branch vertices -/

/-- The old branch vertex of a branch vertex of the contraction. -/
noncomputable def brι (B : MarkedBranchVertex (S P).D (MD P)) : MarkedBranchVertex κ.data (M κ) :=
  ⟨(ι P).sourceVertexEquiv B.1, by
    rcases B.2 with h | h
    · left; rw [GeometricDatumIso.nonDanglingValency_map (ι P) (S_valid P).1]; exact h
    · right; exact (hMarksι P B.1).mpr h⟩

/-- The branch-vertex dictionary is injective. -/
theorem brι_injective : Function.Injective (brι P) := fun _ _ h ↦
  Subtype.ext ((ι P).sourceVertexEquiv.injective (congrArg Subtype.val h))

/-- The branch-vertex dictionary is surjective. -/
theorem brι_surjective : Function.Surjective (brι P) := by
  intro B
  refine ⟨⟨(ι P).sourceVertexEquiv.symm B.1, ?_⟩, Subtype.ext (Equiv.apply_symm_apply _ _)⟩
  rcases B.2 with h | h
  · left
    rw [← GeometricDatumIso.nonDanglingValency_map (ι P) (S_valid P).1, Equiv.apply_symm_apply]
    exact h
  · right; rw [← hMarksι P, Equiv.apply_symm_apply]; exact h

/-- The old label of a branch vertex other than `V'`. -/
noncomputable def oldLab (B : {B : MarkedBranchVertex (D P) (MM P) // B.1 ≠ V' P}) : Fin n :=
  κ.ident.vertex (brι P ((S P).branchEquiv (markHyp P) B))

/-- The old labels are injective. -/
theorem oldLab_injective : Function.Injective (oldLab P) := fun _ _ h ↦
  ((S P).branchEquiv (markHyp P)).injective (brι_injective P (κ.ident.vertex.injective h))

open Classical in
/-- **The labels of the branch vertices.** -/
noncomputable def vertLab (B : MarkedBranchVertex (D P) (MM P)) : Fin (n + 1) :=
  if h : B.1 = V' P then Fin.last n else (oldLab P ⟨B, h⟩).castSucc

/-- `V'` is labelled by the new vertex. -/
theorem vertLab_V' {B : MarkedBranchVertex (D P) (MM P)} (h : B.1 = V' P) :
    vertLab P B = Fin.last n := by simp [vertLab, h]

/-- The other branch vertices keep their old labels. -/
theorem vertLab_of_ne {B : MarkedBranchVertex (D P) (MM P)} (h : B.1 ≠ V' P) :
    vertLab P B = (oldLab P ⟨B, h⟩).castSucc := by simp [vertLab, h]

/-- The vertex labels are a bijection. -/
theorem vertLab_bijective : Function.Bijective (vertLab P) := by
  constructor
  · intro B B' hBB
    by_cases h : B.1 = V' P <;> by_cases h' : B'.1 = V' P
    · exact Subtype.ext (h.trans h'.symm)
    · rw [vertLab_V' P h, vertLab_of_ne P h'] at hBB
      exact absurd hBB.symm (Fin.castSucc_lt_last _).ne
    · rw [vertLab_of_ne P h, vertLab_V' P h'] at hBB
      exact absurd hBB (Fin.castSucc_lt_last _).ne
    · rw [vertLab_of_ne P h, vertLab_of_ne P h'] at hBB
      exact congrArg Subtype.val (oldLab_injective P (Fin.castSucc_injective _ hBB))
  · intro u
    induction u using Fin.lastCases with
    | last => exact ⟨⟨V' P, Or.inr (markHyp P).mem⟩, vertLab_V' P rfl⟩
    | cast u =>
      obtain ⟨Bd, hBd⟩ := brι_surjective P (κ.ident.vertex.symm u)
      obtain ⟨B, rfl⟩ := ((S P).branchEquiv (markHyp P)).surjective Bd
      refine ⟨B.1, ?_⟩
      rw [vertLab_of_ne P B.2]
      congr 1
      unfold oldLab
      rw [hBd, Equiv.apply_symm_apply]

/-- **The branch vertices of the lift**, labelled by the vertices of `subdivide core s`. -/
noncomputable def vertexEquiv : MarkedBranchVertex (D P) (MM P) ≃ Fin (n + 1) :=
  Equiv.ofBijective _ (vertLab_bijective P)

/-- The vertex labelling, unfolded. -/
theorem vertexEquiv_apply (B : MarkedBranchVertex (D P) (MM P)) :
    vertexEquiv P B = vertLab P B := rfl

/-! ## 4.  Incidences -/

/-- The surviving occurrences at `V'`. -/
theorem incidentEdges_V' : StablePathCount.incidentEdges (D P) (V' P) =
    {(S P).fc (markHyp P), (S P).fo (markHyp P)} := by
  ext f
  rw [StablePathCount.mem_incidentEdges, (S P).incident_x_iff (V' P) rfl, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

open Classical in
/-- **The rows at `V'`.** -/
theorem count_V' (r : MarkedStablePath (D P) (MM P)) :
    markedIncidenceCount (D P) (MM P) (V' P) r =
      (if rfc P = r then 1 else 0) + (if rfo P = r then 1 else 0) := by
  unfold markedIncidenceCount
  rw [incidentEdges_V', Finset.filter_insert, Finset.filter_singleton]
  have hne := (S P).fc_ne_fo (markHyp P)
  split_ifs with h₁ h₂ h₂
  · exfalso; exact row_fc_ne_fo P (h₁.trans h₂.symm)
  · simp
  · simp
  · simp

/-- **The row `cs s` is the side of the walk before `g`** (module `DropSide`). -/
theorem incident_iff_side (f : NonDanglingEdge (D P)) :
    markedRow (MM P) f = rfc P ↔ (sideSetup P).Side f := by
  constructor
  · intro h
    exact ((sideSetup P).row_eq_iff_side (congrArg (rmap P) h)).mp h
  · intro h
    refine ((sideSetup P).row_eq_iff_side ?_).mpr h
    rcases h with ⟨j, -, hj⟩ | h
    · change markedRow (MD P) ((S P).ndMap f) = markedRow (MD P) ((S P).ndMap ((S P).fc (markHyp P)))
      have h1 : (S P).ndMap f = ⟨E (M := MD P) (ê' P) (Â' P) j, not_isDangling_E (hNd' P) _⟩ :=
        Subtype.ext hj
      rw [h1, markedRow_E (h₀' P) (hNd' P)]
      exact (sideSetup P).hRow
    · rw [h]; rfl

/-- The image of a branch vertex other than `V'` is a vertex where no row of the contraction
continues. -/
theorem not_continues_vmap {B : MarkedBranchVertex (D P) (MM P)} (h : B.1 ≠ V' P) :
    ¬ Continues (S P).D (MD P) ((S P).vmap B.1) :=
  LiftSmooth.not_continues_branch ((S P).branchEquiv (markHyp P) ⟨B, h⟩)

/-- A branch vertex other than `V'` contracts to the start of the walk exactly when it is labelled `tail s`. -/
theorem vmap_eq_start_iff {B : MarkedBranchVertex (D P) (MM P)} (h : B.1 ≠ V' P) :
    (S P).vmap B.1 = Â' P ↔ core.tail s = oldLab P ⟨B, h⟩ := by
  unfold oldLab
  constructor
  · intro h'
    have hB : brι P ((S P).branchEquiv (markHyp P) ⟨B, h⟩) = B₀ s κ := Subtype.ext (by
      change (ι P).sourceVertexEquiv ((S P).vmap B.1) = A₀ s κ
      rw [h']; exact Equiv.apply_symm_apply _ _)
    rw [hB, Equiv.apply_symm_apply]
  · intro h'
    have hB : brι P ((S P).branchEquiv (markHyp P) ⟨B, h⟩) = B₀ s κ :=
      (κ.ident.vertex.symm_apply_apply _).symm.trans (congrArg _ h'.symm)
    have h2 := congrArg Subtype.val hB
    change (ι P).sourceVertexEquiv ((S P).vmap B.1) = A₀ s κ at h2
    change _ = (ι P).sourceVertexEquiv.symm (A₀ s κ)
    rw [Equiv.eq_symm_apply]
    exact h2

/-- **The row `cs s` meets a branch vertex other than `V'` only at the start of the walk.** -/
theorem count_fc {B : MarkedBranchVertex (D P) (MM P)} (h : B.1 ≠ V' P) :
    markedIncidenceCount (D P) (MM P) B.1 (rfc P) =
      if core.tail s = oldLab P ⟨B, h⟩ then 1 else 0 := by
  classical
  have hBx : B.1.1.1 ≠ (S P).x := (S P).not_over_x (markHyp P) B h
  have hNC := not_continues_vmap P h
  have hiStop : P.i ≤ stop (h₀' P) (hNd' P) (hEnd' P) := (sideSetup P).hi
  have hFilter : (StablePathCount.incidentEdges (D P) B.1).filter
      (fun e ↦ markedRow (MM P) e = rfc P) =
      (StablePathCount.incidentEdges (D P) B.1).filter (fun e ↦ (sideSetup P).Side e) :=
    Finset.filter_congr fun f _ ↦ incident_iff_side P f
  unfold markedIncidenceCount
  rw [hFilter]
  -- `fc` at `B` forces `i = 0` and `B` at the start
  have hcN : (S P).vmap ((S P).cNbr (V' P)) = A (M := MD P) (ê' P) (Â' P) P.i :=
    (congrArg (S P).vmap ((S P).far_fc (markHyp P))).symm.trans (hOrient' P).symm
  have hfc : Incident (D P) ((S P).fc (markHyp P)).1 B.1 → P.i = 0 ∧ (S P).vmap B.1 = Â' P := by
    intro hInc
    rcases ((S P).incident_c_iff _ _).mp hInc with h' | h'
    · exact absurd (congrArg (fun X : (D P).SourceVertex ↦ X.1.1) h') hBx
    · have hv : (S P).vmap B.1 = A (M := MD P) (ê' P) (Â' P) P.i := by
        rw [h']; exact hcN
      have hi0 : P.i = 0 := by
        by_contra hne
        exact hNC (hv ▸ continues_A (h₀' P) (hNd' P) (hEnd' P) hiStop hne)
      refine ⟨hi0, ?_⟩
      rw [hv]
      have : A (M := MD P) (ê' P) (Â' P) P.i = A (M := MD P) (ê' P) (Â' P) 0 := by rw [hi0]
      exact this
  -- an occurrence before `g` at `B` forces `j = 0` and `B` at the start
  have hpre : ∀ f : NonDanglingEdge (D P), Incident (D P) f.1 B.1 → ∀ j < P.i,
      (S P).edgeMap f.1 = E (M := MD P) (ê' P) (Â' P) j → j = 0 ∧ (S P).vmap B.1 = Â' P := by
    intro f hf j hj hfj
    have hInc : Incident (S P).D (E (M := MD P) (ê' P) (Â' P) j) ((S P).vmap B.1) :=
      hfj ▸ (S P).incident_edgeMap hBx hf
    exact eq_zero_of_incident (h₀' P) (hNd' P) (hEnd' P) (lt_of_lt_of_le hj hiStop) hInc hNC
  by_cases hStart : (S P).vmap B.1 = Â' P
  · rw [ite_eq_left ((vmap_eq_start_iff P h).mp hStart)]
    rw [Finset.card_eq_one]
    by_cases hi0 : P.i = 0
    · refine ⟨(S P).fc (markHyp P), ?_⟩
      ext f
      simp only [Finset.mem_filter, Finset.mem_singleton]
      rw [StablePathCount.mem_incidentEdges]
      constructor
      · rintro ⟨-, ⟨j, hj, -⟩ | hf⟩
        · have : j < P.i := hj
          omega
        · exact hf
      · rintro rfl
        refine ⟨?_, Or.inr rfl⟩
        have h3 : A (M := MD P) (ê' P) (Â' P) P.i = Â' P := by rw [hi0]; rfl
        have hBc : B.1 = (S P).cNbr (V' P) :=
          ((S P).vmap_inj hBx (S P).w_ne_x).mp (hStart.trans (h3.symm.trans hcN.symm))
        rw [hBc]
        exact ((S P).incident_c_iff _ _).mpr (Or.inr rfl)
    · obtain ⟨e, he, hee⟩ := (S P).exists_incident_edgeMap hBx (hStart ▸ h₀' P)
      have heNd : ¬ IsDangling (D P) e := ((S P).isDangling_edgeMap_iff e).not.mp (hee ▸ hNd' P)
      refine ⟨⟨e, heNd⟩, ?_⟩
      ext f
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hf, hside⟩
        refine Finset.mem_singleton.mpr ?_
        rw [StablePathCount.mem_incidentEdges] at hf
        rcases hside with ⟨j, hj, hfj⟩ | hf'
        · have hj0 := (hpre f hf j hj hfj).1
          subst hj0
          have hfj' : (S P).edgeMap f.1 = ê' P := hfj
          exact Subtype.ext ((S P).edgeMap_injOn (e := f.1) (f := e) hBx hf he (hfj'.trans hee.symm))
        · subst hf'; exact absurd (hfc hf).1 hi0
      · intro hfm
        rw [Finset.mem_singleton.mp hfm]
        exact ⟨(StablePathCount.mem_incidentEdges _ _ _).mpr he,
          Or.inl ⟨0, Nat.pos_of_ne_zero hi0, hee⟩⟩
  · rw [ite_eq_right fun h' ↦ hStart ((vmap_eq_start_iff P h).mpr h')]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro f hf hSide
    rw [StablePathCount.mem_incidentEdges] at hf
    rcases hSide with ⟨j, hj, hfj⟩ | hf'
    · exact hStart (hpre f hf j hj hfj).2
    · subst hf'; exact hStart (hfc hf).2

/-- The incidence of the row `cs s` of the subdivided core at an old vertex. -/
theorem coreIncidence_cs_s (u : Fin n) :
    coreIncidence (subdivide core s) u.castSucc s.castSucc = if core.tail s = u then 1 else 0 := by
  unfold coreIncidence
  rw [subdivide_tail_castSucc, subdivide_head_castSucc, ite_eq_left rfl]
  have hne : Fin.last n ≠ u.castSucc := (Fin.castSucc_lt_last u).ne'
  simp only [Fin.castSucc_inj, hne, ite_false, add_zero]

/-- **The incidences of the lift**: those of `subdivide core s`. -/
theorem incidence (B : MarkedBranchVertex (D P) (MM P)) (ℓ : Fin (p + 1)) :
    markedIncidenceCount (D P) (MM P) B.1 ((rowEquiv P).symm ℓ) =
      coreIncidence (subdivide core s) (vertexEquiv P B) ℓ := by
  classical
  rw [vertexEquiv_apply]
  by_cases hB : B.1 = V' P
  · rw [vertLab_V' P hB, hB, count_V']
    induction ℓ using Fin.lastCases with
    | last =>
      rw [rowEquiv_symm_last, DropSmooth.coreIncidence_last_last]
      simp [row_fc_ne_fo P]
    | cast j =>
      rw [DropSmooth.coreIncidence_last_castSucc]
      by_cases hj : j = s
      · subst hj
        rw [rowEquiv_symm_cs]
        simp [(row_fc_ne_fo P).symm]
      · have h₁ : rfc P ≠ (rowEquiv P).symm j.castSucc := by
          rw [← rowEquiv_symm_cs]
          exact fun h ↦ hj (Fin.castSucc_injective _ ((rowEquiv P).symm.injective h)).symm
        have h₂ : rfo P ≠ (rowEquiv P).symm j.castSucc := by
          rw [← rowEquiv_symm_last]
          exact fun h ↦ (Fin.castSucc_lt_last j).ne ((rowEquiv P).symm.injective h).symm
        simp [h₁, h₂, hj]
  · rw [vertLab_of_ne P hB]
    have hBx : B.1.1.1 ≠ (S P).x := (S P).not_over_x (markHyp P) B hB
    have hκ : ∀ r : MarkedStablePath (D P) (MM P),
        markedIncidenceCount (S P).D (MD P) ((S P).vmap B.1) (rmap P r) =
          coreIncidence core (oldLab P ⟨B, hB⟩) (κ.ident.row (ρ P (rmap P r))) := by
      intro r
      rw [← markedIncidenceCount_map (ι P) (S_valid P).1 (hMarksι P)]
      have := κ.ident.incidence (brι P ((S P).branchEquiv (markHyp P) ⟨B, hB⟩))
        (κ.ident.row (ρ P (rmap P r)))
      rw [Equiv.symm_apply_apply] at this
      exact this
    induction ℓ using Fin.lastCases with
    | last =>
      rw [rowEquiv_symm_last]
      have hsum := (S P).markedIncidenceCount_rowMap_fc (markHyp P) hBx (row_fc_ne_fo P)
      change markedIncidenceCount (S P).D (MD P) ((S P).vmap B.1) (rmap P (rfc P)) = _ at hsum
      rw [hκ, ρ_rfc, Equiv.apply_symm_apply, count_fc P hB] at hsum
      have hsplit := DropSmooth.coreIncidence_castSucc_split core s (oldLab P ⟨B, hB⟩)
      rw [coreIncidence_cs_s] at hsplit
      have hsum' : coreIncidence core (oldLab P ⟨B, hB⟩) s =
          (if core.tail s = oldLab P ⟨B, hB⟩ then 1 else 0) +
            markedIncidenceCount (D P) (MM P) B.1 (rfo P) := hsum
      omega
    | cast j =>
      by_cases hj : j = s
      · subst hj
        rw [rowEquiv_symm_cs, count_fc P hB, coreIncidence_cs_s]
      · have h₁ : (rowEquiv P).symm j.castSucc ≠ rfc P := by
          rw [← rowEquiv_symm_cs]
          exact fun h ↦ hj (Fin.castSucc_injective _ ((rowEquiv P).symm.injective h))
        have h₂ : (rowEquiv P).symm j.castSucc ≠ rfo P := by
          rw [← rowEquiv_symm_last]
          exact fun h ↦ (Fin.castSucc_lt_last j).ne ((rowEquiv P).symm.injective h)
        have hlab := rowLab_of_ne P h₁ h₂
        rw [← rowEquiv_apply, Equiv.apply_symm_apply] at hlab
        have hj' := (Fin.castSucc_injective _ hlab).symm
        rw [← (S P).markedIncidenceCount_rowMap_of_ne (markHyp P) hBx h₁ h₂]
        change markedIncidenceCount (S P).D (MD P) ((S P).vmap B.1) (rmap P _) = _
        rw [hκ, hj', DropSmooth.coreIncidence_castSucc_castSucc_of_ne core s _ hj]

end LiftSmooth

end DraismaVargas.Count.MarkedCountGeneral
